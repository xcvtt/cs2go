package main

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"math"
	"reflect"
	"strings"
	"unsafe"

	"golang.org/x/sys/windows"
)

func getProcessHandle(pid int) (windows.Handle, error) {
	return windows.OpenProcess(windows.PROCESS_VM_READ, false, uint32(pid))
}

func findProcessId(name string) (int, error) {
	snapshot, err := windows.CreateToolhelp32Snapshot(windows.TH32CS_SNAPPROCESS, 0)
	if err != nil {
		return 0, err
	}

	defer windows.CloseHandle(windows.Handle(snapshot))

	for {
		var process windows.ProcessEntry32
		process.Size = uint32(unsafe.Sizeof(process))
		if windows.Process32Next(windows.Handle(snapshot), &process) != nil {
			break
		}
		if windows.UTF16ToString(process.ExeFile[:]) == name {
			return int(process.ProcessID), nil
		}
	}
	return 0, fmt.Errorf("module not found")
}

func getModuleBaseAddress(pid int, moduleName string) (uintptr, error) {
	snapshot, err := windows.CreateToolhelp32Snapshot(windows.TH32CS_SNAPMODULE, uint32(pid))
	if err != nil {
		return 0, err
	}
	defer windows.CloseHandle(snapshot)

	var me32 windows.ModuleEntry32
	me32.Size = uint32(unsafe.Sizeof(me32))

	if windows.Module32First(snapshot, &me32) != nil {
		return 0, fmt.Errorf("Module32First failed")
	}

	for {
		if strings.EqualFold(windows.UTF16ToString(me32.Module[:]), moduleName) {
			return uintptr(me32.ModBaseAddr), nil
		}
		if windows.Module32Next(snapshot, &me32) != nil {
			break
		}
	}

	return 0, fmt.Errorf("module not found")
}

func read(process windows.Handle, address uintptr, value interface{}) error {
	var buffer []byte
	size := int(reflect.TypeOf(value).Elem().Size())
	buffer = make([]byte, size)
	bytesRead := uintptr(0)
	err := windows.ReadProcessMemory(process, address, &buffer[0], uintptr(len(buffer)), &bytesRead)
	if err != nil {
		return err
	}
	if bytesRead != uintptr(len(buffer)) {
		return fmt.Errorf("read %d bytes, expected %d", bytesRead, len(buffer))
	}
	switch v := value.(type) {
	case *int32:
		*v = int32(binary.LittleEndian.Uint32(buffer))
	case *uint32:
		*v = binary.LittleEndian.Uint32(buffer)
	case *float32:
		*v = math.Float32frombits(binary.LittleEndian.Uint32(buffer))
	case *int64:
		*v = int64(binary.LittleEndian.Uint64(buffer))
	case *uint64:
		*v = binary.LittleEndian.Uint64(buffer)
	case *float64:
		*v = math.Float64frombits(binary.LittleEndian.Uint64(buffer))
	case *uintptr:
		*v = uintptr(binary.LittleEndian.Uint64(buffer))
	case *string:
		*v = string(buffer[:bytesRead])
	case *Vector3:
		v.X = math.Float32frombits(binary.LittleEndian.Uint32(buffer[0:4]))
		v.Y = math.Float32frombits(binary.LittleEndian.Uint32(buffer[4:8]))
		v.Z = math.Float32frombits(binary.LittleEndian.Uint32(buffer[8:12]))
	default:
		err = binary.Read(bytes.NewReader(buffer), binary.LittleEndian, value)
		if err != nil {
			return err
		}
	}
	return nil
}

func findPattern(handle windows.Handle, moduleBase uintptr, pattern string) (uintptr, error) {
	moduleSize, err := getModuleSize(handle, moduleBase)
	if err != nil {
		return 0, err
	}

	buffer := make([]byte, moduleSize)
	var bytesRead uintptr
	err = windows.ReadProcessMemory(handle, moduleBase, &buffer[0], moduleSize, &bytesRead)
	if err != nil {
		return 0, err
	}

	patternBytes, mask := parsePattern(pattern)

	for i := 0; i < len(buffer)-len(patternBytes); i++ {
		found := true
		for j := 0; j < len(patternBytes); j++ {
			if mask[j] && buffer[i+j] != patternBytes[j] {
				found = false
				break
			}
		}
		if found {
			address := moduleBase + uintptr(i)
			return resolveRIP(buffer[i:], address), nil
		}
	}

	return 0, fmt.Errorf("pattern not found")
}

func parsePattern(pattern string) ([]byte, []bool) {
	parts := strings.Split(strings.TrimSpace(pattern), " ")
	patternBytes := make([]byte, len(parts))
	mask := make([]bool, len(parts))

	for i, part := range parts {
		if part == "??" {
			mask[i] = false
		} else {
			var b byte
			fmt.Sscanf(part, "%02X", &b)
			patternBytes[i] = b
			mask[i] = true
		}
	}

	return patternBytes, mask
}

func resolveRIP(buffer []byte, address uintptr) uintptr {
	var ripOffset int32
	var instructionLen int

	if len(buffer) >= 7 && buffer[0] == 0x48 && buffer[1] == 0x8D && buffer[2] == 0x0D {
		// LEA rcx, [rip+offset] - 48 8D 0D [4 bytes]
		ripOffset = int32(binary.LittleEndian.Uint32(buffer[3:7]))
		instructionLen = 7
	} else if len(buffer) >= 7 && buffer[0] == 0x48 && buffer[1] == 0x8D && buffer[2] == 0x05 {
		// LEA rax, [rip+offset] - 48 8D 05 [4 bytes]
		ripOffset = int32(binary.LittleEndian.Uint32(buffer[3:7]))
		instructionLen = 7
	} else if len(buffer) >= 7 && buffer[0] == 0x48 && buffer[1] == 0x89 && buffer[2] == 0x0D {
		// MOV [rip+offset], rcx - 48 89 0D [4 bytes]
		ripOffset = int32(binary.LittleEndian.Uint32(buffer[3:7]))
		instructionLen = 7
	} else if len(buffer) >= 7 && buffer[0] == 0x48 && buffer[1] == 0x8B && buffer[2] == 0x05 {
		// MOV rax, [rip+offset] - 48 8B 05 [4 bytes]
		ripOffset = int32(binary.LittleEndian.Uint32(buffer[3:7]))
		instructionLen = 7
	} else {
		// Default: assume RIP offset at position 3
		ripOffset = int32(binary.LittleEndian.Uint32(buffer[3:7]))
		instructionLen = 7
	}

	// Calculate: instruction address + instruction length + RIP offset
	return address + uintptr(instructionLen) + uintptr(ripOffset)
}

func getModuleSize(handle windows.Handle, moduleBase uintptr) (uintptr, error) {
	var dosHeader [64]byte
	var bytesRead uintptr
	err := windows.ReadProcessMemory(handle, moduleBase, &dosHeader[0], 64, &bytesRead)
	if err != nil {
		return 0, err
	}

	e_lfanew := binary.LittleEndian.Uint32(dosHeader[60:64])

	var ntHeaders [256]byte
	err = windows.ReadProcessMemory(handle, moduleBase+uintptr(e_lfanew), &ntHeaders[0], 256, &bytesRead)
	if err != nil {
		return 0, err
	}

	sizeOfImage := binary.LittleEndian.Uint32(ntHeaders[80:84])

	return uintptr(sizeOfImage), nil
}
