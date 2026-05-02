package main

import (
	"encoding/binary"
	"encoding/json"
	"fmt"
	"log"
	"math"
	"os"
	"runtime"
	"runtime/debug"
	"strconv"
	"strings"
	"syscall"
	"time"
	"unicode"
	"unsafe"

	"github.com/lxn/win"
	"github.com/ttacon/chalk"
	"golang.org/x/sys/windows"
)

type Matrix [4][4]float32

type Vector3 struct {
	X float32
	Y float32
	Z float32
}

func (v Vector3) Dist(other Vector3) float32 {
	return float32(math.Abs(float64(v.X-other.X)) + math.Abs(float64(v.Y-other.Y)) + math.Abs(float64(v.Z-other.Z)))
}

type Vector2 struct {
	X float32
	Y float32
}

type Rectangle struct {
	Top    float32
	Left   float32
	Right  float32
	Bottom float32
}

type Entity struct {
	Health   int32
	Team     int32
	Name     string
	Position Vector2
	Bones    map[string]Vector2
	HeadPos  Vector3
	Distance float32
	Rect     Rectangle
}

type Offset struct {
	DwViewMatrix           uintptr `json:"dwViewMatrix"`
	DwLocalPlayerPawn      uintptr `json:"dwLocalPlayerPawn"`
	DwEntityList           uintptr `json:"dwEntityList"`
	M_hPlayerPawn          uintptr `json:"m_hPlayerPawn"`
	M_iHealth              uintptr `json:"m_iHealth"`
	M_lifeState            uintptr `json:"m_lifeState"`
	M_iTeamNum             uintptr `json:"m_iTeamNum"`
	M_vOldOrigin           uintptr `json:"m_vOldOrigin"`
	M_pGameSceneNode       uintptr `json:"m_pGameSceneNode"`
	M_modelState           uintptr `json:"m_modelState"`
	M_boneArray            uintptr `json:"m_boneArray"`
	M_nodeToWorld          uintptr `json:"m_nodeToWorld"`
	M_sSanitizedPlayerName uintptr `json:"m_sSanitizedPlayerName"`
}

var (
	user32                     = windows.NewLazySystemDLL("user32.dll")
	gdi32                      = windows.NewLazySystemDLL("gdi32.dll")
	winmm                      = windows.NewLazySystemDLL("winmm.dll")
	getSystemMetrics           = user32.NewProc("GetSystemMetrics")
	setLayeredWindowAttributes = user32.NewProc("SetLayeredWindowAttributes")
	showCursor                 = user32.NewProc("ShowCursor")
	setTextAlign               = gdi32.NewProc("SetTextAlign")
	patBlt                     = gdi32.NewProc("PatBlt")
	createFont                 = gdi32.NewProc("CreateFontW")
	createCompatibleDC         = gdi32.NewProc("CreateCompatibleDC")
	createSolidBrush           = gdi32.NewProc("CreateSolidBrush")
	createPen                  = gdi32.NewProc("CreatePen")
	getStockObject             = gdi32.NewProc("GetStockObject")
	peekMessage                = user32.NewProc("PeekMessageW")
	timeBeginPeriod            = winmm.NewProc("timeBeginPeriod")
	timeEndPeriod              = winmm.NewProc("timeEndPeriod")
)

var (
	teamCheck           bool   = true
	headCircle          bool   = true
	skeletonRendering   bool   = true
	boxRendering        bool   = true
	nameRendering       bool   = true
	healthBarRendering  bool   = true
	healthTextRendering bool   = true
	frameDelay          uint32 = 5
)

var (
	cachedScreenWidth  float32
	cachedScreenHeight float32
)

var (
	hpTextBuf [8]byte
	utf16Buf  [256]uint16
	nameUtf16 [64]uint16
)

func init() {
	runtime.LockOSThread()
}

func logAndSleep(message string, err error) {
	log.Printf("%s: %v\n", message, err)
	time.Sleep(5 * time.Second)
}

func worldToScreen(viewMatrix Matrix, position Vector3) (float32, float32) {
	screenX := viewMatrix[0][0]*position.X + viewMatrix[0][1]*position.Y + viewMatrix[0][2]*position.Z + viewMatrix[0][3]
	screenY := viewMatrix[1][0]*position.X + viewMatrix[1][1]*position.Y + viewMatrix[1][2]*position.Z + viewMatrix[1][3]
	w := viewMatrix[3][0]*position.X + viewMatrix[3][1]*position.Y + viewMatrix[3][2]*position.Z + viewMatrix[3][3]
	if w < 0.01 {
		return -1, -1
	}
	invw := 1.0 / w
	screenX *= invw
	screenY *= invw
	x := cachedScreenWidth / 2
	y := cachedScreenHeight / 2
	x += 0.5*screenX*cachedScreenWidth + 0.5
	y -= 0.5*screenY*cachedScreenHeight + 0.5
	return x, y
}

type TestResult int

const (
	TestOK TestResult = iota
	TestOffsetsWrong
	TestNoPlayers
)

func (r TestResult) String() string {
	switch r {
	case TestOK:
		return "OK"
	case TestOffsetsWrong:
		return "OFFSETS_WRONG"
	case TestNoPlayers:
		return "NO_PLAYERS"
	default:
		return "UNKNOWN"
	}
}

func getOffsets(handle windows.Handle, clientBase uintptr) (Offset, error) {
	var offsets Offset

	offsetsJson, err := os.Open("offsets.json")
	if err != nil {
		return offsets, fmt.Errorf("offsets.json not found - please provide valid offsets: %w", err)
	}
	defer offsetsJson.Close()

	err = json.NewDecoder(offsetsJson).Decode(&offsets)
	if err != nil {
		return offsets, fmt.Errorf("error decoding offsets.json: %w", err)
	}

	fmt.Println("[*] Loaded offsets from offsets.json")

	if offsets.M_hPlayerPawn == 0 || offsets.M_iHealth == 0 || offsets.M_iTeamNum == 0 {
		return offsets, fmt.Errorf("missing required member offsets in offsets.json")
	}

	result := functionalTest(handle, clientBase, offsets)
	fmt.Printf("[*] Functional test result: %s\n", result)

	if result == TestOK {
		fmt.Println("[+] Offsets are valid!")
		return offsets, nil
	}

	fmt.Println("[!] Base offsets validation failed, scanning for new offsets...")

	dwViewMatrix, err := findPattern(handle, clientBase, "48 8D 0D ?? ?? ?? ?? 48 C1 E0 06")
	if err != nil {
		return offsets, fmt.Errorf("failed to find dwViewMatrix pattern: %w", err)
	}
	offsets.DwViewMatrix = dwViewMatrix - clientBase
	fmt.Printf("[+] dwViewMatrix: 0x%X\n", offsets.DwViewMatrix)

	dwLocalPlayerPawn, err := findLocalPlayerPawn(handle, clientBase)
	if err != nil {
		return offsets, fmt.Errorf("failed to find dwLocalPlayerPawn: %w", err)
	}
	offsets.DwLocalPlayerPawn = dwLocalPlayerPawn
	fmt.Printf("[+] dwLocalPlayerPawn: 0x%X\n", offsets.DwLocalPlayerPawn)

	dwEntityList, err := findPattern(handle, clientBase, "48 89 0D ?? ?? ?? ?? E9 ?? ?? ?? ?? CC")
	if err != nil {
		return offsets, fmt.Errorf("failed to find dwEntityList pattern: %w", err)
	}
	offsets.DwEntityList = dwEntityList - clientBase
	fmt.Printf("[+] dwEntityList: 0x%X\n", offsets.DwEntityList)

	result = functionalTest(handle, clientBase, offsets)
	fmt.Printf("[*] Functional test after scan: %s\n", result)

	if result == TestOffsetsWrong {
		return offsets, fmt.Errorf("scanned offsets failed validation - member offsets may be outdated")
	}

	err = saveOffsetsToJSON(offsets)
	if err != nil {
		fmt.Println("[!] Warning: Could not save offsets to JSON:", err)
	} else {
		fmt.Println("[+] Saved updated offsets to offsets.json")
	}

	return offsets, nil
}

func findLocalPlayerPawn(handle windows.Handle, moduleBase uintptr) (uintptr, error) {
	dwPrediction, err := findPattern(handle, moduleBase, "48 8D 05 ?? ?? ?? ?? C3 CC CC CC CC CC CC CC CC 40 53 56 41 54")
	if err != nil {
		return 0, fmt.Errorf("dwPrediction pattern not found: %w", err)
	}

	fmt.Printf("[*] dwPrediction found at: 0x%X\n", dwPrediction-moduleBase)

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

	pattern := "4C 39 B6 ?? ?? ?? ?? 74 ?? 44 88 BE"
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
			offsetValue := binary.LittleEndian.Uint32(buffer[i+3 : i+7])

			result := dwPrediction + uintptr(offsetValue)

			fmt.Printf("[*] Found pattern at module+0x%X, offset value: 0x%X\n", i, offsetValue)
			fmt.Printf("[*] dwLocalPlayerPawn = dwPrediction(0x%X) + offset(0x%X) = 0x%X\n",
				dwPrediction-moduleBase, offsetValue, result-moduleBase)

			return result - moduleBase, nil
		}
	}

	return 0, fmt.Errorf("dwLocalPlayerPawn offset pattern not found")
}

func functionalTest(handle windows.Handle, clientBase uintptr, offsets Offset) TestResult {
	if clientBase == 0 {
		fmt.Println("[!] client_base is 0")
		return TestOffsetsWrong
	}

	var entityList uintptr
	err := read(handle, clientBase+offsets.DwEntityList, &entityList)
	if err != nil || entityList == 0 {
		fmt.Printf("[!] entity_list is null (offset 0x%X)\n", offsets.DwEntityList)
		return TestOffsetsWrong
	}

	var firstPage uintptr
	err = read(handle, entityList+16, &firstPage)
	if err != nil || firstPage == 0 {
		return TestNoPlayers
	}

	validPlayers := 0
	bogusReads := 0

	for i := 1; i < 64; i++ {
		var controller uintptr
		err := read(handle, firstPage+112*uintptr(i&0x1FF), &controller)
		if err != nil || controller == 0 {
			continue
		}

		var pawnHandle uint32
		err = read(handle, controller+offsets.M_hPlayerPawn, &pawnHandle)
		if err != nil || pawnHandle == 0 {
			continue
		}

		var pawnPage uintptr
		err = read(handle, entityList+8*uintptr((pawnHandle&0x7FFF)>>9)+16, &pawnPage)
		if err != nil || pawnPage == 0 {
			continue
		}

		var pawn uintptr
		err = read(handle, pawnPage+112*uintptr(pawnHandle&0x1FF), &pawn)
		if err != nil || pawn == 0 {
			continue
		}

		var team int32
		var health int32
		err1 := read(handle, pawn+offsets.M_iTeamNum, &team)
		err2 := read(handle, pawn+offsets.M_iHealth, &health)

		if err1 != nil || err2 != nil {
			continue
		}

		if team >= 0 && team <= 3 {
			if health >= 0 && health <= 100 {
				validPlayers++
			} else if health > 100 || health < -1 {
				bogusReads++
			}
		} else {
			bogusReads++
		}
	}

	if validPlayers > 0 && bogusReads <= validPlayers {
		fmt.Printf("[+] Found %d valid players in functional test\n", validPlayers)
		return TestOK
	}

	if validPlayers == 0 && bogusReads == 0 {
		return TestNoPlayers
	}

	fmt.Printf("[!] Functional test failed: %d valid, %d bogus reads\n", validPlayers, bogusReads)
	return TestOffsetsWrong
}

func saveOffsetsToJSON(offsets Offset) error {
	file, err := os.Create("offsets.json")
	if err != nil {
		return err
	}
	defer file.Close()

	encoder := json.NewEncoder(file)
	encoder.SetIndent("", "    ")
	return encoder.Encode(offsets)
}

var entityPool [64]Entity

var bonePool [64]map[string]Vector2

func initBonePools() {
	boneKeys := []string{
		"head", "neck_0", "spine_1", "spine_2", "pelvis",
		"arm_upper_L", "arm_lower_L", "arm_upper_R", "arm_lower_R",
		"hand_L", "hand_R",
		"leg_upper_L", "leg_lower_L", "leg_upper_R", "leg_lower_R",
		"ankle_L", "ankle_R",
	}
	for i := range bonePool {
		bonePool[i] = make(map[string]Vector2, len(boneKeys))
		for _, k := range boneKeys {
			bonePool[i][k] = Vector2{}
		}
	}
}

func getEntitiesInfo(procHandle windows.Handle, clientDll uintptr, offsets Offset) []Entity {
	entities := entityPool[:0]
	var entityList uintptr
	err := read(procHandle, clientDll+offsets.DwEntityList, &entityList)
	if err != nil {
		return entities
	}

	var (
		localPlayerP           uintptr
		localPlayerGameScene   uintptr
		localPlayerSceneOrigin Vector3
		localTeam              int32
		listEntry              uintptr
		gameScene              uintptr
		entityController       uintptr
		entityControllerPawn   uintptr
		entityPawn             uintptr
		entityNameAddress      uintptr
		entityBoneArray        uintptr
		entityTeam             int32
		entityHealth           int32
		entityLifeState        int32
		entityOrigin           Vector3
		viewMatrix             Matrix
		currentBone            Vector3
		entityHead             Vector3
		entityHeadTop          Vector3
		entityHeadBottom       Vector3
	)

	bones := map[string]int{
		"head": 7, "neck_0": 6, "spine_1": 3, "spine_2": 4, "pelvis": 1,
		"arm_upper_L": 10, "arm_lower_L": 11, "arm_upper_R": 14, "arm_lower_R": 15,
		"hand_L": 11, "hand_R": 15,
		"leg_upper_L": 17, "leg_lower_L": 18, "leg_upper_R": 20, "leg_lower_R": 21,
		"ankle_L": 19, "ankle_R": 22,
	}

	if err = read(procHandle, clientDll+offsets.DwLocalPlayerPawn, &localPlayerP); err != nil {
		return entities
	}
	if err = read(procHandle, localPlayerP+offsets.M_pGameSceneNode, &localPlayerGameScene); err != nil {
		return entities
	}
	if err = read(procHandle, localPlayerGameScene+offsets.M_nodeToWorld, &localPlayerSceneOrigin); err != nil {
		return entities
	}
	if err = read(procHandle, clientDll+offsets.DwViewMatrix, &viewMatrix); err != nil {
		return entities
	}

	entityCount := 0
	for i := 0; i < 64; i++ {
		if err = read(procHandle, entityList+uintptr((8*(i&0x7FFF)>>9)+16), &listEntry); err != nil || listEntry == 0 {
			continue
		}
		if err = read(procHandle, listEntry+uintptr(112)*uintptr(i&0x1FF), &entityController); err != nil || entityController == 0 {
			continue
		}
		if err = read(procHandle, entityController+offsets.M_hPlayerPawn, &entityControllerPawn); err != nil || entityControllerPawn == 0 {
			continue
		}
		if err = read(procHandle, entityList+uintptr(0x8*((entityControllerPawn&0x7FFF)>>9)+16), &listEntry); err != nil || listEntry == 0 {
			continue
		}
		if err = read(procHandle, listEntry+uintptr(112)*uintptr(entityControllerPawn&0x1FF), &entityPawn); err != nil || entityPawn == 0 {
			continue
		}
		if entityPawn == localPlayerP {
			continue
		}
		if err = read(procHandle, entityPawn+offsets.M_lifeState, &entityLifeState); err != nil || entityLifeState != 256 {
			continue
		}
		if err = read(procHandle, entityPawn+offsets.M_iTeamNum, &entityTeam); err != nil || entityTeam == 0 {
			continue
		}
		if teamCheck {
			if err = read(procHandle, localPlayerP+offsets.M_iTeamNum, &localTeam); err != nil {
				continue
			}
			if localTeam == entityTeam {
				continue
			}
		}
		if err = read(procHandle, entityPawn+offsets.M_iHealth, &entityHealth); err != nil || entityHealth < 1 || entityHealth > 100 {
			continue
		}

		var entityName string
		if err = read(procHandle, entityController+offsets.M_sSanitizedPlayerName, &entityNameAddress); err != nil {
			continue
		}
		if err = read(procHandle, entityNameAddress, &entityName); err != nil || entityName == "" {
			continue
		}

		var sb strings.Builder
		sb.Grow(len(entityName))
		for _, c := range entityName {
			if unicode.IsLetter(c) || unicode.IsDigit(c) || unicode.IsPunct(c) || unicode.IsSpace(c) {
				sb.WriteRune(c)
			}
		}

		if err = read(procHandle, entityPawn+offsets.M_pGameSceneNode, &gameScene); err != nil || gameScene == 0 {
			continue
		}
		if err = read(procHandle, gameScene+offsets.M_modelState+offsets.M_boneArray, &entityBoneArray); err != nil || entityBoneArray == 0 {
			continue
		}
		if err = read(procHandle, entityPawn+offsets.M_vOldOrigin, &entityOrigin); err != nil {
			continue
		}

		entityBones := bonePool[entityCount]

		for boneName, boneIndex := range bones {
			if err = read(procHandle, entityBoneArray+uintptr(boneIndex)*32, &currentBone); err != nil {
				goto nextEntity
			}
			if boneName == "head" {
				entityHead = currentBone
				if !skeletonRendering {
					boneX, boneY := worldToScreen(viewMatrix, currentBone)
					entityBones[boneName] = Vector2{boneX, boneY}
					continue
				}
			}
			boneX, boneY := worldToScreen(viewMatrix, currentBone)
			entityBones[boneName] = Vector2{boneX, boneY}
		}

		{
			entityHeadTop = Vector3{entityHead.X, entityHead.Y, entityHead.Z + 7}
			entityHeadBottom = Vector3{entityHead.X, entityHead.Y, entityHead.Z - 5}
			screenPosHeadX, screenPosHeadTopY := worldToScreen(viewMatrix, entityHeadTop)
			_, screenPosHeadBottomY := worldToScreen(viewMatrix, entityHeadBottom)
			screenPosFeetX, screenPosFeetY := worldToScreen(viewMatrix, entityOrigin)
			entityBoxTop := Vector3{entityOrigin.X, entityOrigin.Y, entityOrigin.Z + 70}
			_, screenPosBoxTop := worldToScreen(viewMatrix, entityBoxTop)

			if screenPosHeadX <= -1 || screenPosFeetY <= -1 ||
				screenPosHeadX >= cachedScreenWidth || screenPosHeadTopY >= cachedScreenHeight {
				continue
			}
			boxHeight := screenPosFeetY - screenPosBoxTop

			e := &entityPool[entityCount]
			e.Health = entityHealth
			e.Team = entityTeam
			e.Name = sb.String()
			e.Distance = entityOrigin.Dist(localPlayerSceneOrigin)
			e.Position = Vector2{screenPosFeetX, screenPosFeetY}
			e.Bones = entityBones
			e.HeadPos = Vector3{screenPosHeadX, screenPosHeadTopY, screenPosHeadBottomY}
			e.Rect = Rectangle{screenPosBoxTop, screenPosFeetX - boxHeight/4, screenPosFeetX + boxHeight/4, screenPosFeetY}
			entities = append(entities, *e)
			entityCount++
		}
		continue
	nextEntity:
	}
	return entities
}

func drawSkeleton(hdc win.HDC, pen uintptr, bones map[string]Vector2) {
	win.SelectObject(hdc, win.HGDIOBJ(pen))
	win.MoveToEx(hdc, int(bones["head"].X), int(bones["head"].Y), nil)
	win.LineTo(hdc, int32(bones["neck_0"].X), int32(bones["neck_0"].Y))
	win.LineTo(hdc, int32(bones["spine_1"].X), int32(bones["spine_1"].Y))
	win.LineTo(hdc, int32(bones["spine_2"].X), int32(bones["spine_2"].Y))
	win.LineTo(hdc, int32(bones["pelvis"].X), int32(bones["pelvis"].Y))
	win.LineTo(hdc, int32(bones["leg_upper_L"].X), int32(bones["leg_upper_L"].Y))
	win.LineTo(hdc, int32(bones["leg_lower_L"].X), int32(bones["leg_lower_L"].Y))
	win.LineTo(hdc, int32(bones["ankle_L"].X), int32(bones["ankle_L"].Y))
	win.MoveToEx(hdc, int(bones["pelvis"].X), int(bones["pelvis"].Y), nil)
	win.LineTo(hdc, int32(bones["leg_upper_R"].X), int32(bones["leg_upper_R"].Y))
	win.LineTo(hdc, int32(bones["leg_lower_R"].X), int32(bones["leg_lower_R"].Y))
	win.LineTo(hdc, int32(bones["ankle_R"].X), int32(bones["ankle_R"].Y))
	win.MoveToEx(hdc, int(bones["spine_1"].X), int(bones["spine_1"].Y), nil)
	win.LineTo(hdc, int32(bones["arm_upper_L"].X), int32(bones["arm_upper_L"].Y))
	win.LineTo(hdc, int32(bones["arm_lower_L"].X), int32(bones["arm_lower_L"].Y))
	win.LineTo(hdc, int32(bones["hand_L"].X), int32(bones["hand_L"].Y))
	win.MoveToEx(hdc, int(bones["spine_1"].X), int(bones["spine_1"].Y), nil)
	win.LineTo(hdc, int32(bones["arm_upper_R"].X), int32(bones["arm_upper_R"].Y))
	win.LineTo(hdc, int32(bones["arm_lower_R"].X), int32(bones["arm_lower_R"].Y))
	win.LineTo(hdc, int32(bones["hand_R"].X), int32(bones["hand_R"].Y))
}

func intToUtf16Scratch(n int32, buf []uint16) ([]uint16, int32) {
	s := strconv.AppendInt(hpTextBuf[:0], int64(n), 10)
	l := len(s)
	for i, c := range s {
		buf[i] = uint16(c)
	}
	buf[l] = 0
	return buf[:l], int32(l)
}

func stringToUtf16Scratch(s string, buf []uint16) int32 {
	i := 0
	for _, r := range s {
		if i >= len(buf)-1 {
			break
		}
		buf[i] = uint16(r)
		i++
	}
	buf[i] = 0
	return int32(i)
}

func renderEntityInfo(hdc win.HDC, tPen uintptr, gPen uintptr, oPen uintptr, hPen uintptr, rect Rectangle, hp int32, name string, headPos Vector3) {
	if boxRendering {
		win.SelectObject(hdc, win.HGDIOBJ(tPen))
		win.MoveToEx(hdc, int(rect.Left), int(rect.Top), nil)
		win.LineTo(hdc, int32(rect.Right), int32(rect.Top))
		win.LineTo(hdc, int32(rect.Right), int32(rect.Bottom))
		win.LineTo(hdc, int32(rect.Left), int32(rect.Bottom))
		win.LineTo(hdc, int32(rect.Left), int32(rect.Top))

		win.SelectObject(hdc, win.HGDIOBJ(oPen))
		win.MoveToEx(hdc, int(rect.Left)-1, int(rect.Top)-1, nil)
		win.LineTo(hdc, int32(rect.Right)-1, int32(rect.Top)+1)
		win.LineTo(hdc, int32(rect.Right)+1, int32(rect.Bottom)+1)
		win.LineTo(hdc, int32(rect.Left)+1, int32(rect.Bottom)-1)
		win.LineTo(hdc, int32(rect.Left)-1, int32(rect.Top)-1)
		win.MoveToEx(hdc, int(rect.Left)+1, int(rect.Top)+1, nil)
		win.LineTo(hdc, int32(rect.Right)+1, int32(rect.Top)-1)
		win.LineTo(hdc, int32(rect.Right)-1, int32(rect.Bottom)-1)
		win.LineTo(hdc, int32(rect.Left)-1, int32(rect.Bottom)+1)
		win.LineTo(hdc, int32(rect.Left)+1, int32(rect.Top)+1)
	}

	if headCircle {
		radius := int32((int32(headPos.Z) - int32(headPos.Y)) / 2)
		win.SelectObject(hdc, win.HGDIOBJ(oPen))
		win.Ellipse(hdc, int32(headPos.X)-radius-1, int32(headPos.Y)-1, int32(headPos.X)+radius+1, int32(headPos.Z)+1)
		win.SelectObject(hdc, win.HGDIOBJ(hPen))
		win.Ellipse(hdc, int32(headPos.X)-radius, int32(headPos.Y), int32(headPos.X)+radius, int32(headPos.Z))
		win.SelectObject(hdc, win.HGDIOBJ(oPen))
		win.Ellipse(hdc, int32(headPos.X)-radius+1, int32(headPos.Y)+1, int32(headPos.X)+radius-1, int32(headPos.Z)-1)
	}

	if healthBarRendering {
		win.SelectObject(hdc, win.HGDIOBJ(gPen))
		win.MoveToEx(hdc, int(rect.Left)-4, int(rect.Bottom)+1-int(float64(int(rect.Bottom)+1-int(rect.Top))*float64(hp)/100.0), nil)
		win.LineTo(hdc, int32(rect.Left)-4, int32(rect.Bottom)+1)

		win.SelectObject(hdc, win.HGDIOBJ(oPen))
		win.MoveToEx(hdc, int(rect.Left)-5, int(rect.Top)-1, nil)
		win.LineTo(hdc, int32(rect.Left)-5, int32(rect.Bottom)+1)
		win.LineTo(hdc, int32(rect.Left)-3, int32(rect.Bottom)+1)
		win.LineTo(hdc, int32(rect.Left)-3, int32(rect.Top)-1)
		win.LineTo(hdc, int32(rect.Left)-5, int32(rect.Top)-1)
	}

	if healthTextRendering {
		_, hpLen := intToUtf16Scratch(hp, utf16Buf[:])
		win.SetTextColor(hdc, win.RGB(0, 255, 50))
		setTextAlign.Call(uintptr(hdc), 0x00000002)
		if healthBarRendering {
			win.TextOut(hdc, int32(rect.Left)-8, int32(int(rect.Bottom)+1-int(float64(int(rect.Bottom)+1-int(rect.Top))*float64(hp)/100.0)), &utf16Buf[0], hpLen)
		} else {
			win.TextOut(hdc, int32(rect.Left)-4, int32(rect.Top), &utf16Buf[0], hpLen)
		}
	}

	if nameRendering {
		nameLen := stringToUtf16Scratch(name, nameUtf16[:])
		win.SetTextColor(hdc, win.RGB(255, 255, 255))
		setTextAlign.Call(uintptr(hdc), 0x00000006)
		win.TextOut(hdc, int32(rect.Left)+int32((int32(rect.Right)-int32(rect.Left))/2), int32(rect.Top)-14, &nameUtf16[0], nameLen)
	}
}

func windowProc(hwnd win.HWND, msg uint32, wParam, lParam uintptr) uintptr {
	switch msg {
	case win.WM_DESTROY:
		win.PostQuitMessage(0)
		return 0
	default:
		return win.DefWindowProc(hwnd, msg, wParam, lParam)
	}
}

func initWindow(screenWidth uintptr, screenHeight uintptr) win.HWND {
	className, err := windows.UTF16PtrFromString("cs2goWindow")
	if err != nil {
		logAndSleep("Error creating window class name", err)
		return 0
	}
	windowTitle, err := windows.UTF16PtrFromString("cs2go")
	if err != nil {
		logAndSleep("Error creating window title", err)
		return 0
	}

	wc := win.WNDCLASSEX{
		CbSize:        uint32(unsafe.Sizeof(win.WNDCLASSEX{})),
		Style:         win.CS_HREDRAW | win.CS_VREDRAW,
		LpfnWndProc:   syscall.NewCallback(windowProc),
		HInstance:     win.GetModuleHandle(nil),
		HIcon:         win.LoadIcon(0, (*uint16)(unsafe.Pointer(uintptr(win.IDI_APPLICATION)))),
		HCursor:       win.LoadCursor(0, (*uint16)(unsafe.Pointer(uintptr(win.IDC_ARROW)))),
		HbrBackground: win.COLOR_WINDOW,
		LpszClassName: className,
		HIconSm:       win.LoadIcon(0, (*uint16)(unsafe.Pointer(uintptr(win.IDI_APPLICATION)))),
	}
	if atom := win.RegisterClassEx(&wc); atom == 0 {
		logAndSleep("Error registering window class", fmt.Errorf("%v", win.GetLastError()))
		return 0
	}

	hwnd := win.CreateWindowEx(
		win.WS_EX_TOPMOST|win.WS_EX_NOACTIVATE|win.WS_EX_LAYERED,
		className, windowTitle,
		win.WS_POPUP,
		0, 0, int32(screenWidth), int32(screenHeight),
		0, 0, win.GetModuleHandle(nil), nil,
	)
	if hwnd == 0 {
		logAndSleep("Error creating window", fmt.Errorf("%v", win.GetLastError()))
		return 0
	}

	result, _, _ := setLayeredWindowAttributes.Call(uintptr(hwnd), 0x000000, 0, 0x00000001)
	if result == 0 {
		logAndSleep("Error setting layered window attributes", fmt.Errorf("%v", win.GetLastError()))
	}
	style := win.GetWindowLongPtr(hwnd, win.GWL_EXSTYLE)
	style |= win.WS_EX_TRANSPARENT
	win.SetWindowLongPtr(hwnd, win.GWL_EXSTYLE, style)
	showCursor.Call(0)
	win.ShowWindow(hwnd, win.SW_SHOWDEFAULT)
	return hwnd
}

func cliMenu() {
	for {
		fmt.Print(chalk.Magenta.Color("          ____             \n  ___ ___|___ \\ ____  ___  \n / __/ __| __) / _  |/ _ \\ \n| (__\\__ \\/ __/ (_| | (_) |\n \\___|___/_____\\__, |\\___/ \n               |___/       \n"))
		fmt.Println(chalk.Dim.TextStyle("\t\tby bqj - v1.6\n"))
		printToggle := func(n, label string, v bool) {
			if v {
				fmt.Println(chalk.Green.Color("[" + n + "] " + label + " [ON]"))
			} else {
				fmt.Println(chalk.Red.Color("[" + n + "] " + label + " [OFF]"))
			}
		}
		printToggle("1", "Team check", teamCheck)
		printToggle("2", "Head circle", headCircle)
		printToggle("3", "Skeleton rendering", skeletonRendering)
		printToggle("4", "Box rendering", boxRendering)
		printToggle("5", "Health bar rendering", healthBarRendering)
		printToggle("6", "Health text rendering", healthTextRendering)
		printToggle("7", "Name rendering", nameRendering)
		fmt.Println(chalk.Cyan.Color("[8] Adjust frame delay [") + fmt.Sprint(frameDelay) + chalk.Cyan.Color("]"))
		fmt.Println(chalk.Red.Color("[9] Exit"))
		fmt.Print(chalk.Cyan.Color("[Enter selection]: "))
		var input string
		fmt.Scanln(&input)
		switch input {
		case "1":
			teamCheck = !teamCheck
		case "2":
			headCircle = !headCircle
		case "3":
			skeletonRendering = !skeletonRendering
		case "4":
			boxRendering = !boxRendering
		case "5":
			healthBarRendering = !healthBarRendering
		case "6":
			healthTextRendering = !healthTextRendering
		case "7":
			nameRendering = !nameRendering
		case "8":
			fmt.Println(chalk.Red.Color("Higher frame delay = lower performance impact but higher ESP latency"))
			fmt.Print(chalk.Cyan.Color("[Enter frame delay (ms)]: "))
			var delay uint32
			fmt.Scanln(&delay)
			frameDelay = delay
		case "9":
			os.Exit(0)
		default:
			fmt.Println(chalk.Red.Color("Invalid selection"))
			time.Sleep(1 * time.Second)
		}
		fmt.Print("\033[H\033[2J")
	}
}

func main() {
	debug.SetGCPercent(-1)
	runtime.LockOSThread()

	timeBeginPeriod.Call(1)
	defer timeEndPeriod.Call(1)

	sw, _, _ := getSystemMetrics.Call(0)
	sh, _, _ := getSystemMetrics.Call(1)
	cachedScreenWidth = float32(sw)
	cachedScreenHeight = float32(sh)

	initBonePools()

	pid, err := findProcessId("cs2.exe")
	if err != nil {
		logAndSleep("Error finding process ID", err)
		return
	}
	clientDll, err := getModuleBaseAddress(pid, "client.dll")
	if err != nil {
		logAndSleep("Error getting client.dll base address", err)
		return
	}
	procHandle, err := getProcessHandle(pid)
	if err != nil {
		logAndSleep("Error getting process handle", err)
		return
	}
	offsets, err := getOffsets(procHandle, clientDll)
	if err != nil {
		logAndSleep("Error loading offsets", err)
		return
	}

	go cliMenu()

	hwnd := initWindow(uintptr(cachedScreenWidth), uintptr(cachedScreenHeight))
	if hwnd == 0 {
		logAndSleep("Error creating window", fmt.Errorf("%v", win.GetLastError()))
		return
	}
	defer win.DestroyWindow(hwnd)

	hdc := win.GetDC(hwnd)
	if hdc == 0 {
		logAndSleep("Error getting device context", fmt.Errorf("%v", win.GetLastError()))
		return
	}

	bgBrush, _, _ := createSolidBrush.Call(0x000000)
	redPen, _, _ := createPen.Call(win.PS_SOLID, 1, 0x7a78ff)
	greenPen, _, _ := createPen.Call(win.PS_SOLID, 1, 0x7dff78)
	bluePen, _, _ := createPen.Call(win.PS_SOLID, 1, 0xff8e78)
	bonePen, _, _ := createPen.Call(win.PS_SOLID, 1, 0xffffff)
	outlinePen, _, _ := createPen.Call(win.PS_SOLID, 1, 0x000001)
	font, _, _ := createFont.Call(12, 0, 0, 0, win.FW_HEAVY, 0, 0, 0, win.DEFAULT_CHARSET, win.OUT_DEFAULT_PRECIS, win.CLIP_DEFAULT_PRECIS, win.DEFAULT_QUALITY, win.DEFAULT_PITCH|win.FF_DONTCARE, 0)

	defer win.DeleteObject(win.HGDIOBJ(bgBrush))
	defer win.DeleteObject(win.HGDIOBJ(redPen))
	defer win.DeleteObject(win.HGDIOBJ(greenPen))
	defer win.DeleteObject(win.HGDIOBJ(bluePen))
	defer win.DeleteObject(win.HGDIOBJ(bonePen))
	defer win.DeleteObject(win.HGDIOBJ(outlinePen))

	memhdc, _, _ := createCompatibleDC.Call(uintptr(hdc))
	memBitmap := win.CreateCompatibleBitmap(hdc, int32(cachedScreenWidth), int32(cachedScreenHeight))
	win.SelectObject(win.HDC(memhdc), win.HGDIOBJ(memBitmap))

	nullBrush, _, _ := getStockObject.Call(5)
	win.SelectObject(win.HDC(memhdc), win.HGDIOBJ(nullBrush))
	win.SetBkMode(win.HDC(memhdc), win.TRANSPARENT)
	win.SelectObject(win.HDC(memhdc), win.HGDIOBJ(font))
	defer win.DeleteObject(win.HGDIOBJ(memBitmap))
	defer win.DeleteDC(win.HDC(memhdc))

	var msg win.MSG
	var frameStart time.Time

	for {
		for peekMessage.Call(uintptr(unsafe.Pointer(&msg)), 0, 0, 0, 1 /*PM_REMOVE*/); msg.Message != win.WM_QUIT; {
			win.TranslateMessage(&msg)
			win.DispatchMessage(&msg)
			r, _, _ := peekMessage.Call(uintptr(unsafe.Pointer(&msg)), 0, 0, 0, 1)
			if r == 0 {
				break
			}
		}
		if msg.Message == win.WM_QUIT {
			break
		}

		frameStart = time.Now()

		patBlt.Call(memhdc, 0, 0, uintptr(cachedScreenWidth), uintptr(cachedScreenHeight), 0x00000042)

		entities := getEntitiesInfo(procHandle, clientDll, offsets)
		for _, entity := range entities {
			if entity.Distance < 35 {
				continue
			}
			if skeletonRendering {
				drawSkeleton(win.HDC(memhdc), bonePen, entity.Bones)
			}
			if entity.Team == 2 {
				renderEntityInfo(win.HDC(memhdc), redPen, greenPen, outlinePen, bonePen, entity.Rect, entity.Health, entity.Name, entity.HeadPos)
			} else {
				renderEntityInfo(win.HDC(memhdc), bluePen, greenPen, outlinePen, bonePen, entity.Rect, entity.Health, entity.Name, entity.HeadPos)
			}
		}

		win.BitBlt(hdc, 0, 0, int32(cachedScreenWidth), int32(cachedScreenHeight), win.HDC(memhdc), 0, 0, win.SRCCOPY)

		if frameDelay > 0 {
			elapsed := time.Since(frameStart)
			budget := time.Duration(frameDelay) * time.Millisecond
			if elapsed < budget {
				time.Sleep(budget - elapsed)
			}
		}
	}
}
