//http://www.irit.fr/ABZ2014/landing_system.pdf

//second refinement

asm LandingGearSystemWithCylValvesAndSensors

import StandardLibrary
import CTLlibrary

signature:
	enum domain HandleStatus = {UP | DOWN}
	enum domain DoorStatus = {CLOSED | OPENING | OPEN | CLOSING}
	enum domain GearStatus = {RETRACTED | EXTENDING | EXTENDED | RETRACTING}
	enum domain CylinderStatus = {CYLINDER_RETRACTED | CYLINDER_EXTENDING | CYLINDER_EXTENDED | CYLINDER_RETRACTING}
	dynamic monitored handle: HandleStatus
	dynamic controlled doors: DoorStatus
	dynamic controlled gears: GearStatus

	derived cylindersDoors: CylinderStatus
	derived cylindersGears: CylinderStatus

	dynamic controlled generalElectroValve: Boolean
	dynamic controlled openDoorsElectroValve: Boolean
	dynamic controlled closeDoorsElectroValve: Boolean
	dynamic controlled retractGearsElectroValve: Boolean
	dynamic controlled extendGearsElectroValve: Boolean

	//sensors
	//gearsExtended is true if the corresponding gear is locked in the extended position and false in the other case
	dynamic monitored gearsExtended: Boolean
	//gearsRetracted is true if the corresponding gear is locked in the retracted position and false in the other case
	dynamic monitored gearsRetracted: Boolean
	//doorsClosed($s) is true if and only if the corresponding door is locked closed
	dynamic monitored doorsClosed: Boolean
	//doorsOpen is true if and only if the corresponding door is locked open
	dynamic monitored doorsOpen: Boolean

definitions:
	function cylindersDoors =
		switch doors
			case OPEN:
				CYLINDER_EXTENDED
			case OPENING:
				CYLINDER_EXTENDING
			case CLOSING:
				CYLINDER_RETRACTING
			case CLOSED:
				CYLINDER_RETRACTED
		endswitch

	function cylindersGears =
		switch gears
			case RETRACTED:
				CYLINDER_RETRACTED
			case EXTENDING:
				CYLINDER_EXTENDING
			case EXTENDED:
				CYLINDER_EXTENDED
			case RETRACTING:
				CYLINDER_RETRACTING
		endswitch

	rule r_closeDoor =
		switch doors
			case OPEN:
				par
					closeDoorsElectroValve := true
					doors := CLOSING
				endpar
			case CLOSING:
				if doorsClosed then
					par
						generalElectroValve := false
						closeDoorsElectroValve := false
						doors := CLOSED
					endpar
				endif
			case OPENING:
				par
					closeDoorsElectroValve := true
					openDoorsElectroValve := false
					doors := CLOSING
				endpar
		endswitch

	rule r_retractionSequence =
		if gears != RETRACTED then
			switch doors
				case CLOSED:
					par
						generalElectroValve := true
						openDoorsElectroValve := true
						doors := OPENING
					endpar
				case CLOSING:
					par
						closeDoorsElectroValve := false
						openDoorsElectroValve := true
						doors := OPENING
					endpar
				case OPENING:
					if doorsOpen then
						par
							openDoorsElectroValve := false
							doors := OPEN
						endpar
					endif
				case OPEN:
					switch gears
						case EXTENDED:
							par
								retractGearsElectroValve := true
								gears := RETRACTING
							endpar
						case RETRACTING:
							if gearsRetracted then
								par
									retractGearsElectroValve := false
									gears := RETRACTED
								endpar
							endif
						case EXTENDING:
							par
								extendGearsElectroValve := false
								retractGearsElectroValve := true
								gears := RETRACTING
							endpar
					endswitch
			endswitch
		else
			r_closeDoor[]
		endif

	rule r_outgoingSequence =
		if gears != EXTENDED then
			switch doors
				case CLOSED:
					par
						generalElectroValve := true
						openDoorsElectroValve := true
						doors := OPENING
					endpar
				case OPENING:
					if doorsOpen then
						par
							openDoorsElectroValve := false
							doors := OPEN
						endpar
					endif
				case OPEN:
					switch gears
						case RETRACTED:
							par
								extendGearsElectroValve := true
								gears := EXTENDING
							endpar
						case EXTENDING:
							if gearsExtended then
								par
									extendGearsElectroValve := false
									gears := EXTENDED
								endpar
							endif
						case RETRACTING:
							par
								extendGearsElectroValve := true
								retractGearsElectroValve := false
								gears := EXTENDING
							endpar
					endswitch
			endswitch
		else
			r_closeDoor[]
		endif

	invariant over gears, doors: (gears = EXTENDING or gears = RETRACTING) implies doors = OPEN
	invariant over gears, doors: doors = CLOSED implies (gears = EXTENDED or gears = RETRACTED)

	//R11_bis
	CTLSPEC ag(ag(handle = DOWN) implies af(gears = EXTENDED and doors = CLOSED))
	//R12_bis
	CTLSPEC ag(ag(handle = UP) implies af(gears = RETRACTED and doors = CLOSED))
	//R21
	CTLSPEC ag(ag(handle = DOWN) implies ax(ag(gears != RETRACTING)))
	//R22
	CTLSPEC ag(ag(handle = UP) implies ax(ag(gears != EXTENDING)))

	//R31
	CTLSPEC ag((extendGearsElectroValve or retractGearsElectroValve) implies doors = OPEN)
	//R32
	CTLSPEC ag((openDoorsElectroValve or closeDoorsElectroValve) implies (gears = RETRACTED or gears = EXTENDED))
	//R41
	CTLSPEC ag(not(openDoorsElectroValve and closeDoorsElectroValve))
	//R42
	CTLSPEC ag(not(extendGearsElectroValve and retractGearsElectroValve))
	//R51
	CTLSPEC ag((openDoorsElectroValve or closeDoorsElectroValve or extendGearsElectroValve or retractGearsElectroValve) implies generalElectroValve)

	main rule r_Main =
		if handle = UP then
			r_retractionSequence[]
		else
			r_outgoingSequence[]
		endif

default init s0:
	function doors = CLOSED
	function gears = EXTENDED
	function generalElectroValve = false
	function extendGearsElectroValve = false
	function retractGearsElectroValve = false
	function openDoorsElectroValve = false
	function closeDoorsElectroValve = false
