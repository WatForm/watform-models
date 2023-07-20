//http://www.irit.fr/ABZ2014/landing_system.pdf

//ground model

asm LandingGearSystemGround

import StandardLibrary
import CTLlibrary

signature:
	enum domain HandleStatus = {UP | DOWN}
	enum domain DoorStatus = {CLOSED | OPENING | OPEN | CLOSING}
	enum domain GearStatus = {RETRACTED | EXTENDING | EXTENDED | RETRACTING}
	dynamic monitored handle: HandleStatus
	dynamic controlled doors: DoorStatus
	dynamic controlled gears: GearStatus

definitions:

	rule r_closeDoor =
		switch doors
			case OPEN:
				doors := CLOSING
			case CLOSING:
				doors := CLOSED
			case OPENING:
				doors := CLOSING
		endswitch

	rule r_retractionSequence =
		if gears != RETRACTED then
			switch doors
				case CLOSED:
					doors := OPENING
				case CLOSING:
					doors := OPENING
				case OPENING:
					doors := OPEN
				case OPEN:
					switch gears
						case EXTENDED:
							gears := RETRACTING
						case RETRACTING:
							gears := RETRACTED
						case EXTENDING:
							gears := RETRACTING
					endswitch
			endswitch
		else
			r_closeDoor[]
		endif

	rule r_outgoingSequence =
		if gears != EXTENDED then
			switch doors
				case CLOSED:
					doors := OPENING
				case OPENING:
					doors := OPEN
				case OPEN:
					switch gears
						case RETRACTED:
							gears := EXTENDING
						case EXTENDING:
							gears := EXTENDED
						case RETRACTING:
							gears := EXTENDING
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

	main rule r_Main =
		if handle = UP then
			r_retractionSequence[]
		else
			r_outgoingSequence[]
		endif

default init s0:
	function doors = CLOSED
	function gears = EXTENDED
