/* The Musical Chairs case study - AsmetaL model

Copyright (c) 2018 Jose Serna <jserna@uwaterloo.ca>
Copyright (c) 2018 Nancy Day <nday@uwaterloo.ca>
Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>

This file is part of the Musical Chairs AsmetaL model.

The Musical Chairs AsmetaL model is free software: you can
redistribute it and/or modify it under the terms of the GNU General
Public License as published by the Free Software Foundation, either
version 3 of the License, or (at your option) any later version.

The Musical Chairs AsmetaL model is distributed in the hope that it
will be useful, but WITHOUT ANY WARRANTY; without even the implied
warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See
the GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Musical Chairs AsmetaL model.  If not, see
<https://www.gnu.org/licenses/>.


The Musical Chairs case study is described in~\cite{Nissanke_1999} by
Nissanke.  The Musical Chairs AsmetaL model is an adaptation of the
original model(s) presented there.

@Book{Nissanke_1999,
  author    = {Nissanke, Nimal},
  title     = {Formal Specification: Techniques and Applications},
  year      = 1999,
  doi       = {10.1007/978-1-4471-0791-0},
  url       = {http://dx.doi.org/10.1007/978-1-4471-0791-0},
  isbn      = 9781447107910,
  publisher = {Springer London}
}

This model has appeared in the following publications:

@mastersthesis{bandali2020,
  type      = {{MMath} thesis},
  author    = {Amin Bandali},
  title     = {{A Comprehensive Study of Declarative Modelling Languages}},
  school    = "University of Waterloo, David R. Cheriton School of Computer Science",
  year      = 2020,
  month     = {July},
  publisher = "UWSpace",
  url       = {http://hdl.handle.net/10012/16059},
  note      = {\url{http://hdl.handle.net/10012/16059} and
                  \url{https://bndl.org/mmath}},
  pdf       = {https://p.bndl.org/bandali-mmath-thesis.pdf}
}

*/

asm musical_chairs

import StandardLibrary

signature:
	// domains
	enum domain RuleId = {WALK | SIT | ELIMINATELOSER | WIN}
	enum domain Player = {PP1 | PP2 | PP3}
	enum domain Chair = {CC1 | CC2}
	enum domain State = {START | WALKING | SITTING | WON}

	// functions
	monitored musicPlaying: Boolean

	controlled activePlayers: Powerset(Player)
	controlled activeChairs: Powerset(Chair)
	controlled occupiedChairs: Chair -> Player
	controlled numOccupied: Natural
	controlled state: State
	controlled chosenLoser: Player

definitions:
	// helper rules
	rule r_SitAllBut($l in Player) =
		forall $c in activeChairs with true do
			choose $p in activePlayers with $p != $l do
				if (isUndef(occupiedChairs($c))) then
					seq
						occupiedChairs($c) := $p
						numOccupied := numOccupied + 1n
					endseq
				endif

	rule r_StandAll =
		forall $c in activeChairs with true do
			occupiedChairs($c) := undef

	// rules
	rule r_Walk =
		if (state = START and musicPlaying and size(activePlayers) > 1) then
			state := WALKING
		endif

	rule r_Sit =
		choose $loser in activePlayers with true do
			if (state = WALKING and not musicPlaying) then
				seq
					chosenLoser := $loser
					numOccupied := 0n
					r_SitAllBut[$loser]
					state := SITTING
				endseq
			endif

	rule r_EliminateLoser =
		choose $c in activeChairs with true do
			if (state = SITTING and size(activePlayers) > 1
					and (size(activePlayers) - ntoi(numOccupied) = 1)) then
				seq
					r_StandAll[]
					activePlayers := excluding(activePlayers, chosenLoser)
					activeChairs := excluding(activeChairs, $c)
					chosenLoser := undef
					numOccupied := 0n
					if (size(activePlayers) > 1) then
						state := START
					else
						state := SITTING
					endif
				endseq
			endif

	rule r_Win =
		if (state = SITTING and size(activePlayers) = 1) then
			state := WON
		endif

	main rule r_Main =
		choose $rule in RuleId with true do
				switch($rule)
					case WALK:
						r_Walk[]
					case SIT:
						r_Sit[]
					case ELIMINATELOSER:
						r_EliminateLoser[]
					case WIN:
						r_Win[]
				endswitch

default init s0:
	function activePlayers = Player
	function activeChairs = Chair
	function occupiedChairs($c in Chair) = undef
	function numOccupied = 0n
	function state = START
	function chosenLoser = undef
