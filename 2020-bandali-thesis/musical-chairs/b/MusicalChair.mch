/* The Musical Chairs case study - B model

Copyright (c) 2018 Jose Serna <jserna@uwaterloo.ca>
Copyright (c) 2018 Nancy Day <nday@uwaterloo.ca>
Copyright (c) 2018 Ali Abbassi <aabbassi@uwaterloo.ca>
Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>

This file is part of the Musical Chairs B model.

The Musical Chairs B model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Musical Chairs B model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Musical Chairs B model.  If not, see
<https://www.gnu.org/licenses/>.


The Musical Chairs case study is described in~\cite{Nissanke_1999} by
Nissanke.  The Musical Chairs B model is an adaptation of the original
model(s) presented there.

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

@inproceedings{DBLP:conf/re/AbbassiBDS18,
  author    = {Ali Abbassi and
               Amin Bandali and
               Nancy A. Day and
               Jos{\'{e}} Serna},
  editor    = {Ana Moreira and
               Gunter Mussbacher and
               Jo{\~{a}}o Ara{\'{u}}jo and
               Pablo S{\'{a}}nchez},
  title     = {A Comparison of the Declarative Modelling Languages B, Dash, and {TLA+}},
  booktitle = {8th {IEEE} International Model-Driven Requirements Engineering Workshop,
               MoDRE@RE 2018, Banff, AB, Canada, August 20, 2018},
  pages     = {11--20},
  publisher = {{IEEE} Computer Society},
  year      = {2018},
  url       = {https://doi.org/10.1109/MoDRE.2018.00008},
  doi       = {10.1109/MoDRE.2018.00008},
  timestamp = {Wed, 16 Oct 2019 14:14:56 +0200},
  biburl    = {https://dblp.org/rec/conf/re/AbbassiBDS18.bib},
  bibsource = {dblp computer science bibliography, https://dblp.org}
}

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

MACHINE MusicalChair

SETS
	PlayerState = {standing, sitting, walking, won};
	Chairs;
	Players

VARIABLES
	activePlayers, state, PickedPlayer, PickedChair, occupied, activeChairs
	
INVARIANT
	activePlayers : POW1(Players) & state : PlayerState & activeChairs : POW(Chairs) &
	PickedPlayer : Players & PickedChair : Chairs &
	occupied : Chairs --> Players


DEFINITIONS
	scope_Players == 10;
	scope_Chairs == 9;
	GOAL == (card(activePlayers) = 1)
	
CONSTANTS
	Assign

INITIALISATION
	activePlayers, state, activeChairs, occupied :=
		Players, standing, Chairs, {} ||
	PickedPlayer, PickedChair :: Players, Chairs
	
PROPERTIES
	Assign : (POW(Chairs) * POW(Players)) >-> (Chairs>->Players) &
		!(ch, pl, chs, pls).(ch |-> pl : Assign((chs), (pls)) => 
			chs: POW(Chairs) & pls: POW(Players) & pl: pls & ch: chs)

OPERATIONS
	Walk = 
	PRE
		card(activePlayers) > 1 &
		state = standing
	THEN
		state := walking ||
		occupied := {}
	END;
	
	MusicStop =
	PRE
		state = walking
	THEN
		state := sitting ||
		PickedPlayer :: activePlayers ;
		occupied := Assign(activeChairs, (activePlayers - {PickedPlayer}))
	END;
	
	EliminateLoser =
	PRE
		state = sitting &
		card(activePlayers) > 1
	THEN
		activePlayers := (activePlayers - {PickedPlayer}) ||
		state := standing ||
		PickedChair :: activeChairs ;
		activeChairs := (activeChairs - {PickedChair})
	END;
	
	DeclareWinner =
	PRE
		state = standing &
		card(activePlayers) = 1
	THEN
		state := won
	END

END
