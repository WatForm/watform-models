--------------------------- MODULE musical_chairs ---------------------------
(* The Musical Chairs case study - TLA+ model

Copyright (c) 2018 Jose Serna <jserna@uwaterloo.ca>
Copyright (c) 2018 Nancy Day <nday@uwaterloo.ca>
Copyright (c) 2018-2020 Amin Bandali <bandali@uwaterloo.ca>

This file is part of the Musical Chairs TLA+ model.

The Musical Chairs TLA+ model is free software: you can redistribute
it and/or modify it under the terms of the GNU General Public License
as published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Musical Chairs TLA+ model is distributed in the hope that it will
be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Musical Chairs TLA+ model.  If not, see
<https://www.gnu.org/licenses/>.


The Musical Chairs case study is described in~\cite{Nissanke_1999} by
Nissanke.  The Musical Chairs TLA+ model is an adaptation of the
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

*)

EXTENDS Integers, FiniteSets

CONSTANTS CHAIRS, PLAYERS

VARIABLES
    activePlayers, activeChairs,
    occupied, music_playing, state

vars == << activePlayers, activeChairs, occupied, music_playing, state >>

STATE_ == { "Start", "Walking", "Sitting", "Won" }

\* Helper predicate for range of a function
Range(f) == {f[x]: x \in DOMAIN f}


\* Typing invariant
TypeOK ==
    /\ activePlayers  \subseteq PLAYERS
    /\ activeChairs   \subseteq CHAIRS
    /\ occupied \in [activeChairs -> activePlayers] \union {<<>>}
    /\ music_playing \in BOOLEAN  \* whether music is playing
    /\ state \in STATE_

\* Initial state
Init ==
    /\ activePlayers = PLAYERS  \* force all activePlayers and
    /\ activeChairs = CHAIRS    \* activeChairs to be included
    /\ Cardinality(activePlayers) > 1
    /\ Cardinality(activePlayers) = Cardinality(activeChairs) + 1
    /\ occupied = <<>>  \* initially the empty function
    /\ music_playing \in BOOLEAN
    /\ state = "Start"

Walk ==
    /\ state = "Start"
    /\ music_playing
    /\ Cardinality(activePlayers) > 1
    /\ occupied' = <<>>
    /\ state' = "Walking"
    /\ UNCHANGED <<activeChairs, activePlayers, music_playing>>

Sit ==
    /\ state = "Walking"
    /\ ~music_playing
    /\ occupied' \in [activeChairs -> activePlayers]
    \* each chair maps to only one player
    /\ \A c \in activeChairs, p1, p2 \in activePlayers:
        occupied'[c] = p1 /\ occupied'[c] = p2 => p1 = p2
    \* each occupying player sits on one chair
    /\ \A p \in Range(occupied'), c1, c2 \in DOMAIN occupied':
        occupied'[c1] = p /\ occupied'[c2] = p => c1 = c2
    \* there's a player that didn't get to sit down
    \* /\ \E p \in activePlayers: p \notin Range(occupied')
    /\ state' = "Sitting"
    /\ UNCHANGED <<activeChairs, activePlayers, music_playing>>

EliminateLoser ==
    /\ state = "Sitting"
    /\ Cardinality(activePlayers) > 1
    /\ Cardinality(activePlayers) - Cardinality(Range(occupied)) = 1
    /\ activePlayers' = Range(occupied)
    /\ activeChairs' = activeChairs \ {CHOOSE c \in activeChairs : TRUE}
    /\ Cardinality(activeChairs') = Cardinality(activeChairs) - 1
    /\ occupied' = <<>>
    /\ state' = "Start"
    /\ UNCHANGED music_playing

Win ==
    /\ state = "Sitting"
    /\ Cardinality(activePlayers) = 1
    /\ state' = "Won"

ChangeMusicPlaying ==
    /\ music_playing' \in BOOLEAN
    /\ UNCHANGED <<activeChairs, activePlayers, state, occupied>>

\* Safety invariants

OneMorePlayerThanChairs ==
    Cardinality(activePlayers) = Cardinality(activeChairs) + 1

\* Temporal properties

ExistentialLiveness ==
    \E p \in PLAYERS: <> (activePlayers = {p})

FiniteLiveness == <> ENABLED Sit

InfiniteLiveness == <>[](Cardinality(activePlayers) = 1)


Next ==
    \/ Walk
    \/ Sit
    \/ EliminateLoser
    \/ Win
    \/ ChangeMusicPlaying

PlayActions ==
    \/ Walk
    \/ Sit
    \/ EliminateLoser
    \/ Win

Live == SF_vars(PlayActions) /\ WF_vars(ChangeMusicPlaying)
\*Live == TRUE  \* don't assume fairness

Spec == Init /\ [][Next]_vars /\ Live  \* every transition either satisfies the action
                                       \* formula `Next' or leaves the expression
                                       \* `vars' unchanged. In particular, this admits
                                       \* "stuttering transitions" that do not affect
                                       \* `vars'. That is to say,
                                       \* [][Next]_vars == [](Next \/ (vars' = vars)) 

=============================================================================
\* Modification History
\* Last modified Thu Oct 28 16:44:48 EDT 2021 by bandali
\* Last modified Tue Jul 17 14:05:02 EDT 2018 by amin
\* Created Mon May 14 11:12:23 EDT 2018 by amin
