/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-05-27 17:38:49
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/* The Musical Chairs case study - Dash model

Copyright (c) 2018 Jose Serna <jserna@uwaterloo.ca>
Copyright (c) 2018 Nancy Day <nday@uwaterloo.ca>

This file is part of the Musical Chairs B model.

The Musical Chairs Dash model is free software: you can redistribute
it and/or modify it under the terms of the GNU General Public License
as published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Musical Chairs Dash model is distributed in the hope that it will
be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Musical Chairs Dash model.  If not, see
<https://www.gnu.org/licenses/>.


The Musical Chairs case study is described in~\cite{Nissanke_1999} by
Nissanke.  The Musical Chairs Dash model is an adaptation of the
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

*/

open util/integer

sig Chairs, Players {}

abstract sig DshStates {}
abstract sig Game extends DshStates {} 
one sig Game_Start extends Game {} 
one sig Game_Walking extends Game {} 
one sig Game_Sitting extends Game {} 
one sig Game_End extends Game {} 

abstract sig DshEvents {}
abstract sig DshIntEvents extends DshEvents {} 
one sig Game_MusicStops extends DshIntEvents {} 
one sig Game_MusicStarts extends DshIntEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_events0: set DshEvents,
  Game_activePlayers: set Players,
  Game_activeChairs: set Chairs,
  Game_occupiedChairs: Chairs -> Players
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = Game_Start and
  (# (s.Game_activePlayers)) > (1) and
  (# (s.Game_activePlayers)) =
    ((1).((# (s.Game_activeChairs)).plus)) and
  (s.Game_activePlayers) = Players and
  (s.Game_activeChairs) = Chairs and
  (s.Game_occupiedChairs) = (none -> none)
}

pred Game_Sitting_EliminateLoser_pre [
	s: one DshSnapshot] {
  some (Game_Sitting & (s.dsh_conf0))
  !(Game in (s.dsh_sc_used0))
}


pred Game_Sitting_EliminateLoser_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - Game_Start) - Game_Walking) -
       Game_Sitting) - Game_End) + Game_Start)
  (sn.Game_activePlayers) = (Chairs.(s.Game_occupiedChairs)) and
  (# (sn.Game_activeChairs)) =
    ((1).((# (s.Game_activeChairs)).minus))
}

pred Game_Sitting_EliminateLoser [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Game_Sitting_EliminateLoser_pre
  sn.(s.Game_Sitting_EliminateLoser_post)
}

pred Game_Start_DeclareWinner_pre [
	s: one DshSnapshot] {
  some (Game_Start & (s.dsh_conf0))
  one (s.Game_activePlayers)
  !(Game in (s.dsh_sc_used0))
}


pred Game_Start_DeclareWinner_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - Game_Start) - Game_Walking) -
       Game_Sitting) - Game_End) + Game_End)
}

pred Game_Start_DeclareWinner [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Game_Start_DeclareWinner_pre
  sn.(s.Game_Start_DeclareWinner_post)
}

pred Game_Start_Walk_pre [
	s: one DshSnapshot] {
  some (Game_Start & (s.dsh_conf0))
  (# (s.Game_activePlayers)) > (1)
  !(Game in (s.dsh_sc_used0))
  Game_MusicStarts in (s.dsh_events0)
}


pred Game_Start_Walk_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - Game_Start) - Game_Walking) -
       Game_Sitting) - Game_End) + Game_Walking)
  (sn.Game_occupiedChairs) = (none -> none)
}

pred Game_Start_Walk [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Game_Start_Walk_pre
  sn.(s.Game_Start_Walk_post)
}

pred Game_Walking_Sit_pre [
	s: one DshSnapshot] {
  some (Game_Walking & (s.dsh_conf0))
  !(Game in (s.dsh_sc_used0))
  Game_MusicStops in (s.dsh_events0)
}


pred Game_Walking_Sit_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - Game_Start) - Game_Walking) -
       Game_Sitting) - Game_End) + Game_Sitting)
  (sn.Game_occupiedChairs) in
  ((s.Game_activeChairs) -> (s.Game_activePlayers)) and
  (sn.Game_activeChairs) = (s.Game_activeChairs) and
  (sn.Game_activePlayers) = (s.Game_activePlayers) and
  (all c: sn.Game_activeChairs | one
    (c.(sn.Game_occupiedChairs))) and
  (all p: Chairs.(sn.Game_occupiedChairs) | one
    ((sn.Game_occupiedChairs).p))
}

pred Game_Walking_Sit [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Game_Walking_Sit_pre
  sn.(s.Game_Walking_Sit_post)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.Game_Sitting_EliminateLoser) or
    sn.(s.Game_Start_DeclareWinner) or
    sn.(s.Game_Start_Walk) or
    sn.(s.Game_Walking_Sit) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}



