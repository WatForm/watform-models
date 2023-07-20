/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-07-20 15:37:52
*/

open util/boolean
open util/tcmc[DshSnapshot]

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

abstract sig Transitions {}
one sig NO_TRANS extends Transitions {} 
one sig Game_Sitting_EliminateLoser extends Transitions {} 
one sig Game_Start_DeclareWinner extends Transitions {} 
one sig Game_Start_Walk extends Transitions {} 
one sig Game_Walking_Sit extends Transitions {} 

abstract sig DshEvents {}
abstract sig DshIntEvents extends DshEvents {} 
one sig Game_MusicStarts extends DshIntEvents {} 
one sig Game_MusicStops extends DshIntEvents {} 

sig DshSnapshot {
  dsh_conf0: set DshStates,
  dsh_taken0: set Transitions,
  dsh_events0: set DshEvents,
  Game_activePlayers: set Players,
  Game_activeChairs: set Chairs,
  Game_occupiedChairs: Chairs -> Players
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = Game_Start &&
  (s.dsh_taken0) = NO_TRANS &&
  ((s.dsh_events0) :> DshIntEvents) = none &&
  (# (s.Game_activePlayers)) > (1) &&
  (# (s.Game_activePlayers)) = ((1).((#
    (s.Game_activeChairs)).plus)) &&
  (s.Game_activePlayers) = Players &&
  (s.Game_activeChairs) = Chairs &&
  (s.Game_occupiedChairs) = (none -> none)
}

pred Game_Sitting_EliminateLoser_pre [
	s: one DshSnapshot] {
  some (Game_Sitting & (s.dsh_conf0))
}


pred Game_Sitting_EliminateLoser_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((Game_Start + Game_Walking) + Game_Sitting) +
         Game_End)) + Game_Start)
  ((sn.Game_activePlayers) = (Chairs.(s.Game_occupiedChairs)) &&
   (# (sn.Game_activeChairs)) = ((1).((#
     (s.Game_activeChairs)).minus)))
  (sn.dsh_taken0) = Game_Sitting_EliminateLoser
  (s.Game_occupiedChairs) = (sn.Game_occupiedChairs)
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
}


pred Game_Start_DeclareWinner_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((Game_Start + Game_Walking) + Game_Sitting) +
         Game_End)) + Game_End)
  (sn.dsh_taken0) = Game_Start_DeclareWinner
  (s.Game_activePlayers) = (sn.Game_activePlayers)
  (s.Game_activeChairs) = (sn.Game_activeChairs)
  (s.Game_occupiedChairs) = (sn.Game_occupiedChairs)
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
  Game_MusicStarts in (s.dsh_events0)
}


pred Game_Start_Walk_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((Game_Start + Game_Walking) + Game_Sitting) +
         Game_End)) + Game_Walking)
  (sn.Game_occupiedChairs) = (none -> none)
  (sn.dsh_taken0) = Game_Start_Walk
  (s.Game_activePlayers) = (sn.Game_activePlayers)
  (s.Game_activeChairs) = (sn.Game_activeChairs)
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
  Game_MusicStops in (s.dsh_events0)
}


pred Game_Walking_Sit_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((Game_Start + Game_Walking) + Game_Sitting) +
         Game_End)) + Game_Sitting)
  ((sn.Game_occupiedChairs) in
   ((s.Game_activeChairs) -> (s.Game_activePlayers)) &&
   (sn.Game_activeChairs) = (s.Game_activeChairs) &&
   (sn.Game_activePlayers) = (s.Game_activePlayers) &&
   (all c: sn.Game_activeChairs | one
     (c.(sn.Game_occupiedChairs))) &&
   (all p: Chairs.(sn.Game_occupiedChairs) | one
     ((sn.Game_occupiedChairs).p)))
  (sn.dsh_taken0) = Game_Walking_Sit
}

pred Game_Walking_Sit [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Game_Walking_Sit_pre
  sn.(s.Game_Walking_Sit_post)
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_taken0) = NO_TRANS
  ((sn.dsh_events0) :> DshIntEvents) = none
  (sn.Game_activePlayers) = (s.Game_activePlayers)
  (sn.Game_activeChairs) = (s.Game_activeChairs)
  (sn.Game_occupiedChairs) = (s.Game_occupiedChairs)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.Game_Sitting_EliminateLoser) ||
    sn.(s.Game_Start_DeclareWinner) ||
    sn.(s.Game_Start_Walk) ||
    sn.(s.Game_Walking_Sit) ||
    !({ s.Game_Sitting_EliminateLoser_pre ||
          s.Game_Start_DeclareWinner_pre ||
          s.Game_Start_Walk_pre ||
          s.Game_Walking_Sit_pre }) &&
      sn.(s.dsh_stutter) }
}

fact allSnapshotsDifferent {
  (all s: one
  DshSnapshot,sn: one
  DshSnapshot | ((s.dsh_conf0) = (sn.dsh_conf0) &&
                   (s.dsh_taken0) = (sn.dsh_taken0) &&
                   (s.dsh_events0) = (sn.dsh_events0) &&
                   (s.Game_activePlayers) =
                     (sn.Game_activePlayers) &&
                   (s.Game_activeChairs) =
                     (sn.Game_activeChairs) &&
                   (s.Game_occupiedChairs) =
                     (sn.Game_occupiedChairs)) => (s = sn))
}

pred dsh_enough_operations {
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.Game_Sitting_EliminateLoser))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.Game_Start_DeclareWinner))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.Game_Start_Walk))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.Game_Walking_Sit))
}

pred dsh_reachability {
  (all s: one
  DshSnapshot | s in
                  (DshSnapshot.(tcmc/ks_s0 <: (*
                                  tcmc/ks_sigma))))
}

fact dsh_tcmc_fact {
  (all s: one
  DshSnapshot | (s in tcmc/ks_s0) <=> (s.dsh_initial))
  (all s: one
  DshSnapshot,sn: one
  DshSnapshot | ((s -> sn) in tcmc/ks_sigma) <=>
                  (sn.(s.dsh_small_step)))
}

// make sure the model is consistent
run {
    dsh_reachability
} for exactly 8 DshSnapshot, exactly 3 Players, exactly 2 Chairs expect 1

 // Get a significant scope
 run {
    dsh_reachability
    dsh_enough_operations
} for exactly 12 DshSnapshot, exactly 3 Players, exactly 2 Chairs expect 1


/******************************* PROPERTIES ***********************************/

/********************************* SAFETY *************************************/
assert safety {
    // number of players is walways 1 greater than number of chairs
    ctl_mc[ ag[{ s : DshSnapshot |
        #s.Game_activePlayers = (#s.Game_activeChairs).plus[1]}]]
}
check safety for exactly 8 DshSnapshot, exactly 3 Players , exactly 2 Chairs expect 0
    

/******************************** EXISTENTIAL *********************************/
one sig Alice extends Players {}
pred existential {
    // Alice wins in some instance
    ctl_mc[ef[{ s : DshSnapshot |
        Game_End in s.dsh_conf0 and s.Game_activePlayers = Alice }]]
}
run existential for exactly 8 DshSnapshot, exactly 3 Players, exactly 2 Chairs expect 0

/******************************* FINITE LIVENESS ******************************/
assert finiteLiveness {
    ctl_mc[af [{ s : DshSnapshot | Game_Sitting in s.dsh_conf0 }]]
}
check finiteLiveness for exactly 8 DshSnapshot, exactly 3 Players , exactly 2 Chairs expect 0

/**************************** INFINITE LIVENESS *******************************/
assert infiniteLiveness {
    // number of players eventually always reaches and remains at 1
    ctl_mc[af[ag[{ s : DshSnapshot | #s.Game_activePlayers = 1}]]]
}
check infiniteLiveness for exactly 8 DshSnapshot, exactly 3 Players , exactly 2 Chairs expect 0
    
/*
    How to run this model:

    dashcli -t -m tcmc musical-chairs.dsh
    dashcli musical-chairs-tcmc.als
*/


