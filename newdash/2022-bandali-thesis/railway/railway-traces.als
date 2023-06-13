/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-13 17:09:42
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/* The Railway case study - Dash model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Railway Dash model.

The Railway Dash model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Railway Dash model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Railway Dash model.  If not, see
<https://www.gnu.org/licenses/>.


The Railway case study (train scheduling deadlock avoidance model) is
described in~\cite{DBLP:journals/sttt/MazzantiFS18} by Frappier et al.
The Railway Dash model is an adaptation of the original model(s)
presented there.

@Article{DBLP:journals/sttt/MazzantiFS18,
  author    = {Franco Mazzanti and Alessio Ferrari and Giorgio Oronzo
                  Spagnolo},
  title     = {Towards formal methods diversity in railways: an
                  experience report with seven frameworks},
  year      = 2018,
  volume    = 20,
  number    = 3,
  pages     = {263-288},
  doi       = {10.1007/s10009-018-0488-3},
  url       = {https://doi.org/10.1007/s10009-018-0488-3},
  journal   = {{STTT}},
  timestamp = {Fri, 30 Nov 2018 13:26:45 +0100},
  biburl    = {https://dblp.org/rec/bib/journals/sttt/MazzantiFS18},
  bibsource = {dblp computer science bibliography, https://dblp.org}
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

open util/integer

abstract sig Train {}
one sig t0, t1, t2, t3, t4, t5, t6, t7 extends Train {}

abstract sig Station {}
one sig s1,  s2,  s3,  s4,  s5,  s6,  s7,  s8,  s9, s10,
        s11, s12, s13, s14, s15, s16, s17, s18, s19, s20,
        s21, s22, s23, s24, s25, s26, s27 extends Station {}

// let indices = { 0 + 1 + 2 + 3 + 4 + 5 + 6 }
// let rs = { 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 }
// let LA = 7
// let LB = 7

one sig Const {
    T0, T1, T2, T3, T4, T5, T6, T7: { 0 + 1 + 2 + 3 + 4 + 5 + 6 } -> Station,
    A0, A1, A2, A3, A4, A5, A6, A7,
    B0, B1, B2, B3, B4, B5, B6, B7: { 0 + 1 + 2 + 3 + 4 + 5 + 6 } -> { -1 + 0 + 1 }
}

abstract sig DshStates {}
abstract sig Railway extends DshStates {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  Railway_P0: one
((((((0) + (1)) + (2)) + (3)) + (4)) + (5)) + (6),
  Railway_P1: one
((((((0) + (1)) + (2)) + (3)) + (4)) + (5)) + (6),
  Railway_P2: one
((((((0) + (1)) + (2)) + (3)) + (4)) + (5)) + (6),
  Railway_P3: one
((((((0) + (1)) + (2)) + (3)) + (4)) + (5)) + (6),
  Railway_P4: one
((((((0) + (1)) + (2)) + (3)) + (4)) + (5)) + (6),
  Railway_P5: one
((((((0) + (1)) + (2)) + (3)) + (4)) + (5)) + (6),
  Railway_P6: one
((((((0) + (1)) + (2)) + (3)) + (4)) + (5)) + (6),
  Railway_P7: one
((((((0) + (1)) + (2)) + (3)) + (4)) + (5)) + (6),
  Railway_RA: one
((((((((0) + (1)) + (2)) + (3)) + (4)) + (5)) + (6)) + (7)) +
  (8),
  Railway_RB: one
((((((((0) + (1)) + (2)) + (3)) + (4)) + (5)) + (6)) + (7)) +
  (8),
  Railway_ct: one Train
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = Railway and
  (s.Railway_P0) = (0) and
  (s.Railway_P1) = (0) and
  (s.Railway_P2) = (0) and
  (s.Railway_P3) = (0) and
  (s.Railway_P4) = (0) and
  (s.Railway_P5) = (0) and
  (s.Railway_P6) = (0) and
  (s.Railway_P7) = (0) and
  (s.Railway_RA) = (1) and
  (s.Railway_RB) = (1)
}

fact inv {  (Const.T0) =
  ((((((Int[0] -> s1) + (Int[1] -> s9)) + (Int[2] -> s10)) +
       (Int[3] -> s13)) + (Int[4] -> s15)) + (Int[5] -> s20)) +
    (Int[6] -> s23) and
  (Const.T1) =
    ((((((Int[0] -> s3) + (Int[1] -> s9)) + (Int[2] -> s10)) +
         (Int[3] -> s13)) + (Int[4] -> s15)) +
       (Int[5] -> s20)) + (Int[6] -> s24) and
  (Const.T2) =
    ((((((Int[0] -> s5) + (Int[1] -> s27)) + (Int[2] -> s11)) +
         (Int[3] -> s13)) + (Int[4] -> s16)) +
       (Int[5] -> s20)) + (Int[6] -> s25) and
  (Const.T3) =
    ((((((Int[0] -> s7) + (Int[1] -> s27)) + (Int[2] -> s11)) +
         (Int[3] -> s13)) + (Int[4] -> s16)) +
       (Int[5] -> s20)) + (Int[6] -> s26) and
  (Const.T4) =
    ((((((Int[0] -> s23) + (Int[1] -> s22)) +
          (Int[2] -> s17)) + (Int[3] -> s18)) +
        (Int[4] -> s11)) + (Int[5] -> s9)) + (Int[6] -> s2) and
  (Const.T5) =
    ((((((Int[0] -> s24) + (Int[1] -> s22)) +
          (Int[2] -> s17)) + (Int[3] -> s18)) +
        (Int[4] -> s11)) + (Int[5] -> s9)) + (Int[6] -> s4) and
  (Const.T6) =
    ((((((Int[0] -> s25) + (Int[1] -> s22)) +
          (Int[2] -> s17)) + (Int[3] -> s18)) +
        (Int[4] -> s12)) + (Int[5] -> s27)) + (Int[6] -> s6) and
  (Const.T7) =
    ((((((Int[0] -> s26) + (Int[1] -> s22)) +
          (Int[2] -> s17)) + (Int[3] -> s18)) +
        (Int[4] -> s12)) + (Int[5] -> s27)) + (Int[6] -> s8) and
  (Const.A0) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[0])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[-1])) +
      (Int[6] -> Int[0]) and
  (Const.A1) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[0])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[-1])) +
      (Int[6] -> Int[0]) and
  (Const.A2) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[0])) +
          (Int[2] -> Int[1])) + (Int[3] -> Int[-1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[1])) +
      (Int[6] -> Int[0]) and
  (Const.A3) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[0])) +
          (Int[2] -> Int[1])) + (Int[3] -> Int[-1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[0])) +
      (Int[6] -> Int[0]) and
  (Const.A4) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[1])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[0])) +
        (Int[4] -> Int[-1])) + (Int[5] -> Int[0])) +
      (Int[6] -> Int[0]) and
  (Const.A5) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[1])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[0])) +
        (Int[4] -> Int[-1])) + (Int[5] -> Int[0])) +
      (Int[6] -> Int[0]) and
  (Const.A6) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[0])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[-1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[0])) +
      (Int[6] -> Int[0]) and
  (Const.A7) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[1])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[-1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[0])) +
      (Int[6] -> Int[0]) and
  (Const.B0) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[0])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[-1])) +
      (Int[6] -> Int[0]) and
  (Const.B1) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[0])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[-1])) +
      (Int[6] -> Int[0]) and
  (Const.B2) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[0])) +
          (Int[2] -> Int[1])) + (Int[3] -> Int[-1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[0])) +
      (Int[6] -> Int[0]) and
  (Const.B3) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[0])) +
          (Int[2] -> Int[1])) + (Int[3] -> Int[-1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[1])) +
      (Int[6] -> Int[0]) and
  (Const.B4) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[1])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[0])) +
        (Int[4] -> Int[-1])) + (Int[5] -> Int[0])) +
      (Int[6] -> Int[0]) and
  (Const.B5) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[1])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[0])) +
        (Int[4] -> Int[-1])) + (Int[5] -> Int[0])) +
      (Int[6] -> Int[0]) and
  (Const.B6) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[1])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[-1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[0])) +
      (Int[6] -> Int[0]) and
  (Const.B7) =
    ((((((Int[0] -> Int[0]) + (Int[1] -> Int[0])) +
          (Int[2] -> Int[0])) + (Int[3] -> Int[-1])) +
        (Int[4] -> Int[0])) + (Int[5] -> Int[0])) +
      (Int[6] -> Int[0])
}

pred Railway_move_train3_pre [
	s: one DshSnapshot] {
  some (Railway & (s.dsh_conf0))
  (s.Railway_ct) = t3 and
  s.Railway_P3 < (6) and
  (((1).((s.Railway_P3).plus)).(Const.T3)) !=
    ((s.Railway_P0).(Const.T0)) and
  (((1).((s.Railway_P3).plus)).(Const.T3)) !=
    ((s.Railway_P1).(Const.T1)) and
  (((1).((s.Railway_P3).plus)).(Const.T3)) !=
    ((s.Railway_P2).(Const.T2)) and
  (((1).((s.Railway_P3).plus)).(Const.T3)) !=
    ((s.Railway_P4).(Const.T4)) and
  (((1).((s.Railway_P3).plus)).(Const.T3)) !=
    ((s.Railway_P5).(Const.T5)) and
  (((1).((s.Railway_P3).plus)).(Const.T3)) !=
    ((s.Railway_P6).(Const.T6)) and
  (((1).((s.Railway_P3).plus)).(Const.T3)) !=
    ((s.Railway_P7).(Const.T7)) and
  (7).(((((1).((s.Railway_P3).plus)).(Const.A3)).((s.Railway_RA).plus)).lte) and
  (7).(((((1).((s.Railway_P3).plus)).(Const.B3)).((s.Railway_RB).plus)).lte)
  !(Railway in (s.dsh_sc_used0))
}


pred Railway_move_train3_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Railway) + Railway)
  (sn.Railway_P3) = ((1).((s.Railway_P3).plus)) and
  (sn.Railway_RA) =
    (((sn.Railway_P3).(Const.A3)).((s.Railway_RA).plus)) and
  (sn.Railway_RB) =
    (((sn.Railway_P3).(Const.B3)).((s.Railway_RB).plus))
  (s.Railway_P0) = (sn.Railway_P0)
  (s.Railway_P1) = (sn.Railway_P1)
  (s.Railway_P2) = (sn.Railway_P2)
  (s.Railway_P4) = (sn.Railway_P4)
  (s.Railway_P5) = (sn.Railway_P5)
  (s.Railway_P6) = (sn.Railway_P6)
  (s.Railway_P7) = (sn.Railway_P7)
}

pred Railway_move_train3 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Railway_move_train3_pre
  sn.(s.Railway_move_train3_post)
}

pred Railway_move_train2_pre [
	s: one DshSnapshot] {
  some (Railway & (s.dsh_conf0))
  (s.Railway_ct) = t2 and
  s.Railway_P2 < (6) and
  (((1).((s.Railway_P2).plus)).(Const.T2)) !=
    ((s.Railway_P0).(Const.T0)) and
  (((1).((s.Railway_P2).plus)).(Const.T2)) !=
    ((s.Railway_P1).(Const.T1)) and
  (((1).((s.Railway_P2).plus)).(Const.T2)) !=
    ((s.Railway_P3).(Const.T3)) and
  (((1).((s.Railway_P2).plus)).(Const.T2)) !=
    ((s.Railway_P4).(Const.T4)) and
  (((1).((s.Railway_P2).plus)).(Const.T2)) !=
    ((s.Railway_P5).(Const.T5)) and
  (((1).((s.Railway_P2).plus)).(Const.T2)) !=
    ((s.Railway_P6).(Const.T6)) and
  (((1).((s.Railway_P2).plus)).(Const.T2)) !=
    ((s.Railway_P7).(Const.T7)) and
  (7).(((((1).((s.Railway_P2).plus)).(Const.A2)).((s.Railway_RA).plus)).lte) and
  (7).(((((1).((s.Railway_P2).plus)).(Const.B2)).((s.Railway_RB).plus)).lte)
  !(Railway in (s.dsh_sc_used0))
}


pred Railway_move_train2_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Railway) + Railway)
  (sn.Railway_P2) = ((1).((s.Railway_P2).plus)) and
  (sn.Railway_RA) =
    (((sn.Railway_P2).(Const.A2)).((s.Railway_RA).plus)) and
  (sn.Railway_RB) =
    (((sn.Railway_P2).(Const.B2)).((s.Railway_RB).plus))
  (s.Railway_P0) = (sn.Railway_P0)
  (s.Railway_P1) = (sn.Railway_P1)
  (s.Railway_P3) = (sn.Railway_P3)
  (s.Railway_P4) = (sn.Railway_P4)
  (s.Railway_P5) = (sn.Railway_P5)
  (s.Railway_P6) = (sn.Railway_P6)
  (s.Railway_P7) = (sn.Railway_P7)
}

pred Railway_move_train2 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Railway_move_train2_pre
  sn.(s.Railway_move_train2_post)
}

pred Railway_move_train1_pre [
	s: one DshSnapshot] {
  some (Railway & (s.dsh_conf0))
  (s.Railway_ct) = t1 and
  s.Railway_P1 < (6) and
  (((1).((s.Railway_P1).plus)).(Const.T1)) !=
    ((s.Railway_P0).(Const.T0)) and
  (((1).((s.Railway_P1).plus)).(Const.T1)) !=
    ((s.Railway_P2).(Const.T2)) and
  (((1).((s.Railway_P1).plus)).(Const.T1)) !=
    ((s.Railway_P3).(Const.T3)) and
  (((1).((s.Railway_P1).plus)).(Const.T1)) !=
    ((s.Railway_P4).(Const.T4)) and
  (((1).((s.Railway_P1).plus)).(Const.T1)) !=
    ((s.Railway_P5).(Const.T5)) and
  (((1).((s.Railway_P1).plus)).(Const.T1)) !=
    ((s.Railway_P6).(Const.T6)) and
  (((1).((s.Railway_P1).plus)).(Const.T1)) !=
    ((s.Railway_P7).(Const.T7)) and
  (7).(((((1).((s.Railway_P1).plus)).(Const.A1)).((s.Railway_RA).plus)).lte) and
  (7).(((((1).((s.Railway_P1).plus)).(Const.B1)).((s.Railway_RB).plus)).lte)
  !(Railway in (s.dsh_sc_used0))
}


pred Railway_move_train1_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Railway) + Railway)
  (sn.Railway_P1) = ((1).((s.Railway_P1).plus)) and
  (sn.Railway_RA) =
    (((sn.Railway_P1).(Const.A1)).((s.Railway_RA).plus)) and
  (sn.Railway_RB) =
    (((sn.Railway_P1).(Const.B1)).((s.Railway_RB).plus))
  (s.Railway_P0) = (sn.Railway_P0)
  (s.Railway_P2) = (sn.Railway_P2)
  (s.Railway_P3) = (sn.Railway_P3)
  (s.Railway_P4) = (sn.Railway_P4)
  (s.Railway_P5) = (sn.Railway_P5)
  (s.Railway_P6) = (sn.Railway_P6)
  (s.Railway_P7) = (sn.Railway_P7)
}

pred Railway_move_train1 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Railway_move_train1_pre
  sn.(s.Railway_move_train1_post)
}

pred Railway_move_train0_pre [
	s: one DshSnapshot] {
  some (Railway & (s.dsh_conf0))
  (s.Railway_ct) = t0 and
  s.Railway_P0 < (6) and
  (((1).((s.Railway_P0).plus)).(Const.T0)) !=
    ((s.Railway_P1).(Const.T1)) and
  (((1).((s.Railway_P0).plus)).(Const.T0)) !=
    ((s.Railway_P2).(Const.T2)) and
  (((1).((s.Railway_P0).plus)).(Const.T0)) !=
    ((s.Railway_P3).(Const.T3)) and
  (((1).((s.Railway_P0).plus)).(Const.T0)) !=
    ((s.Railway_P4).(Const.T4)) and
  (((1).((s.Railway_P0).plus)).(Const.T0)) !=
    ((s.Railway_P5).(Const.T5)) and
  (((1).((s.Railway_P0).plus)).(Const.T0)) !=
    ((s.Railway_P6).(Const.T6)) and
  (((1).((s.Railway_P0).plus)).(Const.T0)) !=
    ((s.Railway_P7).(Const.T7)) and
  (7).(((((1).((s.Railway_P0).plus)).(Const.A0)).((s.Railway_RA).plus)).lte) and
  (7).(((((1).((s.Railway_P0).plus)).(Const.B0)).((s.Railway_RB).plus)).lte)
  !(Railway in (s.dsh_sc_used0))
}


pred Railway_move_train0_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Railway) + Railway)
  (sn.Railway_P0) = ((1).((s.Railway_P0).plus)) and
  (sn.Railway_RA) =
    (((sn.Railway_P0).(Const.A0)).((s.Railway_RA).plus)) and
  (sn.Railway_RB) =
    (((sn.Railway_P0).(Const.B0)).((s.Railway_RB).plus))
  (s.Railway_P1) = (sn.Railway_P1)
  (s.Railway_P2) = (sn.Railway_P2)
  (s.Railway_P3) = (sn.Railway_P3)
  (s.Railway_P4) = (sn.Railway_P4)
  (s.Railway_P5) = (sn.Railway_P5)
  (s.Railway_P6) = (sn.Railway_P6)
  (s.Railway_P7) = (sn.Railway_P7)
}

pred Railway_move_train0 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Railway_move_train0_pre
  sn.(s.Railway_move_train0_post)
}

pred Railway_move_train7_pre [
	s: one DshSnapshot] {
  some (Railway & (s.dsh_conf0))
  (s.Railway_ct) = t7 and
  s.Railway_P7 < (6) and
  (((1).((s.Railway_P7).plus)).(Const.T7)) !=
    ((s.Railway_P0).(Const.T0)) and
  (((1).((s.Railway_P7).plus)).(Const.T7)) !=
    ((s.Railway_P1).(Const.T1)) and
  (((1).((s.Railway_P7).plus)).(Const.T7)) !=
    ((s.Railway_P2).(Const.T2)) and
  (((1).((s.Railway_P7).plus)).(Const.T7)) !=
    ((s.Railway_P3).(Const.T3)) and
  (((1).((s.Railway_P7).plus)).(Const.T7)) !=
    ((s.Railway_P4).(Const.T4)) and
  (((1).((s.Railway_P7).plus)).(Const.T7)) !=
    ((s.Railway_P5).(Const.T5)) and
  (((1).((s.Railway_P7).plus)).(Const.T7)) !=
    ((s.Railway_P6).(Const.T6)) and
  (7).(((((1).((s.Railway_P7).plus)).(Const.A7)).((s.Railway_RA).plus)).lte) and
  (7).(((((1).((s.Railway_P7).plus)).(Const.B7)).((s.Railway_RB).plus)).lte)
  !(Railway in (s.dsh_sc_used0))
}


pred Railway_move_train7_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Railway) + Railway)
  (sn.Railway_P7) = ((1).((s.Railway_P7).plus)) and
  (sn.Railway_RA) =
    (((sn.Railway_P7).(Const.A7)).((s.Railway_RA).plus)) and
  (sn.Railway_RB) =
    (((sn.Railway_P7).(Const.B7)).((s.Railway_RB).plus))
  (s.Railway_P0) = (sn.Railway_P0)
  (s.Railway_P1) = (sn.Railway_P1)
  (s.Railway_P2) = (sn.Railway_P2)
  (s.Railway_P3) = (sn.Railway_P3)
  (s.Railway_P4) = (sn.Railway_P4)
  (s.Railway_P5) = (sn.Railway_P5)
  (s.Railway_P6) = (sn.Railway_P6)
}

pred Railway_move_train7 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Railway_move_train7_pre
  sn.(s.Railway_move_train7_post)
}

pred Railway_move_train6_pre [
	s: one DshSnapshot] {
  some (Railway & (s.dsh_conf0))
  (s.Railway_ct) = t6 and
  s.Railway_P6 < (6) and
  (((1).((s.Railway_P6).plus)).(Const.T6)) !=
    ((s.Railway_P0).(Const.T0)) and
  (((1).((s.Railway_P6).plus)).(Const.T6)) !=
    ((s.Railway_P1).(Const.T1)) and
  (((1).((s.Railway_P6).plus)).(Const.T6)) !=
    ((s.Railway_P2).(Const.T2)) and
  (((1).((s.Railway_P6).plus)).(Const.T6)) !=
    ((s.Railway_P3).(Const.T3)) and
  (((1).((s.Railway_P6).plus)).(Const.T6)) !=
    ((s.Railway_P4).(Const.T4)) and
  (((1).((s.Railway_P6).plus)).(Const.T6)) !=
    ((s.Railway_P5).(Const.T5)) and
  (((1).((s.Railway_P6).plus)).(Const.T6)) !=
    ((s.Railway_P7).(Const.T7)) and
  (7).(((((1).((s.Railway_P6).plus)).(Const.A6)).((s.Railway_RA).plus)).lte) and
  (7).(((((1).((s.Railway_P6).plus)).(Const.B6)).((s.Railway_RB).plus)).lte)
  !(Railway in (s.dsh_sc_used0))
}


pred Railway_move_train6_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Railway) + Railway)
  (sn.Railway_P6) = ((1).((s.Railway_P6).plus)) and
  (sn.Railway_RA) =
    (((sn.Railway_P6).(Const.A6)).((s.Railway_RA).plus)) and
  (sn.Railway_RB) =
    (((sn.Railway_P6).(Const.B6)).((s.Railway_RB).plus))
  (s.Railway_P0) = (sn.Railway_P0)
  (s.Railway_P1) = (sn.Railway_P1)
  (s.Railway_P2) = (sn.Railway_P2)
  (s.Railway_P3) = (sn.Railway_P3)
  (s.Railway_P4) = (sn.Railway_P4)
  (s.Railway_P5) = (sn.Railway_P5)
  (s.Railway_P7) = (sn.Railway_P7)
}

pred Railway_move_train6 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Railway_move_train6_pre
  sn.(s.Railway_move_train6_post)
}

pred Railway_move_train5_pre [
	s: one DshSnapshot] {
  some (Railway & (s.dsh_conf0))
  (s.Railway_ct) = t5 and
  s.Railway_P5 < (6) and
  (((1).((s.Railway_P5).plus)).(Const.T5)) !=
    ((s.Railway_P0).(Const.T0)) and
  (((1).((s.Railway_P5).plus)).(Const.T5)) !=
    ((s.Railway_P1).(Const.T1)) and
  (((1).((s.Railway_P5).plus)).(Const.T5)) !=
    ((s.Railway_P2).(Const.T2)) and
  (((1).((s.Railway_P5).plus)).(Const.T5)) !=
    ((s.Railway_P3).(Const.T3)) and
  (((1).((s.Railway_P5).plus)).(Const.T5)) !=
    ((s.Railway_P4).(Const.T4)) and
  (((1).((s.Railway_P5).plus)).(Const.T5)) !=
    ((s.Railway_P6).(Const.T6)) and
  (((1).((s.Railway_P5).plus)).(Const.T5)) !=
    ((s.Railway_P7).(Const.T7)) and
  (7).(((((1).((s.Railway_P5).plus)).(Const.A5)).((s.Railway_RA).plus)).lte) and
  (7).(((((1).((s.Railway_P5).plus)).(Const.B5)).((s.Railway_RB).plus)).lte)
  !(Railway in (s.dsh_sc_used0))
}


pred Railway_move_train5_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Railway) + Railway)
  (sn.Railway_P5) = ((1).((s.Railway_P5).plus)) and
  (sn.Railway_RA) =
    (((sn.Railway_P5).(Const.A5)).((s.Railway_RA).plus)) and
  (sn.Railway_RB) =
    (((sn.Railway_P5).(Const.B5)).((s.Railway_RB).plus))
  (s.Railway_P0) = (sn.Railway_P0)
  (s.Railway_P1) = (sn.Railway_P1)
  (s.Railway_P2) = (sn.Railway_P2)
  (s.Railway_P3) = (sn.Railway_P3)
  (s.Railway_P4) = (sn.Railway_P4)
  (s.Railway_P6) = (sn.Railway_P6)
  (s.Railway_P7) = (sn.Railway_P7)
}

pred Railway_move_train5 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Railway_move_train5_pre
  sn.(s.Railway_move_train5_post)
}

pred Railway_move_train4_pre [
	s: one DshSnapshot] {
  some (Railway & (s.dsh_conf0))
  (s.Railway_ct) = t4 and
  s.Railway_P4 < (6) and
  (((1).((s.Railway_P4).plus)).(Const.T4)) !=
    ((s.Railway_P0).(Const.T0)) and
  (((1).((s.Railway_P4).plus)).(Const.T4)) !=
    ((s.Railway_P1).(Const.T1)) and
  (((1).((s.Railway_P4).plus)).(Const.T4)) !=
    ((s.Railway_P2).(Const.T2)) and
  (((1).((s.Railway_P4).plus)).(Const.T4)) !=
    ((s.Railway_P3).(Const.T3)) and
  (((1).((s.Railway_P4).plus)).(Const.T4)) !=
    ((s.Railway_P5).(Const.T5)) and
  (((1).((s.Railway_P4).plus)).(Const.T4)) !=
    ((s.Railway_P6).(Const.T6)) and
  (((1).((s.Railway_P4).plus)).(Const.T4)) !=
    ((s.Railway_P7).(Const.T7)) and
  (7).(((((1).((s.Railway_P4).plus)).(Const.A4)).((s.Railway_RA).plus)).lte) and
  (7).(((((1).((s.Railway_P4).plus)).(Const.B4)).((s.Railway_RB).plus)).lte)
  !(Railway in (s.dsh_sc_used0))
}


pred Railway_move_train4_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Railway) + Railway)
  (sn.Railway_P4) = ((1).((s.Railway_P4).plus)) and
  (sn.Railway_RA) =
    (((sn.Railway_P4).(Const.A4)).((s.Railway_RA).plus)) and
  (sn.Railway_RB) =
    (((sn.Railway_P4).(Const.B4)).((s.Railway_RB).plus))
  (s.Railway_P0) = (sn.Railway_P0)
  (s.Railway_P1) = (sn.Railway_P1)
  (s.Railway_P2) = (sn.Railway_P2)
  (s.Railway_P3) = (sn.Railway_P3)
  (s.Railway_P5) = (sn.Railway_P5)
  (s.Railway_P6) = (sn.Railway_P6)
  (s.Railway_P7) = (sn.Railway_P7)
}

pred Railway_move_train4 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Railway_move_train4_pre
  sn.(s.Railway_move_train4_post)
}

pred Railway_choose_train_pre [
	s: one DshSnapshot] {
  some (Railway & (s.dsh_conf0))
  !(Railway in (s.dsh_sc_used0))
}


pred Railway_choose_train_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Railway) + Railway)
  { (s.Railway_ct) = t0 and (sn.Railway_ct) = t1 or
    (s.Railway_ct) = t1 and (sn.Railway_ct) = t2 or
    (s.Railway_ct) = t2 and (sn.Railway_ct) = t3 or
    (s.Railway_ct) = t3 and (sn.Railway_ct) = t4 or
    (s.Railway_ct) = t4 and (sn.Railway_ct) = t5 or
    (s.Railway_ct) = t5 and (sn.Railway_ct) = t6 or
    (s.Railway_ct) = t6 and (sn.Railway_ct) = t7 or
    (s.Railway_ct) = t7 and (sn.Railway_ct) = t0 }
  (s.Railway_RA) = (sn.Railway_RA)
  (s.Railway_P0) = (sn.Railway_P0)
  (s.Railway_RB) = (sn.Railway_RB)
  (s.Railway_P1) = (sn.Railway_P1)
  (s.Railway_P2) = (sn.Railway_P2)
  (s.Railway_P3) = (sn.Railway_P3)
  (s.Railway_P4) = (sn.Railway_P4)
  (s.Railway_P5) = (sn.Railway_P5)
  (s.Railway_P6) = (sn.Railway_P6)
  (s.Railway_P7) = (sn.Railway_P7)
}

pred Railway_choose_train [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Railway_choose_train_pre
  sn.(s.Railway_choose_train_post)
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
  (sn.Railway_P0) = (s.Railway_P0)
  (sn.Railway_P1) = (s.Railway_P1)
  (sn.Railway_P2) = (s.Railway_P2)
  (sn.Railway_P3) = (s.Railway_P3)
  (sn.Railway_P4) = (s.Railway_P4)
  (sn.Railway_P5) = (s.Railway_P5)
  (sn.Railway_P6) = (s.Railway_P6)
  (sn.Railway_P7) = (s.Railway_P7)
  (sn.Railway_RA) = (s.Railway_RA)
  (sn.Railway_RB) = (s.Railway_RB)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.Railway_move_train3) or
    sn.(s.Railway_move_train2) or
    sn.(s.Railway_move_train1) or
    sn.(s.Railway_move_train0) or
    sn.(s.Railway_move_train7) or
    sn.(s.Railway_move_train6) or
    sn.(s.Railway_move_train5) or
    sn.(s.Railway_move_train4) or
    sn.(s.Railway_choose_train) or
    !({ s.Railway_move_train3_pre or
          s.Railway_move_train2_pre or
          s.Railway_move_train1_pre or
          s.Railway_move_train0_pre or
          s.Railway_move_train7_pre or
          s.Railway_move_train6_pre or
          s.Railway_move_train5_pre or
          s.Railway_move_train4_pre or
          s.Railway_choose_train_pre }) and
      sn.(s.dsh_stutter) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}

