/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-13 16:48:51
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/*******************************************************************************
 * Title: farmer.dsh
 * Authors: Jose Serna
 * Created: 2018-06-11
 * Last modified: 
 * 2023-06-07 Nancy Day slight syntax changes for newdash
 *
 * Notes: Adaptation to DASH from the original model available in the Alloy's
 *        libraries
 *
 ******************************************************************************/

abstract sig Object {
    eats: set Object
}
one sig Chicken, Farmer, Fox, Grain extends Object {}

fact eating {
    eats = Fox -> Chicken + Chicken -> Grain
}

abstract sig DshStates {}
abstract sig Puzzle extends DshStates {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  Puzzle_near: set Object,
  Puzzle_far: set Object
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = Puzzle and
  (s.Puzzle_near) = Object and
  no
  s.Puzzle_far
}

pred Puzzle_near2far_pre [
	s: one DshSnapshot] {
  some (Puzzle & (s.dsh_conf0))
  Farmer in s.Puzzle_near
  !(Puzzle in (s.dsh_sc_used0))
}


pred Puzzle_near2far_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Puzzle) + Puzzle)
  { (one x: (s.Puzzle_near) - Farmer | (sn.Puzzle_near) =
                                       ((((s.Puzzle_near) -
                                            Farmer) - x) -
                                          ((sn.Puzzle_near).eats)) and
                                       (sn.Puzzle_far) =
                                         (((s.Puzzle_far) +
                                             Farmer) + x)) or
    (sn.Puzzle_near) =
      (((s.Puzzle_near) - Farmer) - ((sn.Puzzle_near).eats)) and
      (sn.Puzzle_far) = ((s.Puzzle_far) + Farmer) }
}

pred Puzzle_near2far [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Puzzle_near2far_pre
  sn.(s.Puzzle_near2far_post)
}

pred Puzzle_far2near_pre [
	s: one DshSnapshot] {
  some (Puzzle & (s.dsh_conf0))
  Farmer in s.Puzzle_far
  !(Puzzle in (s.dsh_sc_used0))
}


pred Puzzle_far2near_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Puzzle) + Puzzle)
  { (one x: (s.Puzzle_far) - Farmer | (sn.Puzzle_far) =
                                      ((((s.Puzzle_far) -
                                           Farmer) - x) -
                                         ((sn.Puzzle_far).eats)) and
                                      (sn.Puzzle_near) =
                                        (((s.Puzzle_near) +
                                            Farmer) + x)) or
    (sn.Puzzle_far) =
      (((s.Puzzle_far) - Farmer) - ((sn.Puzzle_far).eats)) and
      (sn.Puzzle_near) = ((s.Puzzle_near) + Farmer) }
}

pred Puzzle_far2near [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Puzzle_far2near_pre
  sn.(s.Puzzle_far2near_post)
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
  (sn.Puzzle_near) = (s.Puzzle_near)
  (sn.Puzzle_far) = (s.Puzzle_far)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.Puzzle_near2far) or
    sn.(s.Puzzle_far2near) or
    !({ s.Puzzle_near2far_pre or s.Puzzle_far2near_pre }) and
      sn.(s.dsh_stutter) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}



