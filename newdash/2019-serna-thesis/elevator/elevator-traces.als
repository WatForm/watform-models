/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-11 19:17:36
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/*******************************************************************************
 * Title: elevator.dsh
 * Authors: Jose Serna
 * Created: 03-04-2019
 * Last modified: 
 * 2023-06-08 Nancy Day updates for new dash
 *
 * Notes: Dash elevator model from Farheen's MMath thesis. The model should be
 *        checked with the option Vars unchaged set.
 *
 *        Sabria Farheen. Improvements to Transitive-Closure-based Model Checking in Alloy. 
 *        MMath thesis, University of Waterloo, David R. Cheriton School of Computer Science, 2018
 *        https://cs.uwaterloo.ca/~nday/pdf/theses/2018-01-farheen-mmath-thesis.pdf
 *
 ******************************************************************************/
open util/ordering[Floor]
open util/boolean
open util/integer

sig Floor {}
abstract sig Direction {}
one sig Up, Down extends Direction {}

abstract sig DshStates {}
abstract sig Elevator extends DshStates {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  Elevator_direction: one Direction,
  Elevator_called: set Floor,
  Elevator_maintenance: Int,
  Elevator_current: set Floor
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = Elevator and
  no
  s.Elevator_called and
  (s.Elevator_maintenance) = (1) and
  (s.Elevator_direction) = Down and
  (s.Elevator_current) = (Floor.max)
}

pred Elevator_Idle_pre [
	s: one DshSnapshot] {
  some (Elevator & (s.dsh_conf0))
  no s.Elevator_called and (s.Elevator_current) = (Floor.min)
  !(Elevator in (s.dsh_sc_used0))
}


pred Elevator_Idle_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Elevator) + Elevator)
  (sn.Elevator_current) = (s.Elevator_current) and
  (sn.Elevator_maintenance) = (0) and
  (s.Elevator_called) - (sn.Elevator_current) in
    sn.Elevator_called and
  sn.Elevator_current !in sn.Elevator_called
}

pred Elevator_Idle [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Elevator_Idle_pre
  sn.(s.Elevator_Idle_post)
}

pred Elevator_DefaultToGround_pre [
	s: one DshSnapshot] {
  some (Elevator & (s.dsh_conf0))
  no s.Elevator_called and (Floor.min) !in s.Elevator_current
  !(Elevator in (s.dsh_sc_used0))
}


pred Elevator_DefaultToGround_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Elevator) + Elevator)
  (sn.Elevator_current) = (Floor.min) and
  (sn.Elevator_direction) = Down and
  (s.Elevator_called) - (sn.Elevator_current) in
    sn.Elevator_called and
  sn.Elevator_current !in sn.Elevator_called
}

pred Elevator_DefaultToGround [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Elevator_DefaultToGround_pre
  sn.(s.Elevator_DefaultToGround_post)
}

pred Elevator_maintenance_pre [
	s: one DshSnapshot] {
  some (Elevator & (s.dsh_conf0))
  (s.Elevator_maintenance) = (2)
  !(Elevator in (s.dsh_sc_used0))
}


pred Elevator_maintenance_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Elevator) + Elevator)
  (sn.Elevator_current) = (Floor.min) and
  (sn.Elevator_direction) = Down and
  (sn.Elevator_maintenance) = (0) and
  (s.Elevator_called) - (sn.Elevator_current) in
    sn.Elevator_called and
  sn.Elevator_current !in sn.Elevator_called
}

pred Elevator_maintenance [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Elevator_maintenance_pre
  sn.(s.Elevator_maintenance_post)
}

pred Elevator_ChangeDirToDown_pre [
	s: one DshSnapshot] {
  some (Elevator & (s.dsh_conf0))
  some
  s.Elevator_called and
  s.Elevator_maintenance < (2) and
  (s.Elevator_direction) = Up and
  no
  (((s.Elevator_current).nexts) & s.Elevator_called)
  !(Elevator in (s.dsh_sc_used0))
}


pred Elevator_ChangeDirToDown_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Elevator) + Elevator)
  (sn.Elevator_current) = (s.Elevator_current) and
  (sn.Elevator_direction) = Down and
  (sn.Elevator_maintenance) =
    ((1).((s.Elevator_maintenance).plus)) and
  (s.Elevator_called) - (sn.Elevator_current) in
    sn.Elevator_called and
  sn.Elevator_current !in sn.Elevator_called
}

pred Elevator_ChangeDirToDown [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Elevator_ChangeDirToDown_pre
  sn.(s.Elevator_ChangeDirToDown_post)
}

pred Elevator_MoveUp_pre [
	s: one DshSnapshot] {
  some (Elevator & (s.dsh_conf0))
  some
  s.Elevator_called and
  (s.Elevator_direction) = Up and
  some
  (((s.Elevator_current).nexts) & s.Elevator_called)
  !(Elevator in (s.dsh_sc_used0))
}


pred Elevator_MoveUp_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Elevator) + Elevator)
  (sn.Elevator_current) =
  ((((s.Elevator_current).nexts) & s.Elevator_called).min) and
  sn.Elevator_current !in sn.Elevator_called and
  (s.Elevator_called) - (sn.Elevator_current) in
    sn.Elevator_called
}

pred Elevator_MoveUp [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Elevator_MoveUp_pre
  sn.(s.Elevator_MoveUp_post)
}

pred Elevator_ChangeDirToUp_pre [
	s: one DshSnapshot] {
  some (Elevator & (s.dsh_conf0))
  some
  s.Elevator_called and
  s.Elevator_maintenance < (2) and
  (s.Elevator_direction) = Down and
  no
  (((s.Elevator_current).prevs) & s.Elevator_called)
  !(Elevator in (s.dsh_sc_used0))
}


pred Elevator_ChangeDirToUp_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Elevator) + Elevator)
  (sn.Elevator_current) = (s.Elevator_current) and
  (sn.Elevator_direction) = Up and
  (sn.Elevator_maintenance) =
    ((1).((s.Elevator_maintenance).plus)) and
  (s.Elevator_called) - (sn.Elevator_current) in
    sn.Elevator_called and
  sn.Elevator_current !in sn.Elevator_called
}

pred Elevator_ChangeDirToUp [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Elevator_ChangeDirToUp_pre
  sn.(s.Elevator_ChangeDirToUp_post)
}

pred Elevator_MoveDown_pre [
	s: one DshSnapshot] {
  some (Elevator & (s.dsh_conf0))
  some
  s.Elevator_called and
  (s.Elevator_direction) = Down and
  some
  (((s.Elevator_current).prevs) & s.Elevator_called)
  !(Elevator in (s.dsh_sc_used0))
}


pred Elevator_MoveDown_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Elevator) + Elevator)
  (sn.Elevator_current) =
  ((((s.Elevator_current).prevs) & s.Elevator_called).max) and
  sn.Elevator_current !in sn.Elevator_called and
  (s.Elevator_called) - (sn.Elevator_current) in
    sn.Elevator_called
}

pred Elevator_MoveDown [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Elevator_MoveDown_pre
  sn.(s.Elevator_MoveDown_post)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.Elevator_Idle) or
    sn.(s.Elevator_DefaultToGround) or
    sn.(s.Elevator_maintenance) or
    sn.(s.Elevator_ChangeDirToDown) or
    sn.(s.Elevator_MoveUp) or
    sn.(s.Elevator_ChangeDirToUp) or
    sn.(s.Elevator_MoveDown) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}

