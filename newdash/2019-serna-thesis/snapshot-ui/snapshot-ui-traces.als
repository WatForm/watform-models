/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-13 17:09:32
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/*******************************************************************************
 * Title: SnapshotUI.dsh
 * Authors: Jose Serna
 * Created: 2018-11-09
 * Last modified: 
 * 2023-06-07 Nancy Day modifications for new Dash
 *
 * Notes: Dash model of the UI model for the "Snapshot" application described by
 *        Hillel Wayne in https://www.hillelwayne.com/post/formally-specifying-uis
 *
 ******************************************************************************/
abstract sig DshStates {}
abstract sig SnapshotUI extends DshStates {} 
one sig SnapshotUI_LoginPage extends SnapshotUI {} 
abstract sig SnapshotUI_Snapshot extends SnapshotUI {} 
abstract sig SnapshotUI_Snapshot_Reports extends SnapshotUI_Snapshot {} 
one sig SnapshotUI_Snapshot_Reports_Summary extends SnapshotUI_Snapshot_Reports {} 
one sig SnapshotUI_Snapshot_Reports_Students extends SnapshotUI_Snapshot_Reports {} 
one sig SnapshotUI_Snapshot_Reports_Standards extends SnapshotUI_Snapshot_Reports {} 
one sig SnapshotUI_Snapshot_Answers extends SnapshotUI_Snapshot {} 

abstract sig DshEvents {}
abstract sig DshIntEvents extends DshEvents {} 
one sig SnapshotUI_login extends DshIntEvents {} 
one sig SnapshotUI_logout extends DshIntEvents {} 
one sig SnapshotUI_summary extends DshIntEvents {} 
one sig SnapshotUI_students extends DshIntEvents {} 
one sig SnapshotUI_close extends DshIntEvents {} 
one sig SnapshotUI_answer extends DshIntEvents {} 
one sig SnapshotUI_standards extends DshIntEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_events0: set DshEvents
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = SnapshotUI_LoginPage
}

pred SnapshotUI_Snapshot_Reports_SeeStandards_pre [
	s: one DshSnapshot] {
  some (SnapshotUI_Snapshot_Reports & (s.dsh_conf0))
  !(SnapshotUI in (s.dsh_sc_used0))
  SnapshotUI_standards in (s.dsh_events0)
  !(s.SnapshotUI_Snapshot_Logout_pre)
}


pred SnapshotUI_Snapshot_Reports_SeeStandards_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - SnapshotUI_Snapshot_Reports_Summary) -
       SnapshotUI_Snapshot_Reports_Students) -
      SnapshotUI_Snapshot_Reports_Standards) +
     SnapshotUI_Snapshot_Reports_Standards)
}

pred SnapshotUI_Snapshot_Reports_SeeStandards [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.SnapshotUI_Snapshot_Reports_SeeStandards_pre
  sn.(s.SnapshotUI_Snapshot_Reports_SeeStandards_post)
}

pred SnapshotUI_LoginPage_Login_pre [
	s: one DshSnapshot] {
  some (SnapshotUI_LoginPage & (s.dsh_conf0))
  !(SnapshotUI in (s.dsh_sc_used0))
  SnapshotUI_login in (s.dsh_events0)
}


pred SnapshotUI_LoginPage_Login_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((s.dsh_conf0) - SnapshotUI_LoginPage) -
         SnapshotUI_Snapshot_Reports_Summary) -
        SnapshotUI_Snapshot_Reports_Students) -
       SnapshotUI_Snapshot_Reports_Standards) -
      SnapshotUI_Snapshot_Answers) +
     SnapshotUI_Snapshot_Reports_Summary)
}

pred SnapshotUI_LoginPage_Login [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.SnapshotUI_LoginPage_Login_pre
  sn.(s.SnapshotUI_LoginPage_Login_post)
}

pred SnapshotUI_Snapshot_Reports_SeeSummary_pre [
	s: one DshSnapshot] {
  some (SnapshotUI_Snapshot_Reports & (s.dsh_conf0))
  !(SnapshotUI in (s.dsh_sc_used0))
  SnapshotUI_summary in (s.dsh_events0)
  !(s.SnapshotUI_Snapshot_Logout_pre)
}


pred SnapshotUI_Snapshot_Reports_SeeSummary_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - SnapshotUI_Snapshot_Reports_Summary) -
       SnapshotUI_Snapshot_Reports_Students) -
      SnapshotUI_Snapshot_Reports_Standards) +
     SnapshotUI_Snapshot_Reports_Summary)
}

pred SnapshotUI_Snapshot_Reports_SeeSummary [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.SnapshotUI_Snapshot_Reports_SeeSummary_pre
  sn.(s.SnapshotUI_Snapshot_Reports_SeeSummary_post)
}

pred SnapshotUI_Snapshot_Logout_pre [
	s: one DshSnapshot] {
  some (SnapshotUI_Snapshot & (s.dsh_conf0))
  !(SnapshotUI in (s.dsh_sc_used0))
  SnapshotUI_logout in (s.dsh_events0)
}


pred SnapshotUI_Snapshot_Logout_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((s.dsh_conf0) - SnapshotUI_LoginPage) -
         SnapshotUI_Snapshot_Reports_Summary) -
        SnapshotUI_Snapshot_Reports_Students) -
       SnapshotUI_Snapshot_Reports_Standards) -
      SnapshotUI_Snapshot_Answers) + SnapshotUI_LoginPage)
}

pred SnapshotUI_Snapshot_Logout [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.SnapshotUI_Snapshot_Logout_pre
  sn.(s.SnapshotUI_Snapshot_Logout_post)
}

pred SnapshotUI_Snapshot_Reports_Students_SeeAnswers_pre [
	s: one DshSnapshot] {
  some (SnapshotUI_Snapshot_Reports_Students & (s.dsh_conf0))
  !(SnapshotUI in (s.dsh_sc_used0))
  SnapshotUI_answer in (s.dsh_events0)
  !(s.SnapshotUI_Snapshot_Reports_SeeStandards_pre)
  !(s.SnapshotUI_Snapshot_Reports_SeeSummary_pre)
  !(s.SnapshotUI_Snapshot_Logout_pre)
  !(s.SnapshotUI_Snapshot_Reports_SeeStudents_pre)
}


pred SnapshotUI_Snapshot_Reports_Students_SeeAnswers_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - SnapshotUI_Snapshot_Reports_Summary) -
        SnapshotUI_Snapshot_Reports_Students) -
       SnapshotUI_Snapshot_Reports_Standards) -
      SnapshotUI_Snapshot_Answers) +
     SnapshotUI_Snapshot_Answers)
}

pred SnapshotUI_Snapshot_Reports_Students_SeeAnswers [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.SnapshotUI_Snapshot_Reports_Students_SeeAnswers_pre
  sn.(s.SnapshotUI_Snapshot_Reports_Students_SeeAnswers_post)
}

pred SnapshotUI_Snapshot_Answers_SeeStudents_pre [
	s: one DshSnapshot] {
  some (SnapshotUI_Snapshot_Answers & (s.dsh_conf0))
  !(SnapshotUI in (s.dsh_sc_used0))
  SnapshotUI_close in (s.dsh_events0)
  !(s.SnapshotUI_Snapshot_Logout_pre)
}


pred SnapshotUI_Snapshot_Answers_SeeStudents_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - SnapshotUI_Snapshot_Reports_Summary) -
        SnapshotUI_Snapshot_Reports_Students) -
       SnapshotUI_Snapshot_Reports_Standards) -
      SnapshotUI_Snapshot_Answers) +
     SnapshotUI_Snapshot_Reports_Students)
}

pred SnapshotUI_Snapshot_Answers_SeeStudents [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.SnapshotUI_Snapshot_Answers_SeeStudents_pre
  sn.(s.SnapshotUI_Snapshot_Answers_SeeStudents_post)
}

pred SnapshotUI_Snapshot_Reports_SeeStudents_pre [
	s: one DshSnapshot] {
  some (SnapshotUI_Snapshot_Reports & (s.dsh_conf0))
  !(SnapshotUI in (s.dsh_sc_used0))
  SnapshotUI_students in (s.dsh_events0)
  !(s.SnapshotUI_Snapshot_Logout_pre)
}


pred SnapshotUI_Snapshot_Reports_SeeStudents_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - SnapshotUI_Snapshot_Reports_Summary) -
       SnapshotUI_Snapshot_Reports_Students) -
      SnapshotUI_Snapshot_Reports_Standards) +
     SnapshotUI_Snapshot_Reports_Students)
}

pred SnapshotUI_Snapshot_Reports_SeeStudents [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.SnapshotUI_Snapshot_Reports_SeeStudents_pre
  sn.(s.SnapshotUI_Snapshot_Reports_SeeStudents_post)
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
  ((sn.dsh_events0) :> DshIntEvents) = none
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.SnapshotUI_Snapshot_Reports_SeeStandards) or
    sn.(s.SnapshotUI_LoginPage_Login) or
    sn.(s.SnapshotUI_Snapshot_Reports_SeeSummary) or
    sn.(s.SnapshotUI_Snapshot_Logout) or
    sn.(s.SnapshotUI_Snapshot_Reports_Students_SeeAnswers) or
    sn.(s.SnapshotUI_Snapshot_Answers_SeeStudents) or
    sn.(s.SnapshotUI_Snapshot_Reports_SeeStudents) or
    !({ s.SnapshotUI_Snapshot_Reports_SeeStandards_pre or
          s.SnapshotUI_LoginPage_Login_pre or
          s.SnapshotUI_Snapshot_Reports_SeeSummary_pre or
          s.SnapshotUI_Snapshot_Logout_pre or
          s.SnapshotUI_Snapshot_Reports_Students_SeeAnswers_pre or
          s.SnapshotUI_Snapshot_Answers_SeeStudents_pre or
          s.SnapshotUI_Snapshot_Reports_SeeStudents_pre }) and
      sn.(s.dsh_stutter) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}



