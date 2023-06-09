/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-08 21:12:01
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/*******************************************************************************
 * Title: bit-counter.dsh
 * Authors: Jose Serna
 * Created: 14-04-2018
 * Last modified: 07-06-2023 Nancy Day
 *
 * Notes: Two bit counter model taken from Shahram's PhD thesis
 *
 *        Shahram Esmaeilsabzali. Perscriptive Semantics for Big-Step Modelling Languages.
 *        PhD thesis, University of Waterloo, David R. Cheriton School of Computer Science, 2011
 *        https://cs.uwaterloo.ca/~nday/pdf/theses/2011-esmaeilsabzali-phd-thesis.pdf
 *
 ******************************************************************************/

abstract sig DshStates {}
abstract sig Counter extends DshStates {} 
abstract sig Counter_Bit1 extends Counter {} 
one sig Counter_Bit1_Bit11 extends Counter_Bit1 {} 
one sig Counter_Bit1_Bit12 extends Counter_Bit1 {} 
abstract sig Counter_Bit2 extends Counter {} 
one sig Counter_Bit2_Bit21 extends Counter_Bit2 {} 
one sig Counter_Bit2_Bit22 extends Counter_Bit2 {} 

abstract sig DshEvents {}
abstract sig DshIntEvents extends DshEvents {} 
one sig Counter_Bit1_Tk1 extends DshIntEvents {} 
one sig Counter_Bit2_Done extends DshIntEvents {} 
abstract sig DshEnvEvents extends DshEvents {} 
one sig Counter_Tk0 extends DshEnvEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_events0: set DshEvents,
  dsh_stable: one boolean/Bool
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = (Counter_Bit1_Bit11 + Counter_Bit2_Bit21)
  (s.dsh_stable).boolean/isTrue
}

pred Counter_Bit2_T4_pre [
	s: one DshSnapshot] {
  some (Counter_Bit2_Bit22 & (s.dsh_conf0))
  !(Counter in (s.dsh_sc_used0))
  !(Counter_Bit2 in (s.dsh_sc_used0))
  !((s.dsh_stable).boolean/isTrue) and
  Counter_Bit1_Tk1 in (s.dsh_events0)
}


pred Counter_Bit2_T4_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - Counter_Bit2_Bit21) -
      Counter_Bit2_Bit22) + Counter_Bit2_Bit21)
  (Counter_Bit2_Done.(Counter_Bit2.(sn.(s._testIfNextStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              Counter_Bit2_Done)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (Counter_Bit2_Done +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              Counter_Bit2_Done and
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) + Counter_Bit2_Done) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) + Counter_Bit2))
       )

}

pred Counter_Bit2_T4_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (Counter_Bit2_Bit22 & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  Counter_Bit1_Tk1 in ((s.dsh_events0) + dsh_genEvs0)
}

pred Counter_Bit2_T4 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Counter_Bit2_T4_pre
  sn.(s.Counter_Bit2_T4_post)
}

pred Counter_Bit1_T2_pre [
	s: one DshSnapshot] {
  some (Counter_Bit1_Bit12 & (s.dsh_conf0))
  !(Counter in (s.dsh_sc_used0))
  !(Counter_Bit1 in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (Counter_Tk0 in ((s.dsh_events0) :> DshEnvEvents))
  else
    (Counter_Tk0 in (s.dsh_events0))

}


pred Counter_Bit1_T2_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - Counter_Bit1_Bit11) -
      Counter_Bit1_Bit12) + Counter_Bit1_Bit11)
  (Counter_Bit1_Tk1.(Counter_Bit1.(sn.(s._testIfNextStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              Counter_Bit1_Tk1)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (Counter_Bit1_Tk1 +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              Counter_Bit1_Tk1 and
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) + Counter_Bit1_Tk1) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) + Counter_Bit1))
       )

}

pred Counter_Bit1_T2_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (Counter_Bit1_Bit12 & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(Counter in dsh_scp0) and
       !(Counter_Bit1 in dsh_scp0) and
       Counter_Tk0 in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (Counter_Tk0 in ((s.dsh_events0) + dsh_genEvs0))

}

pred Counter_Bit1_T2 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Counter_Bit1_T2_pre
  sn.(s.Counter_Bit1_T2_post)
}

pred Counter_Bit2_T3_pre [
	s: one DshSnapshot] {
  some (Counter_Bit2_Bit21 & (s.dsh_conf0))
  !(Counter in (s.dsh_sc_used0))
  !(Counter_Bit2 in (s.dsh_sc_used0))
  !((s.dsh_stable).boolean/isTrue) and
  Counter_Bit1_Tk1 in (s.dsh_events0)
}


pred Counter_Bit2_T3_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - Counter_Bit2_Bit21) -
      Counter_Bit2_Bit22) + Counter_Bit2_Bit22)
  (none.(Counter_Bit2.(sn.(s._testIfNextStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + Counter_Bit2))
       )

}

pred Counter_Bit2_T3_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (Counter_Bit2_Bit21 & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  Counter_Bit1_Tk1 in ((s.dsh_events0) + dsh_genEvs0)
}

pred Counter_Bit2_T3 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Counter_Bit2_T3_pre
  sn.(s.Counter_Bit2_T3_post)
}

pred Counter_Bit1_T1_pre [
	s: one DshSnapshot] {
  some (Counter_Bit1_Bit11 & (s.dsh_conf0))
  !(Counter in (s.dsh_sc_used0))
  !(Counter_Bit1 in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (Counter_Tk0 in ((s.dsh_events0) :> DshEnvEvents))
  else
    (Counter_Tk0 in (s.dsh_events0))

}


pred Counter_Bit1_T1_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - Counter_Bit1_Bit11) -
      Counter_Bit1_Bit12) + Counter_Bit1_Bit12)
  (none.(Counter_Bit1.(sn.(s._testIfNextStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + Counter_Bit1))
       )

}

pred Counter_Bit1_T1_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (Counter_Bit1_Bit11 & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(Counter in dsh_scp0) and
       !(Counter_Bit1 in dsh_scp0) and
       Counter_Tk0 in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (Counter_Tk0 in ((s.dsh_events0) + dsh_genEvs0))

}

pred Counter_Bit1_T1 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Counter_Bit1_T1_pre
  sn.(s.Counter_Bit1_T1_post)
}

pred _testIfNextStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.Counter_Bit2_T4_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.Counter_Bit1_T2_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.Counter_Bit2_T3_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.Counter_Bit1_T1_enabledAfterStep))))
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.Counter_Bit2_T4) or
    sn.(s.Counter_Bit1_T2) or
    sn.(s.Counter_Bit2_T3) or
    sn.(s.Counter_Bit1_T1) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}




