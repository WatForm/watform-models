/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-06 21:10:27
*/

open util/ordering[PID] as P0

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot
abstract sig DshStates {}
abstract sig Counter extends DshStates {} 
abstract sig Counter_Bit extends Counter {} 
one sig Counter_Bit_Bit1 extends Counter_Bit {} 
one sig Counter_Bit_Bit2 extends Counter_Bit {} 

abstract sig DshIds {}
sig PID extends DshIds {} 

abstract sig DshEvents {}
abstract sig DshIntEvents extends DshEvents {} 
one sig Counter_Bit_Tk1 extends DshIntEvents {} 
one sig Counter_Done extends DshIntEvents {} 
abstract sig DshEnvEvents extends DshEvents {} 
one sig Counter_Tk0 extends DshEnvEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_events0: set DshEvents,
  dsh_sc_used1: DshIds -> DshStates,
  dsh_conf1: DshIds -> DshStates,
  dsh_events1: DshIds -> DshEvents,
  dsh_stable: one boolean/Bool,
  Counter_current: one PID
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = none and
  (s.dsh_conf1) = (PID -> Counter_Bit_Bit1) and
  (s.dsh_sc_used1) = (none -> none) and
  ((s.dsh_events1) :> DshIntEvents) = (none -> none) and
  (s.Counter_current) = P0/first
  (s.dsh_stable).boolean/isTrue
}

pred Counter_Bit_currentBitToBit1_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> Counter_Bit_Bit2) & (s.dsh_conf1))
  p0_PID in s.Counter_current
  !(Counter in (s.dsh_sc_used0))
  !((p0_PID -> Counter_Bit) in (s.dsh_sc_used1))
  ((s.dsh_stable).boolean/isTrue)=>
    (Counter_Tk0 in ((s.dsh_events0) :> DshEnvEvents))
  else
    (Counter_Tk0 in (s.dsh_events0))

}


pred Counter_Bit_currentBitToBit1_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) - (p0_PID -> Counter_Bit_Bit1)) -
      (p0_PID -> Counter_Bit_Bit2)) +
     (p0_PID -> Counter_Bit_Bit1))
  ((p0_PID -> Counter_Bit_Tk1).((p0_PID -> Counter_Bit).(none.(none.(p0_PID.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              ((sn.dsh_events1) :> DshIntEvents) =
                (p0_PID -> Counter_Bit_Tk1))
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents) and
              ((sn.dsh_events1) :> DshIntEvents) =
                ((p0_PID -> Counter_Bit_Tk1) +
                   ((s.dsh_events1) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none and
              ((sn.dsh_events1) :> DshIntEvents) =
                (p0_PID -> Counter_Bit_Tk1) and
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_events1) =
                ((s.dsh_events1) +
                   (p0_PID -> Counter_Bit_Tk1)) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) + (p0_PID -> Counter_Bit)))
       )

}

pred Counter_Bit_currentBitToBit1_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents,
	dsh_scp1: DshIds -> DshStates,
	dsh_genEvs1: DshIds -> DshEvents] {
  some ((p0_PID -> Counter_Bit_Bit2) & (sn.dsh_conf1))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(Counter in dsh_scp0) and
       !((p0_PID -> Counter_Bit) in dsh_scp1) and
       Counter_Tk0 in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (Counter_Tk0 in ((s.dsh_events0) + dsh_genEvs0))

}

pred Counter_Bit_currentBitToBit1 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.Counter_Bit_currentBitToBit1_pre)
  p0_PID.(sn.(s.Counter_Bit_currentBitToBit1_post))
}

pred Counter_Bit_lastBitDone_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> Counter_Bit_Bit2) & (s.dsh_conf1))
  p0_PID in P0/last
  !(Counter in (s.dsh_sc_used0))
  !((p0_PID -> Counter_Bit) in (s.dsh_sc_used1))
  !((s.dsh_stable).boolean/isTrue) and
  (p0_PID -> Counter_Bit_Tk1) in (s.dsh_events1)
}


pred Counter_Bit_lastBitDone_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) - (p0_PID -> Counter_Bit_Bit1)) -
      (p0_PID -> Counter_Bit_Bit2)) +
     (p0_PID -> Counter_Bit_Bit1))
  ((none -> none).((p0_PID -> Counter_Bit).(Counter_Done.(none.(p0_PID.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              Counter_Done and
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (Counter_Done +
                 ((s.dsh_events0) :> DshIntEvents)) and
              ((sn.dsh_events1) :> DshIntEvents) =
                ((s.dsh_events1) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              Counter_Done and
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none and
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) + Counter_Done) and
              (sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) + (p0_PID -> Counter_Bit)))
       )

}

pred Counter_Bit_lastBitDone_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents,
	dsh_scp1: DshIds -> DshStates,
	dsh_genEvs1: DshIds -> DshEvents] {
  some ((p0_PID -> Counter_Bit_Bit2) & (sn.dsh_conf1))
  !((s.dsh_stable).boolean/isTrue) and
  (p0_PID -> Counter_Bit_Tk1) in
    ((s.dsh_events1) + dsh_genEvs1)
}

pred Counter_Bit_lastBitDone [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.Counter_Bit_lastBitDone_pre)
  p0_PID.(sn.(s.Counter_Bit_lastBitDone_post))
}

pred Counter_Bit_currentBitToBit2_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> Counter_Bit_Bit1) & (s.dsh_conf1))
  p0_PID in s.Counter_current
  !(Counter in (s.dsh_sc_used0))
  !((p0_PID -> Counter_Bit) in (s.dsh_sc_used1))
  ((s.dsh_stable).boolean/isTrue)=>
    (Counter_Tk0 in ((s.dsh_events0) :> DshEnvEvents))
  else
    (Counter_Tk0 in (s.dsh_events0))

}


pred Counter_Bit_currentBitToBit2_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) - (p0_PID -> Counter_Bit_Bit1)) -
      (p0_PID -> Counter_Bit_Bit2)) +
     (p0_PID -> Counter_Bit_Bit2))
  ((none -> none).((p0_PID -> Counter_Bit).(none.(none.(p0_PID.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents) and
              ((sn.dsh_events1) :> DshIntEvents) =
                ((s.dsh_events1) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none and
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) + (p0_PID -> Counter_Bit)))
       )

}

pred Counter_Bit_currentBitToBit2_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents,
	dsh_scp1: DshIds -> DshStates,
	dsh_genEvs1: DshIds -> DshEvents] {
  some ((p0_PID -> Counter_Bit_Bit1) & (sn.dsh_conf1))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(Counter in dsh_scp0) and
       !((p0_PID -> Counter_Bit) in dsh_scp1) and
       Counter_Tk0 in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (Counter_Tk0 in ((s.dsh_events0) + dsh_genEvs0))

}

pred Counter_Bit_currentBitToBit2 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.Counter_Bit_currentBitToBit2_pre)
  p0_PID.(sn.(s.Counter_Bit_currentBitToBit2_post))
}

pred Counter_Bit_nextBitToBit1_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> Counter_Bit_Bit2) & (s.dsh_conf1))
  p0_PID in ((s.Counter_current).P0/next) and
  ((s.Counter_current).P0/next) !in P0/last
  !(Counter in (s.dsh_sc_used0))
  !((p0_PID -> Counter_Bit) in (s.dsh_sc_used1))
  !((s.dsh_stable).boolean/isTrue) and
  (p0_PID -> Counter_Bit_Tk1) in (s.dsh_events1)
}


pred Counter_Bit_nextBitToBit1_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) - (p0_PID -> Counter_Bit_Bit1)) -
      (p0_PID -> Counter_Bit_Bit2)) +
     (p0_PID -> Counter_Bit_Bit1))
  (sn.Counter_current) = ((s.Counter_current).P0/next)
  ((none -> none).((p0_PID -> Counter_Bit).(none.(none.(p0_PID.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents) and
              ((sn.dsh_events1) :> DshIntEvents) =
                ((s.dsh_events1) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none and
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) + (p0_PID -> Counter_Bit)))
       )

}

pred Counter_Bit_nextBitToBit1_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents,
	dsh_scp1: DshIds -> DshStates,
	dsh_genEvs1: DshIds -> DshEvents] {
  some ((p0_PID -> Counter_Bit_Bit2) & (sn.dsh_conf1))
  !((s.dsh_stable).boolean/isTrue) and
  (p0_PID -> Counter_Bit_Tk1) in
    ((s.dsh_events1) + dsh_genEvs1)
}

pred Counter_Bit_nextBitToBit1 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.Counter_Bit_nextBitToBit1_pre)
  p0_PID.(sn.(s.Counter_Bit_nextBitToBit1_post))
}

pred Counter_Bit_nextBitToBit2_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> Counter_Bit_Bit1) & (s.dsh_conf1))
  p0_PID in ((s.Counter_current).P0/next)
  !(Counter in (s.dsh_sc_used0))
  !((p0_PID -> Counter_Bit) in (s.dsh_sc_used1))
  !((s.dsh_stable).boolean/isTrue) and
  (p0_PID -> Counter_Bit_Tk1) in (s.dsh_events1)
}


pred Counter_Bit_nextBitToBit2_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) - (p0_PID -> Counter_Bit_Bit1)) -
      (p0_PID -> Counter_Bit_Bit2)) +
     (p0_PID -> Counter_Bit_Bit2))
  ((none -> none).((p0_PID -> Counter_Bit).(none.(none.(p0_PID.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents) and
              ((sn.dsh_events1) :> DshIntEvents) =
                ((s.dsh_events1) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none and
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) + (p0_PID -> Counter_Bit)))
       )

}

pred Counter_Bit_nextBitToBit2_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents,
	dsh_scp1: DshIds -> DshStates,
	dsh_genEvs1: DshIds -> DshEvents] {
  some ((p0_PID -> Counter_Bit_Bit1) & (sn.dsh_conf1))
  !((s.dsh_stable).boolean/isTrue) and
  (p0_PID -> Counter_Bit_Tk1) in
    ((s.dsh_events1) + dsh_genEvs1)
}

pred Counter_Bit_nextBitToBit2 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.Counter_Bit_nextBitToBit2_pre)
  p0_PID.(sn.(s.Counter_Bit_nextBitToBit2_post))
}

pred _testIfNextStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents,
	dsh_scp1: DshIds -> DshStates,
	dsh_genEvs1: DshIds -> DshEvents] {
  !(dsh_genEvs1.(dsh_scp1.(dsh_genEvs0.(dsh_scp0.(p0_PID.(sn.(s.Counter_Bit_currentBitToBit1_enabledAfterStep)))))))
  !(dsh_genEvs1.(dsh_scp1.(dsh_genEvs0.(dsh_scp0.(p0_PID.(sn.(s.Counter_Bit_lastBitDone_enabledAfterStep)))))))
  !(dsh_genEvs1.(dsh_scp1.(dsh_genEvs0.(dsh_scp0.(p0_PID.(sn.(s.Counter_Bit_currentBitToBit2_enabledAfterStep)))))))
  !(dsh_genEvs1.(dsh_scp1.(dsh_genEvs0.(dsh_scp0.(p0_PID.(sn.(s.Counter_Bit_nextBitToBit1_enabledAfterStep)))))))
  !(dsh_genEvs1.(dsh_scp1.(dsh_genEvs0.(dsh_scp0.(p0_PID.(sn.(s.Counter_Bit_nextBitToBit2_enabledAfterStep)))))))
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (some p0_PID: one
  PID | { p0_PID.(sn.(s.Counter_Bit_currentBitToBit1)) or
            p0_PID.(sn.(s.Counter_Bit_lastBitDone)) or
            p0_PID.(sn.(s.Counter_Bit_currentBitToBit2)) or
            p0_PID.(sn.(s.Counter_Bit_nextBitToBit1)) or
            p0_PID.(sn.(s.Counter_Bit_nextBitToBit2)) })
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}

