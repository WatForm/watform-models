/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-28 16:50:03
*/

open util/ordering[PID] as P0

open util/boolean
open util/tcmc[DshSnapshot]
abstract sig DshStates {}
abstract sig Counter extends DshStates {} 
abstract sig DshScopes {}
one sig CounterScope extends DshScopes {} 
one sig Counter_BitScope extends DshScopes {} 
abstract sig Counter_Bit extends Counter {} 
one sig Counter_Bit_Bit1Scope extends DshScopes {} 
one sig Counter_Bit_Bit1 extends Counter_Bit {} 
one sig Counter_Bit_Bit2Scope extends DshScopes {} 
one sig Counter_Bit_Bit2 extends Counter_Bit {} 

abstract sig Transitions {}
one sig NO_TRANS extends Transitions {} 
one sig Counter_Bit_currentBitToBit1 extends Transitions {} 
one sig Counter_Bit_lastBitDone extends Transitions {} 
one sig Counter_Bit_currentBitToBit2 extends Transitions {} 
one sig Counter_Bit_nextBitToBit1 extends Transitions {} 
one sig Counter_Bit_nextBitToBit2 extends Transitions {} 

abstract sig DshIds {}
sig PID extends DshIds {} 

abstract sig DshEvents {}
abstract sig DshIntEvents extends DshEvents {} 
one sig Counter_Bit_Tk1 extends DshIntEvents {} 
one sig Counter_Done extends DshIntEvents {} 
abstract sig DshEnvEvents extends DshEvents {} 
one sig Counter_Tk0 extends DshEnvEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshScopes,
  dsh_conf0: set DshStates,
  dsh_taken0: set Transitions,
  dsh_events0: set DshEvents,
  dsh_sc_used1: DshIds -> DshScopes,
  dsh_conf1: DshIds -> DshStates,
  dsh_taken1: DshIds -> Transitions,
  dsh_events1: DshIds -> DshEvents,
  dsh_stable: one boolean/Bool,
  Counter_current: one PID
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = none &&
  (s.dsh_conf1) = (PID -> Counter_Bit_Bit1) &&
  (s.dsh_sc_used0) = none &&
  (s.dsh_taken0) = NO_TRANS &&
  ((s.dsh_events0) :> DshIntEvents) = none &&
  (s.dsh_sc_used1) = (none -> none) &&
  (s.dsh_taken1) = (none -> none) &&
  ((s.dsh_events1) :> DshIntEvents) = (none -> none) &&
  (s.Counter_current) = P0/first
  (s.dsh_stable).boolean/isTrue
}

pred Counter_Bit_currentBitToBit1_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> Counter_Bit_Bit2) & (s.dsh_conf1))
  p0_PID in s.Counter_current
  !(CounterScope in (s.dsh_sc_used0))
  !((p0_PID -> Counter_BitScope) in (s.dsh_sc_used1))
  {((s.dsh_stable).boolean/isTrue)=>
    (Counter_Tk0 in ((s.dsh_events0) :> DshEnvEvents))
  else
    (Counter_Tk0 in (s.dsh_events0))}

}


pred Counter_Bit_currentBitToBit1_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_PID -> Counter_Bit_Bit1) +
         (p0_PID -> Counter_Bit_Bit2))) +
     (p0_PID -> Counter_Bit_Bit1))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) = (p0_PID -> Counter_Bit_currentBitToBit1)
  (s.Counter_current) = (sn.Counter_current)
  {((p0_PID -> Counter_Bit_Tk1).((p0_PID -> Counter_Bit).(none.(none.(p0_PID.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events1) :> DshIntEvents) =
                (p0_PID -> Counter_Bit_Tk1))
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents) &&
              ((sn.dsh_events1) :> DshIntEvents) =
                ((p0_PID -> Counter_Bit_Tk1) +
                   ((s.dsh_events1) :> DshIntEvents)))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshIntEvents) =
                (p0_PID -> Counter_Bit_Tk1) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_events1) =
                ((s.dsh_events1) +
                   (p0_PID -> Counter_Bit_Tk1)) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_PID -> Counter_BitScope)))}
       )}

}

pred Counter_Bit_currentBitToBit1_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some ((p0_PID -> Counter_Bit_Bit2) & (sn.dsh_conf1))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(Counter in sc0) &&
       !((p0_PID -> Counter_Bit) in sc1) &&
       Counter_Tk0 in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (Counter_Tk0 in ((s.dsh_events0) + genEvs0))}

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
  !(CounterScope in (s.dsh_sc_used0))
  !((p0_PID -> Counter_BitScope) in (s.dsh_sc_used1))
  !((s.dsh_stable).boolean/isTrue) &&
  (p0_PID -> Counter_Bit_Tk1) in (s.dsh_events1)
}


pred Counter_Bit_lastBitDone_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_PID -> Counter_Bit_Bit1) +
         (p0_PID -> Counter_Bit_Bit2))) +
     (p0_PID -> Counter_Bit_Bit1))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) = (p0_PID -> Counter_Bit_lastBitDone)
  (s.Counter_current) = (sn.Counter_current)
  {((none -> none).((p0_PID -> Counter_Bit).(Counter_Done.(none.(p0_PID.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              Counter_Done &&
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (Counter_Done +
                 ((s.dsh_events0) :> DshIntEvents)) &&
              ((sn.dsh_events1) :> DshIntEvents) =
                ((s.dsh_events1) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              Counter_Done &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) + Counter_Done) &&
              (sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_PID -> Counter_BitScope)))}
       )}

}

pred Counter_Bit_lastBitDone_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some ((p0_PID -> Counter_Bit_Bit2) & (sn.dsh_conf1))
  !((s.dsh_stable).boolean/isTrue) &&
  (p0_PID -> Counter_Bit_Tk1) in ((s.dsh_events1) + genEvs1)
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
  !(CounterScope in (s.dsh_sc_used0))
  !((p0_PID -> Counter_BitScope) in (s.dsh_sc_used1))
  {((s.dsh_stable).boolean/isTrue)=>
    (Counter_Tk0 in ((s.dsh_events0) :> DshEnvEvents))
  else
    (Counter_Tk0 in (s.dsh_events0))}

}


pred Counter_Bit_currentBitToBit2_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_PID -> Counter_Bit_Bit1) +
         (p0_PID -> Counter_Bit_Bit2))) +
     (p0_PID -> Counter_Bit_Bit2))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) = (p0_PID -> Counter_Bit_currentBitToBit2)
  (s.Counter_current) = (sn.Counter_current)
  {((none -> none).((p0_PID -> Counter_Bit).(none.(none.(p0_PID.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents) &&
              ((sn.dsh_events1) :> DshIntEvents) =
                ((s.dsh_events1) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_PID -> Counter_BitScope)))}
       )}

}

pred Counter_Bit_currentBitToBit2_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some ((p0_PID -> Counter_Bit_Bit1) & (sn.dsh_conf1))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(Counter in sc0) &&
       !((p0_PID -> Counter_Bit) in sc1) &&
       Counter_Tk0 in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (Counter_Tk0 in ((s.dsh_events0) + genEvs0))}

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
  p0_PID in ((s.Counter_current).P0/next) &&
  ((s.Counter_current).P0/next) !in P0/last
  !(CounterScope in (s.dsh_sc_used0))
  !((p0_PID -> Counter_BitScope) in (s.dsh_sc_used1))
  !((s.dsh_stable).boolean/isTrue) &&
  (p0_PID -> Counter_Bit_Tk1) in (s.dsh_events1)
}


pred Counter_Bit_nextBitToBit1_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_PID -> Counter_Bit_Bit1) +
         (p0_PID -> Counter_Bit_Bit2))) +
     (p0_PID -> Counter_Bit_Bit1))
  (sn.Counter_current) = ((s.Counter_current).P0/next)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) = (p0_PID -> Counter_Bit_nextBitToBit1)
  {((none -> none).((p0_PID -> Counter_Bit).(none.(none.(p0_PID.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents) &&
              ((sn.dsh_events1) :> DshIntEvents) =
                ((s.dsh_events1) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_PID -> Counter_BitScope)))}
       )}

}

pred Counter_Bit_nextBitToBit1_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some ((p0_PID -> Counter_Bit_Bit2) & (sn.dsh_conf1))
  !((s.dsh_stable).boolean/isTrue) &&
  (p0_PID -> Counter_Bit_Tk1) in ((s.dsh_events1) + genEvs1)
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
  !(CounterScope in (s.dsh_sc_used0))
  !((p0_PID -> Counter_BitScope) in (s.dsh_sc_used1))
  !((s.dsh_stable).boolean/isTrue) &&
  (p0_PID -> Counter_Bit_Tk1) in (s.dsh_events1)
}


pred Counter_Bit_nextBitToBit2_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_PID -> Counter_Bit_Bit1) +
         (p0_PID -> Counter_Bit_Bit2))) +
     (p0_PID -> Counter_Bit_Bit2))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) = (p0_PID -> Counter_Bit_nextBitToBit2)
  (s.Counter_current) = (sn.Counter_current)
  {((none -> none).((p0_PID -> Counter_Bit).(none.(none.(p0_PID.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents) &&
              ((sn.dsh_events1) :> DshIntEvents) =
                ((s.dsh_events1) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshIntEvents) =
                (none -> none) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_PID -> Counter_BitScope)))}
       )}

}

pred Counter_Bit_nextBitToBit2_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some ((p0_PID -> Counter_Bit_Bit1) & (sn.dsh_conf1))
  !((s.dsh_stable).boolean/isTrue) &&
  (p0_PID -> Counter_Bit_Tk1) in ((s.dsh_events1) + genEvs1)
}

pred Counter_Bit_nextBitToBit2 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.Counter_Bit_nextBitToBit2_pre)
  p0_PID.(sn.(s.Counter_Bit_nextBitToBit2_post))
}

pred _nextIsStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_PID.(sn.(s.Counter_Bit_currentBitToBit1_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_PID.(sn.(s.Counter_Bit_lastBitDone_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_PID.(sn.(s.Counter_Bit_currentBitToBit2_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_PID.(sn.(s.Counter_Bit_nextBitToBit1_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_PID.(sn.(s.Counter_Bit_nextBitToBit2_enabledAfterStep)))))))
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_stable) = (s.dsh_stable)
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
  (sn.dsh_taken0) = NO_TRANS
  ((sn.dsh_events0) :> DshIntEvents) = none
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_sc_used1) = (s.dsh_sc_used1)
  (sn.dsh_taken1) = (none -> none)
  ((sn.dsh_events1) :> DshIntEvents) = (none -> none)
  (sn.Counter_current) = (s.Counter_current)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { (some p0_PID: one
      PID | { p0_PID.(sn.(s.Counter_Bit_currentBitToBit1)) ||
                p0_PID.(sn.(s.Counter_Bit_lastBitDone)) ||
                p0_PID.(sn.(s.Counter_Bit_currentBitToBit2)) ||
                p0_PID.(sn.(s.Counter_Bit_nextBitToBit1)) ||
                p0_PID.(sn.(s.Counter_Bit_nextBitToBit2)) }) ||
    !((some p0_PID: one
         PID | { p0_PID.(s.Counter_Bit_currentBitToBit1_pre) ||
                   p0_PID.(s.Counter_Bit_lastBitDone_pre) ||
                   p0_PID.(s.Counter_Bit_currentBitToBit2_pre) ||
                   p0_PID.(s.Counter_Bit_nextBitToBit1_pre) ||
                   p0_PID.(s.Counter_Bit_nextBitToBit2_pre) })) &&
      sn.(s.dsh_stutter) }
}

fact dsh_complete_big_steps {
  (all s: one
  DshSnapshot | ((s.dsh_stable).boolean/isFalse) =>
                  ((some sn: one
                      DshSnapshot | sn.(s.dsh_small_step))))
}

fact allSnapshotsDifferent {
  (all s: one
  DshSnapshot,sn: one
  DshSnapshot | ((s.dsh_conf0) = (sn.dsh_conf0) &&
                   (s.dsh_sc_used0) = (sn.dsh_sc_used0) &&
                   (s.dsh_taken0) = (sn.dsh_taken0) &&
                   (s.dsh_events0) = (sn.dsh_events0) &&
                   (s.dsh_conf1) = (sn.dsh_conf1) &&
                   (s.dsh_sc_used1) = (sn.dsh_sc_used1) &&
                   (s.dsh_taken1) = (sn.dsh_taken1) &&
                   (s.dsh_events1) = (sn.dsh_events1) &&
                   (s.dsh_stable) = (sn.dsh_stable)) =>
                  (s = sn))
}

fact dsh_tcmc_fact {
  (all s: one
  DshSnapshot | (s in tcmc/ks_s0) <=> (s.dsh_initial))
  (all s: one
  DshSnapshot,sn: one
  DshSnapshot | ((s -> sn) in tcmc/ks_sigma) <=>
                  (sn.(s.dsh_small_step)))
}

/*

trans currentBitToBit2{
			from Bit1
			when thisBit in current
			on Tk0
			goto Bit2
		} 

*/ 

fun is_a_next_state: set DshSnapshot {
    ex[ {s: DshSnapshot | boolean/isTrue[boolean/True] } ]
}

one sig P extends PID {}

pred ef_trans_currentBitToBit2 {
    ctl_mc[
        imp_ctl[and_ctl[{ s : DshSnapshot | 
                Counter_Tk0 in s.dsh_events0 and
		 P in s.Counter_current and
                some ((P -> Counter_Bit_Bit1) & (s.dsh_conf1)) },
                is_a_next_state ],
                ef[{s: DshSnapshot | P -> Counter_Bit_currentBitToBit2 in  s.dsh_taken1 }]
            ]
    ]
}

// this property is valid (Alloy returns UNSAT)
// takes perceptible time at 7 snapshots

check {
    ef_trans_currentBitToBit2
}
for exactly 24 DshSnapshot, 4 PID   expect 1

/*

dashcli -t -m tcmc bit-counter.dsh
cat bit-counter-tcmc.als bit-counter-tcmc-trans-ef-T1.ver > bit-counter-tcmc-trans-ef-T1.als
time dashcli bit-counter-tcmc-trans-ef-T1.als

*/