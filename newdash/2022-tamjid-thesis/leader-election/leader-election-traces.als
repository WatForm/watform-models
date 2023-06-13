/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-13 15:57:42
*/

open util/ring[Identifier] as P0


open util/boolean
open util/traces[DshSnapshot] as DshSnapshot
open util/buffer[bufIdx0, Identifier] as token
abstract sig DshStates {}
abstract sig System extends DshStates {} 
abstract sig System_Process extends System {} 
one sig System_Process_Electing extends System_Process {} 
one sig System_Process_Elected extends System_Process {} 

abstract sig DshIds {}
sig Identifier extends DshIds {} 

sig bufIdx0 {}
sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_sc_used1: DshIds -> DshStates,
  dsh_conf1: DshIds -> DshStates,
  dsh_stable: one boolean/Bool,
  System_Process_succ: Identifier -> one Identifier,
  System_elected: set Identifier,
  System_Process_token: Identifier -> (bufIdx0 -> Identifier)
}

pred dsh_initial [
	s: one DshSnapshot] {
  (all p0_Identifier: one
  Identifier | (s.dsh_conf0) = none and
                 (s.dsh_conf1) =
                   (Identifier -> System_Process_Electing) and
                 (s.dsh_sc_used1) = (none -> none) and
                 one
                 p0_Identifier.(s.System_Process_token) and
                 (((p0_Identifier.nextRing).(s.System_Process_token)).firstElem) =
                   p0_Identifier and
                 no
                 s.System_elected)
  (s.dsh_stable).boolean/isTrue
}

pred System_Process_Electing_ConsumeToken_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier -> System_Process_Electing) & (s.dsh_conf1))
  no
  s.System_elected and
  some
  ((p0_Identifier.(s.System_Process_token)).elems) and
  ((p0_Identifier.(s.System_Process_token)).firstElem).(p0_Identifier.gt)
  !(System in (s.dsh_sc_used0))
  !((p0_Identifier -> System_Process) in (s.dsh_sc_used1))
}


pred System_Process_Electing_ConsumeToken_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (p0_Identifier -> System_Process_Electing)) +
     (p0_Identifier -> System_Process_Electing))
  (p0_Identifier.(sn.System_Process_token)).((p0_Identifier.(s.System_Process_token)).removeFirst)
  (all Identifier_aa: Identifier - p0_Identifier | (Identifier_aa.(s.System_Process_token)) =
                                                   (Identifier_aa.(sn.System_Process_token)))
  (s.System_elected) = (sn.System_elected)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.System_Process_succ)) =
                 (Identifier_aa.(sn.System_Process_succ)))
  ((p0_Identifier -> System_Process).(none.(p0_Identifier.(sn.(s._nextIsStable)))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier -> System_Process)))
       )

}

pred System_Process_Electing_ConsumeToken_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_Identifier -> System_Process_Electing) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_Identifier -> System_Process) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Process_Electing_ConsumeToken [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.System_Process_Electing_ConsumeToken_pre)
  p0_Identifier.(sn.(s.System_Process_Electing_ConsumeToken_post))
}

pred System_Process_Electing_PassToken_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier -> System_Process_Electing) & (s.dsh_conf1))
  no
  s.System_elected and
  some
  ((p0_Identifier.(s.System_Process_token)).elems) and
  ((p0_Identifier.(s.System_Process_token)).firstElem).(p0_Identifier.lt)
  !(System in (s.dsh_sc_used0))
  !((p0_Identifier -> System_Process) in (s.dsh_sc_used1))
}


pred System_Process_Electing_PassToken_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (p0_Identifier -> System_Process_Electing)) +
     (p0_Identifier -> System_Process_Electing))
  ((p0_Identifier.(s.System_Process_token)).firstElem).(((p0_Identifier.nextRing).(sn.System_Process_token)).(((p0_Identifier.nextRing).(s.System_Process_token)).addFirst)) and
  (all others: Identifier - (p0_Identifier.nextRing) | (others.(sn.System_Process_token)) =
                                                         (others.(s.System_Process_token)))
  (s.System_elected) = (sn.System_elected)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.System_Process_succ)) =
                 (Identifier_aa.(sn.System_Process_succ)))
  ((p0_Identifier -> System_Process).(none.(p0_Identifier.(sn.(s._nextIsStable)))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier -> System_Process)))
       )

}

pred System_Process_Electing_PassToken_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_Identifier -> System_Process_Electing) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_Identifier -> System_Process) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Process_Electing_PassToken [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.System_Process_Electing_PassToken_pre)
  p0_Identifier.(sn.(s.System_Process_Electing_PassToken_post))
}

pred System_Process_Electing_ElectLeader_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier -> System_Process_Electing) & (s.dsh_conf1))
  no
  s.System_elected and
  ((p0_Identifier.(s.System_Process_token)).firstElem) =
    p0_Identifier
  !(System in (s.dsh_sc_used0))
  !((p0_Identifier -> System_Process) in (s.dsh_sc_used1))
}


pred System_Process_Electing_ElectLeader_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) -
       (p0_Identifier -> System_Process_Electing)) -
      (p0_Identifier -> System_Process_Elected)) +
     (p0_Identifier -> System_Process_Elected))
  (sn.System_elected) = p0_Identifier
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.System_Process_succ)) =
                 (Identifier_aa.(sn.System_Process_succ)))
  ((p0_Identifier -> System_Process).(none.(p0_Identifier.(sn.(s._nextIsStable)))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier -> System_Process)))
       )

}

pred System_Process_Electing_ElectLeader_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_Identifier -> System_Process_Electing) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_Identifier -> System_Process) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Process_Electing_ElectLeader [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.System_Process_Electing_ElectLeader_pre)
  p0_Identifier.(sn.(s.System_Process_Electing_ElectLeader_post))
}

pred _nextIsStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  !(dsh_scp1.(dsh_scp0.(p0_Identifier.(sn.(s.System_Process_Electing_ConsumeToken_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_Identifier.(sn.(s.System_Process_Electing_PassToken_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_Identifier.(sn.(s.System_Process_Electing_ElectLeader_enabledAfterStep)))))
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { (some p0_Identifier: one
      Identifier | { p0_Identifier.(sn.(s.System_Process_Electing_ConsumeToken)) or
                       p0_Identifier.(sn.(s.System_Process_Electing_PassToken)) or
                       p0_Identifier.(sn.(s.System_Process_Electing_ElectLeader)) }) or
    !((some p0_Identifier: one
         Identifier | { p0_Identifier.(s.System_Process_Electing_ConsumeToken_pre) or
                          p0_Identifier.(s.System_Process_Electing_PassToken_pre) or
                          p0_Identifier.(s.System_Process_Electing_ElectLeader_pre) })) and
      s = sn }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}





