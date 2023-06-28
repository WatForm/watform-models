/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-28 18:10:51
*/

open util/ring[Identifier] as P0


open util/boolean
open util/tcmc[DshSnapshot]
open util/buffer[bufIdx0, Identifier] as token
abstract sig DshStates {}
abstract sig System extends DshStates {} 
abstract sig DshScopes {}
one sig SystemScope extends DshScopes {} 
one sig System_ProcessScope extends DshScopes {} 
abstract sig System_Process extends System {} 
one sig System_Process_ElectingScope extends DshScopes {} 
one sig System_Process_Electing extends System_Process {} 
one sig System_Process_ElectedScope extends DshScopes {} 
one sig System_Process_Elected extends System_Process {} 

abstract sig Transitions {}
one sig NO_TRANS extends Transitions {} 
one sig System_Process_Electing_ConsumeToken extends Transitions {} 
one sig System_Process_Electing_PassToken extends Transitions {} 
one sig System_Process_Electing_ElectLeader extends Transitions {} 

abstract sig DshIds {}
sig Identifier extends DshIds {} 

sig bufIdx0 {}
sig DshSnapshot {
  dsh_sc_used0: set DshScopes,
  dsh_conf0: set DshStates,
  dsh_taken0: set Transitions,
  dsh_sc_used1: DshIds -> DshScopes,
  dsh_conf1: DshIds -> DshStates,
  dsh_taken1: DshIds -> Transitions,
  dsh_stable: one boolean/Bool,
  System_Process_succ: Identifier -> one Identifier,
  System_elected: set Identifier,
  System_Process_token: Identifier -> (bufIdx0 -> Identifier)
}

pred dsh_initial [
	s: one DshSnapshot] {
  (all p0_Identifier: one
  Identifier | (s.dsh_conf0) = none &&
                 (s.dsh_conf1) =
                   (Identifier -> System_Process_Electing) &&
                 (s.dsh_sc_used0) = none &&
                 (s.dsh_taken0) = NO_TRANS &&
                 (s.dsh_sc_used1) = (none -> none) &&
                 (s.dsh_taken1) = (none -> none) &&
                 one
                 p0_Identifier.(s.System_Process_token) &&
                 (((p0_Identifier.nextRing).(s.System_Process_token)).firstElem) =
                   p0_Identifier &&
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
  s.System_elected &&
  some
  ((p0_Identifier.(s.System_Process_token)).elems) &&
  ((p0_Identifier.(s.System_Process_token)).firstElem).(p0_Identifier.gt)
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> System_ProcessScope) in (s.dsh_sc_used1))
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
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier -> System_Process_Electing_ConsumeToken)
  (all Identifier_aa: Identifier - p0_Identifier | (Identifier_aa.(s.System_Process_token)) =
                                                   (Identifier_aa.(sn.System_Process_token)))
  (s.System_elected) = (sn.System_elected)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.System_Process_succ)) =
                 (Identifier_aa.(sn.System_Process_succ)))
  {((p0_Identifier -> System_Process).(none.(p0_Identifier.(sn.(s._nextIsStable)))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier -> System_ProcessScope)))}
       )}

}

pred System_Process_Electing_ConsumeToken_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_Identifier -> System_Process_Electing) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_Identifier -> System_Process) in sc1) ||
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
  s.System_elected &&
  some
  ((p0_Identifier.(s.System_Process_token)).elems) &&
  ((p0_Identifier.(s.System_Process_token)).firstElem).(p0_Identifier.lt)
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> System_ProcessScope) in (s.dsh_sc_used1))
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
  ((p0_Identifier.(s.System_Process_token)).firstElem).(((p0_Identifier.nextRing).(sn.System_Process_token)).(((p0_Identifier.nextRing).(s.System_Process_token)).addFirst)) &&
  (all others: Identifier - (p0_Identifier.nextRing) | (others.(sn.System_Process_token)) =
                                                         (others.(s.System_Process_token)))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier -> System_Process_Electing_PassToken)
  (s.System_elected) = (sn.System_elected)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.System_Process_succ)) =
                 (Identifier_aa.(sn.System_Process_succ)))
  {((p0_Identifier -> System_Process).(none.(p0_Identifier.(sn.(s._nextIsStable)))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier -> System_ProcessScope)))}
       )}

}

pred System_Process_Electing_PassToken_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_Identifier -> System_Process_Electing) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_Identifier -> System_Process) in sc1) ||
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
  s.System_elected &&
  ((p0_Identifier.(s.System_Process_token)).firstElem) =
    p0_Identifier
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> System_ProcessScope) in (s.dsh_sc_used1))
}


pred System_Process_Electing_ElectLeader_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_Identifier -> System_Process_Electing) +
         (p0_Identifier -> System_Process_Elected))) +
     (p0_Identifier -> System_Process_Elected))
  (sn.System_elected) = p0_Identifier
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier -> System_Process_Electing_ElectLeader)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.System_Process_token)) =
                 (Identifier_aa.(sn.System_Process_token)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.System_Process_succ)) =
                 (Identifier_aa.(sn.System_Process_succ)))
  {((p0_Identifier -> System_Process).(none.(p0_Identifier.(sn.(s._nextIsStable)))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier -> System_ProcessScope)))}
       )}

}

pred System_Process_Electing_ElectLeader_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_Identifier -> System_Process_Electing) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_Identifier -> System_Process) in sc1) ||
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
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  !(sc1.(sc0.(p0_Identifier.(sn.(s.System_Process_Electing_ConsumeToken_enabledAfterStep)))))
  !(sc1.(sc0.(p0_Identifier.(sn.(s.System_Process_Electing_PassToken_enabledAfterStep)))))
  !(sc1.(sc0.(p0_Identifier.(sn.(s.System_Process_Electing_ElectLeader_enabledAfterStep)))))
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_stable) = (s.dsh_stable)
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
  (sn.dsh_taken0) = NO_TRANS
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_sc_used1) = (s.dsh_sc_used1)
  (sn.dsh_taken1) = (none -> none)
  (sn.System_Process_succ) = (s.System_Process_succ)
  (sn.System_elected) = (s.System_elected)
  (sn.System_Process_token) = (s.System_Process_token)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { (some p0_Identifier: one
      Identifier | { p0_Identifier.(sn.(s.System_Process_Electing_ConsumeToken)) ||
                       p0_Identifier.(sn.(s.System_Process_Electing_PassToken)) ||
                       p0_Identifier.(sn.(s.System_Process_Electing_ElectLeader)) }) ||
    !((some p0_Identifier: one
         Identifier | { p0_Identifier.(s.System_Process_Electing_ConsumeToken_pre) ||
                          p0_Identifier.(s.System_Process_Electing_PassToken_pre) ||
                          p0_Identifier.(s.System_Process_Electing_ElectLeader_pre) })) &&
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
                   (s.dsh_conf1) = (sn.dsh_conf1) &&
                   (s.dsh_sc_used1) = (sn.dsh_sc_used1) &&
                   (s.dsh_taken1) = (sn.dsh_taken1) &&
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

trans ElectLeader {
	when {
		no elected
		token.firstElem = thisProcess
	}
	do {
		elected' =  thisProcess // Elect Leader
	}
	goto Elected
}

*/

fun is_a_next_state: set DshSnapshot {
    ex[ {s: DshSnapshot | boolean/isTrue[boolean/True] } ]
}

one sig I extends Identifier {}

pred ef_trans_ElectLeader {
    ctl_mc[
        imp_ctl[and_ctl[{ s : DshSnapshot | 
                (I -> System_Process_Electing) in s.dsh_conf1 and
                no  s.System_elected and
				((I.(s.System_Process_token)).firstElem) = I
                 },
                is_a_next_state ],
                ef[{s: DshSnapshot | I -> System_Process_Electing_ElectLeader in s.dsh_taken1 }]
            ]
    ]
}

check {
    ef_trans_ElectLeader
}
for 
exactly 20 DshSnapshot,
exactly 6 Identifier,
exactly 6 bufIdx0
expect 0


/*

dashcli -t -m tcmc leader-election.dsh
cat leader-election-tcmc.als leader-election-tcmc-trans-ef-ElectLeader.ver > leader-election-tcmc-trans-ef-ElectLeader.als
time dashcli leader-election-tcmc-trans-ef-ElectLeader.als

*/