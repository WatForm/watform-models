/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-28 18:43:14
*/

open util/ordering[Level] as nodeLevel

open util/boolean
open util/tcmc[DshSnapshot]

sig Level {}

abstract sig DshStates {}
abstract sig DistributedTreeSpanning extends DshStates {} 
abstract sig DshScopes {}
one sig DistributedTreeSpanningScope extends DshScopes {} 
one sig DistributedTreeSpanning_NScope extends DshScopes {} 
abstract sig DistributedTreeSpanning_N extends DistributedTreeSpanning {} 
one sig DistributedTreeSpanning_N_UnassignedScope extends DshScopes {} 
one sig DistributedTreeSpanning_N_Unassigned extends DistributedTreeSpanning_N {} 
one sig DistributedTreeSpanning_N_AssignedScope extends DshScopes {} 
one sig DistributedTreeSpanning_N_Assigned extends DistributedTreeSpanning_N {} 

abstract sig Transitions {}
one sig NO_TRANS extends Transitions {} 
one sig DistributedTreeSpanning_N_Assigned_sendMessage extends Transitions {} 
one sig DistributedTreeSpanning_N_Unassigned_RootAssign extends Transitions {} 
one sig DistributedTreeSpanning_N_Unassigned_NodeAssign extends Transitions {} 

abstract sig DshIds {}
sig Node extends DshIds {} 

sig DshSnapshot {
  dsh_sc_used0: set DshScopes,
  dsh_conf0: set DshStates,
  dsh_taken0: set Transitions,
  dsh_sc_used1: DshIds -> DshScopes,
  dsh_conf1: DshIds -> DshStates,
  dsh_taken1: DshIds -> Transitions,
  dsh_stable: one boolean/Bool,
  DistributedTreeSpanning_N_level: Node -> lone Level,
  DistributedTreeSpanning_N_parent: Node -> lone Node,
  DistributedTreeSpanning_N_message: Node -> (Node -> Level),
  DistributedTreeSpanning_root: one Node
}

pred dsh_initial [
	s: one DshSnapshot] {
  (all p0_Node: one
  Node | (s.dsh_conf0) = none &&
           (s.dsh_conf1) =
             (Node -> DistributedTreeSpanning_N_Unassigned) &&
           (s.dsh_sc_used0) = none &&
           (s.dsh_taken0) = NO_TRANS &&
           (s.dsh_sc_used1) = (none -> none) &&
           (s.dsh_taken1) = (none -> none) &&
           no
           p0_Node.(s.DistributedTreeSpanning_N_level) &&
           no
           p0_Node.(s.DistributedTreeSpanning_N_parent) &&
           no
           p0_Node.(s.DistributedTreeSpanning_N_message))
  (s.dsh_stable).boolean/isTrue
}

pred DistributedTreeSpanning_N_Assigned_sendMessage_pre [
	s: one DshSnapshot,
	p0_Node: one Node] {
  some
((p0_Node -> DistributedTreeSpanning_N_Assigned) &
   (s.dsh_conf1))
  (some n: Node | no n.(s.DistributedTreeSpanning_N_level))
  !(DistributedTreeSpanningScope in (s.dsh_sc_used0))
  !((p0_Node -> DistributedTreeSpanning_NScope) in
    (s.dsh_sc_used1))
}


pred DistributedTreeSpanning_N_Assigned_sendMessage_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (p0_Node -> DistributedTreeSpanning_N_Assigned)) +
     (p0_Node -> DistributedTreeSpanning_N_Assigned))
  (one n: Node - p0_Node | no
                           n.(s.DistributedTreeSpanning_N_message) &&
                           (n.(sn.DistributedTreeSpanning_N_message)) =
                             (p0_Node ->
                                p0_Node.(s.DistributedTreeSpanning_N_level)) &&
                           (all others: Node - n | (others.(sn.DistributedTreeSpanning_N_message)) =
                                                     (others.(s.DistributedTreeSpanning_N_message))))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Node -> DistributedTreeSpanning_N_Assigned_sendMessage)
  (s.DistributedTreeSpanning_root) =
  (sn.DistributedTreeSpanning_root)
  (all Node_aa: one
  Node | (Node_aa.(s.DistributedTreeSpanning_N_level)) =
           (Node_aa.(sn.DistributedTreeSpanning_N_level)))
  (all Node_aa: one
  Node | (Node_aa.(s.DistributedTreeSpanning_N_parent)) =
           (Node_aa.(sn.DistributedTreeSpanning_N_parent)))
  {((p0_Node -> DistributedTreeSpanning_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node ->
                      DistributedTreeSpanning_NScope)))}
       )}

}

pred DistributedTreeSpanning_N_Assigned_sendMessage_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_Node -> DistributedTreeSpanning_N_Assigned) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(DistributedTreeSpanning in sc0) &&
    !((p0_Node -> DistributedTreeSpanning_N) in sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred DistributedTreeSpanning_N_Assigned_sendMessage [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  p0_Node.(s.DistributedTreeSpanning_N_Assigned_sendMessage_pre)
  p0_Node.(sn.(s.DistributedTreeSpanning_N_Assigned_sendMessage_post))
}

pred DistributedTreeSpanning_N_Unassigned_RootAssign_pre [
	s: one DshSnapshot,
	p0_Node: one Node] {
  some
((p0_Node -> DistributedTreeSpanning_N_Unassigned) &
   (s.dsh_conf1))
  p0_Node in s.DistributedTreeSpanning_root
  !(DistributedTreeSpanningScope in (s.dsh_sc_used0))
  !((p0_Node -> DistributedTreeSpanning_NScope) in
    (s.dsh_sc_used1))
}


pred DistributedTreeSpanning_N_Unassigned_RootAssign_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_Node -> DistributedTreeSpanning_N_Unassigned) +
         (p0_Node -> DistributedTreeSpanning_N_Assigned))) +
     (p0_Node -> DistributedTreeSpanning_N_Assigned))
  (p0_Node.(sn.DistributedTreeSpanning_N_level)) =
  nodeLevel/first &&
  (p0_Node.(sn.DistributedTreeSpanning_N_parent)) = p0_Node
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Node ->
     DistributedTreeSpanning_N_Unassigned_RootAssign)
  (all Node_aa: Node - p0_Node | (Node_aa.(s.DistributedTreeSpanning_N_level)) =
                                 (Node_aa.(sn.DistributedTreeSpanning_N_level)))
  (all Node_aa: Node - p0_Node | (Node_aa.(s.DistributedTreeSpanning_N_parent)) =
                                 (Node_aa.(sn.DistributedTreeSpanning_N_parent)))
  (s.DistributedTreeSpanning_root) =
  (sn.DistributedTreeSpanning_root)
  (all Node_aa: one
  Node | (Node_aa.(s.DistributedTreeSpanning_N_message)) =
           (Node_aa.(sn.DistributedTreeSpanning_N_message)))
  {((p0_Node -> DistributedTreeSpanning_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node ->
                      DistributedTreeSpanning_NScope)))}
       )}

}

pred DistributedTreeSpanning_N_Unassigned_RootAssign_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_Node -> DistributedTreeSpanning_N_Unassigned) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(DistributedTreeSpanning in sc0) &&
    !((p0_Node -> DistributedTreeSpanning_N) in sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred DistributedTreeSpanning_N_Unassigned_RootAssign [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  p0_Node.(s.DistributedTreeSpanning_N_Unassigned_RootAssign_pre)
  p0_Node.(sn.(s.DistributedTreeSpanning_N_Unassigned_RootAssign_post))
}

pred DistributedTreeSpanning_N_Unassigned_NodeAssign_pre [
	s: one DshSnapshot,
	p0_Node: one Node] {
  some
((p0_Node -> DistributedTreeSpanning_N_Unassigned) &
   (s.dsh_conf1))
  some p0_Node.(s.DistributedTreeSpanning_N_message)
  !(DistributedTreeSpanningScope in (s.dsh_sc_used0))
  !((p0_Node -> DistributedTreeSpanning_NScope) in
    (s.dsh_sc_used1))
}


pred DistributedTreeSpanning_N_Unassigned_NodeAssign_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_Node -> DistributedTreeSpanning_N_Unassigned) +
         (p0_Node -> DistributedTreeSpanning_N_Assigned))) +
     (p0_Node -> DistributedTreeSpanning_N_Assigned))
  (p0_Node.(sn.DistributedTreeSpanning_N_level)) =
  ((Node.(p0_Node.(s.DistributedTreeSpanning_N_message))).nodeLevel/next) &&
  (p0_Node.(sn.DistributedTreeSpanning_N_parent)) =
    ((p0_Node.(s.DistributedTreeSpanning_N_message)).Level)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Node ->
     DistributedTreeSpanning_N_Unassigned_NodeAssign)
  (all Node_aa: Node - p0_Node | (Node_aa.(s.DistributedTreeSpanning_N_level)) =
                                 (Node_aa.(sn.DistributedTreeSpanning_N_level)))
  (all Node_aa: Node - p0_Node | (Node_aa.(s.DistributedTreeSpanning_N_parent)) =
                                 (Node_aa.(sn.DistributedTreeSpanning_N_parent)))
  (s.DistributedTreeSpanning_root) =
  (sn.DistributedTreeSpanning_root)
  (all Node_aa: one
  Node | (Node_aa.(s.DistributedTreeSpanning_N_message)) =
           (Node_aa.(sn.DistributedTreeSpanning_N_message)))
  {((p0_Node -> DistributedTreeSpanning_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node ->
                      DistributedTreeSpanning_NScope)))}
       )}

}

pred DistributedTreeSpanning_N_Unassigned_NodeAssign_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_Node -> DistributedTreeSpanning_N_Unassigned) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(DistributedTreeSpanning in sc0) &&
    !((p0_Node -> DistributedTreeSpanning_N) in sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred DistributedTreeSpanning_N_Unassigned_NodeAssign [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  p0_Node.(s.DistributedTreeSpanning_N_Unassigned_NodeAssign_pre)
  p0_Node.(sn.(s.DistributedTreeSpanning_N_Unassigned_NodeAssign_post))
}

pred _nextIsStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  !(sc1.(sc0.(p0_Node.(sn.(s.DistributedTreeSpanning_N_Assigned_sendMessage_enabledAfterStep)))))
  !(sc1.(sc0.(p0_Node.(sn.(s.DistributedTreeSpanning_N_Unassigned_RootAssign_enabledAfterStep)))))
  !(sc1.(sc0.(p0_Node.(sn.(s.DistributedTreeSpanning_N_Unassigned_NodeAssign_enabledAfterStep)))))
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
  (sn.DistributedTreeSpanning_N_level) =
  (s.DistributedTreeSpanning_N_level)
  (sn.DistributedTreeSpanning_N_parent) =
  (s.DistributedTreeSpanning_N_parent)
  (sn.DistributedTreeSpanning_N_message) =
  (s.DistributedTreeSpanning_N_message)
  (sn.DistributedTreeSpanning_root) =
  (s.DistributedTreeSpanning_root)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { (some p0_Node: one
      Node | { p0_Node.(sn.(s.DistributedTreeSpanning_N_Assigned_sendMessage)) ||
                 p0_Node.(sn.(s.DistributedTreeSpanning_N_Unassigned_RootAssign)) ||
                 p0_Node.(sn.(s.DistributedTreeSpanning_N_Unassigned_NodeAssign)) }) ||
    !((some p0_Node: one
         Node | { p0_Node.(s.DistributedTreeSpanning_N_Assigned_sendMessage_pre) ||
                    p0_Node.(s.DistributedTreeSpanning_N_Unassigned_RootAssign_pre) ||
                    p0_Node.(s.DistributedTreeSpanning_N_Unassigned_NodeAssign_pre) })) &&
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

