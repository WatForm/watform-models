/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-13 16:49:10
*/

open util/ordering[Level] as nodeLevel

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

sig Level {}

abstract sig DshStates {}
abstract sig DistributedTreeSpanning extends DshStates {} 
abstract sig DistributedTreeSpanning_N extends DistributedTreeSpanning {} 
one sig DistributedTreeSpanning_N_Unassigned extends DistributedTreeSpanning_N {} 
one sig DistributedTreeSpanning_N_Assigned extends DistributedTreeSpanning_N {} 

abstract sig DshIds {}
sig Node extends DshIds {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_sc_used1: DshIds -> DshStates,
  dsh_conf1: DshIds -> DshStates,
  dsh_stable: one boolean/Bool,
  DistributedTreeSpanning_N_level: Node -> lone Level,
  DistributedTreeSpanning_N_parent: Node -> lone Node,
  DistributedTreeSpanning_N_message: Node -> (Node -> Level),
  DistributedTreeSpanning_root: one Node
}

pred dsh_initial [
	s: one DshSnapshot] {
  (all p0_Node: one
  Node | (s.dsh_conf0) = none and
           (s.dsh_conf1) =
             (Node -> DistributedTreeSpanning_N_Unassigned) and
           (s.dsh_sc_used1) = (none -> none) and
           no
           p0_Node.(s.DistributedTreeSpanning_N_level) and
           no
           p0_Node.(s.DistributedTreeSpanning_N_parent) and
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
  !(DistributedTreeSpanning in (s.dsh_sc_used0))
  !((p0_Node -> DistributedTreeSpanning_N) in (s.dsh_sc_used1))
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
                           n.(s.DistributedTreeSpanning_N_message) and
                           (n.(sn.DistributedTreeSpanning_N_message)) =
                             (p0_Node ->
                                p0_Node.(s.DistributedTreeSpanning_N_level)) and
                           (all others: Node - n | (others.(sn.DistributedTreeSpanning_N_message)) =
                                                     (others.(s.DistributedTreeSpanning_N_message))))
  (s.DistributedTreeSpanning_root) =
  (sn.DistributedTreeSpanning_root)
  (all Node_aa: one
  Node | (Node_aa.(s.DistributedTreeSpanning_N_level)) =
           (Node_aa.(sn.DistributedTreeSpanning_N_level)))
  (all Node_aa: one
  Node | (Node_aa.(s.DistributedTreeSpanning_N_parent)) =
           (Node_aa.(sn.DistributedTreeSpanning_N_parent)))
  ((p0_Node -> DistributedTreeSpanning_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node -> DistributedTreeSpanning_N)))
       )

}

pred DistributedTreeSpanning_N_Assigned_sendMessage_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_Node -> DistributedTreeSpanning_N_Assigned) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(DistributedTreeSpanning in dsh_scp0) and
    !((p0_Node -> DistributedTreeSpanning_N) in dsh_scp1) or
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
  !(DistributedTreeSpanning in (s.dsh_sc_used0))
  !((p0_Node -> DistributedTreeSpanning_N) in (s.dsh_sc_used1))
}


pred DistributedTreeSpanning_N_Unassigned_RootAssign_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) -
       (p0_Node -> DistributedTreeSpanning_N_Unassigned)) -
      (p0_Node -> DistributedTreeSpanning_N_Assigned)) +
     (p0_Node -> DistributedTreeSpanning_N_Assigned))
  (p0_Node.(sn.DistributedTreeSpanning_N_level)) =
  nodeLevel/first and
  (p0_Node.(sn.DistributedTreeSpanning_N_parent)) = p0_Node
  (all Node_aa: Node - p0_Node | (Node_aa.(s.DistributedTreeSpanning_N_level)) =
                                 (Node_aa.(sn.DistributedTreeSpanning_N_level)))
  (all Node_aa: Node - p0_Node | (Node_aa.(s.DistributedTreeSpanning_N_parent)) =
                                 (Node_aa.(sn.DistributedTreeSpanning_N_parent)))
  (s.DistributedTreeSpanning_root) =
  (sn.DistributedTreeSpanning_root)
  (all Node_aa: one
  Node | (Node_aa.(s.DistributedTreeSpanning_N_message)) =
           (Node_aa.(sn.DistributedTreeSpanning_N_message)))
  ((p0_Node -> DistributedTreeSpanning_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node -> DistributedTreeSpanning_N)))
       )

}

pred DistributedTreeSpanning_N_Unassigned_RootAssign_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_Node -> DistributedTreeSpanning_N_Unassigned) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(DistributedTreeSpanning in dsh_scp0) and
    !((p0_Node -> DistributedTreeSpanning_N) in dsh_scp1) or
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
  !(DistributedTreeSpanning in (s.dsh_sc_used0))
  !((p0_Node -> DistributedTreeSpanning_N) in (s.dsh_sc_used1))
}


pred DistributedTreeSpanning_N_Unassigned_NodeAssign_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) -
       (p0_Node -> DistributedTreeSpanning_N_Unassigned)) -
      (p0_Node -> DistributedTreeSpanning_N_Assigned)) +
     (p0_Node -> DistributedTreeSpanning_N_Assigned))
  (p0_Node.(sn.DistributedTreeSpanning_N_level)) =
  ((Node.(p0_Node.(s.DistributedTreeSpanning_N_message))).nodeLevel/next) and
  (p0_Node.(sn.DistributedTreeSpanning_N_parent)) =
    ((p0_Node.(s.DistributedTreeSpanning_N_message)).Level)
  (all Node_aa: Node - p0_Node | (Node_aa.(s.DistributedTreeSpanning_N_level)) =
                                 (Node_aa.(sn.DistributedTreeSpanning_N_level)))
  (all Node_aa: Node - p0_Node | (Node_aa.(s.DistributedTreeSpanning_N_parent)) =
                                 (Node_aa.(sn.DistributedTreeSpanning_N_parent)))
  (s.DistributedTreeSpanning_root) =
  (sn.DistributedTreeSpanning_root)
  (all Node_aa: one
  Node | (Node_aa.(s.DistributedTreeSpanning_N_message)) =
           (Node_aa.(sn.DistributedTreeSpanning_N_message)))
  ((p0_Node -> DistributedTreeSpanning_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node -> DistributedTreeSpanning_N)))
       )

}

pred DistributedTreeSpanning_N_Unassigned_NodeAssign_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_Node -> DistributedTreeSpanning_N_Unassigned) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(DistributedTreeSpanning in dsh_scp0) and
    !((p0_Node -> DistributedTreeSpanning_N) in dsh_scp1) or
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
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  !(dsh_scp1.(dsh_scp0.(p0_Node.(sn.(s.DistributedTreeSpanning_N_Assigned_sendMessage_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_Node.(sn.(s.DistributedTreeSpanning_N_Unassigned_RootAssign_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_Node.(sn.(s.DistributedTreeSpanning_N_Unassigned_NodeAssign_enabledAfterStep)))))
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_stable) = (s.dsh_stable)
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_sc_used1) = (s.dsh_sc_used1)
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
      Node | { p0_Node.(sn.(s.DistributedTreeSpanning_N_Assigned_sendMessage)) or
                 p0_Node.(sn.(s.DistributedTreeSpanning_N_Unassigned_RootAssign)) or
                 p0_Node.(sn.(s.DistributedTreeSpanning_N_Unassigned_NodeAssign)) }) or
    !((some p0_Node: one
         Node | { p0_Node.(s.DistributedTreeSpanning_N_Assigned_sendMessage_pre) or
                    p0_Node.(s.DistributedTreeSpanning_N_Unassigned_RootAssign_pre) or
                    p0_Node.(s.DistributedTreeSpanning_N_Unassigned_NodeAssign_pre) })) and
      sn.(s.dsh_stutter) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}

