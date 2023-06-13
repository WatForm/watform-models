/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-13 16:49:11
*/

open util/ordering[Floor]

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

sig Floor {}
abstract sig Direction {}
one sig Up, Down extends Direction {}

pred between [n1, nb, n2: Floor] {
	     lt[n1,n2] =>   ( lt[n1,nb] && lt[nb,n2] )
             else ( lt[n1,nb] || lt[nb,n2] )  }

abstract sig DshStates {}
abstract sig System extends DshStates {} 
abstract sig System_Controller extends System {} 
one sig System_Controller_Sending extends System_Controller {} 
abstract sig System_Elevator extends System {} 
one sig System_Elevator_MovingUp extends System_Elevator {} 
one sig System_Elevator_MovingDown extends System_Elevator {} 
one sig System_Elevator_Idle extends System_Elevator {} 

abstract sig DshIds {}
sig PID extends DshIds {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_sc_used1: DshIds -> DshStates,
  dsh_conf1: DshIds -> DshStates,
  dsh_stable: one boolean/Bool,
  System_Controller_callToSend: Floor -> Direction,
  System_Elevator_direction: PID -> one Direction,
  System_Elevator_called: PID -> set Floor,
  System_Elevator_current: PID -> one Floor
}

pred dsh_initial [
	s: one DshSnapshot] {
  (all p0_PID: one
  PID | (s.dsh_conf0) = System_Controller_Sending and
          (s.dsh_conf1) = (PID -> System_Elevator_Idle) and
          (s.dsh_sc_used1) = (none -> none) and
          no
          p0_PID.(s.System_Elevator_called) and
          (p0_PID.(s.System_Elevator_current)) = (Floor.min) and
          (p0_PID.(s.System_Elevator_direction)) = Up and
          (# s.System_Controller_callToSend) = (3) and
          Up !in (Floor.(s.System_Controller_callToSend)))
  (s.dsh_stable).boolean/isTrue
}

pred System_Controller_SendingDownRequest_pre [
	s: one DshSnapshot] {
  some (System_Controller_Sending & (s.dsh_conf0))
  Down in (Floor.(s.System_Controller_callToSend))
  !(System in (s.dsh_sc_used0))
  !(System_Controller in (s.dsh_sc_used0))
}


pred System_Controller_SendingDownRequest_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) - System_Controller_Sending) +
     System_Controller_Sending)
  (sn.dsh_conf1) = (s.dsh_conf1)
  ((some p: PID,f: (s.System_Controller_callToSend).Down | (p.(s.System_Elevator_current)).(f.lte) and
                                                           (p.(s.System_Elevator_direction)) =
                                                             Down))=>
    (one e0: PID,f: (s.System_Controller_callToSend).Down | (e0.(s.System_Elevator_direction)) =
                                                              Down and
                                                              f.((e0.(s.System_Elevator_current)).gte) and
                                                              (e0.(sn.System_Elevator_called)) =
                                                                ((e0.(s.System_Elevator_called)) +
                                                                   f) and
                                                              (sn.System_Controller_callToSend) =
                                                                ((s.System_Controller_callToSend) -
                                                                   (f ->
                                                                      Down)) and
                                                              (no e1: PID -
                                                                        e0 | (e1.(s.System_Elevator_direction)) =
                                                                               Down and
                                                                               (e1.(s.System_Elevator_current)).((e0.(s.System_Elevator_current)).(f.between))) and
                                                              (all others: PID -
                                                                             e0 | (others.(sn.System_Elevator_called)) =
                                                                                    (others.(s.System_Elevator_called))))
  else
    (one e0: PID,f: (s.System_Controller_callToSend).Direction | (e0.(sn.System_Elevator_called)) =
                                                                   ((e0.(s.System_Elevator_called)) +
                                                                      f) and
                                                                   (sn.System_Controller_callToSend) =
                                                                     ((s.System_Controller_callToSend) -
                                                                        (f ->
                                                                           (f.(s.System_Controller_callToSend)))) and
                                                                   (all others: PID -
                                                                                  e0 | (others.(sn.System_Elevator_called)) =
                                                                                         (others.(s.System_Elevator_called))))

  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_current)) =
          (PID_aa.(sn.System_Elevator_current)))
  ((none -> none).(System_Controller.(none.(sn.(s._nextIsStable)))))=>
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
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + System_Controller) and
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))
       )

}

pred System_Controller_SendingDownRequest_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some (System_Controller_Sending & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !(System_Controller in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Controller_SendingDownRequest [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.System_Controller_SendingDownRequest_pre
  sn.(s.System_Controller_SendingDownRequest_post)
}

pred System_Elevator_MovingUp_ChangeDirToDown_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> System_Elevator_MovingUp) & (s.dsh_conf1))
  some
  p0_PID.(s.System_Elevator_called) and
  no
  (((p0_PID.(s.System_Elevator_current)).nexts) &
     p0_PID.(s.System_Elevator_called)) and
  some
  (((p0_PID.(s.System_Elevator_current)).prevs) &
     p0_PID.(s.System_Elevator_called)) and
  p0_PID.(s.System_Elevator_current) !in
    p0_PID.(s.System_Elevator_called)
  !(System in (s.dsh_sc_used0))
  !((p0_PID -> System_Elevator) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingUp_ChangeDirToDown_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((((s.dsh_conf1) - (p0_PID -> System_Elevator_MovingUp)) -
       (p0_PID -> System_Elevator_MovingDown)) -
      (p0_PID -> System_Elevator_Idle)) +
     (p0_PID -> System_Elevator_MovingDown))
  (p0_PID.(sn.System_Elevator_direction)) = Down
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_direction)) =
                              (PID_aa.(sn.System_Elevator_direction)))
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_called)) =
          (PID_aa.(sn.System_Elevator_called)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_current)) =
          (PID_aa.(sn.System_Elevator_current)))
  ((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_Elevator)))
       )

}

pred System_Elevator_MovingUp_ChangeDirToDown_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_MovingUp) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_PID -> System_Elevator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Elevator_MovingUp_ChangeDirToDown [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.System_Elevator_MovingUp_ChangeDirToDown_pre)
  p0_PID.(sn.(s.System_Elevator_MovingUp_ChangeDirToDown_post))
}

pred System_Elevator_Idle_Move_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> System_Elevator_Idle) & (s.dsh_conf1))
  some p0_PID.(s.System_Elevator_called)
  !(System in (s.dsh_sc_used0))
  !((p0_PID -> System_Elevator) in (s.dsh_sc_used1))
}


pred System_Elevator_Idle_Move_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((((s.dsh_conf1) - (p0_PID -> System_Elevator_MovingUp)) -
       (p0_PID -> System_Elevator_MovingDown)) -
      (p0_PID -> System_Elevator_Idle)) +
     (p0_PID -> System_Elevator_MovingUp))
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_called)) =
          (PID_aa.(sn.System_Elevator_called)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_current)) =
          (PID_aa.(sn.System_Elevator_current)))
  ((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_Elevator)))
       )

}

pred System_Elevator_Idle_Move_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_Idle) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_PID -> System_Elevator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Elevator_Idle_Move [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.System_Elevator_Idle_Move_pre)
  p0_PID.(sn.(s.System_Elevator_Idle_Move_post))
}

pred System_Elevator_MovingDown_Idle_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some
((p0_PID -> System_Elevator_MovingDown) & (s.dsh_conf1))
  no p0_PID.(s.System_Elevator_called)
  !(System in (s.dsh_sc_used0))
  !((p0_PID -> System_Elevator) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingDown_Idle_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((((s.dsh_conf1) - (p0_PID -> System_Elevator_MovingUp)) -
       (p0_PID -> System_Elevator_MovingDown)) -
      (p0_PID -> System_Elevator_Idle)) +
     (p0_PID -> System_Elevator_Idle))
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_called)) =
          (PID_aa.(sn.System_Elevator_called)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_current)) =
          (PID_aa.(sn.System_Elevator_current)))
  ((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_Elevator)))
       )

}

pred System_Elevator_MovingDown_Idle_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_PID -> System_Elevator_MovingDown) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_PID -> System_Elevator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Elevator_MovingDown_Idle [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.System_Elevator_MovingDown_Idle_pre)
  p0_PID.(sn.(s.System_Elevator_MovingDown_Idle_post))
}

pred System_Elevator_MovingDown_MoveDown_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some
((p0_PID -> System_Elevator_MovingDown) & (s.dsh_conf1))
  some
  p0_PID.(s.System_Elevator_called) and
  (p0_PID.(s.System_Elevator_direction)) = Down and
  some
  (((p0_PID.(s.System_Elevator_current)).prevs) &
     p0_PID.(s.System_Elevator_called)) and
  p0_PID.(s.System_Elevator_current) !in
    p0_PID.(s.System_Elevator_called)
  !(System in (s.dsh_sc_used0))
  !((p0_PID -> System_Elevator) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingDown_MoveDown_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) - (p0_PID -> System_Elevator_MovingDown)) +
     (p0_PID -> System_Elevator_MovingDown))
  (p0_PID.(sn.System_Elevator_current)) =
  ((((p0_PID.(s.System_Elevator_current)).prevs) &
      p0_PID.(s.System_Elevator_called)).max) and
  (p0_PID.(sn.System_Elevator_called)) =
    ((p0_PID.(s.System_Elevator_called)) -
       (p0_PID.(sn.System_Elevator_current)))
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_called)) =
                              (PID_aa.(sn.System_Elevator_called)))
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_current)) =
                              (PID_aa.(sn.System_Elevator_current)))
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  ((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_Elevator)))
       )

}

pred System_Elevator_MovingDown_MoveDown_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_PID -> System_Elevator_MovingDown) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_PID -> System_Elevator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Elevator_MovingDown_MoveDown [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.System_Elevator_MovingDown_MoveDown_pre)
  p0_PID.(sn.(s.System_Elevator_MovingDown_MoveDown_post))
}

pred System_Elevator_Idle_DefaultToGround_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> System_Elevator_Idle) & (s.dsh_conf1))
  no
  p0_PID.(s.System_Elevator_called) and
  (Floor.min) !in p0_PID.(s.System_Elevator_current)
  !(System in (s.dsh_sc_used0))
  !((p0_PID -> System_Elevator) in (s.dsh_sc_used1))
}


pred System_Elevator_Idle_DefaultToGround_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) - (p0_PID -> System_Elevator_Idle)) +
     (p0_PID -> System_Elevator_Idle))
  (p0_PID.(sn.System_Elevator_current)) = (Floor.min)
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_current)) =
                              (PID_aa.(sn.System_Elevator_current)))
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_called)) =
          (PID_aa.(sn.System_Elevator_called)))
  ((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_Elevator)))
       )

}

pred System_Elevator_Idle_DefaultToGround_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_Idle) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_PID -> System_Elevator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Elevator_Idle_DefaultToGround [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.System_Elevator_Idle_DefaultToGround_pre)
  p0_PID.(sn.(s.System_Elevator_Idle_DefaultToGround_post))
}

pred System_Elevator_MovingUp_MoveUp_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> System_Elevator_MovingUp) & (s.dsh_conf1))
  some
  p0_PID.(s.System_Elevator_called) and
  (p0_PID.(s.System_Elevator_direction)) = Up and
  some
  (((p0_PID.(s.System_Elevator_current)).nexts) &
     p0_PID.(s.System_Elevator_called)) and
  p0_PID.(s.System_Elevator_current) !in
    p0_PID.(s.System_Elevator_called)
  !(System in (s.dsh_sc_used0))
  !((p0_PID -> System_Elevator) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingUp_MoveUp_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) - (p0_PID -> System_Elevator_MovingUp)) +
     (p0_PID -> System_Elevator_MovingUp))
  (p0_PID.(sn.System_Elevator_current)) =
  ((((p0_PID.(s.System_Elevator_current)).nexts) &
      p0_PID.(s.System_Elevator_called)).min) and
  (p0_PID.(sn.System_Elevator_called)) =
    ((p0_PID.(s.System_Elevator_called)) -
       (p0_PID.(sn.System_Elevator_current)))
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_called)) =
                              (PID_aa.(sn.System_Elevator_called)))
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_current)) =
                              (PID_aa.(sn.System_Elevator_current)))
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  ((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_Elevator)))
       )

}

pred System_Elevator_MovingUp_MoveUp_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_MovingUp) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_PID -> System_Elevator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Elevator_MovingUp_MoveUp [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.System_Elevator_MovingUp_MoveUp_pre)
  p0_PID.(sn.(s.System_Elevator_MovingUp_MoveUp_post))
}

pred System_Elevator_MovingUp_Idle_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> System_Elevator_MovingUp) & (s.dsh_conf1))
  no p0_PID.(s.System_Elevator_called)
  !(System in (s.dsh_sc_used0))
  !((p0_PID -> System_Elevator) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingUp_Idle_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((((s.dsh_conf1) - (p0_PID -> System_Elevator_MovingUp)) -
       (p0_PID -> System_Elevator_MovingDown)) -
      (p0_PID -> System_Elevator_Idle)) +
     (p0_PID -> System_Elevator_Idle))
  (p0_PID.(s.System_Elevator_current)) = (Floor.min)
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_called)) =
          (PID_aa.(sn.System_Elevator_called)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_current)) =
          (PID_aa.(sn.System_Elevator_current)))
  ((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_Elevator)))
       )

}

pred System_Elevator_MovingUp_Idle_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_MovingUp) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_PID -> System_Elevator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Elevator_MovingUp_Idle [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.System_Elevator_MovingUp_Idle_pre)
  p0_PID.(sn.(s.System_Elevator_MovingUp_Idle_post))
}

pred System_Elevator_MovingDown_ElevatorInCalled_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some
((p0_PID -> System_Elevator_MovingDown) & (s.dsh_conf1))
  some
  p0_PID.(s.System_Elevator_called) and
  p0_PID.(s.System_Elevator_called) in
    p0_PID.(s.System_Elevator_current)
  !(System in (s.dsh_sc_used0))
  !((p0_PID -> System_Elevator) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingDown_ElevatorInCalled_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) - (p0_PID -> System_Elevator_MovingDown)) +
     (p0_PID -> System_Elevator_MovingDown))
  (p0_PID.(sn.System_Elevator_called)) =
  ((p0_PID.(s.System_Elevator_called)) -
     (p0_PID.(s.System_Elevator_current)))
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_called)) =
                              (PID_aa.(sn.System_Elevator_called)))
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_current)) =
          (PID_aa.(sn.System_Elevator_current)))
  ((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_Elevator)))
       )

}

pred System_Elevator_MovingDown_ElevatorInCalled_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_PID -> System_Elevator_MovingDown) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_PID -> System_Elevator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Elevator_MovingDown_ElevatorInCalled [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.System_Elevator_MovingDown_ElevatorInCalled_pre)
  p0_PID.(sn.(s.System_Elevator_MovingDown_ElevatorInCalled_post))
}

pred System_Elevator_MovingDown_ChangeDirToUp_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some
((p0_PID -> System_Elevator_MovingDown) & (s.dsh_conf1))
  some
  p0_PID.(s.System_Elevator_called) and
  no
  (((p0_PID.(s.System_Elevator_current)).prevs) &
     p0_PID.(s.System_Elevator_called)) and
  some
  (((p0_PID.(s.System_Elevator_current)).nexts) &
     p0_PID.(s.System_Elevator_called)) and
  p0_PID.(s.System_Elevator_current) !in
    p0_PID.(s.System_Elevator_called)
  !(System in (s.dsh_sc_used0))
  !((p0_PID -> System_Elevator) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingDown_ChangeDirToUp_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((((s.dsh_conf1) - (p0_PID -> System_Elevator_MovingUp)) -
       (p0_PID -> System_Elevator_MovingDown)) -
      (p0_PID -> System_Elevator_Idle)) +
     (p0_PID -> System_Elevator_MovingUp))
  (p0_PID.(sn.System_Elevator_direction)) = Up
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_direction)) =
                              (PID_aa.(sn.System_Elevator_direction)))
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_called)) =
          (PID_aa.(sn.System_Elevator_called)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_current)) =
          (PID_aa.(sn.System_Elevator_current)))
  ((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_Elevator)))
       )

}

pred System_Elevator_MovingDown_ChangeDirToUp_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_PID -> System_Elevator_MovingDown) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_PID -> System_Elevator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Elevator_MovingDown_ChangeDirToUp [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.System_Elevator_MovingDown_ChangeDirToUp_pre)
  p0_PID.(sn.(s.System_Elevator_MovingDown_ChangeDirToUp_post))
}

pred System_Controller_SendingUpRequest_pre [
	s: one DshSnapshot] {
  some (System_Controller_Sending & (s.dsh_conf0))
  Up in (Floor.(s.System_Controller_callToSend))
  !(System in (s.dsh_sc_used0))
  !(System_Controller in (s.dsh_sc_used0))
}


pred System_Controller_SendingUpRequest_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) - System_Controller_Sending) +
     System_Controller_Sending)
  (sn.dsh_conf1) = (s.dsh_conf1)
  ((some p: PID,f: (s.System_Controller_callToSend).Up | f.((p.(s.System_Elevator_current)).lte) and
                                                         (p.(s.System_Elevator_direction)) =
                                                           Up))=>
    (one e0: PID,f: (s.System_Controller_callToSend).Up | (e0.(s.System_Elevator_direction)) =
                                                            Up and
                                                            f.((e0.(s.System_Elevator_current)).lte) and
                                                            (e0.(sn.System_Elevator_called)) =
                                                              ((e0.(s.System_Elevator_called)) +
                                                                 f) and
                                                            (sn.System_Controller_callToSend) =
                                                              ((s.System_Controller_callToSend) -
                                                                 (f ->
                                                                    Up)) and
                                                            (no e1: PID -
                                                                      e0 | (e1.(s.System_Elevator_direction)) =
                                                                             Up and
                                                                             f.((e1.(s.System_Elevator_current)).((e0.(s.System_Elevator_current)).between))) and
                                                            (all others: PID -
                                                                           e0 | (others.(sn.System_Elevator_called)) =
                                                                                  (others.(s.System_Elevator_called))))
  else
    (one e0: PID,f: (s.System_Controller_callToSend).Direction | (e0.(sn.System_Elevator_called)) =
                                                                   ((e0.(s.System_Elevator_called)) +
                                                                      f) and
                                                                   (sn.System_Controller_callToSend) =
                                                                     ((s.System_Controller_callToSend) -
                                                                        (f ->
                                                                           (f.(s.System_Controller_callToSend)))) and
                                                                   (all others: PID -
                                                                                  e0 | (others.(sn.System_Elevator_called)) =
                                                                                         (others.(s.System_Elevator_called))))

  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_current)) =
          (PID_aa.(sn.System_Elevator_current)))
  ((none -> none).(System_Controller.(none.(sn.(s._nextIsStable)))))=>
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
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + System_Controller) and
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))
       )

}

pred System_Controller_SendingUpRequest_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some (System_Controller_Sending & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !(System_Controller in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Controller_SendingUpRequest [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.System_Controller_SendingUpRequest_pre
  sn.(s.System_Controller_SendingUpRequest_post)
}

pred System_Elevator_MovingUp_ElevatorInCalled_pre [
	s: one DshSnapshot,
	p0_PID: one PID] {
  some ((p0_PID -> System_Elevator_MovingUp) & (s.dsh_conf1))
  some
  p0_PID.(s.System_Elevator_called) and
  p0_PID.(s.System_Elevator_called) in
    p0_PID.(s.System_Elevator_current)
  !(System in (s.dsh_sc_used0))
  !((p0_PID -> System_Elevator) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingUp_ElevatorInCalled_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) - (p0_PID -> System_Elevator_MovingUp)) +
     (p0_PID -> System_Elevator_MovingUp))
  (p0_PID.(sn.System_Elevator_called)) =
  ((p0_PID.(s.System_Elevator_called)) -
     (p0_PID.(s.System_Elevator_current)))
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_called)) =
                              (PID_aa.(sn.System_Elevator_called)))
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_current)) =
          (PID_aa.(sn.System_Elevator_current)))
  ((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_Elevator)))
       )

}

pred System_Elevator_MovingUp_ElevatorInCalled_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_MovingUp) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_PID -> System_Elevator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_Elevator_MovingUp_ElevatorInCalled [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  p0_PID.(s.System_Elevator_MovingUp_ElevatorInCalled_pre)
  p0_PID.(sn.(s.System_Elevator_MovingUp_ElevatorInCalled_post))
}

pred _nextIsStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  !(dsh_scp1.(dsh_scp0.(sn.(s.System_Controller_SendingDownRequest_enabledAfterStep))))
  !(dsh_scp1.(dsh_scp0.(p0_PID.(sn.(s.System_Elevator_MovingUp_ChangeDirToDown_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_PID.(sn.(s.System_Elevator_Idle_Move_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_PID.(sn.(s.System_Elevator_MovingDown_Idle_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_PID.(sn.(s.System_Elevator_MovingDown_MoveDown_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_PID.(sn.(s.System_Elevator_Idle_DefaultToGround_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_PID.(sn.(s.System_Elevator_MovingUp_MoveUp_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_PID.(sn.(s.System_Elevator_MovingUp_Idle_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_PID.(sn.(s.System_Elevator_MovingDown_ElevatorInCalled_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_PID.(sn.(s.System_Elevator_MovingDown_ChangeDirToUp_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(sn.(s.System_Controller_SendingUpRequest_enabledAfterStep))))
  !(dsh_scp1.(dsh_scp0.(p0_PID.(sn.(s.System_Elevator_MovingUp_ElevatorInCalled_enabledAfterStep)))))
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_stable) = (s.dsh_stable)
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_sc_used1) = (s.dsh_sc_used1)
  (sn.System_Controller_callToSend) =
  (s.System_Controller_callToSend)
  (sn.System_Elevator_direction) =
  (s.System_Elevator_direction)
  (sn.System_Elevator_called) = (s.System_Elevator_called)
  (sn.System_Elevator_current) = (s.System_Elevator_current)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { (some p0_PID: one
      PID | { sn.(s.System_Controller_SendingDownRequest) or
                p0_PID.(sn.(s.System_Elevator_MovingUp_ChangeDirToDown)) or
                p0_PID.(sn.(s.System_Elevator_Idle_Move)) or
                p0_PID.(sn.(s.System_Elevator_MovingDown_Idle)) or
                p0_PID.(sn.(s.System_Elevator_MovingDown_MoveDown)) or
                p0_PID.(sn.(s.System_Elevator_Idle_DefaultToGround)) or
                p0_PID.(sn.(s.System_Elevator_MovingUp_MoveUp)) or
                p0_PID.(sn.(s.System_Elevator_MovingUp_Idle)) or
                p0_PID.(sn.(s.System_Elevator_MovingDown_ElevatorInCalled)) or
                p0_PID.(sn.(s.System_Elevator_MovingDown_ChangeDirToUp)) or
                sn.(s.System_Controller_SendingUpRequest) or
                p0_PID.(sn.(s.System_Elevator_MovingUp_ElevatorInCalled)) }) or
    !((some p0_PID: one
         PID | { s.System_Controller_SendingDownRequest_pre or
                   p0_PID.(s.System_Elevator_MovingUp_ChangeDirToDown_pre) or
                   p0_PID.(s.System_Elevator_Idle_Move_pre) or
                   p0_PID.(s.System_Elevator_MovingDown_Idle_pre) or
                   p0_PID.(s.System_Elevator_MovingDown_MoveDown_pre) or
                   p0_PID.(s.System_Elevator_Idle_DefaultToGround_pre) or
                   p0_PID.(s.System_Elevator_MovingUp_MoveUp_pre) or
                   p0_PID.(s.System_Elevator_MovingUp_Idle_pre) or
                   p0_PID.(s.System_Elevator_MovingDown_ElevatorInCalled_pre) or
                   p0_PID.(s.System_Elevator_MovingDown_ChangeDirToUp_pre) or
                   s.System_Controller_SendingUpRequest_pre or
                   p0_PID.(s.System_Elevator_MovingUp_ElevatorInCalled_pre) })) and
      sn.(s.dsh_stutter) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}

