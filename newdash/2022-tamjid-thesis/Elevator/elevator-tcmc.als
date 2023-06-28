/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-28 18:42:20
*/

open util/ordering[Floor]

open util/boolean
open util/tcmc[DshSnapshot]

sig Floor {}
abstract sig Direction {}
one sig Up, Down extends Direction {}

pred between [n1, nb, n2: Floor] {
	     lt[n1,n2] =>   ( lt[n1,nb] && lt[nb,n2] )
             else ( lt[n1,nb] || lt[nb,n2] )  }

abstract sig DshStates {}
abstract sig System extends DshStates {} 
abstract sig DshScopes {}
one sig SystemScope extends DshScopes {} 
one sig System_ControllerScope extends DshScopes {} 
abstract sig System_Controller extends System {} 
one sig System_Controller_SendingScope extends DshScopes {} 
one sig System_Controller_Sending extends System_Controller {} 
one sig System_ElevatorScope extends DshScopes {} 
abstract sig System_Elevator extends System {} 
one sig System_Elevator_MovingUpScope extends DshScopes {} 
one sig System_Elevator_MovingUp extends System_Elevator {} 
one sig System_Elevator_MovingDownScope extends DshScopes {} 
one sig System_Elevator_MovingDown extends System_Elevator {} 
one sig System_Elevator_IdleScope extends DshScopes {} 
one sig System_Elevator_Idle extends System_Elevator {} 

abstract sig Transitions {}
one sig NO_TRANS extends Transitions {} 
one sig System_Controller_SendingDownRequest extends Transitions {} 
one sig System_Elevator_MovingUp_ChangeDirToDown extends Transitions {} 
one sig System_Elevator_Idle_Move extends Transitions {} 
one sig System_Elevator_MovingDown_Idle extends Transitions {} 
one sig System_Elevator_MovingDown_MoveDown extends Transitions {} 
one sig System_Elevator_Idle_DefaultToGround extends Transitions {} 
one sig System_Elevator_MovingUp_MoveUp extends Transitions {} 
one sig System_Elevator_MovingUp_Idle extends Transitions {} 
one sig System_Elevator_MovingDown_ElevatorInCalled extends Transitions {} 
one sig System_Elevator_MovingDown_ChangeDirToUp extends Transitions {} 
one sig System_Controller_SendingUpRequest extends Transitions {} 
one sig System_Elevator_MovingUp_ElevatorInCalled extends Transitions {} 

abstract sig DshIds {}
sig PID extends DshIds {} 

sig DshSnapshot {
  dsh_sc_used0: set DshScopes,
  dsh_conf0: set DshStates,
  dsh_taken0: set Transitions,
  dsh_sc_used1: DshIds -> DshScopes,
  dsh_conf1: DshIds -> DshStates,
  dsh_taken1: DshIds -> Transitions,
  dsh_stable: one boolean/Bool,
  System_Controller_callToSend: Floor -> Direction,
  System_Elevator_direction: PID -> one Direction,
  System_Elevator_called: PID -> set Floor,
  System_Elevator_current: PID -> one Floor
}

pred dsh_initial [
	s: one DshSnapshot] {
  (all p0_PID: one
  PID | (s.dsh_conf0) = System_Controller_Sending &&
          (s.dsh_conf1) = (PID -> System_Elevator_Idle) &&
          (s.dsh_sc_used0) = none &&
          (s.dsh_taken0) = NO_TRANS &&
          (s.dsh_sc_used1) = (none -> none) &&
          (s.dsh_taken1) = (none -> none) &&
          no
          p0_PID.(s.System_Elevator_called) &&
          (p0_PID.(s.System_Elevator_current)) = (Floor.min) &&
          (p0_PID.(s.System_Elevator_direction)) = Up &&
          (# s.System_Controller_callToSend) = (3) &&
          Up !in (Floor.(s.System_Controller_callToSend)))
  (s.dsh_stable).boolean/isTrue
}

pred System_Controller_SendingDownRequest_pre [
	s: one DshSnapshot] {
  some (System_Controller_Sending & (s.dsh_conf0))
  Down in (Floor.(s.System_Controller_callToSend))
  !(SystemScope in (s.dsh_sc_used0))
  !(System_ControllerScope in (s.dsh_sc_used0))
}


pred System_Controller_SendingDownRequest_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) - System_Controller_Sending) +
     System_Controller_Sending)
  (sn.dsh_conf1) = (s.dsh_conf1)
  {((some p: PID,f: (s.System_Controller_callToSend).Down | (p.(s.System_Elevator_current)).(f.lte) &&
                                                            (p.(s.System_Elevator_direction)) =
                                                              Down))=>
    (one e0: PID,f: (s.System_Controller_callToSend).Down | (e0.(s.System_Elevator_direction)) =
                                                              Down &&
                                                              f.((e0.(s.System_Elevator_current)).gte) &&
                                                              (e0.(sn.System_Elevator_called)) =
                                                                ((e0.(s.System_Elevator_called)) +
                                                                   f) &&
                                                              (sn.System_Controller_callToSend) =
                                                                ((s.System_Controller_callToSend) -
                                                                   (f ->
                                                                      Down)) &&
                                                              (no e1: PID -
                                                                        e0 | (e1.(s.System_Elevator_direction)) =
                                                                               Down &&
                                                                               (e1.(s.System_Elevator_current)).((e0.(s.System_Elevator_current)).(f.between))) &&
                                                              (all others: PID -
                                                                             e0 | (others.(sn.System_Elevator_called)) =
                                                                                    (others.(s.System_Elevator_called))))
  else
    (one e0: PID,f: (s.System_Controller_callToSend).Direction | (e0.(sn.System_Elevator_called)) =
                                                                   ((e0.(s.System_Elevator_called)) +
                                                                      f) &&
                                                                   (sn.System_Controller_callToSend) =
                                                                     ((s.System_Controller_callToSend) -
                                                                        (f ->
                                                                           (f.(s.System_Controller_callToSend)))) &&
                                                                   (all others: PID -
                                                                                  e0 | (others.(sn.System_Elevator_called)) =
                                                                                         (others.(s.System_Elevator_called))))}

  (sn.dsh_taken0) = System_Controller_SendingDownRequest
  (sn.dsh_taken1) = (none -> none)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_current)) =
          (PID_aa.(sn.System_Elevator_current)))
  {((none -> none).(System_Controller.(none.(sn.(s._nextIsStable)))))=>
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
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + System_ControllerScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred System_Controller_SendingDownRequest_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some (System_Controller_Sending & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !(System_Controller in sc0) ||
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
  p0_PID.(s.System_Elevator_called) &&
  no
  (((p0_PID.(s.System_Elevator_current)).nexts) &
     p0_PID.(s.System_Elevator_called)) &&
  some
  (((p0_PID.(s.System_Elevator_current)).prevs) &
     p0_PID.(s.System_Elevator_called)) &&
  p0_PID.(s.System_Elevator_current) !in
    p0_PID.(s.System_Elevator_called)
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_PID -> System_ElevatorScope) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingUp_ChangeDirToDown_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (((p0_PID -> System_Elevator_MovingUp) +
          (p0_PID -> System_Elevator_MovingDown)) +
         (p0_PID -> System_Elevator_Idle))) +
     (p0_PID -> System_Elevator_MovingDown))
  (p0_PID.(sn.System_Elevator_direction)) = Down
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_PID -> System_Elevator_MovingUp_ChangeDirToDown)
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
  {((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_ElevatorScope)))}
       )}

}

pred System_Elevator_MovingUp_ChangeDirToDown_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_MovingUp) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_PID -> System_Elevator) in sc1) ||
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
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_PID -> System_ElevatorScope) in (s.dsh_sc_used1))
}


pred System_Elevator_Idle_Move_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (((p0_PID -> System_Elevator_MovingUp) +
          (p0_PID -> System_Elevator_MovingDown)) +
         (p0_PID -> System_Elevator_Idle))) +
     (p0_PID -> System_Elevator_MovingUp))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) = (p0_PID -> System_Elevator_Idle_Move)
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
  {((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_ElevatorScope)))}
       )}

}

pred System_Elevator_Idle_Move_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_Idle) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_PID -> System_Elevator) in sc1) ||
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
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_PID -> System_ElevatorScope) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingDown_Idle_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (((p0_PID -> System_Elevator_MovingUp) +
          (p0_PID -> System_Elevator_MovingDown)) +
         (p0_PID -> System_Elevator_Idle))) +
     (p0_PID -> System_Elevator_Idle))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_PID -> System_Elevator_MovingDown_Idle)
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
  {((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_ElevatorScope)))}
       )}

}

pred System_Elevator_MovingDown_Idle_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_PID -> System_Elevator_MovingDown) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_PID -> System_Elevator) in sc1) ||
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
  p0_PID.(s.System_Elevator_called) &&
  (p0_PID.(s.System_Elevator_direction)) = Down &&
  some
  (((p0_PID.(s.System_Elevator_current)).prevs) &
     p0_PID.(s.System_Elevator_called)) &&
  p0_PID.(s.System_Elevator_current) !in
    p0_PID.(s.System_Elevator_called)
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_PID -> System_ElevatorScope) in (s.dsh_sc_used1))
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
      p0_PID.(s.System_Elevator_called)).max) &&
  (p0_PID.(sn.System_Elevator_called)) =
    ((p0_PID.(s.System_Elevator_called)) -
       (p0_PID.(sn.System_Elevator_current)))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_PID -> System_Elevator_MovingDown_MoveDown)
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_called)) =
                              (PID_aa.(sn.System_Elevator_called)))
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_current)) =
                              (PID_aa.(sn.System_Elevator_current)))
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  {((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_ElevatorScope)))}
       )}

}

pred System_Elevator_MovingDown_MoveDown_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_PID -> System_Elevator_MovingDown) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_PID -> System_Elevator) in sc1) ||
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
  p0_PID.(s.System_Elevator_called) &&
  (Floor.min) !in p0_PID.(s.System_Elevator_current)
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_PID -> System_ElevatorScope) in (s.dsh_sc_used1))
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
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_PID -> System_Elevator_Idle_DefaultToGround)
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
  {((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_ElevatorScope)))}
       )}

}

pred System_Elevator_Idle_DefaultToGround_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_Idle) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_PID -> System_Elevator) in sc1) ||
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
  p0_PID.(s.System_Elevator_called) &&
  (p0_PID.(s.System_Elevator_direction)) = Up &&
  some
  (((p0_PID.(s.System_Elevator_current)).nexts) &
     p0_PID.(s.System_Elevator_called)) &&
  p0_PID.(s.System_Elevator_current) !in
    p0_PID.(s.System_Elevator_called)
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_PID -> System_ElevatorScope) in (s.dsh_sc_used1))
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
      p0_PID.(s.System_Elevator_called)).min) &&
  (p0_PID.(sn.System_Elevator_called)) =
    ((p0_PID.(s.System_Elevator_called)) -
       (p0_PID.(sn.System_Elevator_current)))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_PID -> System_Elevator_MovingUp_MoveUp)
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_called)) =
                              (PID_aa.(sn.System_Elevator_called)))
  (all PID_aa: PID - p0_PID | (PID_aa.(s.System_Elevator_current)) =
                              (PID_aa.(sn.System_Elevator_current)))
  (s.System_Controller_callToSend) =
  (sn.System_Controller_callToSend)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  {((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_ElevatorScope)))}
       )}

}

pred System_Elevator_MovingUp_MoveUp_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_MovingUp) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_PID -> System_Elevator) in sc1) ||
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
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_PID -> System_ElevatorScope) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingUp_Idle_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (((p0_PID -> System_Elevator_MovingUp) +
          (p0_PID -> System_Elevator_MovingDown)) +
         (p0_PID -> System_Elevator_Idle))) +
     (p0_PID -> System_Elevator_Idle))
  (p0_PID.(s.System_Elevator_current)) = (Floor.min)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) = (p0_PID -> System_Elevator_MovingUp_Idle)
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
  {((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_ElevatorScope)))}
       )}

}

pred System_Elevator_MovingUp_Idle_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_MovingUp) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_PID -> System_Elevator) in sc1) ||
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
  p0_PID.(s.System_Elevator_called) &&
  p0_PID.(s.System_Elevator_called) in
    p0_PID.(s.System_Elevator_current)
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_PID -> System_ElevatorScope) in (s.dsh_sc_used1))
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
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_PID -> System_Elevator_MovingDown_ElevatorInCalled)
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
  {((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_ElevatorScope)))}
       )}

}

pred System_Elevator_MovingDown_ElevatorInCalled_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_PID -> System_Elevator_MovingDown) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_PID -> System_Elevator) in sc1) ||
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
  p0_PID.(s.System_Elevator_called) &&
  no
  (((p0_PID.(s.System_Elevator_current)).prevs) &
     p0_PID.(s.System_Elevator_called)) &&
  some
  (((p0_PID.(s.System_Elevator_current)).nexts) &
     p0_PID.(s.System_Elevator_called)) &&
  p0_PID.(s.System_Elevator_current) !in
    p0_PID.(s.System_Elevator_called)
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_PID -> System_ElevatorScope) in (s.dsh_sc_used1))
}


pred System_Elevator_MovingDown_ChangeDirToUp_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (((p0_PID -> System_Elevator_MovingUp) +
          (p0_PID -> System_Elevator_MovingDown)) +
         (p0_PID -> System_Elevator_Idle))) +
     (p0_PID -> System_Elevator_MovingUp))
  (p0_PID.(sn.System_Elevator_direction)) = Up
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_PID -> System_Elevator_MovingDown_ChangeDirToUp)
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
  {((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_ElevatorScope)))}
       )}

}

pred System_Elevator_MovingDown_ChangeDirToUp_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_PID -> System_Elevator_MovingDown) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_PID -> System_Elevator) in sc1) ||
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
  !(SystemScope in (s.dsh_sc_used0))
  !(System_ControllerScope in (s.dsh_sc_used0))
}


pred System_Controller_SendingUpRequest_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) - System_Controller_Sending) +
     System_Controller_Sending)
  (sn.dsh_conf1) = (s.dsh_conf1)
  {((some p: PID,f: (s.System_Controller_callToSend).Up | f.((p.(s.System_Elevator_current)).lte) &&
                                                          (p.(s.System_Elevator_direction)) =
                                                            Up))=>
    (one e0: PID,f: (s.System_Controller_callToSend).Up | (e0.(s.System_Elevator_direction)) =
                                                            Up &&
                                                            f.((e0.(s.System_Elevator_current)).lte) &&
                                                            (e0.(sn.System_Elevator_called)) =
                                                              ((e0.(s.System_Elevator_called)) +
                                                                 f) &&
                                                            (sn.System_Controller_callToSend) =
                                                              ((s.System_Controller_callToSend) -
                                                                 (f ->
                                                                    Up)) &&
                                                            (no e1: PID -
                                                                      e0 | (e1.(s.System_Elevator_direction)) =
                                                                             Up &&
                                                                             f.((e1.(s.System_Elevator_current)).((e0.(s.System_Elevator_current)).between))) &&
                                                            (all others: PID -
                                                                           e0 | (others.(sn.System_Elevator_called)) =
                                                                                  (others.(s.System_Elevator_called))))
  else
    (one e0: PID,f: (s.System_Controller_callToSend).Direction | (e0.(sn.System_Elevator_called)) =
                                                                   ((e0.(s.System_Elevator_called)) +
                                                                      f) &&
                                                                   (sn.System_Controller_callToSend) =
                                                                     ((s.System_Controller_callToSend) -
                                                                        (f ->
                                                                           (f.(s.System_Controller_callToSend)))) &&
                                                                   (all others: PID -
                                                                                  e0 | (others.(sn.System_Elevator_called)) =
                                                                                         (others.(s.System_Elevator_called))))}

  (sn.dsh_taken0) = System_Controller_SendingUpRequest
  (sn.dsh_taken1) = (none -> none)
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_direction)) =
          (PID_aa.(sn.System_Elevator_direction)))
  (all PID_aa: one
  PID | (PID_aa.(s.System_Elevator_current)) =
          (PID_aa.(sn.System_Elevator_current)))
  {((none -> none).(System_Controller.(none.(sn.(s._nextIsStable)))))=>
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
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + System_ControllerScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred System_Controller_SendingUpRequest_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some (System_Controller_Sending & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !(System_Controller in sc0) ||
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
  p0_PID.(s.System_Elevator_called) &&
  p0_PID.(s.System_Elevator_called) in
    p0_PID.(s.System_Elevator_current)
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_PID -> System_ElevatorScope) in (s.dsh_sc_used1))
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
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_PID -> System_Elevator_MovingUp_ElevatorInCalled)
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
  {((p0_PID -> System_Elevator).(none.(p0_PID.(sn.(s._nextIsStable)))))=>
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
                   (p0_PID -> System_ElevatorScope)))}
       )}

}

pred System_Elevator_MovingUp_ElevatorInCalled_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_PID: one PID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_PID -> System_Elevator_MovingUp) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_PID -> System_Elevator) in sc1) ||
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
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  !(sc1.(sc0.(sn.(s.System_Controller_SendingDownRequest_enabledAfterStep))))
  !(sc1.(sc0.(p0_PID.(sn.(s.System_Elevator_MovingUp_ChangeDirToDown_enabledAfterStep)))))
  !(sc1.(sc0.(p0_PID.(sn.(s.System_Elevator_Idle_Move_enabledAfterStep)))))
  !(sc1.(sc0.(p0_PID.(sn.(s.System_Elevator_MovingDown_Idle_enabledAfterStep)))))
  !(sc1.(sc0.(p0_PID.(sn.(s.System_Elevator_MovingDown_MoveDown_enabledAfterStep)))))
  !(sc1.(sc0.(p0_PID.(sn.(s.System_Elevator_Idle_DefaultToGround_enabledAfterStep)))))
  !(sc1.(sc0.(p0_PID.(sn.(s.System_Elevator_MovingUp_MoveUp_enabledAfterStep)))))
  !(sc1.(sc0.(p0_PID.(sn.(s.System_Elevator_MovingUp_Idle_enabledAfterStep)))))
  !(sc1.(sc0.(p0_PID.(sn.(s.System_Elevator_MovingDown_ElevatorInCalled_enabledAfterStep)))))
  !(sc1.(sc0.(p0_PID.(sn.(s.System_Elevator_MovingDown_ChangeDirToUp_enabledAfterStep)))))
  !(sc1.(sc0.(sn.(s.System_Controller_SendingUpRequest_enabledAfterStep))))
  !(sc1.(sc0.(p0_PID.(sn.(s.System_Elevator_MovingUp_ElevatorInCalled_enabledAfterStep)))))
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
      PID | { sn.(s.System_Controller_SendingDownRequest) ||
                p0_PID.(sn.(s.System_Elevator_MovingUp_ChangeDirToDown)) ||
                p0_PID.(sn.(s.System_Elevator_Idle_Move)) ||
                p0_PID.(sn.(s.System_Elevator_MovingDown_Idle)) ||
                p0_PID.(sn.(s.System_Elevator_MovingDown_MoveDown)) ||
                p0_PID.(sn.(s.System_Elevator_Idle_DefaultToGround)) ||
                p0_PID.(sn.(s.System_Elevator_MovingUp_MoveUp)) ||
                p0_PID.(sn.(s.System_Elevator_MovingUp_Idle)) ||
                p0_PID.(sn.(s.System_Elevator_MovingDown_ElevatorInCalled)) ||
                p0_PID.(sn.(s.System_Elevator_MovingDown_ChangeDirToUp)) ||
                sn.(s.System_Controller_SendingUpRequest) ||
                p0_PID.(sn.(s.System_Elevator_MovingUp_ElevatorInCalled)) }) ||
    !((some p0_PID: one
         PID | { s.System_Controller_SendingDownRequest_pre ||
                   p0_PID.(s.System_Elevator_MovingUp_ChangeDirToDown_pre) ||
                   p0_PID.(s.System_Elevator_Idle_Move_pre) ||
                   p0_PID.(s.System_Elevator_MovingDown_Idle_pre) ||
                   p0_PID.(s.System_Elevator_MovingDown_MoveDown_pre) ||
                   p0_PID.(s.System_Elevator_Idle_DefaultToGround_pre) ||
                   p0_PID.(s.System_Elevator_MovingUp_MoveUp_pre) ||
                   p0_PID.(s.System_Elevator_MovingUp_Idle_pre) ||
                   p0_PID.(s.System_Elevator_MovingDown_ElevatorInCalled_pre) ||
                   p0_PID.(s.System_Elevator_MovingDown_ChangeDirToUp_pre) ||
                   s.System_Controller_SendingUpRequest_pre ||
                   p0_PID.(s.System_Elevator_MovingUp_ElevatorInCalled_pre) })) &&
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

