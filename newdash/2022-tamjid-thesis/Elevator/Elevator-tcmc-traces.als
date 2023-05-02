open util/ordering[Floor]

open util/boolean
open util/ordering[Snapshot] as Snapshot

sig Floor {}
abstract sig Direction {}
one sig Up, Down extends Direction {}

pred between [n1, nb, n2: Floor] {
	     lt[n1,n2] =>   ( lt[n1,nb] && lt[nb,n2] )
             else ( lt[n1,nb] || lt[nb,n2] )  }

assert ctl_allCallsAreEventuallySend { 
	ctl_mc[af[{s: one Snapshot | no s.(Snapshot <: System_Controller_callToSend)}]]
}

assert ctl_closestElevatorHasCall {
    ctl_mc[af[{s: one Snapshot | (one e0: one PID,f: one Floor | f in e0. (s.(Snapshot <: System_Elevator_called)) and
            e0. (s.(Snapshot <: System_Elevator_direction)) = Up => (
            (no e1: one PID - e0 | between[e0. (s.(Snapshot <: System_Elevator_current)), e1. (s.(Snapshot <: System_Elevator_current)), f] and
                e1. (s.(Snapshot <: System_Elevator_direction)) = Up))) }]]
}

//check ctl_allCallsAreEventuallySend for 17 Snapshot, exactly 3 PID, exactly 4 Floor, 1 PathNode
//check ctl_allCallsAreEventuallySend for 17 Snapshot, exactly 4 PID, exactly 4 Floor, 1 PathNode
check ctl_closestElevatorHasCall for 17 Snapshot, exactly 3 PID, exactly 4 Floor, 1 PathNode
check ctl_closestElevatorHasCall for 17 Snapshot, exactly 4 PID, exactly 4 Floor, 1 PathNode
abstract sig StateLabel {}
sig System extends StateLabel {} 
one sig System_Controller extends System {} 
one sig System_Controller_Sending extends System_Controller {} 
one sig System_Elevator extends System {} 
one sig System_Elevator_MovingUp extends System_Elevator {} 
one sig System_Elevator_MovingDown extends System_Elevator {} 
one sig System_Elevator_Idle extends System_Elevator {} 

abstract sig Identifiers {}
sig PID extends Identifiers {} 

sig Snapshot {
  scopesUsed0 : set StateLabel,
  conf0 : set StateLabel,
  scopesUsed1 : Identifiers -> Identifiers -> StateLabel,
  conf1 : Identifiers -> Identifiers -> StateLabel,
  stable : one boolean/Bool
}

pred System_Controller_SendingDownRequest_pre[s : one Snapshot] {
  System/Controller/Sending in s. (conf0)
  ! {System in scopesUsed0}
  ! {System/Controller in scopesUsed0}
}


pred System_Controller_SendingDownRequest_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - System/Controller/Sending } + System/Controller/Sending }
  sNext. (conf1) = s. (conf1)
  (none. (System/Controller. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Controller_SendingDownRequest_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  System/Controller/Sending in sNext. (conf0)
}

pred System_Controller_SendingDownRequest[s : one Snapshot, sNext : one Snapshot] {
  s. (System_Controller_SendingDownRequest_pre)
  sNext. (s. (System_Controller_SendingDownRequest_post))
}

pred System_Elevator_MovingUp_ChangeDirToDown_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> System/Elevator/MovingUp } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pPID -> System/Elevator } in scopesUsed1}
}


pred System_Elevator_MovingUp_ChangeDirToDown_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> System/Elevator/MovingUp } - { pPID -> System/Elevator/MovingDown } - { pPID -> System/Elevator/Idle } } + { pPID -> System/Elevator/MovingDown } }
  (pPID -> System/Elevator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Elevator_MovingUp_ChangeDirToDown_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPID -> System/Elevator/MovingUp } in sNext. (conf1)
}

pred System_Elevator_MovingUp_ChangeDirToDown[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (System_Elevator_MovingUp_ChangeDirToDown_pre))
  pPID. (sNext. (s. (System_Elevator_MovingUp_ChangeDirToDown_post)))
}

pred System_Elevator_Idle_Move_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> System/Elevator/Idle } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pPID -> System/Elevator } in scopesUsed1}
}


pred System_Elevator_Idle_Move_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> System/Elevator/MovingUp } - { pPID -> System/Elevator/MovingDown } - { pPID -> System/Elevator/Idle } } + { pPID -> System/Elevator/MovingUp } }
  (pPID -> System/Elevator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Elevator_Idle_Move_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPID -> System/Elevator/Idle } in sNext. (conf1)
}

pred System_Elevator_Idle_Move[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (System_Elevator_Idle_Move_pre))
  pPID. (sNext. (s. (System_Elevator_Idle_Move_post)))
}

pred System_Elevator_MovingDown_Idle_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> System/Elevator/MovingDown } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pPID -> System/Elevator } in scopesUsed1}
}


pred System_Elevator_MovingDown_Idle_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> System/Elevator/MovingUp } - { pPID -> System/Elevator/MovingDown } - { pPID -> System/Elevator/Idle } } + { pPID -> System/Elevator/Idle } }
  (pPID -> System/Elevator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Elevator_MovingDown_Idle_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPID -> System/Elevator/MovingDown } in sNext. (conf1)
}

pred System_Elevator_MovingDown_Idle[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (System_Elevator_MovingDown_Idle_pre))
  pPID. (sNext. (s. (System_Elevator_MovingDown_Idle_post)))
}

pred System_Elevator_MovingDown_MoveDown_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> System/Elevator/MovingDown } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pPID -> System/Elevator } in scopesUsed1}
}


pred System_Elevator_MovingDown_MoveDown_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> System/Elevator/MovingDown } } + { pPID -> System/Elevator/MovingDown } }
  (pPID -> System/Elevator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Elevator_MovingDown_MoveDown_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPID -> System/Elevator/MovingDown } in sNext. (conf1)
}

pred System_Elevator_MovingDown_MoveDown[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (System_Elevator_MovingDown_MoveDown_pre))
  pPID. (sNext. (s. (System_Elevator_MovingDown_MoveDown_post)))
}

pred System_Elevator_Idle_DefaultToGround_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> System/Elevator/Idle } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pPID -> System/Elevator } in scopesUsed1}
}


pred System_Elevator_Idle_DefaultToGround_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> System/Elevator/Idle } } + { pPID -> System/Elevator/Idle } }
  (pPID -> System/Elevator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Elevator_Idle_DefaultToGround_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPID -> System/Elevator/Idle } in sNext. (conf1)
}

pred System_Elevator_Idle_DefaultToGround[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (System_Elevator_Idle_DefaultToGround_pre))
  pPID. (sNext. (s. (System_Elevator_Idle_DefaultToGround_post)))
}

pred System_Elevator_MovingUp_MoveUp_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> System/Elevator/MovingUp } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pPID -> System/Elevator } in scopesUsed1}
}


pred System_Elevator_MovingUp_MoveUp_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> System/Elevator/MovingUp } } + { pPID -> System/Elevator/MovingUp } }
  (pPID -> System/Elevator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Elevator_MovingUp_MoveUp_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPID -> System/Elevator/MovingUp } in sNext. (conf1)
}

pred System_Elevator_MovingUp_MoveUp[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (System_Elevator_MovingUp_MoveUp_pre))
  pPID. (sNext. (s. (System_Elevator_MovingUp_MoveUp_post)))
}

pred System_Elevator_MovingUp_Idle_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> System/Elevator/MovingUp } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pPID -> System/Elevator } in scopesUsed1}
}


pred System_Elevator_MovingUp_Idle_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> System/Elevator/MovingUp } - { pPID -> System/Elevator/MovingDown } - { pPID -> System/Elevator/Idle } } + { pPID -> System/Elevator/Idle } }
  (pPID -> System/Elevator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Elevator_MovingUp_Idle_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPID -> System/Elevator/MovingUp } in sNext. (conf1)
}

pred System_Elevator_MovingUp_Idle[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (System_Elevator_MovingUp_Idle_pre))
  pPID. (sNext. (s. (System_Elevator_MovingUp_Idle_post)))
}

pred System_Elevator_MovingDown_ElevatorInCalled_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> System/Elevator/MovingDown } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pPID -> System/Elevator } in scopesUsed1}
}


pred System_Elevator_MovingDown_ElevatorInCalled_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> System/Elevator/MovingDown } } + { pPID -> System/Elevator/MovingDown } }
  (pPID -> System/Elevator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Elevator_MovingDown_ElevatorInCalled_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPID -> System/Elevator/MovingDown } in sNext. (conf1)
}

pred System_Elevator_MovingDown_ElevatorInCalled[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (System_Elevator_MovingDown_ElevatorInCalled_pre))
  pPID. (sNext. (s. (System_Elevator_MovingDown_ElevatorInCalled_post)))
}

pred System_Elevator_MovingDown_ChangeDirToUp_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> System/Elevator/MovingDown } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pPID -> System/Elevator } in scopesUsed1}
}


pred System_Elevator_MovingDown_ChangeDirToUp_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> System/Elevator/MovingUp } - { pPID -> System/Elevator/MovingDown } - { pPID -> System/Elevator/Idle } } + { pPID -> System/Elevator/MovingUp } }
  (pPID -> System/Elevator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Elevator_MovingDown_ChangeDirToUp_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPID -> System/Elevator/MovingDown } in sNext. (conf1)
}

pred System_Elevator_MovingDown_ChangeDirToUp[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (System_Elevator_MovingDown_ChangeDirToUp_pre))
  pPID. (sNext. (s. (System_Elevator_MovingDown_ChangeDirToUp_post)))
}

pred System_Controller_SendingUpRequest_pre[s : one Snapshot] {
  System/Controller/Sending in s. (conf0)
  ! {System in scopesUsed0}
  ! {System/Controller in scopesUsed0}
}


pred System_Controller_SendingUpRequest_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - System/Controller/Sending } + System/Controller/Sending }
  sNext. (conf1) = s. (conf1)
  (none. (System/Controller. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Controller_SendingUpRequest_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  System/Controller/Sending in sNext. (conf0)
}

pred System_Controller_SendingUpRequest[s : one Snapshot, sNext : one Snapshot] {
  s. (System_Controller_SendingUpRequest_pre)
  sNext. (s. (System_Controller_SendingUpRequest_post))
}

pred System_Elevator_MovingUp_ElevatorInCalled_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> System/Elevator/MovingUp } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pPID -> System/Elevator } in scopesUsed1}
}


pred System_Elevator_MovingUp_ElevatorInCalled_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> System/Elevator/MovingUp } } + { pPID -> System/Elevator/MovingUp } }
  (pPID -> System/Elevator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Elevator_MovingUp_ElevatorInCalled_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPID -> System/Elevator/MovingUp } in sNext. (conf1)
}

pred System_Elevator_MovingUp_ElevatorInCalled[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (System_Elevator_MovingUp_ElevatorInCalled_pre))
  pPID. (sNext. (s. (System_Elevator_MovingUp_ElevatorInCalled_post)))
}

pred testIfNextStable[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Controller_SendingDownRequest_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Elevator_MovingUp_ChangeDirToDown_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Elevator_Idle_Move_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Elevator_MovingDown_Idle_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Elevator_MovingDown_MoveDown_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Elevator_Idle_DefaultToGround_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Elevator_MovingUp_MoveUp_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Elevator_MovingUp_Idle_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Elevator_MovingDown_ElevatorInCalled_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Elevator_MovingDown_ChangeDirToUp_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Controller_SendingUpRequest_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Elevator_MovingUp_ElevatorInCalled_enabledAfterStep))))}
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pPID: one PID | { sNext. (s. (System_Controller_SendingDownRequest)) or
    pPID. (sNext. (s. (System_Elevator_MovingUp_ChangeDirToDown))) or
    pPID. (sNext. (s. (System_Elevator_Idle_Move))) or
    pPID. (sNext. (s. (System_Elevator_MovingDown_Idle))) or
    pPID. (sNext. (s. (System_Elevator_MovingDown_MoveDown))) or
    pPID. (sNext. (s. (System_Elevator_Idle_DefaultToGround))) or
    pPID. (sNext. (s. (System_Elevator_MovingUp_MoveUp))) or
    pPID. (sNext. (s. (System_Elevator_MovingUp_Idle))) or
    pPID. (sNext. (s. (System_Elevator_MovingDown_ElevatorInCalled))) or
    pPID. (sNext. (s. (System_Elevator_MovingDown_ChangeDirToUp))) or
    sNext. (s. (System_Controller_SendingUpRequest)) or
    pPID. (sNext. (s. (System_Elevator_MovingUp_ElevatorInCalled))) })
}

