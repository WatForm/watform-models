open util/ordering[Temp] as temp

open util/boolean
open util/ordering[Snapshot] as Snapshot

sig Temp{}
abstract sig ValvePos {}
one sig OPEN, HALF, CLOSED extends ValvePos {}

assert FurnaceActivates {
	(no s0: Snapshot | (HeatingSystem_ERROR in s0.conf0)) => 
	(some s1: Snapshot | HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3 in s1.taken0)
}

assert heaterOnIfNotDesiredTemp{
    (no s0: Snapshot | (HeatingSystem_ERROR in s0.conf0)) =>
    (some s0: one Snapshot,p0: one Identifier | lt[p0.(s0.HeatingSystem_Functioning_Room_actualTemp), p0.(s0.HeatingSystem_Functioning_Room_actualTemp)] => 
	(some s1: nexts[s0] | HeatingSystem_Functioning_Controller_On_Heater_Active in s1.conf0))
}

check heaterOnIfNotDesiredTemp for 25 Snapshot, exactly 2 Identifier, exactly 4 Temp
check heaterOnIfNotDesiredTemp for 30 Snapshot, exactly 3 Identifier, exactly 4 Temp
check FurnaceActivates for 25 Snapshot, exactly 2 Identifier, exactly 4 Temp
check FurnaceActivates for 30 Snapshot, exactly 3 Identifier, exactly 4 Temp

abstract sig StateLabel {}
sig HeatingSystem extends StateLabel {} 
abstract sig HeatingSystem_Functioning extends HeatingSystem {} 
one sig HeatingSystem_Functioning_Furnace extends HeatingSystem_Functioning {} 
abstract sig HeatingSystem_Functioning_Furnace_Furnace_Normal extends HeatingSystem_Functioning_Furnace {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off extends HeatingSystem_Functioning_Furnace_Furnace_Normal {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating extends HeatingSystem_Functioning_Furnace_Furnace_Normal {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running extends HeatingSystem_Functioning_Furnace_Furnace_Normal {} 
one sig HeatingSystem_Functioning_Controller extends HeatingSystem_Functioning {} 
one sig HeatingSystem_Functioning_Controller_Off extends HeatingSystem_Functioning_Controller {} 
abstract sig HeatingSystem_Functioning_Controller_On extends HeatingSystem_Functioning_Controller {} 
one sig HeatingSystem_Functioning_Controller_On_Idle extends HeatingSystem_Functioning_Controller_On {} 
one sig HeatingSystem_Functioning_Controller_On_Heater_Active extends HeatingSystem_Functioning_Controller_On {} 
one sig HeatingSystem_Functioning_Room extends HeatingSystem_Functioning {} 
abstract sig HeatingSystem_Functioning_Room_No_Heat_Request extends HeatingSystem_Functioning_Room {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat extends HeatingSystem_Functioning_Room_No_Heat_Request {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat extends HeatingSystem_Functioning_Room_No_Heat_Request {} 
abstract sig HeatingSystem_Functioning_Room_Heat_Requested extends HeatingSystem_Functioning_Room {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating extends HeatingSystem_Functioning_Room_Heat_Requested {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool extends HeatingSystem_Functioning_Room_Heat_Requested {} 
one sig HeatingSystem_ERROR extends HeatingSystem {} 

abstract sig Identifiers {}
sig Identifier extends Identifiers {} 

abstract sig AllEvents {}
abstract sig AllInternalEvent extends AllEvents {} 
one sig HeatingSystem_furnaceReset extends AllInternalEvent {} 
one sig HeatingSystem_furnaceNotRunning extends AllInternalEvent {} 
one sig HeatingSystem_deactivate extends AllInternalEvent {} 
one sig HeatingSystem_furnaceRunning extends AllInternalEvent {} 
one sig HeatingSystem_activate extends AllInternalEvent {} 
abstract sig AllEnvironmentalEvents extends AllEvents {} 
one sig HeatingSystem_Functioning_Room_waitedForWarmth extends AllEnvironmentalEvents {} 
one sig HeatingSystem_Functioning_Room_waitedForCool extends AllEnvironmentalEvents {} 
one sig HeatingSystem_TurnOn extends AllEnvironmentalEvents {} 
one sig HeatingSystem_furnaceFault extends AllEnvironmentalEvents {} 
one sig HeatingSystem_heatSwitchOn extends AllEnvironmentalEvents {} 
one sig HeatingSystem_Reset extends AllEnvironmentalEvents {} 
one sig HeatingSystem_userReset extends AllEnvironmentalEvents {} 

sig Snapshot {
  scopesUsed0 : set StateLabel,
  conf0 : set StateLabel,
  events0 : set AllEvents,
  scopesUsed1 : Identifiers -> Identifiers -> StateLabel,
  conf1 : Identifiers -> Identifiers -> StateLabel,
  events1 : Identifiers -> Identifiers -> AllEvents,
  stable : one boolean/Bool
}

pred HeatingSystem_Functioning_Controller_Off_T8_pre[s : one Snapshot] {
  HeatingSystem/Functioning/Controller/Off in s. (conf0)
  ! {HeatingSystem in scopesUsed0}
  ! {HeatingSystem/Functioning/Controller in scopesUsed0}
  (s. (stable) = boolean/True => 
    HeatingSystem/heatSwitchOn in { s. (events0) & AllEnvironmentalEvents }
 else {
    HeatingSystem/heatSwitchOn in s. (events0) }
)
}


pred HeatingSystem_Functioning_Controller_Off_T8_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - HeatingSystem/Functioning/Controller/Off - HeatingSystem/Functioning/Controller/On/Idle - HeatingSystem/Functioning/Controller/On/Heater_Active } + HeatingSystem/Functioning/Controller/On/Idle }
  sNext. (conf1) = s. (conf1)
  (none. (none. (HeatingSystem/furnaceReset. (HeatingSystem/Functioning/Controller. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = HeatingSystem/furnaceReset and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { HeatingSystem/furnaceReset + { AllInternalEvent & s. (events0) } } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = HeatingSystem/furnaceReset and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        sNext. (events0) = { s. (events0) + HeatingSystem/furnaceReset } }
    ) }
)
}

pred HeatingSystem_Functioning_Controller_Off_T8_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  HeatingSystem/Functioning/Controller/Off in sNext. (conf0)
}

pred HeatingSystem_Functioning_Controller_Off_T8[s : one Snapshot, sNext : one Snapshot] {
  s. (HeatingSystem_Functioning_Controller_Off_T8_pre)
  sNext. (s. (HeatingSystem_Functioning_Controller_Off_T8_post))
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10_pre[s : one Snapshot] {
  HeatingSystem/Functioning/Controller/On/Heater_Active in s. (conf0)
  ! {HeatingSystem in scopesUsed0}
  ! {HeatingSystem/Functioning/Controller in scopesUsed0}
}


pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - HeatingSystem/Functioning/Controller/On/Idle - HeatingSystem/Functioning/Controller/On/Heater_Active } + HeatingSystem/Functioning/Controller/On/Idle }
  sNext. (conf1) = s. (conf1)
  (none. (none. (HeatingSystem/deactivate. (HeatingSystem/Functioning/Controller. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = HeatingSystem/deactivate and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { HeatingSystem/deactivate + { AllInternalEvent & s. (events0) } } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = HeatingSystem/deactivate and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        sNext. (events0) = { s. (events0) + HeatingSystem/deactivate } }
    ) }
)
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  HeatingSystem/Functioning/Controller/On/Heater_Active in sNext. (conf0)
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10[s : one Snapshot, sNext : one Snapshot] {
  s. (HeatingSystem_Functioning_Controller_On_Heater_Active_T10_pre)
  sNext. (s. (HeatingSystem_Functioning_Controller_On_Heater_Active_T10_post))
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11_pre[s : one Snapshot] {
  HeatingSystem/Functioning/Controller/On/Heater_Active in s. (conf0)
  ! {HeatingSystem in scopesUsed0}
  (s. (stable) = boolean/True => 
    HeatingSystem/furnaceFault in { s. (events0) & AllEnvironmentalEvents }
 else {
    HeatingSystem/furnaceFault in s. (events0) }
)
}


pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running - HeatingSystem/Functioning/Controller/Off - HeatingSystem/Functioning/Controller/On/Idle - HeatingSystem/Functioning/Controller/On/Heater_Active - HeatingSystem/ERROR } + HeatingSystem/ERROR }
  sNext. (conf1) = { s. (conf1) - { Identifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } - { Identifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } - { Identifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } - { Identifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } }
  (none. (none. (none. (HeatingSystem. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  HeatingSystem/Functioning/Controller/On/Heater_Active in sNext. (conf0)
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11[s : one Snapshot, sNext : one Snapshot] {
  s. (HeatingSystem_Functioning_Controller_On_Heater_Active_T11_pre)
  sNext. (s. (HeatingSystem_Functioning_Controller_On_Heater_Active_T11_post))
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_pre[s : one Snapshot] {
  HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running in s. (conf0)
  ! {HeatingSystem in scopesUsed0}
  ! {HeatingSystem/Functioning/Furnace in scopesUsed0}
  (s. (stable) = boolean/True => 
    HeatingSystem/deactivate in { s. (events0) & AllEnvironmentalEvents }
 else {
    HeatingSystem/deactivate in s. (events0) }
)
}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running } + HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off }
  sNext. (conf1) = s. (conf1)
  (none. (none. (none. (HeatingSystem/Functioning/Furnace. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running in sNext. (conf0)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4[s : one Snapshot, sNext : one Snapshot] {
  s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_pre)
  sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_post))
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_pre[s : one Snapshot] {
  HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running in s. (conf0)
  ! {HeatingSystem in scopesUsed0}
  (s. (stable) = boolean/True => 
    HeatingSystem/furnaceFault in { s. (events0) & AllEnvironmentalEvents }
 else {
    HeatingSystem/furnaceFault in s. (events0) }
)
}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running - HeatingSystem/Functioning/Controller/Off - HeatingSystem/Functioning/Controller/On/Idle - HeatingSystem/Functioning/Controller/On/Heater_Active - HeatingSystem/ERROR } + HeatingSystem/ERROR }
  sNext. (conf1) = { s. (conf1) - { Identifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } - { Identifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } - { Identifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } - { Identifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } }
  (none. (none. (none. (HeatingSystem. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running in sNext. (conf0)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5[s : one Snapshot, sNext : one Snapshot] {
  s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_pre)
  sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_post))
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_pre[s : one Snapshot] {
  HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating in s. (conf0)
  ! {HeatingSystem in scopesUsed0}
  ! {HeatingSystem/Functioning/Furnace in scopesUsed0}
}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running } + HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running }
  sNext. (conf1) = s. (conf1)
  (none. (none. (HeatingSystem/furnaceRunning. (HeatingSystem/Functioning/Furnace. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = HeatingSystem/furnaceRunning and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { HeatingSystem/furnaceRunning + { AllInternalEvent & s. (events0) } } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = HeatingSystem/furnaceRunning and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        sNext. (events0) = { s. (events0) + HeatingSystem/furnaceRunning } }
    ) }
)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating in sNext. (conf0)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3[s : one Snapshot, sNext : one Snapshot] {
  s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_pre)
  sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_post))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } in s. (conf1)
  ! {HeatingSystem in scopesUsed0}
  ! {{ pIdentifier -> HeatingSystem/Functioning/Room } in scopesUsed1}
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } } + { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } }
  (none. (pIdentifier -> HeatingSystem/Functioning/Room. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } in sNext. (conf1)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_pre))
  pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_post)))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } in s. (conf1)
  ! {HeatingSystem in scopesUsed0}
  ! {{ pIdentifier -> HeatingSystem/Functioning/Room } in scopesUsed1}
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } - { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } } + { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } }
  (none. (pIdentifier -> HeatingSystem/Functioning/Room. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } in sNext. (conf1)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_pre))
  pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_post)))
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } in s. (conf1)
  ! {HeatingSystem in scopesUsed0}
  ! {{ pIdentifier -> HeatingSystem/Functioning/Room } in scopesUsed1}
  (s. (stable) = boolean/True => 
    { pIdentifier -> HeatingSystem/Functioning/Room/waitedForCool } in { s. (events1) & AllEnvironmentalEvents }
 else {
    { pIdentifier -> HeatingSystem/Functioning/Room/waitedForCool } in s. (events1) }
)
}


pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } } + { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } }
  (none. (pIdentifier -> HeatingSystem/Functioning/Room. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } in sNext. (conf1)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_pre))
  pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_post)))
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_pre[s : one Snapshot] {
  HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off in s. (conf0)
  ! {HeatingSystem in scopesUsed0}
  ! {HeatingSystem/Functioning/Furnace in scopesUsed0}
  (s. (stable) = boolean/True => 
    HeatingSystem/activate in { s. (events0) & AllEnvironmentalEvents }
 else {
    HeatingSystem/activate in s. (events0) }
)
}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running } + HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating }
  sNext. (conf1) = s. (conf1)
  (none. (none. (none. (HeatingSystem/Functioning/Furnace. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off in sNext. (conf0)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1[s : one Snapshot, sNext : one Snapshot] {
  s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_pre)
  sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_post))
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } in s. (conf1)
  ! {HeatingSystem in scopesUsed0}
  ! {{ pIdentifier -> HeatingSystem/Functioning/Room } in scopesUsed1}
}


pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } - { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } } + { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } }
  (none. (pIdentifier -> HeatingSystem/Functioning/Room. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } in sNext. (conf1)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_pre))
  pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_post)))
}

pred HeatingSystem_ERROR_T19_pre[s : one Snapshot] {
  HeatingSystem/ERROR in s. (conf0)
  ! {HeatingSystem in scopesUsed0}
  (s. (stable) = boolean/True => 
    HeatingSystem/heatSwitchOn in { s. (events0) & AllEnvironmentalEvents }
 else {
    HeatingSystem/heatSwitchOn in s. (events0) }
)
}


pred HeatingSystem_ERROR_T19_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running - HeatingSystem/Functioning/Controller/Off - HeatingSystem/Functioning/Controller/On/Idle - HeatingSystem/Functioning/Controller/On/Heater_Active - HeatingSystem/ERROR } + HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off + HeatingSystem/Functioning/Controller/Off }
  sNext. (conf1) = { { s. (conf1) - { Identifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } - { Identifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } - { Identifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } - { Identifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } } + { Identifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } }
  (none. (none. (none. (HeatingSystem. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_ERROR_T19_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  HeatingSystem/ERROR in sNext. (conf0)
}

pred HeatingSystem_ERROR_T19[s : one Snapshot, sNext : one Snapshot] {
  s. (HeatingSystem_ERROR_T19_pre)
  sNext. (s. (HeatingSystem_ERROR_T19_post))
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } in s. (conf1)
  ! {HeatingSystem in scopesUsed0}
  ! {{ pIdentifier -> HeatingSystem/Functioning/Room } in scopesUsed1}
  (s. (stable) = boolean/True => 
    { pIdentifier -> HeatingSystem/Functioning/Room/waitedForCool } in { s. (events1) & AllEnvironmentalEvents }
 else {
    { pIdentifier -> HeatingSystem/Functioning/Room/waitedForCool } in s. (events1) }
)
}


pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } - { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } - { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } - { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } } + { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } }
  (none. (pIdentifier -> HeatingSystem/Functioning/Room. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } in sNext. (conf1)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_pre))
  pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_post)))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } in s. (conf1)
  ! {HeatingSystem in scopesUsed0}
  ! {{ pIdentifier -> HeatingSystem/Functioning/Room } in scopesUsed1}
  (s. (stable) = boolean/True => 
    { pIdentifier -> HeatingSystem/Functioning/Room/waitedForWarmth } in { s. (events1) & AllEnvironmentalEvents }
 else {
    { pIdentifier -> HeatingSystem/Functioning/Room/waitedForWarmth } in s. (events1) }
)
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } } + { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } }
  (none. (pIdentifier -> HeatingSystem/Functioning/Room. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } in sNext. (conf1)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_pre))
  pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_post)))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } in s. (conf1)
  ! {HeatingSystem in scopesUsed0}
  ! {{ pIdentifier -> HeatingSystem/Functioning/Room } in scopesUsed1}
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } - { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } - { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } - { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } } + { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } }
  (none. (pIdentifier -> HeatingSystem/Functioning/Room. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } in sNext. (conf1)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_pre))
  pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_post)))
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_pre[s : one Snapshot] {
  HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating in s. (conf0)
  ! {HeatingSystem in scopesUsed0}
  ! {HeatingSystem/Functioning/Furnace in scopesUsed0}
  (s. (stable) = boolean/True => 
    HeatingSystem/deactivate in { s. (events0) & AllEnvironmentalEvents }
 else {
    HeatingSystem/deactivate in s. (events0) }
)
}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating - HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Running } + HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Off }
  sNext. (conf1) = s. (conf1)
  (none. (none. (none. (HeatingSystem/Functioning/Furnace. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  HeatingSystem/Functioning/Furnace/Furnace_Normal/Furnace_Activating in sNext. (conf0)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2[s : one Snapshot, sNext : one Snapshot] {
  s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_pre)
  sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_post))
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } in s. (conf1)
  ! {HeatingSystem in scopesUsed0}
  ! {{ pIdentifier -> HeatingSystem/Functioning/Room } in scopesUsed1}
}


pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } - { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } } + { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Wait_For_Cool } }
  (none. (pIdentifier -> HeatingSystem/Functioning/Room. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } in sNext. (conf1)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_pre))
  pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_post)))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } in s. (conf1)
  ! {HeatingSystem in scopesUsed0}
  ! {{ pIdentifier -> HeatingSystem/Functioning/Room } in scopesUsed1}
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } - { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } } + { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Idle_No_Heat } }
  (none. (pIdentifier -> HeatingSystem/Functioning/Room. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pIdentifier -> HeatingSystem/Functioning/Room/No_Heat_Request/Wait_For_Heat } in sNext. (conf1)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_pre))
  pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_post)))
}

pred HeatingSystem_Functioning_Controller_On_Idle_T9_pre[s : one Snapshot] {
  HeatingSystem/Functioning/Controller/On/Idle in s. (conf0)
  ! {HeatingSystem in scopesUsed0}
  ! {HeatingSystem/Functioning/Controller in scopesUsed0}
}


pred HeatingSystem_Functioning_Controller_On_Idle_T9_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - HeatingSystem/Functioning/Controller/On/Idle - HeatingSystem/Functioning/Controller/On/Heater_Active } + HeatingSystem/Functioning/Controller/On/Heater_Active }
  sNext. (conf1) = s. (conf1)
  (none. (none. (HeatingSystem/activate. (HeatingSystem/Functioning/Controller. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = HeatingSystem/activate and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { HeatingSystem/activate + { AllInternalEvent & s. (events0) } } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = HeatingSystem/activate and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        sNext. (events0) = { s. (events0) + HeatingSystem/activate } }
    ) }
)
}

pred HeatingSystem_Functioning_Controller_On_Idle_T9_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  HeatingSystem/Functioning/Controller/On/Idle in sNext. (conf0)
}

pred HeatingSystem_Functioning_Controller_On_Idle_T9[s : one Snapshot, sNext : one Snapshot] {
  s. (HeatingSystem_Functioning_Controller_On_Idle_T9_pre)
  sNext. (s. (HeatingSystem_Functioning_Controller_On_Idle_T9_post))
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } in s. (conf1)
  ! {HeatingSystem in scopesUsed0}
  ! {{ pIdentifier -> HeatingSystem/Functioning/Room } in scopesUsed1}
}


pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } } + { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } }
  (none. (pIdentifier -> HeatingSystem/Functioning/Room. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        boolean/True }
    ) }
)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pIdentifier -> HeatingSystem/Functioning/Room/Heat_Requested/Idle_Heating } in sNext. (conf1)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_pre))
  pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_post)))
}

pred testIfNextStable[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Controller_Off_T8_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Controller_On_Heater_Active_T10_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Controller_On_Heater_Active_T11_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_ERROR_T19_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Controller_On_Idle_T9_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_enabledAfterStep))))))}
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pIdentifier: one Identifier | { sNext. (s. (HeatingSystem_Functioning_Controller_Off_T8)) or
    sNext. (s. (HeatingSystem_Functioning_Controller_On_Heater_Active_T10)) or
    sNext. (s. (HeatingSystem_Functioning_Controller_On_Heater_Active_T11)) or
    sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4)) or
    sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5)) or
    sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3)) or
    pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom))) or
    pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12))) or
    pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17))) or
    sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1)) or
    pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16))) or
    sNext. (s. (HeatingSystem_ERROR_T19)) or
    pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18))) or
    pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14))) or
    pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15))) or
    sNext. (s. (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2)) or
    pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15))) or
    pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13))) or
    sNext. (s. (HeatingSystem_Functioning_Controller_On_Idle_T9)) or
    pIdentifier. (sNext. (s. (HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom))) })
}

