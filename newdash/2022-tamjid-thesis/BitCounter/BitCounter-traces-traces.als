open util/ordering[PID] as P0

// remember to have traces option set

assert allBitsInBit0 {
	some s: Snapshot | Counter_Done in s.events0 and
		(some p: PID | Counter_Bit_Bit1 !in p.(s.conf1))
}

check allBitsInBit0 for 12 Snapshot, exactly 3 PID
check allBitsInBit0 for 20 Snapshot, exactly 4 PID
abstract sig StateLabel {}
sig Counter extends StateLabel {} 
one sig Counter_Bit extends Counter {} 
one sig Counter_Bit_Bit1 extends Counter_Bit {} 
one sig Counter_Bit_Bit2 extends Counter_Bit {} 

abstract sig Identifiers {}
sig PID extends Identifiers {} 

abstract sig AllEvents {}
abstract sig AllInternalEvent extends AllEvents {} 
one sig Counter_Done extends AllInternalEvent {} 
one sig Counter_Bit_Tk1 extends AllInternalEvent {} 
abstract sig AllEnvironmentalEvents extends AllEvents {} 
one sig Counter_Tk0 extends AllEnvironmentalEvents {} 

sig Snapshot {
  scopesUsed0 : set StateLabel,
  conf0 : set StateLabel,
  events0 : set AllEvents,
  scopesUsed1 : Identifiers -> Identifiers -> StateLabel,
  conf1 : Identifiers -> Identifiers -> StateLabel,
  events1 : Identifiers -> Identifiers -> AllEvents,
  stable : one boolean/Bool
}

pred Counter_Bit_currentBitToBit1_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> Counter/Bit/Bit2 } in s. (conf1)
  ! {Counter in scopesUsed0}
  ! {{ pPID -> Counter/Bit } in scopesUsed1}
  (s. (stable) = boolean/True => 
    Counter/Tk0 in { s. (events0) & AllEnvironmentalEvents }
 else {
    Counter/Tk0 in s. (events0) }
)
}


pred Counter_Bit_currentBitToBit1_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> Counter/Bit/Bit1 } - { pPID -> Counter/Bit/Bit2 } } + { pPID -> Counter/Bit/Bit1 } }
  ((this).(P0/next) -> Tk1. (pPID -> Counter/Bit. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events1) & AllInternalEvent } = { (this).(P0/next) -> Tk1 }
     else {
        { sNext. (events0) & AllInternalEvent } = { AllInternalEvent & s. (events0) } and
        { sNext. (events1) & AllInternalEvent } = { { (this).(P0/next) -> Tk1 } + { AllInternalEvent & s. (events1) } } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = none and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = { (this).(P0/next) -> Tk1 } and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        sNext. (events1) = { s. (events1) + { (this).(P0/next) -> Tk1 } } }
    ) }
)
}

pred Counter_Bit_currentBitToBit1_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pPID -> Counter/Bit/Bit2 } in sNext. (conf1)
}

pred Counter_Bit_currentBitToBit1[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (Counter_Bit_currentBitToBit1_pre))
  pPID. (sNext. (s. (Counter_Bit_currentBitToBit1_post)))
}

pred Counter_Bit_lastBitDone_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> Counter/Bit/Bit2 } in s. (conf1)
  ! {Counter in scopesUsed0}
  ! {{ pPID -> Counter/Bit } in scopesUsed1}
  (s. (stable) = boolean/True => 
    { pPID -> Counter/Bit/Tk1 } in { s. (events1) & AllEnvironmentalEvents }
 else {
    { pPID -> Counter/Bit/Tk1 } in s. (events1) }
)
}


pred Counter_Bit_lastBitDone_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> Counter/Bit/Bit1 } - { pPID -> Counter/Bit/Bit2 } } + { pPID -> Counter/Bit/Bit1 } }
  (none. (pPID -> Counter/Bit. (Counter/Done. (none. (sNext. (s. (testIfNextStable)))))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = Counter/Done and
        { sNext. (events1) & AllInternalEvent } = none
     else {
        { sNext. (events0) & AllInternalEvent } = { Counter/Done + { AllInternalEvent & s. (events0) } } and
        { sNext. (events1) & AllInternalEvent } = { AllInternalEvent & s. (events1) } }
    )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True => 
        { sNext. (events0) & AllInternalEvent } = Counter/Done and
        { sNext. (events0) & AllEnvironmentalEvents } = { s. (events0) & AllEnvironmentalEvents } and
        { sNext. (events1) & AllInternalEvent } = none and
        { sNext. (events1) & AllEnvironmentalEvents } = { s. (events1) & AllEnvironmentalEvents }
     else {
        sNext. (events0) = { s. (events0) + Counter/Done } }
    ) }
)
}

pred Counter_Bit_lastBitDone_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pPID -> Counter/Bit/Bit2 } in sNext. (conf1)
}

pred Counter_Bit_lastBitDone[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (Counter_Bit_lastBitDone_pre))
  pPID. (sNext. (s. (Counter_Bit_lastBitDone_post)))
}

pred Counter_Bit_currentBitToBit2_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> Counter/Bit/Bit1 } in s. (conf1)
  ! {Counter in scopesUsed0}
  ! {{ pPID -> Counter/Bit } in scopesUsed1}
  (s. (stable) = boolean/True => 
    Counter/Tk0 in { s. (events0) & AllEnvironmentalEvents }
 else {
    Counter/Tk0 in s. (events0) }
)
}


pred Counter_Bit_currentBitToBit2_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> Counter/Bit/Bit1 } - { pPID -> Counter/Bit/Bit2 } } + { pPID -> Counter/Bit/Bit2 } }
  (none. (pPID -> Counter/Bit. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
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

pred Counter_Bit_currentBitToBit2_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pPID -> Counter/Bit/Bit1 } in sNext. (conf1)
}

pred Counter_Bit_currentBitToBit2[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (Counter_Bit_currentBitToBit2_pre))
  pPID. (sNext. (s. (Counter_Bit_currentBitToBit2_post)))
}

pred Counter_Bit_nextBitToBit1_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> Counter/Bit/Bit2 } in s. (conf1)
  ! {Counter in scopesUsed0}
  ! {{ pPID -> Counter/Bit } in scopesUsed1}
  (s. (stable) = boolean/True => 
    { pPID -> Counter/Bit/Tk1 } in { s. (events1) & AllEnvironmentalEvents }
 else {
    { pPID -> Counter/Bit/Tk1 } in s. (events1) }
)
}


pred Counter_Bit_nextBitToBit1_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> Counter/Bit/Bit1 } - { pPID -> Counter/Bit/Bit2 } } + { pPID -> Counter/Bit/Bit1 } }
  (none. (pPID -> Counter/Bit. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
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

pred Counter_Bit_nextBitToBit1_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pPID -> Counter/Bit/Bit2 } in sNext. (conf1)
}

pred Counter_Bit_nextBitToBit1[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (Counter_Bit_nextBitToBit1_pre))
  pPID. (sNext. (s. (Counter_Bit_nextBitToBit1_post)))
}

pred Counter_Bit_nextBitToBit2_pre[s : one Snapshot, pPID : one PID] {
  { pPID -> Counter/Bit/Bit1 } in s. (conf1)
  ! {Counter in scopesUsed0}
  ! {{ pPID -> Counter/Bit } in scopesUsed1}
  (s. (stable) = boolean/True => 
    { pPID -> Counter/Bit/Tk1 } in { s. (events1) & AllEnvironmentalEvents }
 else {
    { pPID -> Counter/Bit/Tk1 } in s. (events1) }
)
}


pred Counter_Bit_nextBitToBit2_post[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPID -> Counter/Bit/Bit1 } - { pPID -> Counter/Bit/Bit2 } } + { pPID -> Counter/Bit/Bit2 } }
  (none. (pPID -> Counter/Bit. (none. (none. (sNext. (s. (testIfNextStable)))))) => 
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

pred Counter_Bit_nextBitToBit2_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  { pPID -> Counter/Bit/Bit1 } in sNext. (conf1)
}

pred Counter_Bit_nextBitToBit2[s : one Snapshot, sNext : one Snapshot, pPID : one PID] {
  pPID. (s. (Counter_Bit_nextBitToBit2_pre))
  pPID. (sNext. (s. (Counter_Bit_nextBitToBit2_post)))
}

pred testIfNextStable[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, events0 : one AllEvents, scopesUsed1 : one StateLabel, events1 : one AllEvents] {
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (Counter_Bit_currentBitToBit1_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (Counter_Bit_lastBitDone_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (Counter_Bit_currentBitToBit2_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (Counter_Bit_nextBitToBit1_enabledAfterStep))))))}
  ! {events1. (scopesUsed1. (events0. (scopesUsed0. (sNext. (s. (Counter_Bit_nextBitToBit2_enabledAfterStep))))))}
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pPID: one PID | { pPID. (sNext. (s. (Counter_Bit_currentBitToBit1))) or
    pPID. (sNext. (s. (Counter_Bit_lastBitDone))) or
    pPID. (sNext. (s. (Counter_Bit_currentBitToBit2))) or
    pPID. (sNext. (s. (Counter_Bit_nextBitToBit1))) or
    pPID. (sNext. (s. (Counter_Bit_nextBitToBit2))) })
}

