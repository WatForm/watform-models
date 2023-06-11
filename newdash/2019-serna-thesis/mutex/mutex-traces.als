/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-11 19:17:38
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/*******************************************************************************
 * Title: Mutex.dsh
 * Authors: Jose Serna - jserna@uwaterloo.ca
 * Created: 2018-06-20
 * Last modified: 
 * 2023-06-07 Nancy Day changes for newdash
 *
 * Notes: Semaphore basded mutual exclusion system
 *
 ******************************************************************************/

open util/boolean

abstract sig DshStates {}
abstract sig Mutex extends DshStates {} 
abstract sig Mutex_Process1 extends Mutex {} 
one sig Mutex_Process1_NonCritical extends Mutex_Process1 {} 
one sig Mutex_Process1_Critical extends Mutex_Process1 {} 
one sig Mutex_Process1_Wait extends Mutex_Process1 {} 
abstract sig Mutex_Process2 extends Mutex {} 
one sig Mutex_Process2_NonCritical extends Mutex_Process2 {} 
one sig Mutex_Process2_Critical extends Mutex_Process2 {} 
one sig Mutex_Process2_Wait extends Mutex_Process2 {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_stable: one boolean/Bool,
  Mutex_semaphore_free: one Bool
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) =
  (Mutex_Process1_NonCritical + Mutex_Process2_NonCritical) and
  (s.Mutex_semaphore_free) = True
  (s.dsh_stable).boolean/isTrue
}

pred Mutex_Process1_enter_critical_section_pre [
	s: one DshSnapshot] {
  some (Mutex_Process1_Wait & (s.dsh_conf0))
  (s.Mutex_semaphore_free) = True
  !(Mutex in (s.dsh_sc_used0))
  !(Mutex_Process1 in (s.dsh_sc_used0))
}


pred Mutex_Process1_enter_critical_section_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - Mutex_Process1_NonCritical) -
       Mutex_Process1_Critical) - Mutex_Process1_Wait) +
     Mutex_Process1_Critical)
  (sn.Mutex_semaphore_free) = False
  (Mutex_Process1.(sn.(s._testIfNextStable)))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + Mutex_Process1))
       )

}

pred Mutex_Process1_enter_critical_section_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates] {
  some (Mutex_Process1_Wait & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(Mutex in dsh_scp0) and
    !(Mutex_Process1 in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Mutex_Process1_enter_critical_section [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Mutex_Process1_enter_critical_section_pre
  sn.(s.Mutex_Process1_enter_critical_section_post)
}

pred Mutex_Process1_give_up_pre [
	s: one DshSnapshot] {
  some (Mutex_Process1_Wait & (s.dsh_conf0))
  !(Mutex in (s.dsh_sc_used0))
  !(Mutex_Process1 in (s.dsh_sc_used0))
}


pred Mutex_Process1_give_up_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - Mutex_Process1_NonCritical) -
       Mutex_Process1_Critical) - Mutex_Process1_Wait) +
     Mutex_Process1_NonCritical)
  (Mutex_Process1.(sn.(s._testIfNextStable)))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + Mutex_Process1))
       )

}

pred Mutex_Process1_give_up_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates] {
  some (Mutex_Process1_Wait & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(Mutex in dsh_scp0) and
    !(Mutex_Process1 in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Mutex_Process1_give_up [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Mutex_Process1_give_up_pre
  sn.(s.Mutex_Process1_give_up_post)
}

pred Mutex_Process2_wait_pre [
	s: one DshSnapshot] {
  some (Mutex_Process2_NonCritical & (s.dsh_conf0))
  !(Mutex in (s.dsh_sc_used0))
  !(Mutex_Process2 in (s.dsh_sc_used0))
}


pred Mutex_Process2_wait_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - Mutex_Process2_NonCritical) -
       Mutex_Process2_Critical) - Mutex_Process2_Wait) +
     Mutex_Process2_Wait)
  (Mutex_Process2.(sn.(s._testIfNextStable)))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + Mutex_Process2))
       )

}

pred Mutex_Process2_wait_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates] {
  some (Mutex_Process2_NonCritical & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(Mutex in dsh_scp0) and
    !(Mutex_Process2 in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Mutex_Process2_wait [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Mutex_Process2_wait_pre
  sn.(s.Mutex_Process2_wait_post)
}

pred Mutex_Process2_enter_critical_section_pre [
	s: one DshSnapshot] {
  some (Mutex_Process2_Wait & (s.dsh_conf0))
  (s.Mutex_semaphore_free) = True
  !(Mutex in (s.dsh_sc_used0))
  !(Mutex_Process2 in (s.dsh_sc_used0))
}


pred Mutex_Process2_enter_critical_section_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - Mutex_Process2_NonCritical) -
       Mutex_Process2_Critical) - Mutex_Process2_Wait) +
     Mutex_Process2_Critical)
  (sn.Mutex_semaphore_free) = False
  (Mutex_Process2.(sn.(s._testIfNextStable)))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + Mutex_Process2))
       )

}

pred Mutex_Process2_enter_critical_section_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates] {
  some (Mutex_Process2_Wait & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(Mutex in dsh_scp0) and
    !(Mutex_Process2 in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Mutex_Process2_enter_critical_section [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Mutex_Process2_enter_critical_section_pre
  sn.(s.Mutex_Process2_enter_critical_section_post)
}

pred Mutex_Process2_exit_critical_section_pre [
	s: one DshSnapshot] {
  some (Mutex_Process2_Critical & (s.dsh_conf0))
  (s.Mutex_semaphore_free) = False
  !(Mutex in (s.dsh_sc_used0))
  !(Mutex_Process2 in (s.dsh_sc_used0))
}


pred Mutex_Process2_exit_critical_section_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - Mutex_Process2_NonCritical) -
       Mutex_Process2_Critical) - Mutex_Process2_Wait) +
     Mutex_Process2_NonCritical)
  (sn.Mutex_semaphore_free) = True
  (Mutex_Process2.(sn.(s._testIfNextStable)))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + Mutex_Process2))
       )

}

pred Mutex_Process2_exit_critical_section_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates] {
  some (Mutex_Process2_Critical & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(Mutex in dsh_scp0) and
    !(Mutex_Process2 in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Mutex_Process2_exit_critical_section [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Mutex_Process2_exit_critical_section_pre
  sn.(s.Mutex_Process2_exit_critical_section_post)
}

pred Mutex_Process1_wait_pre [
	s: one DshSnapshot] {
  some (Mutex_Process1_NonCritical & (s.dsh_conf0))
  !(Mutex in (s.dsh_sc_used0))
  !(Mutex_Process1 in (s.dsh_sc_used0))
}


pred Mutex_Process1_wait_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - Mutex_Process1_NonCritical) -
       Mutex_Process1_Critical) - Mutex_Process1_Wait) +
     Mutex_Process1_Wait)
  (Mutex_Process1.(sn.(s._testIfNextStable)))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + Mutex_Process1))
       )

}

pred Mutex_Process1_wait_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates] {
  some (Mutex_Process1_NonCritical & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(Mutex in dsh_scp0) and
    !(Mutex_Process1 in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Mutex_Process1_wait [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Mutex_Process1_wait_pre
  sn.(s.Mutex_Process1_wait_post)
}

pred Mutex_Process1_exit_critical_section_pre [
	s: one DshSnapshot] {
  some (Mutex_Process1_Critical & (s.dsh_conf0))
  (s.Mutex_semaphore_free) = False
  !(Mutex in (s.dsh_sc_used0))
  !(Mutex_Process1 in (s.dsh_sc_used0))
}


pred Mutex_Process1_exit_critical_section_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - Mutex_Process1_NonCritical) -
       Mutex_Process1_Critical) - Mutex_Process1_Wait) +
     Mutex_Process1_NonCritical)
  (sn.Mutex_semaphore_free) = True
  (Mutex_Process1.(sn.(s._testIfNextStable)))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + Mutex_Process1))
       )

}

pred Mutex_Process1_exit_critical_section_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates] {
  some (Mutex_Process1_Critical & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(Mutex in dsh_scp0) and
    !(Mutex_Process1 in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Mutex_Process1_exit_critical_section [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Mutex_Process1_exit_critical_section_pre
  sn.(s.Mutex_Process1_exit_critical_section_post)
}

pred Mutex_Process2_give_up_pre [
	s: one DshSnapshot] {
  some (Mutex_Process2_Wait & (s.dsh_conf0))
  !(Mutex in (s.dsh_sc_used0))
  !(Mutex_Process2 in (s.dsh_sc_used0))
}


pred Mutex_Process2_give_up_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - Mutex_Process2_NonCritical) -
       Mutex_Process2_Critical) - Mutex_Process2_Wait) +
     Mutex_Process2_NonCritical)
  (Mutex_Process2.(sn.(s._testIfNextStable)))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + Mutex_Process2))
       )

}

pred Mutex_Process2_give_up_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates] {
  some (Mutex_Process2_Wait & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(Mutex in dsh_scp0) and
    !(Mutex_Process2 in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Mutex_Process2_give_up [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Mutex_Process2_give_up_pre
  sn.(s.Mutex_Process2_give_up_post)
}

pred _testIfNextStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates] {
  !(dsh_scp0.(sn.(s.Mutex_Process1_enter_critical_section_enabledAfterStep)))
  !(dsh_scp0.(sn.(s.Mutex_Process1_give_up_enabledAfterStep)))
  !(dsh_scp0.(sn.(s.Mutex_Process2_wait_enabledAfterStep)))
  !(dsh_scp0.(sn.(s.Mutex_Process2_enter_critical_section_enabledAfterStep)))
  !(dsh_scp0.(sn.(s.Mutex_Process2_exit_critical_section_enabledAfterStep)))
  !(dsh_scp0.(sn.(s.Mutex_Process1_wait_enabledAfterStep)))
  !(dsh_scp0.(sn.(s.Mutex_Process1_exit_critical_section_enabledAfterStep)))
  !(dsh_scp0.(sn.(s.Mutex_Process2_give_up_enabledAfterStep)))
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.Mutex_Process1_enter_critical_section) or
    sn.(s.Mutex_Process1_give_up) or
    sn.(s.Mutex_Process2_wait) or
    sn.(s.Mutex_Process2_enter_critical_section) or
    sn.(s.Mutex_Process2_exit_critical_section) or
    sn.(s.Mutex_Process1_wait) or
    sn.(s.Mutex_Process1_exit_critical_section) or
    sn.(s.Mutex_Process2_give_up) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}




