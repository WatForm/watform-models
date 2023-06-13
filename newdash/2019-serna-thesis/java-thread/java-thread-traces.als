/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-13 15:57:20
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/*******************************************************************************
 * Title: JavaThread.dsh
 * Authors: Jose Serna - jserna@uwaterloo.ca
 * Created: 2019-06-10
 * Last modified: 
 * 2023-06-07 Nancy Day updates for new dash and no syntactic sugar
 *
 * Notes: Dash model of the thread states and lifecycle for the Thread class in 
 *   Java 6.
 *   The model uses transition comprehension and templates
 *   Source: https://www.uml-diagrams.org/examples/java-6-thread-state-machine-diagram-example.html
 *
 ******************************************************************************/

abstract sig DshStates {}
abstract sig ThreadStates extends DshStates {} 
one sig ThreadStates_New extends ThreadStates {} 
abstract sig ThreadStates_Runnable extends ThreadStates {} 
one sig ThreadStates_Runnable_Ready extends ThreadStates_Runnable {} 
one sig ThreadStates_Runnable_Running extends ThreadStates_Runnable {} 
one sig ThreadStates_Terminated extends ThreadStates {} 
one sig ThreadStates_TimedWaiting extends ThreadStates {} 
one sig ThreadStates_Waiting extends ThreadStates {} 
one sig ThreadStates_Blocked extends ThreadStates {} 

abstract sig DshEvents {}
abstract sig DshIntEvents extends DshEvents {} 
one sig ThreadStates_ThreadStart extends DshIntEvents {} 
one sig ThreadStates_ThreadYield extends DshIntEvents {} 
one sig ThreadStates_ThreadTerminated extends DshIntEvents {} 
one sig ThreadStates_ThreadJoin extends DshIntEvents {} 
one sig ThreadStates_ThreadJoinTimeout extends DshIntEvents {} 
one sig ThreadStates_ThreadSleepTime extends DshIntEvents {} 
one sig ThreadStates_ThreadSleepTimeElapsed extends DshIntEvents {} 
one sig ThreadStates_ObjectWaitTimeOut extends DshIntEvents {} 
one sig ThreadStates_ObjectWait extends DshIntEvents {} 
one sig ThreadStates_ObjectNotifyAll extends DshIntEvents {} 
one sig ThreadStates_ObjectNotify extends DshIntEvents {} 
one sig ThreadStates_LockSupportParkUntil extends DshIntEvents {} 
one sig ThreadStates_LockSupportParkNanos extends DshIntEvents {} 
one sig ThreadStates_LockSupportPark extends DshIntEvents {} 
one sig ThreadStates_SchedulerSelected extends DshIntEvents {} 
one sig ThreadStates_SchedulerSuspended extends DshIntEvents {} 
one sig ThreadStates_WaitForLockToEnterSynchro extends DshIntEvents {} 
one sig ThreadStates_WaitForLockToReEnterSynchro extends DshIntEvents {} 
one sig ThreadStates_MonitorLockAcquired extends DshIntEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_events0: set DshEvents
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = ThreadStates_New
}

pred ThreadStates_t16_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_LockSupportPark in (s.dsh_events0)
}


pred ThreadStates_t16_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Waiting)
}

pred ThreadStates_t16 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t16_pre
  sn.(s.ThreadStates_t16_post)
}

pred ThreadStates_t17_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_WaitForLockToEnterSynchro in (s.dsh_events0)
}


pred ThreadStates_t17_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Blocked)
}

pred ThreadStates_t17 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t17_pre
  sn.(s.ThreadStates_t17_post)
}

pred ThreadStates_t14_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ObjectWait in (s.dsh_events0)
}


pred ThreadStates_t14_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Waiting)
}

pred ThreadStates_t14 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t14_pre
  sn.(s.ThreadStates_t14_post)
}

pred ThreadStates_t9_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ThreadSleepTime in (s.dsh_events0)
}


pred ThreadStates_t9_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_TimedWaiting)
}

pred ThreadStates_t9 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t9_pre
  sn.(s.ThreadStates_t9_post)
}

pred ThreadStates_t15_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ThreadJoin in (s.dsh_events0)
}


pred ThreadStates_t15_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Waiting)
}

pred ThreadStates_t15 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t15_pre
  sn.(s.ThreadStates_t15_post)
}

pred ThreadStates_t12_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_LockSupportParkNanos in (s.dsh_events0)
}


pred ThreadStates_t12_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_TimedWaiting)
}

pred ThreadStates_t12 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t12_pre
  sn.(s.ThreadStates_t12_post)
}

pred ThreadStates_t23_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Blocked & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_MonitorLockAcquired in (s.dsh_events0)
}


pred ThreadStates_t23_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Runnable_Ready)
}

pred ThreadStates_t23 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t23_pre
  sn.(s.ThreadStates_t23_post)
}

pred ThreadStates_t13_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_LockSupportParkUntil in (s.dsh_events0)
}


pred ThreadStates_t13_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_TimedWaiting)
}

pred ThreadStates_t13 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t13_pre
  sn.(s.ThreadStates_t13_post)
}

pred ThreadStates_t24_pre [
	s: one DshSnapshot] {
  some (ThreadStates_TimedWaiting & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ThreadSleepTimeElapsed in (s.dsh_events0)
}


pred ThreadStates_t24_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Runnable_Ready)
}

pred ThreadStates_t24 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t24_pre
  sn.(s.ThreadStates_t24_post)
}

pred ThreadStates_t10_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ObjectWaitTimeOut in (s.dsh_events0)
}


pred ThreadStates_t10_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_TimedWaiting)
}

pred ThreadStates_t10 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t10_pre
  sn.(s.ThreadStates_t10_post)
}

pred ThreadStates_t21_pre [
	s: one DshSnapshot] {
  some (ThreadStates_TimedWaiting & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ObjectNotifyAll in (s.dsh_events0)
}


pred ThreadStates_t21_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Blocked)
}

pred ThreadStates_t21 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t21_pre
  sn.(s.ThreadStates_t21_post)
}

pred ThreadStates_t11_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ThreadJoinTimeout in (s.dsh_events0)
}


pred ThreadStates_t11_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_TimedWaiting)
}

pred ThreadStates_t11 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t11_pre
  sn.(s.ThreadStates_t11_post)
}

pred ThreadStates_t22_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Waiting & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ObjectNotifyAll in (s.dsh_events0)
}


pred ThreadStates_t22_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Blocked)
}

pred ThreadStates_t22 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t22_pre
  sn.(s.ThreadStates_t22_post)
}

pred ThreadStates_t8_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Blocked & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ThreadTerminated in (s.dsh_events0)
}


pred ThreadStates_t8_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Terminated)
}

pred ThreadStates_t8 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t8_pre
  sn.(s.ThreadStates_t8_post)
}

pred ThreadStates_t7_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Waiting & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ThreadTerminated in (s.dsh_events0)
}


pred ThreadStates_t7_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Terminated)
}

pred ThreadStates_t7 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t7_pre
  sn.(s.ThreadStates_t7_post)
}

pred ThreadStates_t6_pre [
	s: one DshSnapshot] {
  some (ThreadStates_TimedWaiting & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ThreadTerminated in (s.dsh_events0)
}


pred ThreadStates_t6_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Terminated)
}

pred ThreadStates_t6 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t6_pre
  sn.(s.ThreadStates_t6_post)
}

pred ThreadStates_t18_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_WaitForLockToReEnterSynchro in (s.dsh_events0)
}


pred ThreadStates_t18_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Blocked)
}

pred ThreadStates_t18 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t18_pre
  sn.(s.ThreadStates_t18_post)
}

pred ThreadStates_t5_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ThreadTerminated in (s.dsh_events0)
}


pred ThreadStates_t5_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Terminated)
}

pred ThreadStates_t5 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t5_pre
  sn.(s.ThreadStates_t5_post)
}

pred ThreadStates_t19_pre [
	s: one DshSnapshot] {
  some (ThreadStates_TimedWaiting & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ObjectNotify in (s.dsh_events0)
}


pred ThreadStates_t19_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Blocked)
}

pred ThreadStates_t19 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t19_pre
  sn.(s.ThreadStates_t19_post)
}

pred ThreadStates_New_t1_pre [
	s: one DshSnapshot] {
  some (ThreadStates_New & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ThreadStart in (s.dsh_events0)
}


pred ThreadStates_New_t1_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Runnable_Ready)
}

pred ThreadStates_New_t1 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_New_t1_pre
  sn.(s.ThreadStates_New_t1_post)
}

pred ThreadStates_t20_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Waiting & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ObjectNotify in (s.dsh_events0)
}


pred ThreadStates_t20_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((((((s.dsh_conf0) - ThreadStates_New) -
           ThreadStates_Runnable_Ready) -
          ThreadStates_Runnable_Running) -
         ThreadStates_Terminated) -
        ThreadStates_TimedWaiting) - ThreadStates_Waiting) -
      ThreadStates_Blocked) + ThreadStates_Blocked)
}

pred ThreadStates_t20 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_t20_pre
  sn.(s.ThreadStates_t20_post)
}

pred ThreadStates_Runnable_t3_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable_Running & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_ThreadYield in (s.dsh_events0)
  !(s.ThreadStates_t16_pre)
  !(s.ThreadStates_t17_pre)
  !(s.ThreadStates_t14_pre)
  !(s.ThreadStates_t9_pre)
  !(s.ThreadStates_t15_pre)
  !(s.ThreadStates_t12_pre)
  !(s.ThreadStates_t13_pre)
  !(s.ThreadStates_t10_pre)
  !(s.ThreadStates_t11_pre)
  !(s.ThreadStates_t18_pre)
  !(s.ThreadStates_t5_pre)
}


pred ThreadStates_Runnable_t3_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - ThreadStates_Runnable_Ready) -
      ThreadStates_Runnable_Running) +
     ThreadStates_Runnable_Ready)
}

pred ThreadStates_Runnable_t3 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_Runnable_t3_pre
  sn.(s.ThreadStates_Runnable_t3_post)
}

pred ThreadStates_Runnable_t4_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable_Running & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_SchedulerSuspended in (s.dsh_events0)
  !(s.ThreadStates_t16_pre)
  !(s.ThreadStates_t17_pre)
  !(s.ThreadStates_t14_pre)
  !(s.ThreadStates_t9_pre)
  !(s.ThreadStates_t15_pre)
  !(s.ThreadStates_t12_pre)
  !(s.ThreadStates_t13_pre)
  !(s.ThreadStates_t10_pre)
  !(s.ThreadStates_t11_pre)
  !(s.ThreadStates_t18_pre)
  !(s.ThreadStates_t5_pre)
}


pred ThreadStates_Runnable_t4_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - ThreadStates_Runnable_Ready) -
      ThreadStates_Runnable_Running) +
     ThreadStates_Runnable_Ready)
}

pred ThreadStates_Runnable_t4 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_Runnable_t4_pre
  sn.(s.ThreadStates_Runnable_t4_post)
}

pred ThreadStates_Runnable_t2_pre [
	s: one DshSnapshot] {
  some (ThreadStates_Runnable_Ready & (s.dsh_conf0))
  !(ThreadStates in (s.dsh_sc_used0))
  ThreadStates_SchedulerSelected in (s.dsh_events0)
  !(s.ThreadStates_t16_pre)
  !(s.ThreadStates_t17_pre)
  !(s.ThreadStates_t14_pre)
  !(s.ThreadStates_t9_pre)
  !(s.ThreadStates_t15_pre)
  !(s.ThreadStates_t12_pre)
  !(s.ThreadStates_t13_pre)
  !(s.ThreadStates_t10_pre)
  !(s.ThreadStates_t11_pre)
  !(s.ThreadStates_t18_pre)
  !(s.ThreadStates_t5_pre)
}


pred ThreadStates_Runnable_t2_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - ThreadStates_Runnable_Ready) -
      ThreadStates_Runnable_Running) +
     ThreadStates_Runnable_Running)
}

pred ThreadStates_Runnable_t2 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.ThreadStates_Runnable_t2_pre
  sn.(s.ThreadStates_Runnable_t2_post)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.ThreadStates_t16) or
    sn.(s.ThreadStates_t17) or
    sn.(s.ThreadStates_t14) or
    sn.(s.ThreadStates_t9) or
    sn.(s.ThreadStates_t15) or
    sn.(s.ThreadStates_t12) or
    sn.(s.ThreadStates_t23) or
    sn.(s.ThreadStates_t13) or
    sn.(s.ThreadStates_t24) or
    sn.(s.ThreadStates_t10) or
    sn.(s.ThreadStates_t21) or
    sn.(s.ThreadStates_t11) or
    sn.(s.ThreadStates_t22) or
    sn.(s.ThreadStates_t8) or
    sn.(s.ThreadStates_t7) or
    sn.(s.ThreadStates_t6) or
    sn.(s.ThreadStates_t18) or
    sn.(s.ThreadStates_t5) or
    sn.(s.ThreadStates_t19) or
    sn.(s.ThreadStates_New_t1) or
    sn.(s.ThreadStates_t20) or
    sn.(s.ThreadStates_Runnable_t3) or
    sn.(s.ThreadStates_Runnable_t4) or
    sn.(s.ThreadStates_Runnable_t2) or
    !({ s.ThreadStates_t16_pre or
          s.ThreadStates_t17_pre or
          s.ThreadStates_t14_pre or
          s.ThreadStates_t9_pre or
          s.ThreadStates_t15_pre or
          s.ThreadStates_t12_pre or
          s.ThreadStates_t23_pre or
          s.ThreadStates_t13_pre or
          s.ThreadStates_t24_pre or
          s.ThreadStates_t10_pre or
          s.ThreadStates_t21_pre or
          s.ThreadStates_t11_pre or
          s.ThreadStates_t22_pre or
          s.ThreadStates_t8_pre or
          s.ThreadStates_t7_pre or
          s.ThreadStates_t6_pre or
          s.ThreadStates_t18_pre or
          s.ThreadStates_t5_pre or
          s.ThreadStates_t19_pre or
          s.ThreadStates_New_t1_pre or
          s.ThreadStates_t20_pre or
          s.ThreadStates_Runnable_t3_pre or
          s.ThreadStates_Runnable_t4_pre or
          s.ThreadStates_Runnable_t2_pre }) and
      s = sn }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}

