/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-13 17:09:33
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/*******************************************************************************
 * Title: TrafficLight.dsh
 * Authors: Jose Serna
 * Created: 27-04-2018
 * Last modified: 
 * 2023-06-07 Nancy Day small changes for new Dash
 *
 * Notes: Traffic light system model taken from Shahram's PhD thesis.
 *  The single input assumption is required for the model to have the expected
 *  behaviour
 *  
 *  Shahram Esmaeilsabzali. Perscriptive Semantics for Big-Step Modelling Languages.
 *  PhD thesis, University of Waterloo, David R. Cheriton School of Computer Science, 2011
 *  https://cs.uwaterloo.ca/~nday/pdf/theses/2011-esmaeilsabzali-phd-thesis.pdf
 *
 ******************************************************************************/

abstract sig DshStates {}
abstract sig TrafficLight extends DshStates {} 
abstract sig TrafficLight_NorthSouth extends TrafficLight {} 
one sig TrafficLight_NorthSouth_Green extends TrafficLight_NorthSouth {} 
one sig TrafficLight_NorthSouth_Yellow extends TrafficLight_NorthSouth {} 
one sig TrafficLight_NorthSouth_Red extends TrafficLight_NorthSouth {} 
abstract sig TrafficLight_EastWest extends TrafficLight {} 
one sig TrafficLight_EastWest_Green extends TrafficLight_EastWest {} 
one sig TrafficLight_EastWest_Yellow extends TrafficLight_EastWest {} 
one sig TrafficLight_EastWest_Red extends TrafficLight_EastWest {} 

abstract sig DshEvents {}
abstract sig DshEnvEvents extends DshEvents {} 
one sig TrafficLight_Change extends DshEnvEvents {} 
one sig TrafficLight_End extends DshEnvEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_events0: set DshEvents,
  dsh_stable: one boolean/Bool
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) =
  (TrafficLight_NorthSouth_Green + TrafficLight_EastWest_Red)
  (s.dsh_stable).boolean/isTrue
}

pred TrafficLight_EastWest_Green_T5_pre [
	s: one DshSnapshot] {
  some (TrafficLight_EastWest_Green & (s.dsh_conf0))
  !(TrafficLight in (s.dsh_sc_used0))
  !(TrafficLight_EastWest in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (TrafficLight_End in ((s.dsh_events0) :> DshEnvEvents))
  else
    (TrafficLight_End in (s.dsh_events0))

}


pred TrafficLight_EastWest_Green_T5_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - TrafficLight_EastWest_Green) -
       TrafficLight_EastWest_Yellow) -
      TrafficLight_EastWest_Red) +
     TrafficLight_EastWest_Yellow)
  (none.(TrafficLight_EastWest.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshEnvEvents) =
              ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + TrafficLight_EastWest))
       )

}

pred TrafficLight_EastWest_Green_T5_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (TrafficLight_EastWest_Green & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(TrafficLight in dsh_scp0) and
       !(TrafficLight_EastWest in dsh_scp0) and
       TrafficLight_End in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (TrafficLight_End in ((s.dsh_events0) + dsh_genEvs0))

}

pred TrafficLight_EastWest_Green_T5 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.TrafficLight_EastWest_Green_T5_pre
  sn.(s.TrafficLight_EastWest_Green_T5_post)
}

pred TrafficLight_NorthSouth_Yellow_T2_pre [
	s: one DshSnapshot] {
  some (TrafficLight_NorthSouth_Yellow & (s.dsh_conf0))
  !(TrafficLight in (s.dsh_sc_used0))
  !(TrafficLight_NorthSouth in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (TrafficLight_Change in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (TrafficLight_Change in (s.dsh_events0))

}


pred TrafficLight_NorthSouth_Yellow_T2_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - TrafficLight_NorthSouth_Green) -
       TrafficLight_NorthSouth_Yellow) -
      TrafficLight_NorthSouth_Red) +
     TrafficLight_NorthSouth_Red)
  (none.(TrafficLight_NorthSouth.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshEnvEvents) =
              ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + TrafficLight_NorthSouth))
       )

}

pred TrafficLight_NorthSouth_Yellow_T2_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (TrafficLight_NorthSouth_Yellow & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(TrafficLight in dsh_scp0) and
       !(TrafficLight_NorthSouth in dsh_scp0) and
       TrafficLight_Change in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (TrafficLight_Change in ((s.dsh_events0) + dsh_genEvs0))

}

pred TrafficLight_NorthSouth_Yellow_T2 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.TrafficLight_NorthSouth_Yellow_T2_pre
  sn.(s.TrafficLight_NorthSouth_Yellow_T2_post)
}

pred TrafficLight_NorthSouth_Green_T1_pre [
	s: one DshSnapshot] {
  some (TrafficLight_NorthSouth_Green & (s.dsh_conf0))
  !(TrafficLight in (s.dsh_sc_used0))
  !(TrafficLight_NorthSouth in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (TrafficLight_End in ((s.dsh_events0) :> DshEnvEvents))
  else
    (TrafficLight_End in (s.dsh_events0))

}


pred TrafficLight_NorthSouth_Green_T1_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - TrafficLight_NorthSouth_Green) -
       TrafficLight_NorthSouth_Yellow) -
      TrafficLight_NorthSouth_Red) +
     TrafficLight_NorthSouth_Yellow)
  (none.(TrafficLight_NorthSouth.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshEnvEvents) =
              ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + TrafficLight_NorthSouth))
       )

}

pred TrafficLight_NorthSouth_Green_T1_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (TrafficLight_NorthSouth_Green & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(TrafficLight in dsh_scp0) and
       !(TrafficLight_NorthSouth in dsh_scp0) and
       TrafficLight_End in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (TrafficLight_End in ((s.dsh_events0) + dsh_genEvs0))

}

pred TrafficLight_NorthSouth_Green_T1 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.TrafficLight_NorthSouth_Green_T1_pre
  sn.(s.TrafficLight_NorthSouth_Green_T1_post)
}

pred TrafficLight_NorthSouth_Red_T3_pre [
	s: one DshSnapshot] {
  some (TrafficLight_NorthSouth_Red & (s.dsh_conf0))
  !(TrafficLight in (s.dsh_sc_used0))
  !(TrafficLight_NorthSouth in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (TrafficLight_Change in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (TrafficLight_Change in (s.dsh_events0))

}


pred TrafficLight_NorthSouth_Red_T3_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - TrafficLight_NorthSouth_Green) -
       TrafficLight_NorthSouth_Yellow) -
      TrafficLight_NorthSouth_Red) +
     TrafficLight_NorthSouth_Green)
  (none.(TrafficLight_NorthSouth.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshEnvEvents) =
              ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + TrafficLight_NorthSouth))
       )

}

pred TrafficLight_NorthSouth_Red_T3_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (TrafficLight_NorthSouth_Red & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(TrafficLight in dsh_scp0) and
       !(TrafficLight_NorthSouth in dsh_scp0) and
       TrafficLight_Change in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (TrafficLight_Change in ((s.dsh_events0) + dsh_genEvs0))

}

pred TrafficLight_NorthSouth_Red_T3 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.TrafficLight_NorthSouth_Red_T3_pre
  sn.(s.TrafficLight_NorthSouth_Red_T3_post)
}

pred TrafficLight_EastWest_Red_T4_pre [
	s: one DshSnapshot] {
  some (TrafficLight_EastWest_Red & (s.dsh_conf0))
  !(TrafficLight in (s.dsh_sc_used0))
  !(TrafficLight_EastWest in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (TrafficLight_Change in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (TrafficLight_Change in (s.dsh_events0))

}


pred TrafficLight_EastWest_Red_T4_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - TrafficLight_EastWest_Green) -
       TrafficLight_EastWest_Yellow) -
      TrafficLight_EastWest_Red) +
     TrafficLight_EastWest_Green)
  (none.(TrafficLight_EastWest.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshEnvEvents) =
              ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + TrafficLight_EastWest))
       )

}

pred TrafficLight_EastWest_Red_T4_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (TrafficLight_EastWest_Red & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(TrafficLight in dsh_scp0) and
       !(TrafficLight_EastWest in dsh_scp0) and
       TrafficLight_Change in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (TrafficLight_Change in ((s.dsh_events0) + dsh_genEvs0))

}

pred TrafficLight_EastWest_Red_T4 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.TrafficLight_EastWest_Red_T4_pre
  sn.(s.TrafficLight_EastWest_Red_T4_post)
}

pred TrafficLight_EastWest_Yellow_T6_pre [
	s: one DshSnapshot] {
  some (TrafficLight_EastWest_Yellow & (s.dsh_conf0))
  !(TrafficLight in (s.dsh_sc_used0))
  !(TrafficLight_EastWest in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (TrafficLight_Change in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (TrafficLight_Change in (s.dsh_events0))

}


pred TrafficLight_EastWest_Yellow_T6_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - TrafficLight_EastWest_Green) -
       TrafficLight_EastWest_Yellow) -
      TrafficLight_EastWest_Red) + TrafficLight_EastWest_Red)
  (none.(TrafficLight_EastWest.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshEnvEvents) =
              ((s.dsh_events0) :> DshEnvEvents) and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + TrafficLight_EastWest))
       )

}

pred TrafficLight_EastWest_Yellow_T6_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (TrafficLight_EastWest_Yellow & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(TrafficLight in dsh_scp0) and
       !(TrafficLight_EastWest in dsh_scp0) and
       TrafficLight_Change in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (TrafficLight_Change in ((s.dsh_events0) + dsh_genEvs0))

}

pred TrafficLight_EastWest_Yellow_T6 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.TrafficLight_EastWest_Yellow_T6_pre
  sn.(s.TrafficLight_EastWest_Yellow_T6_post)
}

pred _nextIsStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.TrafficLight_EastWest_Green_T5_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.TrafficLight_NorthSouth_Yellow_T2_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.TrafficLight_NorthSouth_Green_T1_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.TrafficLight_NorthSouth_Red_T3_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.TrafficLight_EastWest_Red_T4_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.TrafficLight_EastWest_Yellow_T6_enabledAfterStep))))
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_stable) = (s.dsh_stable)
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.TrafficLight_EastWest_Green_T5) or
    sn.(s.TrafficLight_NorthSouth_Yellow_T2) or
    sn.(s.TrafficLight_NorthSouth_Green_T1) or
    sn.(s.TrafficLight_NorthSouth_Red_T3) or
    sn.(s.TrafficLight_EastWest_Red_T4) or
    sn.(s.TrafficLight_EastWest_Yellow_T6) or
    !({ s.TrafficLight_EastWest_Green_T5_pre or
          s.TrafficLight_NorthSouth_Yellow_T2_pre or
          s.TrafficLight_NorthSouth_Green_T1_pre or
          s.TrafficLight_NorthSouth_Red_T3_pre or
          s.TrafficLight_EastWest_Red_T4_pre or
          s.TrafficLight_EastWest_Yellow_T6_pre }) and
      sn.(s.dsh_stutter) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}



// Environmental assumptions

fact {
    // Environment generates End First
    all s: DshSnapshot | {
        dsh_initial[s] => s.dsh_events0 = TrafficLight_End
    }
    // Events alternate after each stable snapshot
    all s: DshSnapshot, sn: DshSnapshot | dsh_small_step[s,sn] => {
        s.dsh_stable = True and sn.dsh_stable = True => sn.dsh_events0 != s.dsh_events0
        s.dsh_stable = False and sn.dsh_stable = True => sn.dsh_events0 != s.dsh_events0
        s.dsh_stable = True and sn.dsh_stable = False => sn.dsh_events0 = s.dsh_events0
        s.dsh_stable = False and sn.dsh_stable = False => sn.dsh_events0 = s.dsh_events0
    }
}



