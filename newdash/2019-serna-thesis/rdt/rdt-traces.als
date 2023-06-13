/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-13 15:57:24
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/*******************************************************************************
 * Title: rdt.dsh
 * Authors: Jose Serna
 * Created: 03-04-2019
 * Last modified: 
 * 2023-06-7 Nancy Day modifications for new Dash
 *
 * Notes: Dash model of a Reliable Data Transfer (RDT) protocol.
 *
 *      Mitchell Kember, Lynn Tran, George Gao, and Nancy A. Day. 
 *      Extracting counterexamples from transitive-closure-based model checking. 
 *      In Workshop on Modelling in Software Engineering (MISE) @ International 
 *      Conference on Software Engineering (ICSE), pages 47--54. ACM, May 2019.
 *      https://cs.uwaterloo.ca/~nday/pdf/refereed/2019-KeTrGaDa-mise.pdf
 *
 ******************************************************************************/

abstract sig DshStates {}
abstract sig RDT extends DshStates {} 
abstract sig RDT_Sender extends RDT {} 
one sig RDT_Sender_ReadySendNext extends RDT_Sender {} 
one sig RDT_Sender_WaitAck extends RDT_Sender {} 
one sig RDT_Sender_ReadyResend extends RDT_Sender {} 
abstract sig RDT_Receiver extends RDT {} 
one sig RDT_Receiver_ReadyReceiveNext extends RDT_Receiver {} 
one sig RDT_Receiver_ReceiveSuccess extends RDT_Receiver {} 
one sig RDT_Receiver_ReceiveError extends RDT_Receiver {} 
one sig RDT_Receiver_ReadyReceiveResend extends RDT_Receiver {} 

abstract sig DshEvents {}
abstract sig DshEnvEvents extends DshEvents {} 
one sig RDT_SendSuccess extends DshEnvEvents {} 
one sig RDT_SendError extends DshEnvEvents {} 
one sig RDT_AckSuccess extends DshEnvEvents {} 
one sig RDT_AckError extends DshEnvEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_events0: set DshEvents,
  dsh_stable: one boolean/Bool
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) =
  (RDT_Sender_ReadySendNext + RDT_Receiver_ReadyReceiveNext)
  (s.dsh_stable).boolean/isTrue
}

pred RDT_Sender_t2_pre [
	s: one DshSnapshot] {
  some (RDT_Sender_ReadySendNext & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Sender in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_SendError in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_SendError in (s.dsh_events0))

}


pred RDT_Sender_t2_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - RDT_Sender_ReadySendNext) -
       RDT_Sender_WaitAck) - RDT_Sender_ReadyResend) +
     RDT_Sender_WaitAck)
  (none.(RDT_Sender.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Sender))
       )

}

pred RDT_Sender_t2_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Sender_ReadySendNext & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Sender in dsh_scp0) and
       RDT_SendError in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_SendError in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Sender_t2 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Sender_t2_pre
  sn.(s.RDT_Sender_t2_post)
}

pred RDT_Sender_t1_pre [
	s: one DshSnapshot] {
  some (RDT_Sender_ReadySendNext & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Sender in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_SendSuccess in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_SendSuccess in (s.dsh_events0))

}


pred RDT_Sender_t1_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - RDT_Sender_ReadySendNext) -
       RDT_Sender_WaitAck) - RDT_Sender_ReadyResend) +
     RDT_Sender_WaitAck)
  (none.(RDT_Sender.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Sender))
       )

}

pred RDT_Sender_t1_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Sender_ReadySendNext & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Sender in dsh_scp0) and
       RDT_SendSuccess in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_SendSuccess in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Sender_t1 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Sender_t1_pre
  sn.(s.RDT_Sender_t1_post)
}

pred RDT_Sender_t6_pre [
	s: one DshSnapshot] {
  some (RDT_Sender_ReadyResend & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Sender in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_SendError in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_SendError in (s.dsh_events0))

}


pred RDT_Sender_t6_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - RDT_Sender_ReadySendNext) -
       RDT_Sender_WaitAck) - RDT_Sender_ReadyResend) +
     RDT_Sender_WaitAck)
  (none.(RDT_Sender.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Sender))
       )

}

pred RDT_Sender_t6_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Sender_ReadyResend & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Sender in dsh_scp0) and
       RDT_SendError in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_SendError in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Sender_t6 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Sender_t6_pre
  sn.(s.RDT_Sender_t6_post)
}

pred RDT_Sender_t5_pre [
	s: one DshSnapshot] {
  some (RDT_Sender_ReadyResend & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Sender in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_SendSuccess in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_SendSuccess in (s.dsh_events0))

}


pred RDT_Sender_t5_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - RDT_Sender_ReadySendNext) -
       RDT_Sender_WaitAck) - RDT_Sender_ReadyResend) +
     RDT_Sender_WaitAck)
  (none.(RDT_Sender.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Sender))
       )

}

pred RDT_Sender_t5_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Sender_ReadyResend & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Sender in dsh_scp0) and
       RDT_SendSuccess in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_SendSuccess in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Sender_t5 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Sender_t5_pre
  sn.(s.RDT_Sender_t5_post)
}

pred RDT_Sender_t4_pre [
	s: one DshSnapshot] {
  some (RDT_Sender_WaitAck & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Sender in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_AckError in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_AckError in (s.dsh_events0))

}


pred RDT_Sender_t4_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - RDT_Sender_ReadySendNext) -
       RDT_Sender_WaitAck) - RDT_Sender_ReadyResend) +
     RDT_Sender_ReadyResend)
  (none.(RDT_Sender.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Sender))
       )

}

pred RDT_Sender_t4_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Sender_WaitAck & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Sender in dsh_scp0) and
       RDT_AckError in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_AckError in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Sender_t4 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Sender_t4_pre
  sn.(s.RDT_Sender_t4_post)
}

pred RDT_Sender_t3_pre [
	s: one DshSnapshot] {
  some (RDT_Sender_WaitAck & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Sender in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_AckSuccess in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_AckSuccess in (s.dsh_events0))

}


pred RDT_Sender_t3_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - RDT_Sender_ReadySendNext) -
       RDT_Sender_WaitAck) - RDT_Sender_ReadyResend) +
     RDT_Sender_ReadySendNext)
  (none.(RDT_Sender.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Sender))
       )

}

pred RDT_Sender_t3_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Sender_WaitAck & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Sender in dsh_scp0) and
       RDT_AckSuccess in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_AckSuccess in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Sender_t3 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Sender_t3_pre
  sn.(s.RDT_Sender_t3_post)
}

pred RDT_Receiver_t13_pre [
	s: one DshSnapshot] {
  some (RDT_Receiver_ReadyReceiveResend & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Receiver in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_SendSuccess in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_SendSuccess in (s.dsh_events0))

}


pred RDT_Receiver_t13_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - RDT_Receiver_ReadyReceiveNext) -
        RDT_Receiver_ReceiveSuccess) -
       RDT_Receiver_ReceiveError) -
      RDT_Receiver_ReadyReceiveResend) +
     RDT_Receiver_ReceiveSuccess)
  (none.(RDT_Receiver.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Receiver))
       )

}

pred RDT_Receiver_t13_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Receiver_ReadyReceiveResend & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Receiver in dsh_scp0) and
       RDT_SendSuccess in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_SendSuccess in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Receiver_t13 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Receiver_t13_pre
  sn.(s.RDT_Receiver_t13_post)
}

pred RDT_Receiver_t12_pre [
	s: one DshSnapshot] {
  some (RDT_Receiver_ReadyReceiveResend & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Receiver in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_SendError in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_SendError in (s.dsh_events0))

}


pred RDT_Receiver_t12_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - RDT_Receiver_ReadyReceiveNext) -
        RDT_Receiver_ReceiveSuccess) -
       RDT_Receiver_ReceiveError) -
      RDT_Receiver_ReadyReceiveResend) +
     RDT_Receiver_ReceiveError)
  (none.(RDT_Receiver.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Receiver))
       )

}

pred RDT_Receiver_t12_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Receiver_ReadyReceiveResend & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Receiver in dsh_scp0) and
       RDT_SendError in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_SendError in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Receiver_t12 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Receiver_t12_pre
  sn.(s.RDT_Receiver_t12_post)
}

pred RDT_Receiver_t11_pre [
	s: one DshSnapshot] {
  some (RDT_Receiver_ReceiveError & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Receiver in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_AckError in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_AckError in (s.dsh_events0))

}


pred RDT_Receiver_t11_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - RDT_Receiver_ReadyReceiveNext) -
        RDT_Receiver_ReceiveSuccess) -
       RDT_Receiver_ReceiveError) -
      RDT_Receiver_ReadyReceiveResend) +
     RDT_Receiver_ReadyReceiveResend)
  (none.(RDT_Receiver.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Receiver))
       )

}

pred RDT_Receiver_t11_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Receiver_ReceiveError & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Receiver in dsh_scp0) and
       RDT_AckError in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_AckError in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Receiver_t11 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Receiver_t11_pre
  sn.(s.RDT_Receiver_t11_post)
}

pred RDT_Receiver_t10_pre [
	s: one DshSnapshot] {
  some (RDT_Receiver_ReadyReceiveNext & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Receiver in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_SendError in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_SendError in (s.dsh_events0))

}


pred RDT_Receiver_t10_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - RDT_Receiver_ReadyReceiveNext) -
        RDT_Receiver_ReceiveSuccess) -
       RDT_Receiver_ReceiveError) -
      RDT_Receiver_ReadyReceiveResend) +
     RDT_Receiver_ReceiveError)
  (none.(RDT_Receiver.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Receiver))
       )

}

pred RDT_Receiver_t10_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Receiver_ReadyReceiveNext & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Receiver in dsh_scp0) and
       RDT_SendError in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_SendError in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Receiver_t10 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Receiver_t10_pre
  sn.(s.RDT_Receiver_t10_post)
}

pred RDT_Receiver_t8_pre [
	s: one DshSnapshot] {
  some (RDT_Receiver_ReceiveSuccess & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Receiver in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_AckSuccess in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_AckSuccess in (s.dsh_events0))

}


pred RDT_Receiver_t8_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - RDT_Receiver_ReadyReceiveNext) -
        RDT_Receiver_ReceiveSuccess) -
       RDT_Receiver_ReceiveError) -
      RDT_Receiver_ReadyReceiveResend) +
     RDT_Receiver_ReadyReceiveNext)
  (none.(RDT_Receiver.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Receiver))
       )

}

pred RDT_Receiver_t8_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Receiver_ReceiveSuccess & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Receiver in dsh_scp0) and
       RDT_AckSuccess in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_AckSuccess in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Receiver_t8 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Receiver_t8_pre
  sn.(s.RDT_Receiver_t8_post)
}

pred RDT_Receiver_t7_pre [
	s: one DshSnapshot] {
  some (RDT_Receiver_ReadyReceiveNext & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Receiver in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_SendSuccess in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_SendSuccess in (s.dsh_events0))

}


pred RDT_Receiver_t7_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - RDT_Receiver_ReadyReceiveNext) -
        RDT_Receiver_ReceiveSuccess) -
       RDT_Receiver_ReceiveError) -
      RDT_Receiver_ReadyReceiveResend) +
     RDT_Receiver_ReceiveSuccess)
  (none.(RDT_Receiver.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Receiver))
       )

}

pred RDT_Receiver_t7_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Receiver_ReadyReceiveNext & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Receiver in dsh_scp0) and
       RDT_SendSuccess in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_SendSuccess in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Receiver_t7 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Receiver_t7_pre
  sn.(s.RDT_Receiver_t7_post)
}

pred RDT_Receiver_t9_pre [
	s: one DshSnapshot] {
  some (RDT_Receiver_ReceiveSuccess & (s.dsh_conf0))
  !(RDT in (s.dsh_sc_used0))
  !(RDT_Receiver in (s.dsh_sc_used0))
  ((s.dsh_stable).boolean/isTrue)=>
    (RDT_AckError in ((s.dsh_events0) :> DshEnvEvents))
  else
    (RDT_AckError in (s.dsh_events0))

}


pred RDT_Receiver_t9_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - RDT_Receiver_ReadyReceiveNext) -
        RDT_Receiver_ReceiveSuccess) -
       RDT_Receiver_ReceiveError) -
      RDT_Receiver_ReadyReceiveResend) +
     RDT_Receiver_ReadyReceiveNext)
  (none.(RDT_Receiver.(sn.(s._nextIsStable))))=>
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
              ((s.dsh_sc_used0) + RDT_Receiver))
       )

}

pred RDT_Receiver_t9_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (RDT_Receiver_ReceiveSuccess & (sn.dsh_conf0))
  ((s.dsh_stable).boolean/isTrue)=>
    (!(RDT in dsh_scp0) and
       !(RDT_Receiver in dsh_scp0) and
       RDT_AckError in
         (((s.dsh_events0) :> DshEnvEvents) + dsh_genEvs0))
  else
    (RDT_AckError in ((s.dsh_events0) + dsh_genEvs0))

}

pred RDT_Receiver_t9 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.RDT_Receiver_t9_pre
  sn.(s.RDT_Receiver_t9_post)
}

pred _nextIsStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Sender_t2_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Sender_t1_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Sender_t6_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Sender_t5_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Sender_t4_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Sender_t3_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Receiver_t13_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Receiver_t12_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Receiver_t11_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Receiver_t10_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Receiver_t8_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Receiver_t7_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.RDT_Receiver_t9_enabledAfterStep))))
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.RDT_Sender_t2) or
    sn.(s.RDT_Sender_t1) or
    sn.(s.RDT_Sender_t6) or
    sn.(s.RDT_Sender_t5) or
    sn.(s.RDT_Sender_t4) or
    sn.(s.RDT_Sender_t3) or
    sn.(s.RDT_Receiver_t13) or
    sn.(s.RDT_Receiver_t12) or
    sn.(s.RDT_Receiver_t11) or
    sn.(s.RDT_Receiver_t10) or
    sn.(s.RDT_Receiver_t8) or
    sn.(s.RDT_Receiver_t7) or
    sn.(s.RDT_Receiver_t9) or
    !({ s.RDT_Sender_t2_pre or
          s.RDT_Sender_t1_pre or
          s.RDT_Sender_t6_pre or
          s.RDT_Sender_t5_pre or
          s.RDT_Sender_t4_pre or
          s.RDT_Sender_t3_pre or
          s.RDT_Receiver_t13_pre or
          s.RDT_Receiver_t12_pre or
          s.RDT_Receiver_t11_pre or
          s.RDT_Receiver_t10_pre or
          s.RDT_Receiver_t8_pre or
          s.RDT_Receiver_t7_pre or
          s.RDT_Receiver_t9_pre }) and
      s = sn }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}


