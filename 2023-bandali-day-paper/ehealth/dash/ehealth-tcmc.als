/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-07-20 15:17:39
*/

open util/boolean
open util/tcmc[DshSnapshot]

/* The EHealth case study - Dash model

Copyright (c) 2018 Jose Serna <jserna@uwaterloo.ca>
Copyright (c) 2018,2022 Nancy Day <nday@uwaterloo.ca>

This file is part of the EHealth Dash model.

The EHealth Dash model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The EHealth Dash model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the EHealth Dash model.  If not, see
<https://www.gnu.org/licenses/>.


The EHealth case study is described in Prof. Jonathan S. Ostroff's
technical report~\cite{ostroff2017} and used for teaching EECS 4312,
the Software Engineering Requirements course, at York University,
Toronto, Canada.

@techreport{ostroff2017,
  author      = {Jonathan S. Ostroff},
  title       = {Validating Software via Abstract State Specifications},
  year        = {2017},
  number      = {EECS-2017-02},
  institution = {York University},
  url         = {http://www.eecs.yorku.ca/research/techreports/2017/?abstract=EECS-2017-02}
}

The EHealth Dash model is an adaptation of the TLA+ one by Bandali,
itself based on the snippets presented by
Prof. Ostroff~\cite{ostroff2017}.

This model has appeared in the following publications:

@inproceedings{DBLP:conf/re/AbbassiBDS18,
  author    = {Ali Abbassi and
               Amin Bandali and
               Nancy A. Day and
               Jos{\'{e}} Serna},
  editor    = {Ana Moreira and
               Gunter Mussbacher and
               Jo{\~{a}}o Ara{\'{u}}jo and
               Pablo S{\'{a}}nchez},
  title     = {A Comparison of the Declarative Modelling Languages B, Dash, and {TLA+}},
  booktitle = {8th {IEEE} International Model-Driven Requirements Engineering Workshop,
               MoDRE@RE 2018, Banff, AB, Canada, August 20, 2018},
  pages     = {11--20},
  publisher = {{IEEE} Computer Society},
  year      = {2018},
  url       = {https://doi.org/10.1109/MoDRE.2018.00008},
  doi       = {10.1109/MoDRE.2018.00008},
  timestamp = {Wed, 16 Oct 2019 14:14:56 +0200},
  biburl    = {https://dblp.org/rec/conf/re/AbbassiBDS18.bib},
  bibsource = {dblp computer science bibliography, https://dblp.org}
}

@mastersthesis{bandali2020,
  type      = {{MMath} thesis},
  author    = {Amin Bandali},
  title     = {{A Comprehensive Study of Declarative Modelling Languages}},
  school    = "University of Waterloo, David R. Cheriton School of Computer Science",
  year      = 2020,
  month     = {July},
  publisher = "UWSpace",
  url       = {http://hdl.handle.net/10012/16059},
  note      = {\url{http://hdl.handle.net/10012/16059} and
                  \url{https://bndl.org/mmath}},
  pdf       = {https://p.bndl.org/bandali-mmath-thesis.pdf}
}

*/

sig Patient {}
sig Medication {}


abstract sig Transitions {}
one sig NO_TRANS extends Transitions {} 
one sig EHealthSystem_add_interaction extends Transitions {} 
one sig EHealthSystem_add_patient extends Transitions {} 
one sig EHealthSystem_remove_interaction extends Transitions {} 
one sig EHealthSystem_add_prescription extends Transitions {} 
one sig EHealthSystem_add_medication extends Transitions {} 
one sig EHealthSystem_remove_prescription extends Transitions {} 

sig DshSnapshot {
  dsh_taken0: set Transitions,
  EHealthSystem_in_p: one Patient,
  EHealthSystem_in_m1: one Medication,
  EHealthSystem_in_m2: one Medication,
  EHealthSystem_medications: set Medication,
  EHealthSystem_patients: set Patient,
  EHealthSystem_prescriptions: Patient -> Medication,
  EHealthSystem_interactions: Medication -> Medication
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_taken0) = NO_TRANS &&
  no
  (s.EHealthSystem_medications) &&
  no
  (s.EHealthSystem_prescriptions) &&
  no
  (s.EHealthSystem_patients) &&
  no
  (s.EHealthSystem_interactions)
}

pred EHealthSystem_add_interaction_pre [
	s: one DshSnapshot] {
  ((s.EHealthSystem_in_m1) != (s.EHealthSystem_in_m2) &&
   !(((s.EHealthSystem_in_m1) -> (s.EHealthSystem_in_m2)) in
       (s.EHealthSystem_interactions)) &&
   !(((s.EHealthSystem_in_m2) -> (s.EHealthSystem_in_m1)) in
       (s.EHealthSystem_interactions)) &&
   (s.EHealthSystem_in_m1) in (s.EHealthSystem_medications) &&
   (s.EHealthSystem_in_m2) in (s.EHealthSystem_medications))
}


pred EHealthSystem_add_interaction_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.EHealthSystem_interactions) =
  ((s.EHealthSystem_interactions) +
     (((s.EHealthSystem_in_m1) -> (s.EHealthSystem_in_m2)) +
        ((s.EHealthSystem_in_m2) -> (s.EHealthSystem_in_m1))))
  (sn.dsh_taken0) = EHealthSystem_add_interaction
  (s.EHealthSystem_prescriptions) =
  (sn.EHealthSystem_prescriptions)
  (s.EHealthSystem_patients) = (sn.EHealthSystem_patients)
  (s.EHealthSystem_medications) =
  (sn.EHealthSystem_medications)
}

pred EHealthSystem_add_interaction [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.EHealthSystem_add_interaction_pre
  sn.(s.EHealthSystem_add_interaction_post)
}

pred EHealthSystem_add_patient_pre [
	s: one DshSnapshot] {
  !((s.EHealthSystem_in_p) in (s.EHealthSystem_patients))
}


pred EHealthSystem_add_patient_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.EHealthSystem_patients) =
  ((s.EHealthSystem_patients) + (s.EHealthSystem_in_p))
  (sn.dsh_taken0) = EHealthSystem_add_patient
  (s.EHealthSystem_interactions) =
  (sn.EHealthSystem_interactions)
  (s.EHealthSystem_prescriptions) =
  (sn.EHealthSystem_prescriptions)
  (s.EHealthSystem_medications) =
  (sn.EHealthSystem_medications)
}

pred EHealthSystem_add_patient [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.EHealthSystem_add_patient_pre
  sn.(s.EHealthSystem_add_patient_post)
}

pred EHealthSystem_remove_interaction_pre [
	s: one DshSnapshot] {
  ((s.EHealthSystem_in_m1) in (s.EHealthSystem_medications) &&
   (s.EHealthSystem_in_m2) in (s.EHealthSystem_medications) &&
   ((s.EHealthSystem_in_m1) -> (s.EHealthSystem_in_m2)) in
     (s.EHealthSystem_interactions))
}


pred EHealthSystem_remove_interaction_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.EHealthSystem_interactions) =
  ((s.EHealthSystem_interactions) -
     (((s.EHealthSystem_in_m1) -> (s.EHealthSystem_in_m2)) +
        ((s.EHealthSystem_in_m2) -> (s.EHealthSystem_in_m1))))
  (sn.dsh_taken0) = EHealthSystem_remove_interaction
  (s.EHealthSystem_prescriptions) =
  (sn.EHealthSystem_prescriptions)
  (s.EHealthSystem_patients) = (sn.EHealthSystem_patients)
  (s.EHealthSystem_medications) =
  (sn.EHealthSystem_medications)
}

pred EHealthSystem_remove_interaction [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.EHealthSystem_remove_interaction_pre
  sn.(s.EHealthSystem_remove_interaction_post)
}

pred EHealthSystem_add_prescription_pre [
	s: one DshSnapshot] {
  ((s.EHealthSystem_in_p) in (s.EHealthSystem_patients) &&
   !(((s.EHealthSystem_in_p) -> (s.EHealthSystem_in_m1)) in
       (s.EHealthSystem_prescriptions)) &&
   (all x: (s.EHealthSystem_in_p).(s.EHealthSystem_prescriptions) | !(((s.EHealthSystem_in_m1)
                                                                         ->
                                                                         x)
                                                                        in
                                                                        (s.EHealthSystem_interactions))))
}


pred EHealthSystem_add_prescription_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.EHealthSystem_prescriptions) =
  ((s.EHealthSystem_prescriptions) +
     ((s.EHealthSystem_in_p) -> (s.EHealthSystem_in_m1)))
  (sn.dsh_taken0) = EHealthSystem_add_prescription
  (s.EHealthSystem_interactions) =
  (sn.EHealthSystem_interactions)
  (s.EHealthSystem_patients) = (sn.EHealthSystem_patients)
  (s.EHealthSystem_medications) =
  (sn.EHealthSystem_medications)
}

pred EHealthSystem_add_prescription [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.EHealthSystem_add_prescription_pre
  sn.(s.EHealthSystem_add_prescription_post)
}

pred EHealthSystem_add_medication_pre [
	s: one DshSnapshot] {
  !((s.EHealthSystem_in_m1) in (s.EHealthSystem_medications))
}


pred EHealthSystem_add_medication_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.EHealthSystem_medications) =
  ((s.EHealthSystem_medications) + (s.EHealthSystem_in_m1))
  (sn.dsh_taken0) = EHealthSystem_add_medication
  (s.EHealthSystem_interactions) =
  (sn.EHealthSystem_interactions)
  (s.EHealthSystem_prescriptions) =
  (sn.EHealthSystem_prescriptions)
  (s.EHealthSystem_patients) = (sn.EHealthSystem_patients)
}

pred EHealthSystem_add_medication [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.EHealthSystem_add_medication_pre
  sn.(s.EHealthSystem_add_medication_post)
}

pred EHealthSystem_remove_prescription_pre [
	s: one DshSnapshot] {
  ((s.EHealthSystem_in_p) in (s.EHealthSystem_patients) &&
   (s.EHealthSystem_in_m1) in (s.EHealthSystem_medications) &&
   ((s.EHealthSystem_in_p) -> (s.EHealthSystem_in_m1)) in
     (s.EHealthSystem_prescriptions))
}


pred EHealthSystem_remove_prescription_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.EHealthSystem_prescriptions) =
  ((s.EHealthSystem_prescriptions) -
     ((s.EHealthSystem_in_p) -> (s.EHealthSystem_in_m1)))
  (sn.dsh_taken0) = EHealthSystem_remove_prescription
  (s.EHealthSystem_interactions) =
  (sn.EHealthSystem_interactions)
  (s.EHealthSystem_patients) = (sn.EHealthSystem_patients)
  (s.EHealthSystem_medications) =
  (sn.EHealthSystem_medications)
}

pred EHealthSystem_remove_prescription [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.EHealthSystem_remove_prescription_pre
  sn.(s.EHealthSystem_remove_prescription_post)
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_taken0) = NO_TRANS
  (sn.EHealthSystem_medications) =
  (s.EHealthSystem_medications)
  (sn.EHealthSystem_patients) = (s.EHealthSystem_patients)
  (sn.EHealthSystem_prescriptions) =
  (s.EHealthSystem_prescriptions)
  (sn.EHealthSystem_interactions) =
  (s.EHealthSystem_interactions)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.EHealthSystem_add_interaction) ||
    sn.(s.EHealthSystem_add_patient) ||
    sn.(s.EHealthSystem_remove_interaction) ||
    sn.(s.EHealthSystem_add_prescription) ||
    sn.(s.EHealthSystem_add_medication) ||
    sn.(s.EHealthSystem_remove_prescription) ||
    !({ s.EHealthSystem_add_interaction_pre ||
          s.EHealthSystem_add_patient_pre ||
          s.EHealthSystem_remove_interaction_pre ||
          s.EHealthSystem_add_prescription_pre ||
          s.EHealthSystem_add_medication_pre ||
          s.EHealthSystem_remove_prescription_pre }) &&
      sn.(s.dsh_stutter) }
}

fact allSnapshotsDifferent {
  (all s: one
  DshSnapshot,sn: one
  DshSnapshot | ((s.dsh_taken0) = (sn.dsh_taken0) &&
                   (s.EHealthSystem_in_p) =
                     (sn.EHealthSystem_in_p) &&
                   (s.EHealthSystem_in_m1) =
                     (sn.EHealthSystem_in_m1) &&
                   (s.EHealthSystem_in_m2) =
                     (sn.EHealthSystem_in_m2) &&
                   (s.EHealthSystem_medications) =
                     (sn.EHealthSystem_medications) &&
                   (s.EHealthSystem_patients) =
                     (sn.EHealthSystem_patients) &&
                   (s.EHealthSystem_prescriptions) =
                     (sn.EHealthSystem_prescriptions) &&
                   (s.EHealthSystem_interactions) =
                     (sn.EHealthSystem_interactions)) =>
                  (s = sn))
}

pred dsh_enough_operations {
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.EHealthSystem_add_interaction))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.EHealthSystem_add_patient))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.EHealthSystem_remove_interaction))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.EHealthSystem_add_prescription))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.EHealthSystem_add_medication))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.EHealthSystem_remove_prescription))
}

pred dsh_reachability {
  (all s: one
  DshSnapshot | s in
                  (DshSnapshot.(tcmc/ks_s0 <: (*
                                  tcmc/ks_sigma))))
}

fact dsh_tcmc_fact {
  (all s: one
  DshSnapshot | (s in tcmc/ks_s0) <=> (s.dsh_initial))
  (all s: one
  DshSnapshot,sn: one
  DshSnapshot | ((s -> sn) in tcmc/ks_sigma) <=>
                  (sn.(s.dsh_small_step)))
}

// significant scope
// running this for 7 (unsat) take much longer than running it for 8 (sat)
run { 
    dsh_reachability
    dsh_enough_operations 
} for exactly 8 DshSnapshot, 3 Patient, 4 Medication expect 1

pred symmetry {
    ctl_mc[
        ag[{s: DshSnapshot | all m1, m2: Medication |
            m1 -> m2  in s.EHealthSystem_interactions iff m2 -> m1 in s.EHealthSystem_interactions}]
    ]
}

check { symmetry } for 8 DshSnapshot, 3 Patient, 4 Medication   expect 0 

pred no_self_interaction {
    ctl_mc[
        ag[{s:DshSnapshot | all m: Medication | not (m -> m in s. EHealthSystem_interactions)}]
    ]
}

check { no_self_interaction } for 8 DshSnapshot, 3 Patient, 4 Medication expect 0  

pred safe_prescriptions {
    ctl_mc[
        ag[{s:DshSnapshot | all m1, m2: Medication, p: Patient |
            m1 -> m2 in s.EHealthSystem_interactions =>
            !((p -> m1 in s.EHealthSystem_prescriptions) and (p -> m2 in s.EHealthSystem_prescriptions))}]
    ]
}

check { safe_prescriptions } for 8 DshSnapshot, 3 Patient, 4 Medication   expect 0 

/*
    How to run this model:

    dashcli -t -m tcmc ehealth.dsh
    dashcli ehealth-tcmc.als
*/
