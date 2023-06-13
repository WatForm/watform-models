/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-13 15:57:28
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

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

abstract sig DshStates {}
abstract sig EHealthSystem extends DshStates {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  EHealthSystem_in_p: lone Patient,
  EHealthSystem_in_m1: lone Medication,
  EHealthSystem_in_m2: lone Medication,
  EHealthSystem_medications: set Medication,
  EHealthSystem_patients: set Patient,
  EHealthSystem_prescriptions: Patient -> Medication,
  EHealthSystem_interactions: Medication -> Medication
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = EHealthSystem and
  no
  s.EHealthSystem_medications and
  no
  s.EHealthSystem_prescriptions and
  no
  s.EHealthSystem_patients and
  no
  s.EHealthSystem_interactions
}

fact inv {  (all s: one
  DshSnapshot | (all m1,m2: Medication | ((m1 -> m2) in
                                            s.EHealthSystem_interactions) <=>
                                           ((m2 -> m1) in
                                              s.EHealthSystem_interactions)) and
                  (all m: s.EHealthSystem_medications | !((m ->
                                                             m) in
                                                            s.EHealthSystem_interactions)) and
                  (all m1,m2: s.EHealthSystem_medications,p: s.EHealthSystem_patients | ((m1 ->
                                                                                            m2) in
                                                                                           s.EHealthSystem_interactions) =>
                                                                                          !((p ->
                                                                                               m1) in
                                                                                              s.EHealthSystem_prescriptions and
                                                                                              (p ->
                                                                                                 m2) in
                                                                                                s.EHealthSystem_prescriptions)))
}

pred EHealthSystem_add_interaction_pre [
	s: one DshSnapshot] {
  some (EHealthSystem & (s.dsh_conf0))
  (s.EHealthSystem_in_m1) != (s.EHealthSystem_in_m2) and
  !((s.EHealthSystem_in_m1 -> s.EHealthSystem_in_m2) in
      s.EHealthSystem_interactions) and
  !((s.EHealthSystem_in_m2 -> s.EHealthSystem_in_m1) in
      s.EHealthSystem_interactions) and
  s.EHealthSystem_in_m1 in s.EHealthSystem_medications and
  s.EHealthSystem_in_m2 in s.EHealthSystem_medications
  !(EHealthSystem in (s.dsh_sc_used0))
}


pred EHealthSystem_add_interaction_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) - EHealthSystem) + EHealthSystem)
  (sn.EHealthSystem_interactions) =
  ((s.EHealthSystem_interactions) +
     (s.EHealthSystem_in_m1 -> s.EHealthSystem_in_m2) +
       (s.EHealthSystem_in_m2 -> s.EHealthSystem_in_m1))
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
  some (EHealthSystem & (s.dsh_conf0))
  !(s.EHealthSystem_in_p in s.EHealthSystem_patients)
  !(EHealthSystem in (s.dsh_sc_used0))
}


pred EHealthSystem_add_patient_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) - EHealthSystem) + EHealthSystem)
  (sn.EHealthSystem_patients) =
  ((s.EHealthSystem_patients) + (s.EHealthSystem_in_p))
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
  some (EHealthSystem & (s.dsh_conf0))
  s.EHealthSystem_in_m1 in s.EHealthSystem_medications and
  s.EHealthSystem_in_m2 in s.EHealthSystem_medications and
  (s.EHealthSystem_in_m1 -> s.EHealthSystem_in_m2) in
    s.EHealthSystem_interactions
  !(EHealthSystem in (s.dsh_sc_used0))
}


pred EHealthSystem_remove_interaction_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) - EHealthSystem) + EHealthSystem)
  (sn.EHealthSystem_interactions) =
  ((s.EHealthSystem_interactions) -
     (s.EHealthSystem_in_m1 -> s.EHealthSystem_in_m2) +
       (s.EHealthSystem_in_m2 -> s.EHealthSystem_in_m1))
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
  some (EHealthSystem & (s.dsh_conf0))
  s.EHealthSystem_in_p in s.EHealthSystem_patients and
  !((s.EHealthSystem_in_p -> s.EHealthSystem_in_m1) in
      s.EHealthSystem_prescriptions) and
  (all x: (s.EHealthSystem_in_p).(s.EHealthSystem_prescriptions) | !((s.EHealthSystem_in_m1 ->
                                                                        x) in
                                                                       s.EHealthSystem_interactions))
  !(EHealthSystem in (s.dsh_sc_used0))
}


pred EHealthSystem_add_prescription_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) - EHealthSystem) + EHealthSystem)
  (sn.EHealthSystem_prescriptions) =
  ((s.EHealthSystem_prescriptions) +
     (s.EHealthSystem_in_p -> s.EHealthSystem_in_m1))
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
  some (EHealthSystem & (s.dsh_conf0))
  !(s.EHealthSystem_in_m1 in s.EHealthSystem_medications)
  !(EHealthSystem in (s.dsh_sc_used0))
}


pred EHealthSystem_add_medication_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) - EHealthSystem) + EHealthSystem)
  (sn.EHealthSystem_medications) =
  ((s.EHealthSystem_medications) + (s.EHealthSystem_in_m1))
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
  some (EHealthSystem & (s.dsh_conf0))
  s.EHealthSystem_in_p in s.EHealthSystem_patients and
  s.EHealthSystem_in_m1 in s.EHealthSystem_medications and
  (s.EHealthSystem_in_p -> s.EHealthSystem_in_m1) in
    s.EHealthSystem_prescriptions
  !(EHealthSystem in (s.dsh_sc_used0))
}


pred EHealthSystem_remove_prescription_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) - EHealthSystem) + EHealthSystem)
  (sn.EHealthSystem_prescriptions) =
  ((s.EHealthSystem_prescriptions) -
     (s.EHealthSystem_in_p -> s.EHealthSystem_in_m1))
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

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.EHealthSystem_add_interaction) or
    sn.(s.EHealthSystem_add_patient) or
    sn.(s.EHealthSystem_remove_interaction) or
    sn.(s.EHealthSystem_add_prescription) or
    sn.(s.EHealthSystem_add_medication) or
    sn.(s.EHealthSystem_remove_prescription) or
    !({ s.EHealthSystem_add_interaction_pre or
          s.EHealthSystem_add_patient_pre or
          s.EHealthSystem_remove_interaction_pre or
          s.EHealthSystem_add_prescription_pre or
          s.EHealthSystem_add_medication_pre or
          s.EHealthSystem_remove_prescription_pre }) and
      s = sn }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}




