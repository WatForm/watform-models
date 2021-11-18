/* The EHealth case study - Alloy model (using the ctlfc_path library)

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the EHealth Alloy model.

The EHealth Alloy model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The EHealth Alloy model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the EHealth Alloy model.  If not, see
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

The EHealth Alloy model is an adaptation of the TLA+ one by Bandali,
itself based on the snippets presented by
Prof. Ostroff~\cite{ostroff2017}.

This model has appeared in the following publications:

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

open ctlfc_path[State]

sig Patient, Medication {}

sig State {
  patients: set Patient,
  medications: set Medication,
  interactions: Medication set -> set Medication,
  prescriptions: Patient lone -> set Medication,
  in_patient: lone Patient,
  in_medication1: lone Medication,
  in_medication2: lone Medication
}

pred pre_add_patient [s: State] {
  !(s.in_patient in s.patients)
}
pred post_add_patient[s, s': State] {
  s'.patients = s.patients + s.in_patient
  s'.medications = s.medications
  s'.interactions = s.interactions
  s'.prescriptions = s.prescriptions
}
pred add_patient[s, s': State] {
  pre_add_patient[s]
  post_add_patient[s, s']
}


pred pre_add_medication[s: State] {
  !(s.in_medication1 in s.medications)
}
pred post_add_medication[s, s': State] {
  s'.medications = s.medications + s.in_medication1
  s'.patients = s.patients
  s'.interactions = s.interactions
  s'.prescriptions = s.prescriptions
}
pred add_medication[s, s': State] {
  pre_add_medication[s]
  post_add_medication[s, s']
}

pred pre_add_interaction[s: State] {
  s.in_medication1 in s.medications
  s.in_medication2 in s.medications
  s.in_medication1 != s.in_medication2
  !(s.in_medication2 in s.interactions[s.in_medication1])
  all p: s.patients |
    !((p->s.in_medication1 in s.prescriptions) and
      (p->s.in_medication2 in s.prescriptions))
}
pred post_add_interaction[s, s': State] {
  s'.interactions = s.interactions + { s.in_medication1->s.in_medication2 +
                                       s.in_medication2->s.in_medication1 }
  s'.patients = s.patients
  s'.medications = s.medications
  s'.prescriptions = s.prescriptions
}
pred add_interaction[s, s': State] {
  pre_add_interaction[s]
  post_add_interaction[s, s']
}

pred pre_add_prescription[s: State] {
  s.in_patient in s.patients
  s.in_medication1 in s.medications
  !(s.in_medication1 in s.prescriptions[s.in_patient])
  all m0: s.prescriptions[s.in_patient] | !(s.in_medication1 in s.interactions[m0] or
                                            m0 in s.interactions[s.in_medication1])
}
pred post_add_prescription[s, s': State] {
  s'.prescriptions = s.prescriptions + s.in_patient->s.in_medication1
  s'.patients = s.patients
  s'.medications = s.medications
  s'.interactions = s.interactions
}
pred add_prescription[s, s': State] {
  pre_add_prescription[s]
  post_add_prescription[s, s']
}

pred pre_remove_interaction[s: State] {
  s.in_medication1 in s.medications
  s.in_medication2 in s.medications
  s.in_medication1->s.in_medication2 in s.interactions
}
pred post_remove_interaction[s, s': State] {
  s'.interactions = s.interactions - { s.in_medication1->s.in_medication2 +
                                       s.in_medication2->s.in_medication1 }
  s'.patients = s.patients
  s'.medications = s.medications
  s'.prescriptions = s.prescriptions
}
pred remove_interaction[s, s': State] {
  pre_remove_interaction[s]
  post_remove_interaction[s, s']
}

pred pre_remove_prescription[s: State] {
  s.in_patient in s.patients
  s.in_medication1 in s.medications
  s.in_patient->s.in_medication1 in s.prescriptions
}
pred post_remove_prescription[s, s': State] {
  s'.prescriptions = s.prescriptions - s.in_patient->s.in_medication1
  s'.patients = s.patients
  s'.medications = s.medications
  s'.interactions = s.interactions
}
pred remove_prescription[s, s': State] {
  pre_remove_prescription[s]
  post_remove_prescription[s, s']
}


pred init[s: State] {
  no s.patients
  no s.medications
  no s.interactions
  no s.prescriptions
}

pred next[s, s': State] {
  add_patient[s, s'] or
  add_medication[s, s'] or
  add_interaction[s, s'] or
  add_prescription[s, s'] or
  remove_interaction[s, s'] or
  remove_prescription[s, s']
}


fact {
  all s:     State | s in initialState iff init[s]
  all s, s': State | s->s' in nextState iff next[s,s']
  all s, s': State |
    s.patients = s'.patients and
    s.medications = s'.medications and
    s.interactions = s'.interactions and
    s.prescriptions = s'.prescriptions and
    s.in_patient = s'.in_patient and
    s.in_medication1 = s'.in_medication1 and
    s.in_medication2 = s'.in_medication2
    implies s = s'
}

pred reachablity_axiom {
  all s: State | s in State.(initialState <: *nextState)
}
pred operations_axiom {
  some s, s':State | add_patient[s, s']
  some s, s':State | add_medication[s, s']
  some s, s':State | add_interaction[s, s']
  some s, s':State | add_prescription[s, s']
  some s, s':State | remove_interaction[s, s']
  some s, s':State | remove_prescription[s, s']
}
pred significance_axioms {
  reachablity_axiom
  operations_axiom
}
run significance_axioms for 1 Patient,
                            2 Medication,
                            3 State,
                            3 PathNode

pred symmetry {
  ctlfc_mc[ag[{s: State | all m1, m2: Medication |
    m1->m2 in s.interactions iff
    m2->m1 in s.interactions}]]
}

pred irreflexive {
 ctlfc_mc[ag[{s: State | all m: Medication | not m in s.interactions[m]}]]
}

pred safe_prescriptions {
  ctlfc_mc[ag[{s: State | all m1, m2: s.medications, p: s.patients |
    m2 in s.interactions[m1] =>
      !((m1 in s.prescriptions[p]) and
        (m2 in s.prescriptions[p]))}]]
}

check safety_properties {
  symmetry
  irreflexive
  safe_prescriptions
} for 3
