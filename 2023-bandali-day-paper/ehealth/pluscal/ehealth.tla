------------------------------ MODULE ehealth ------------------------------
(* The EHealth case study - PlusCal model

Copyright (c) 2017 Jonathan Ostroff <jonathan@yorku.ca>
Copyright (c) 2017, 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the EHealth PlusCal model.

The EHealth PlusCal model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The EHealth PlusCal model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the EHealth PlusCal model.  If not, see
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

The EHealth PlusCal model is a port of the TLA+ one also by Bandali,
based on the snippets presented by Prof. Ostroff~\cite{ostroff2017}.

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

*)

EXTENDS Naturals, Sequences

CONSTANTS
  Patients,   \* set of all patients in the universe
  Medications \* set of all medications in the universe

(* --algorithm ehealth_pluscal
variables patients = {},
          medications = {},
          prescriptions = {},
          interactions = {};

define
TypeOK ==
    /\ patients \subseteq Patients
    /\ medications \subseteq Medications
    /\ prescriptions \subseteq patients \X medications
    /\ interactions \subseteq medications \X medications

\* Invariants

Symmetry == \A i_m1, i_m2 \in medications:
    <<i_m1, i_m2>> \in interactions <=>
    <<i_m2, i_m1>> \in interactions

\* A medication does not interact with itself
Irreflexive == \A i_m \in medications:
    <<i_m, i_m>> \notin interactions

\* All prescriptions are safe
\* i.e. do not have dangerous interactions
SafePrescriptions ==
    \A i_m1, i_m2 \in medications, i_p \in patients:
        <<i_m1, i_m2>> \in interactions =>
            ~ (<<i_p, i_m1>> \in prescriptions
            /\ <<i_p, i_m2>> \in prescriptions)
end define

process add_patient = "add_patient"
variable p \in Patients
begin
  a_p:
    if p \notin patients then
      patients := patients \union {p}
    end if
end process

process add_medication = "add_medication"
variable m \in Medications
begin
  a_m:
    if p \notin medications then
      medications := medications \union {m}
    end if
end process

process add_interaction = "add_interaction"
variables m1 \in Medications, m2 \in Medications
begin
  a_i:
    if
      /\ m1 \in medications
      /\ m2 \in medications
      /\ m1 /= m2
      /\ <<m1, m2>> \notin interactions
      /\ \A pat \in patients: ~ (<<pat, m1>> \in prescriptions
                              /\ <<pat, m2>> \in prescriptions)
  then
    interactions := interactions \union {<<m1, m2>>, <<m2, m1>>}
  end if
end process

process add_prescription = "add_prescription"
variables p \in Patients, m \in Medications
begin
  a_pr:
    if
      /\ p \in patients
      /\ m \in medications
      /\ <<p, m>> \notin prescriptions
      /\ \A m0 \in medications: <<p, m0>> \in prescriptions =>
           <<m0, m>> \notin interactions
    then
      prescriptions := prescriptions \union {<<p, m>>}
    end if
end process

process remove_interaction = "remove_interaction"
variables m1 \in Medications, m2 \in Medications
begin
  r_i:
    if
      /\ m1 \in medications
      /\ m2 \in medications
      /\ <<m1, m2>> \in interactions
    then
      interactions := interactions \ {<<m1, m2>>, <<m2, m1>>}
  end if
end process

process remove_prescription = "remove_prescription"
variables p \in Patients, m \in Medications
begin
  r_pr:
    if
      /\ p \in patients
      /\ m \in medications
      /\ <<p, m>> \in prescriptions
    then
      prescriptions := prescriptions \ {<<p, m>>}
    end if
end process

end algorithm; *)
\* BEGIN TRANSLATION
\* Process variable p of process add_patient at line 79 col 10 changed to p_
\* Process variable m of process add_medication at line 88 col 10 changed to m_
\* Process variable m1 of process add_interaction at line 97 col 11 changed to m1_
\* Process variable m2 of process add_interaction at line 97 col 31 changed to m2_
\* Process variable p of process add_prescription at line 113 col 11 changed to p_a
\* Process variable m of process add_prescription at line 113 col 27 changed to m_a
VARIABLES patients, medications, prescriptions, interactions, pc

(* define statement *)
TypeOK ==
    /\ patients \subseteq Patients
    /\ medications \subseteq Medications
    /\ prescriptions \subseteq patients \X medications
    /\ interactions \subseteq medications \X medications



Symmetry == \A i_m1, i_m2 \in medications:
    <<i_m1, i_m2>> \in interactions <=>
    <<i_m2, i_m1>> \in interactions


Irreflexive == \A i_m \in medications:
    <<i_m, i_m>> \notin interactions



SafePrescriptions ==
    \A i_m1, i_m2 \in medications, i_p \in patients:
        <<i_m1, i_m2>> \in interactions =>
            ~ (<<i_p, i_m1>> \in prescriptions
            /\ <<i_p, i_m2>> \in prescriptions)

VARIABLES p_, m_, m1_, m2_, p_a, m_a, m1, m2, p, m

vars == << patients, medications, prescriptions, interactions, pc, p_, m_, 
           m1_, m2_, p_a, m_a, m1, m2, p, m >>

ProcSet == {"add_patient"} \cup {"add_medication"} \cup {"add_interaction"} \cup {"add_prescription"} \cup {"remove_interaction"} \cup {"remove_prescription"}

Init == (* Global variables *)
        /\ patients = {}
        /\ medications = {}
        /\ prescriptions = {}
        /\ interactions = {}
        (* Process add_patient *)
        /\ p_ \in Patients
        (* Process add_medication *)
        /\ m_ \in Medications
        (* Process add_interaction *)
        /\ m1_ \in Medications
        /\ m2_ \in Medications
        (* Process add_prescription *)
        /\ p_a \in Patients
        /\ m_a \in Medications
        (* Process remove_interaction *)
        /\ m1 \in Medications
        /\ m2 \in Medications
        (* Process remove_prescription *)
        /\ p \in Patients
        /\ m \in Medications
        /\ pc = [self \in ProcSet |-> CASE self = "add_patient" -> "a_p"
                                        [] self = "add_medication" -> "a_m"
                                        [] self = "add_interaction" -> "a_i"
                                        [] self = "add_prescription" -> "a_pr"
                                        [] self = "remove_interaction" -> "r_i"
                                        [] self = "remove_prescription" -> "r_pr"]

a_p == /\ pc["add_patient"] = "a_p"
       /\ IF p_ \notin patients
             THEN /\ patients' = (patients \union {p_})
             ELSE /\ TRUE
                  /\ UNCHANGED patients
       /\ pc' = [pc EXCEPT !["add_patient"] = "Done"]
       /\ UNCHANGED << medications, prescriptions, interactions, p_, m_, m1_, 
                       m2_, p_a, m_a, m1, m2, p, m >>

add_patient == a_p

a_m == /\ pc["add_medication"] = "a_m"
       /\ IF p \notin medications
             THEN /\ medications' = (medications \union {m_})
             ELSE /\ TRUE
                  /\ UNCHANGED medications
       /\ pc' = [pc EXCEPT !["add_medication"] = "Done"]
       /\ UNCHANGED << patients, prescriptions, interactions, p_, m_, m1_, m2_, 
                       p_a, m_a, m1, m2, p, m >>

add_medication == a_m

a_i == /\ pc["add_interaction"] = "a_i"
       /\ IF /\ m1_ \in medications
             /\ m2_ \in medications
             /\ m1_ /= m2_
             /\ <<m1_, m2_>> \notin interactions
             /\ \A pat \in patients: ~ (<<pat, m1_>> \in prescriptions
                                     /\ <<pat, m2_>> \in prescriptions)
             THEN /\ interactions' = (interactions \union {<<m1_, m2_>>, <<m2_, m1_>>})
             ELSE /\ TRUE
                  /\ UNCHANGED interactions
       /\ pc' = [pc EXCEPT !["add_interaction"] = "Done"]
       /\ UNCHANGED << patients, medications, prescriptions, p_, m_, m1_, m2_, 
                       p_a, m_a, m1, m2, p, m >>

add_interaction == a_i

a_pr == /\ pc["add_prescription"] = "a_pr"
        /\ IF /\ p_a \in patients
              /\ m_a \in medications
              /\ <<p_a, m_a>> \notin prescriptions
              /\ \A m0 \in medications: <<p_a, m0>> \in prescriptions =>
                   <<m0, m_a>> \notin interactions
              THEN /\ prescriptions' = (prescriptions \union {<<p_a, m_a>>})
              ELSE /\ TRUE
                   /\ UNCHANGED prescriptions
        /\ pc' = [pc EXCEPT !["add_prescription"] = "Done"]
        /\ UNCHANGED << patients, medications, interactions, p_, m_, m1_, m2_, 
                        p_a, m_a, m1, m2, p, m >>

add_prescription == a_pr

r_i == /\ pc["remove_interaction"] = "r_i"
       /\ IF /\ m1 \in medications
             /\ m2 \in medications
             /\ <<m1, m2>> \in interactions
             THEN /\ interactions' = interactions \ {<<m1, m2>>, <<m2, m1>>}
             ELSE /\ TRUE
                  /\ UNCHANGED interactions
       /\ pc' = [pc EXCEPT !["remove_interaction"] = "Done"]
       /\ UNCHANGED << patients, medications, prescriptions, p_, m_, m1_, m2_, 
                       p_a, m_a, m1, m2, p, m >>

remove_interaction == r_i

r_pr == /\ pc["remove_prescription"] = "r_pr"
        /\ IF /\ p \in patients
              /\ m \in medications
              /\ <<p, m>> \in prescriptions
              THEN /\ prescriptions' = prescriptions \ {<<p, m>>}
              ELSE /\ TRUE
                   /\ UNCHANGED prescriptions
        /\ pc' = [pc EXCEPT !["remove_prescription"] = "Done"]
        /\ UNCHANGED << patients, medications, interactions, p_, m_, m1_, m2_, 
                        p_a, m_a, m1, m2, p, m >>

remove_prescription == r_pr

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == add_patient \/ add_medication \/ add_interaction
           \/ add_prescription \/ remove_interaction \/ remove_prescription
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Jul 05 16:15:40 EDT 2020 by bandali
\* Created Fri Oct 04 01:03:50 EDT 2019 by bandali
