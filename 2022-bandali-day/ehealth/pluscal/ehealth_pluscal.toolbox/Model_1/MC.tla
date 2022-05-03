---- MODULE MC ----
EXTENDS ehealth, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
mm1, mm2, mm3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
pp1, pp2, pp3
----

\* MV CONSTANT definitions Medications
const_15939921305582000 == 
{mm1, mm2, mm3}
----

\* MV CONSTANT definitions Patients
const_15939921305583000 == 
{pp1, pp2, pp3}
----

=============================================================================
\* Modification History
\* Created Sun Jul 05 19:35:30 EDT 2020 by bandali
