---- MODULE MC ----
EXTENDS library, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1, b2, b3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2, m3
----

\* MV CONSTANT definitions BookID
const_157817747930832000 == 
{b1, b2, b3}
----

\* MV CONSTANT definitions MemberID
const_157817747930833000 == 
{m1, m2, m3}
----

=============================================================================
\* Modification History
\* Created Sat Jan 04 17:37:59 EST 2020 by bandali
