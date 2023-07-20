---- MODULE MC ----
EXTENDS musical_chairs, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3, p4
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT definitions PLAYERS
const_152903167283697000 == 
{p1, p2, p3, p4}
----

\* MV CONSTANT definitions CHAIRS
const_152903167283698000 == 
{c1, c2, c3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_152903167283699000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1529031672836100000 ==
OneMorePlayerThanChairs
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1529031672836101000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1529031672836102000 ==
ExistentialLiveness
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1529031672836103000 ==
InfiniteLiveness
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1529031672836104000 ==
FiniteLiveness
----
=============================================================================
\* Modification History
\* Created Thu Jun 14 23:01:12 EDT 2018 by amin
