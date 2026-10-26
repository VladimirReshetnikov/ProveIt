# Attribution and scope

New analysis, polynomial circuits, proofs and verification work were prepared
with AI assistance on 25 October 2026 for Vladimir Reshetnikov.

The compact parent is the incoming ProveIt package
`ConZFC_Lucas_Corrections_and_Witness_Elimination_2026-10-25.zip`, at the inspected
commit `7a8da414376a80b90ecf799f37ceb26fb9ac674e`. Its complete compact component
is retained under `upstream_lucas/`. The projection-before-denominator method
and the 80/338 comparison circuit are retained from
`ConZFC_Cofinal_Witnesses_Centered_Carriers_2026-10-25.zip` as
`parent_cofinal_proof.md` and `parent_q1_bv.json`.

The polynomial-ring checker implementation is adapted from that cofinal
component's `positive/verify.py`, copied as `parent_verify_reference.py`.
The new literal cuts, leading forms, mutation list, producer and unbounded
proof are specific to this component. No literature-wide priority is claimed.

The inherited compact encoding ultimately uses the native compiler and K215
refutation calibration. This component changes the arithmetic architecture;
it does not claim to remove that ancestry or newly formalize the endpoint.

Inherited license files and attribution notices remain under
`upstream_lucas/parent/licenses/`.
