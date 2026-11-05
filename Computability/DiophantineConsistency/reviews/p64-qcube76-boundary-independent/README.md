# Independent review of the 76 transport boundary packet

On 2026-11-04 this read-only review inspected the changed-port and conditional
fixed-port constructions in
[`p64-qcube76-boundary-obstruction`](../../research/p64-qcube76-boundary-obstruction/README.md).
The reviewed `check.py` SHA-256 was
`5a5eb2e8c4197df9faad8926be9842c1cf5e99c74654b6cec3ee7f8b06eaf8cf`.

For the changed-port construction, `C>0` and `alpha>0` imply `q−F≥2`, so
the stated `delta` is positive. The `MC` adjustment contributes exactly
`delta*(q²−1)` to `R`, since `q−1=beta*J`; the new transport vanishes and
the proposed positive witnesses and natural ports have the required signs.
For the fixed-port construction, the stated divisibility makes the shift of
`z` integral, the gap and transport are unchanged, and the new strict-bound
expression is `1−F−C<0`. Both constructions preserve all five residuals
and the output by inspection of the pinned graph dependencies.

An independent execution of the pinned checker under its documented Python
flags exited 0 and reproduced 482 changed-port cases and 460 fixed-port cases,
with zero sampled seed zeros. The checker also rejects optimized Python,
important because it uses assertions. These finite checks do not establish
the conditional hypotheses for an actual zero, a full counterexample to
existence equivalence, a Lean theorem, or the ancestry and external-file
bindings of the iPRA endpoint. The related
[generalized fixed-port analysis](../../research/p64-qcube76-fixed-port-boundary/README.md)
contains a separate exact polynomial identity check.
