# Independent review: two 72 zeros at the same scale

**PASS within captured-provider scope.**
[`two_zero_no_old_gamma`](../../research/p64-qcube72-two-zero-scale-obstruction-draft/FreeMainTwoZeroScaleObstruction.lean)
quantifies over arbitrary natural K and two positive valuations in an IΣ₁
model, each an actual 72 graph zero at the same `compactPorts K`. It assumes
`3|q` for the first valuation and equality of X, Y, c and k across the two.
It concludes there is no model element gamma satisfying the displayed old
carrier for the second valuation; gamma is not required positive.

The proof applies the checked generic scale-rigidity theorem to each zero's
extracted main index/root/carrier, obtaining the same h. It separately uses
the checked fixed-port ranked-main theorem and strict ordinate monotonicity
to identify the two graph ranks. Equal k and Y then transfer any proposed
second old carrier to the first, contradicting the first zero's checked
no-gamma theorem. It does not require equal q values and does not assert
that either zero exists or give an unconditional 72-to-76 result.

The retained attempt02 log/result match the temporary originals, with
recorded Lean exit 0, no stop and the expected axiom report. The output
object and both direct provider identities match their recorded hashes.
Independent [check.py](check.py) ran exit 0 and rechecked all 32 direct
input, companion and shadow guards; [result.json](result.json) records the
result. Attempt01 failed and was not used as proof evidence. No Lean replay
or transitive/dynamic ancestry audit was run; sampled monitoring limits are
inherited.

Checker SHA-256
`7c9fdb5c65224056ff45b46f78821a49b7ba67354bfff75674ca24ab90e14e1c`;
result SHA-256
`4d2b0da658853e0641f41f107668217a596381828b807a96784a7b21eb5d9619`.
