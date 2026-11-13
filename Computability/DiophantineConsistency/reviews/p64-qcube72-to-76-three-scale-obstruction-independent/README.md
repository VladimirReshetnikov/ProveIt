# Independent review: 72-to-76 obstruction at equal X,Y,c

**PASS within captured-provider scope.** The checked
[`no_fixed_scale_target`](../../research/p64-qcube72-to-76-three-scale-obstruction-draft/FreeMain72To76ThreeScaleObstruction.lean)
is quantified over arbitrary IΣ₁ models, natural K, and two valuations. It
assumes actual positive 72 source and 76Y target zeros at the same fixed
`compactPorts K`, divisibility `3|q` for the source, and equality of X,Y,c.
It concludes False. Equal q and equal k are not premises; neither zero's
existence is asserted.

The proof constructs the specific positive forward 72 target by updating
only the 76Y coordinate 13, verifies its graph zero and obtains its old
carrier with the original target coordinate 13 as gamma. This update retains
X,Y,c. The separately reviewed arbitrary-port actual first-ordinate theorem
then derives the source/updated-target k equality from the two 72 zeros and
the three assumed equalities. The checked two-zero no-gamma theorem applies
with that derived k equality, producing the contradiction. This is a checked
all-model composition conditional on those premises; it does not exclude a
76Y witness with any of X,Y,c changed and does not disprove the existential
reverse implication.

Attempt01's retained result/log match their temporary originals and record
Lean exit 0, no resource stop and the expected axiom report. The output
object and all three direct captured providers match their pinned hashes.
Independent [check.py](check.py) ran exit 0 and rechecked 112 direct,
companion and shadow guards; [result.json](result.json) records the output.
No Lean replay or transitive/dynamic ancestry audit was run; sampled resource
monitoring limits remain inherited.

Checker SHA-256
`f743e320be02284078819326cd531cbdd4307c2b75bb8112e8240c2068c4ec0d`;
result SHA-256
`3b61c4212c0c85b4ca4d3e2926433293a293906e129722a136fab93d7eec17ab`.
