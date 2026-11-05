# Independent review: first Pell ordinate uniqueness

**PASS within captured-provider scope.** In an arbitrary IΣ₁ model,
[`first_index_unique`](../../research/p64-qcube72-first-ordinate-unique-draft/FreeMainFirstOrdinateUnique.lean)
assumes the same B,Y,c, `1≤Y`, `c=kY+eta=k'Y+eta'`,
`0<eta<k`, `0<eta'<k'`, and `k=2*ycoord n B`,
`k'=2*ycoord n' B`. It concludes both indices and k values equal;
no graph-zero, compact-port or existence premise is hidden.

The checked growth helper gives `2*ycoord n B<ycoord m B` whenever
`n<m`, including n=0. Thus distinct indices force one k value to be
strictly more than twice the other. The interval inequalities give
`Y*k'<c<(Y+1)*k` and `Y+1≤2Y`, which rule out `2k<k'`; the symmetric
case is analogous. Under the full uniqueness hypotheses, index zero is in
fact impossible: its ordinate and k are zero, contradicting `0<eta<k`.
The helper's validity at zero and this vacuity are distinct observations.

The retained attempt02 result/log match their temporary originals, record
Lean exit 0 and no resource stop, and have exactly the three expected axiom
reports. The result object and direct `ArithmeticPellPowerRecovery` provider
match their pinned hashes. Independent [check.py](check.py) ran exit 0 and
rechecked all 232 recorded direct/companion/shadow guards;
[result.json](result.json) records its output. Attempt01 failed and is not
used as theorem evidence. No Lean replay was run; transitive/dynamic ancestry
and sampling limits remain inherited. This lemma alone does not establish a
72-to-76 witness map or a graph-zero existence statement.

Checker SHA-256
`054fbc6b389aba19de96d2a0373192e8c5b5128cb44ac94efb0602904e5eff6e`;
result SHA-256
`edb958bb94526479e181efc3b4f4897dfd42c41495a7aee46fff5694b4b9a689`.
