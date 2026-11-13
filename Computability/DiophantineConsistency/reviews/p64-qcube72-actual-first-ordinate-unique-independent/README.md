# Independent review: actual two-zero first-ordinate uniqueness

**PASS within captured-provider scope.**
[`same_k`](../../research/p64-qcube72-actual-first-ordinate-unique-draft/FreeMainActualFirstOrdinateUnique.lean)
assumes an arbitrary natural port tuple p, two positive valuations in an
arbitrary IΣ₁ model, an actual 72-graph zero for each at that same p, and
matching X,Y,c. It concludes equality of `v 10+v 11` and `w 10+w 11`.
It does not require fixed compact ports, equal q, a `3|q` condition, or
assume the desired equality of k. Neither graph zero's existence is asserted.

The checked first-index extraction supplies a first Pell index on each zero.
The X,Y equalities make the Pell base identical; positive q and the positive
seventh coordinate give `1≤Y`. Matching c gives the two interval equations;
positivity of coordinates 10 and 11 supplies `0<eta<k` on each side. The
previously checked generic first-ordinate lemma then yields the desired
k equality. Its separate [independent review](../p64-qcube72-first-ordinate-unique-independent/README.md)
explains the interval/growth argument and index-zero scope.

Attempt01's retained result and log match their temporary originals, record
Lean exit 0, no resource stop and the expected axiom report. The output
object and the three direct captured providers match their pinned hashes.
Independent [check.py](check.py) ran exit 0 and rechecked all 252 captured
provider, companion and shadow guards; [result.json](result.json) records
its output. No Lean replay or transitive/dynamic ancestry audit was run;
sampled resource-monitoring limits are inherited. This theorem by itself
does not establish a reverse witness map or equation equivalence.

Checker SHA-256
`b02ff95a769691f672063704c52c9299785ad4c6cb7c0a94aefc659aa81940f5`;
result SHA-256
`f0d9b19c1dfa79949cd53e1cbbee3b750dcf42807f396c60c57075b4b45a61eb`.
