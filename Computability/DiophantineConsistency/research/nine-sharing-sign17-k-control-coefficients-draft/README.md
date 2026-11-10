# K 44-position control coefficient vector: source-only draft

The isolated generator derives 44 candidate natural coefficients for
positions 942–985 from the four symbolic control groups and externally
compares them with the pinned frozen array slice. The emitted Lean source
proposes to prove that these coefficients reproduce all four control sums
for arbitrary natural base and then substitute the result into the actual
ranked `rawWord` identity. The three sentinels remain separate, as in the
external recipe. Tile/control positions are disjoint; the sentinel at
exponent 1004 is not silently folded into the coefficient vector.

This is an uncompiled draft; the external comparison is not a Lean theorem
about the frozen array or a filesystem/gzip binding. No guarded run or
independent review exists for this source. Generator SHA-256:
`c66358a11a2cd7fbbb7248dbfe4d3462fba78059a04de37dd6e9b04a942b9f9f`;
source SHA-256:
`73ae2cbd7d3b970f1cc05a18e3772ca43db8983cb8c922c106d7c7aa3043b7b4`.
