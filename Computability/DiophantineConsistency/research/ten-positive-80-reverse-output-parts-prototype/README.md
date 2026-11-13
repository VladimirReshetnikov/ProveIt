# Exact 80 output from coherent scalar parts

`TenPositive80ReverseOutputParts.output_zero` is an arbitrary-commutative-ring
theorem for the **actual selected 80 Lean graph**. If its evaluated e, a, q,
v and z equal the explicitly supplied same τ,f,I,u,y,M parts and the
auxiliary Pell norm holds, the graph output evaluates to zero. It rewrites
the previously checked exact graph `output_eval` and applies the separate
factored cross-product identity. The theorem supplies no valuation, positive
coordinates, port calibration, halt implication or iPRA result; all of its
part equalities are explicit hypotheses.

Accepted guarded check `observations/parts-attempt02/` produced
`/tmp/tenpositive-80reverseoutputparts-rgoz2hbb/Direct80ReverseOutputParts.olean`,
SHA-256 `a74ef818061432bddc4914aea57c52e3e08e705ffb385ccf4fe6b387ce07b33e`.
Attempt01 failed because a transitive ReverseCarrier object was missing from
the search path; attempt02 adds and pins it. The two direct source imports
are resolved, pinned, and rechecked before/after. This does not assert a
complete transitive source-object, project/package or dynamic-library audit.
