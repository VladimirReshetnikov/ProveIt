# Source review: same-witness halt, first carrier and positive gamma

This is a **source-only** review, with no independent Lean replay or full
provider-closure audit. The reviewed final
`compact44-halt-first-gamma-prototype/CompactHaltFirstGamma.lean` has
SHA-256 `0c928eee0eeee3edd0c3786cca902b08e69fdff3c84032e237b5cc4de307ef71`.
The directly invoked positive-tail predecessor source has SHA-256
`54f8b4edcbf725c78dcb894ae89af8d21b78e040da6a6a748219f264053c2c56`;
the pointwise compact positive-gamma client source has SHA-256
`13dc3c1e4b78ea42a15f9d6e17bebcbf37336d9ac038fd21ee6450b86072774d`.
These source hashes do not independently authenticate compiled objects or
their complete ancestry.

`halt_first_gamma` has only the model-internal decimal215 halt as an explicit
starting assumption, apart from the `ORingStructure` and `IΣ₁` model. Its
conclusion retains the chosen definable Boolean controller and word, full
symbolic compact packing, rank calibration, positive shifted transport,
outer seed, positive auxiliary-tail data and first-carrier data. The local
instance binder for the word's Σ₁-definability follows an explicit conjunct
proving that property.

The new `GammaData` uses exactly the retained outer parameters `sY,eta,zeta`
and `gammaOld`, together with the **same** transport power `w`. Its proof
passes the already-unpacked `SeedRelations`, positivity of `sY` and
`gammaOld`, and the reversed already-unpacked `q*w=Exp.exp R` to the
pointwise positive-gamma theorem. It constructs an existential positive
graph `gamma` and a correction quotient satisfying both additive lift
equations, without reselecting the outer or auxiliary seeds or first-carrier
witness. The correction quotient is named `t` inside `GammaData`; it is not
the graph coordinate `t=f-1`. The graph gamma is also distinct from the
positive outer seed coordinate `gammaOld`. The auxiliary witness inside
`PositiveAuxData` and the first-carrier `r` remain separate existential
witnesses sharing the retained outer/transport data.

The source proves natural-number correction equations, not their evaluation
at the exact graph expression. It does not by itself construct the complete
positive valuation, prove the free-J graph zero, identify the symbolic ports
with retained coefficient/PDF bytes, or prove an iPRA derivation. The
successful author build and its direct guards are separate evidence; this
review does not establish a paired replay or full transitive, package or
dynamic provider provenance.
