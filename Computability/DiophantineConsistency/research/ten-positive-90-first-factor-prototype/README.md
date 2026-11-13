# Exact 90 first-factor recipe and conditional residual

`TenPositive90FirstFactor.first_recipe` evaluates the selected 90 Lean graph
first factor in an arbitrary commutative ring and identifies its exact
factored form. `residual_zero` proves the related ring residual is zero from
explicit first-coordinate and first Pell-norm identities; the transport
substitution is still a separate hypothesis to be bound at a valuation.
These are conditional ingredients, not an 80-to-90 graph equivalence or an
iPRA theorem.

The accepted guarded check is `observations/first-attempt02/`, object
`/tmp/tenpositive-90firstfactor-juvdji4p/Direct90FirstFactor.olean`, SHA-256
`3216dfa5676e4702265fd75444e500f983ca353ee08b38d583f92ec3356169d6`.
Attempt01 produced an object but was rejected because of an unused-simp
warning; it is not the accepted check. The receipt pins selected direct
90-graph objects and inherits project/package, dynamic-library and historical
transitive source-object boundaries.
