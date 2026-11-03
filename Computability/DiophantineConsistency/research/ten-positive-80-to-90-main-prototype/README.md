# Actual 80 zero gives an exact 90-graph main-factor zero

`TenPositive80To90Main.graph_main_factor` proves that an actual positive
80-graph zero in a model of IΣ₁, with the explicit symbolic β, low-mask, and
shifted-high-mask port equalities, yields positive fresh η, ζ, γ and a natural
h for which the selected 90 Lean graph's **main factor** evaluates to zero.
The port p₁ is arbitrary: no external K0 byte string is identified here.

The precise positive 12-input valuation is

    [v₀, v₁, v₂, 1, 1, v₅, v₆, 1, η, ζ, 1, γ+h].

The η, ζ, γ and h are extracted together from one fresh unscaled source
construction, and the proof explicitly identifies the old graph rank with
the same actual 80 graph rank. The four ones are positive placeholders for
coordinates which the main factor does not use; no claim is made that this
particular tuple zeros the other factors. They must be replaced by compatible
positive witnesses before any whole-graph source existence or equivalence
can follow. In particular this is not a graph-to-halt or internal iPRA
endpoint and does not bind an external 80/90 coefficient/PDF to p₁.

The check composes the fresh main-offset theorem, exact 90 main-factor
recipe, and the two unscaled Pell identities through the model difference
ring. `observations/fixeddigits-attempt07/` is the accepted guarded check;
the resulting object is `/tmp/tenpositive-80to90main-7nccdbz1/Direct80To90Main.olean`,
SHA-256 `d1a7e37d24f475f7546394a467fdc58462b4752a7c80daf3e958c0435f443d54`.
Attempts 01–03 are unfinished exploratory snapshots containing `sorry` and
were rejected by the runner; attempts 04–05 have cast/elaboration errors;
attempt06 produced an object but was rejected for an unused-simp warning.
None is an accepted proof. The successful source has no `sorry` and the
receipt records selected tool, source, runner and provider pins plus resource
samples. The inherited project/package provider, transitive historical
source-to-object and dynamic-library limitations remain.

The exact 90 main recipe is checked separately in
`research/ten-positive-90-main-recipe-prototype/`; its first attempt exceeded
the 3-GiB Lean limit when it expanded the polynomial. The accepted proof
preserves the factored expression and no failed run is treated as evidence of
that identity.

A fresh self-pinning `run-v2.py` rebuild selects the corrected offset
producer `/tmp/tenpositive-80freshmainoffset-zbew9euo/`, whose v2 receipt
individually pins its direct `ArithmeticPellCongruences.olean` import. The
accepted dependent replay is `observations/v2-attempt01/` and its object
`/tmp/tenpositive-80to90main-36rqgq9d/Direct80To90Main.olean` has SHA-256 `d1a7e37d24f475f7546394a467fdc58462b4752a7c80daf3e958c0435f443d54`, identical to the earlier object. These
selected-edge checks do not expand the inherited transitive source-object,
package or dynamic-library coverage.
