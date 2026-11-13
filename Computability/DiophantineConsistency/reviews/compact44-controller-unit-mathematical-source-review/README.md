# Source review: conditional compact44 controller unit

Reviewed the source in commit `3a5f90046c`, including
[`gamma_unit` and `gamma_unit_nat`](../../research/ordinary12-ipra-bridge/compact44-controller-unit-prototype/ArithmeticConstructionUnitCompact44.lean),
the imported `ArithmeticControllerLift.lte` argument, the compact controller
data's cast and oddness statements, and the author compiler receipt. No defect
was found in the inspected mathematical argument. This is a source review and
finite external calculation, not an independent Lean replay or authenticated
transitive source closure.

For arbitrary model elements `K,m,e`, the first theorem **assumes** the
displayed residue of `K` and constructs an inverse of the stated `Gamma`
modulo `590069 * 581197^(m+1)`. Both the congruence-of-powers theorem and the
iterated Frobenius theorem use model Σ₁ induction with definable matrices;
the exponent-lifting dependency likewise quantifies over model exponents and
uses model Σ₁ induction. The proof therefore covers nonstandard `m,e` under
its stated IΣ₁-model hypotheses; it does not merely iterate over standard
natural numbers. `lte` uses oddness of `581197`, not an additional
unmentioned primality assumption.

The `q²−1` step is handled through `sub_one_res`, whose hypotheses require
the residue itself to be at least 1 and less than the modulus. The computed
`q²` residue is `201792753151`, which meets both bounds; this correctly
handles natural truncated subtraction. After the finite power identity gives
`Gamma^581196 = 1 + (590069*581197)*v`, lifting yields the required congruence
modulo the model-dependent power. The selected inverse exponent
`581196*581197^m - 1` is justified by a positivity proof before subtraction.
The `gamma_unit_nat` client transfers its explicit standard-natural remainder
premise through `cast_mod_eq` and applies the same model theorem.

[`audit.py`](audit.py) independently recomputes the displayed finite
residues, Frobenius identity, positive subtraction remainder and unit-power
identity with modular exponentiation. It verifies point-in-time source and
receipt hashes before and after and rejects optimized Python. This calculation
does not establish that the kernel residue premise holds, that the displayed
`Gamma` is the actual rank variation, or that particular graph witnesses
exist. The separate symbolic-kernel residue theorem was compiled on a
different provider; a same-provider join must be checked separately. Nor does
this theorem bind retained gzip or displayed coefficients or prove an iPRA
derivation. The single-author compile's direct-object snapshot, historical
provider and inherited package/transitive/dynamic/between-check limitations
remain as documented in its receipt.
