# Source and proof boundaries

All upstream references are pinned to ProveIt commit
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.

`upstream_sources.json` maps each copied upstream file to its full repository
path and SHA-256 digest. The Hilbert-tenth proof notes and compiler sources
were also checked against Git blob SHA-1 identifiers from the pinned tree.
Use this prefix with any recorded repository path:

<https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/>

## Immediate inherited mathematics

- `FIXED_RAW_UNIVERSAL_75_PROOF.md`: native tableau, arithmetic compiler, and
  ordinary-input acceptance framework.
- `complete75_half_binomial_compiler.md`: the exact modified compiler and mask
  conventions used here.
- `complete85_auxiliary_bezout_projection.md`: the normalized 85-operation
  positive-variable parent and auxiliary-quotient projection.
- `complete84_scaled_strong_output.md`: positive discriminant scaling and the
  coefficient-sharing identity.
- `PELL_RELAXED_AUXILIARY_PROOF.md`: the local strong-rank lemma.
- `complete75_reversed_auxiliary89.md`: the signed auxiliary step-down argument.
- `K215_VERIFICATION_README.md` and `KEndpoint215.lean`: inherited literal-machine
  calibration and external proof-assistant endpoint.

The full dependency developments remain in the pinned repository; the copies
here are immediate sources for review, not a standalone Lean or Rocq project.

## New work in this contribution

1. A four-state input eraser and direct two-sided normalization of literal K215.
2. The two-blank-margin extension of the helical completeness argument.
3. A closed coefficient recipe, an exact factored window count, and evaluation
   of the layout scalars `b = 5^35`, `L = 5^36`, `d = 5^71`.
4. Fixed-input elimination, the affine unit guard, and reconstruction of the
   deleted input witnesses before invoking the parent acceptance theorem.
5. The 73-operation circuit and its exact degree proof.
6. The 44-integer-variable substitution and explicit 83-variable quadratic system.

`DIRECT_NORMALIZER_PROOF.md` and `COEFFICIENT_RECIPE.md` give supporting
derivations. `FIXED_INPUT_AUDIT.md` records a separate mathematical review of
the input-elimination argument. The final integrated treatment, including
clarifications made after that review, is `../zfc_diophantine.tex`.

The review was performed by a separate agent within this research collaboration.
It is not an external human review or a proof-assistant kernel certificate.
The new theorem is supported by the mathematical proof and finite executable
checks. No claim of a newly completed Lean/Rocq proof, globally minimal equation,
or unconditional proof of ZFC consistency is made.
