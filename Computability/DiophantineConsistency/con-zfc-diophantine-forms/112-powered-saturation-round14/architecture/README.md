# Shared-factorial and derived-range architecture

## Recommended completed endpoint

`derived16_cantor/natural/equation.json` is the complete quadratic-residual
definition of a sum-of-squares quartic in **349 nonnegative integer
unknowns**. `expanded_polynomial.json` gives all 12768 literal integer
coefficients; the coefficient height is 86915503. The absence of natural
zeros is equivalent to no finite C222 refutation, hence to Con(ZFC) with
the inherited ordinary C222/ZFC calibration. This does not prove
consistency or claim a new Lean endpoint.

The two new structural ingredients are:

1. Reuse one small factorial t! for pairwise-coprime proof-label weights
   and for reciprocal CRT moduli. This removes the old enormous carrier.
2. Bound a whole polynomial expression by a prime-power binomial range,
   instead of adding a ninth bounded local witness column.

The supporting hybrid theorem combines reciprocal moduli with amplified
prime-power decoding. A carrier/factorial floor allows amplification K=2R
rather than 8388608R, avoiding its huge literal coefficient.

## Proof order

1. `HYBRID_PROOF.md`: reciprocal prime-power bounded-universal elimination,
   exact small factorial and noncircular digit/radix bootstrap.
2. `FACTORIAL_CARRIER_PROOF.md`: complete label separation, Horn-flow
   soundness modulo the truth unit, positive-state cancellation, and
   constructive padded-proof completeness.
3. `DERIVED_LABEL_RANGE_PROOF.md`: the final derived-expression range,
   separate carry budget, and 349-variable endpoint.

The supplied older manuscripts are explicitly credited by these proofs
and pinned in `SOURCE_BINDING.json`. No K215 or Jones universal polynomial
is used by this direct branch. No global size optimality is asserted.

## Literal comparisons

| Directory | Natural unknowns | Degree | Monomials | Height |
|---|---:|---:|---:|---:|
| carrier_hybrid_cantor | 360 | 4 | 7343 | 83853107 |
| carrier_hybrid_shell | 361 | 4 | 7282 | 7002692 |
| factorial16_cantor | 350 | 4 | 11472 | 86523090 |
| factorial16_shell | 351 | 4 | 14871 | 10855087 |
| derived16_cantor | 349 | 4 | 12768 | 86915503 |
| derived16_shell | 351 | 4 | 16193 | 15317516 |

Other directories are preserved intermediate or horizon-constant
experiments, not stronger claims. The smaller-variable endpoints increase
support relative to the earlier 363-natural reciprocal equation.

## Exact verification

`REPRODUCTION.json` records byte-identical regeneration of all 12 final
endpoint files in normal and Python -O mode, and same-process shell/Cantor
source-order tests. Every endpoint's natural/VERIFICATION.json records the
independent expansion of each rational nonnegative restoration certificate,
all monic substitutions, and the complete collected quartic.

`SEMANTIC_CHECKS.json` records 361200 one-sided range cases, 32 constructive
CRT tests, 10 derived-polynomial range tests, 600 proposed factorial values,
47904 Horn-rule multisets and specific negative controls. These finite tests
are regression evidence, not an unbounded theorem or a consistency test.

From the workspace root, reproduce the recommended endpoint:

    PYTHONDONTWRITEBYTECODE=1 python diophantine_zfc_round14/architecture/build_derived_label_range.py --output NEW_EMPTY_DIRECTORY

Use `--syntax xx0` for the shell companion. For the local-slack predecessor,
use build_factorial_carrier.py, default horizon minimum 16; the original
factorial_carrier_* snapshots specifically require --horizon-minimum 32.

The builders import only inspected frozen input modules from the supplied
intake tree and write only to the explicit output path. Preserve that
relative intake layout or adapt its declared path before replay. There are
no repository writes, uploads, subprocess installs or network operations.
