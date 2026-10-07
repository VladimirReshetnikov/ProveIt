# Exact bounded companion for Report287

This Python-standard-library companion provides deterministic, exact finite
regression checks for the written arguments. It is not a proof assistant, a
construction of the huge-scale words, or an optimizer for the energy infimum.
It runs offline and neither installs software nor executes the bundled Lean
snapshots. All energy sums use counting measure and ordered quadruples.

## Run

From the report directory:

```sh
python3 -I -B tests/test_build.py
python3 -I -B tests/test_companion.py
python3 -I -B companion/exact_checks.py
python3 -I -B -O companion/exact_checks.py
```

The diagnostic CLI accepts no arguments. Its JSON output is byte-identical in
normal and optimized modes. Both test files can also be run with `-O`. The
report-level `build.py reproduce` command stages all sources externally, runs
all three commands in both modes, checks unchanged byte inventories, builds the
PDF, and packages a deterministic archive. See the report README for that
workflow and its system requirements.

## Checks and public routines

- `additive_energy`, `respected_energy`, and `energy_ratio` use cyclic or graph
  convolution with exact rational weights. Tests compare them with independent
  four-index enumeration. `full_group_energy` independently uses increment
  histograms
- `four_window_certificate` checks the `44 -> at most 32` argument and
  `M=A+B`. The fixed diagnostic enumerates all 6,497 four-image words for
  moduli 7 and 8
- `classify_small_words` exhausts the full word spaces for `N=1,...,5` and the
  7,776 words with `a(0)=0` for `N=6`: 11,189 tested words in total. Subtracting
  the constant `a(0)` preserves every respected quadruple. Counts and all
  small-modulus histogram bounds are checked, including the parity exception
- `relative_energy_certificate` accepts a same-cyclic-target word for `N<=64`.
  It scans consecutive middle relations. A failure at `N>=7` returns a
  four-point indicator witness with ratio at most `8/11`; for `N<=6` a uniform
  witness is used. Otherwise it recovers an affine or parity representation.
  General maps receive only a witnessed upper bound, with `exact_r=null`.
  Only the affine and parity branches report the proved exact values `1` and
  `3/4`. The scan and representation recovery take `O(N)` arithmetic
  operations; no claim of linear bit complexity or of linear complexity for
  the separate weighted-energy routines is made
- `parity_identity` checks the rational sum-of-squares identity. Fixed checks
  cover 132 rational/uniform examples across six even moduli, 44 uniform
  equality cases and their `N/2` affine-agreement bounds. A one-point defect
  on `Z/8Z`, witnessed on `{0,1,2,3}`, has energies `32/44`; this is an upper
  witness, not a computation of its exact infimum
- `check_partial_domain_caveat` verifies the Sidon support `{0,1,3}` in
  `Z/7Z`: all 15 supported ordered additive quadruples are trivial, so every
  supported map has relative coefficient one. The values `(0,0,1)` have no
  ambient affine extension. Tests check all 343 image assignments on that
  support, illustrating why the full-domain hypothesis matters
- `graph_convolution_certificate` checks the disjoint inside/outside families,
  `E >= A^4/N+B^4/M`, and the interval sumset bound. The Holder comparison
  accepts a rational `t` with `N*t^3>=M` and cross-multiplies throughout; no
  irrational cube root is evaluated. The default run checks 12 mass examples
  and an algebraic Holder equality example
- `deletion_certificate` checks arbitrary finite retained, covered and kept
  sets with `H intersect D subset C`. The default run covers all 1,863
  admissible triples in a five-point model. In 1,842 of them, deleted points
  belong to `H`. The equality example has three such points and makes clear
  why they cannot be omitted from the local count
- `finite_surrogate` uses only `E=8,16,32`, with rational `u` and `gamma=u^3`,
  so `eta=(u^-8-1)^3` is rational. It checks the rounded alphabet, loss
  coefficient, image budget, exact fixed-loss square identity, finite loss
  grid, and rounded density inequalities. It also checks the original
  alphabet's `3/16` bound and, for `E>=16`, its improved `3/8` bound. The
  routine does not claim that the `3/8` bound holds at `E=8`. A weaker rational
  constant using `8` replaces `e^2` only in the diagnostics; the sharper
  `e^2` statement is proved in the manuscript. Its sample `N` serves only
  rounding tests and is not claimed to meet the theorem's enormous
  long-progression/width thresholds
- `target_respected_energy`, `abelian_small_certificate` and
  `abelian_parity_identity` add bounded examples with targets `Z` and `Z/MZ`.
  They test 5,460 words using labels `{0,1,2}` on domains `N=1,...,6`, and
  40 exact parity identities. They include non-affine `N=2` integer-target
  parity, the `93/125` bound at `N=5`, both `N=6` histogram cases, and a
  division-free even normal form whose step is not divisible by two. These
  checks do not establish arbitrary-group coverage and do not assert the
  same-target `8/11` classification for arbitrary abelian targets

The manuscript supplies the universal proofs, nonvacuity thresholds,
all-weight statements, arbitrary retained-domain argument, arbitrary abelian
extension, and transfer of the named source predicates. The code never
constructs the actual exponent `E_d=2^(2^(d+8))`.

## Bounds, failure behavior, and source evidence

- General energy routines use `1<=N<=16`; the local certificate scan allows
  `1<=N<=64`. Small-word enumeration uses `N<=6` and at most 50,000 words
- Public rational inputs are exact built-in integers or `Fraction`, with at
  most 128 numerator/denominator bits. Booleans, floats, numeric strings,
  subclasses, negative weights, duplicate set points, iterators, malformed
  words, and zero weights for a ratio are rejected before enumeration
- Deletion models use at most eight points. Surrogate inputs restrict `E` to
  the three listed values and `u` to numerator/denominator sizes at most eight
  bits. Integer target labels lie in `[-256,256]`; target cyclic moduli are
  at most 32
- Gates use explicit exceptions and remain live under `python -O`. No random
  input, floating-point arithmetic, network call, or symbolic/numerical
  optimizer is used
- Provenance tests hard-code all four bundled Lean record dictionaries and
  verify raw byte lengths, raw SHA-256, Git blob SHA-1, canonical-base64
  SHA-256, pinned commit/URLs, exact record count, and exact snapshot names.
  External references remain metadata and are covered by the report's
  distribution manifest. Hash verification is source evidence, not a Lean
  build or a formalization of Report287
