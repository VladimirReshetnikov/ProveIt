# Report 299 exact companion

This is an offline, standard-library Python companion. It performs exact
rational/integer checks and bounded finite illustrations of mechanisms in the
written proof. It does not construct the theorem's balanced word, evaluate its
tower constant, compile Lean, execute upstream code, or establish an all-prime
or all-dimension theorem by experiment.

## Run

From the `Report299` directory, using Python 3.11 or later on POSIX with
no-follow directory-descriptor support:

    python -I -B -X int_max_str_digits=640 companion/exact_checks.py
    python -I -B -O -X int_max_str_digits=640 companion/exact_checks.py
    python -I -B -X int_max_str_digits=640 tests/test_companion.py
    python -I -B -O -X int_max_str_digits=640 tests/test_companion.py

The checker accepts no arguments, reads only the five pinned data files below,
and writes deterministic JSON to stdout. It does not write files or request
network access. The tests use temporary directories and subprocesses; they do
not change the report bundle. Ordinary, optimized, and read-only-copy checker
runs produce identical stdout. The standalone suite contains 35 test methods.

## What is checked

- 22 exact coefficient identities or sufficient monomial inequalities for a
  formal variable `K >= 1`: `R=4K`, `theta=1/(32K)`, `beta=9/(32K)`, the
  Hoeffding exponent denominator `512K^2`, square-root threshold `8192K^3`,
  the `7/8` union-bound logarithm margin, `t >= 32KR`, modal-selection mass
  comparisons, and the strict cover gap `1/2 - 5/16 = 3/16`
- 674 weighted graph-sum cases over prime moduli `2,3,5,7,11,17`, intervals
  of length at most three, alphabet size at most three, and weights in
  `{0,1,2}`. Cases are included only when `|E+E||S+S| <= N`. Each pair-sum
  energy is compared independently with the ordered-quadruple sum, and the
  exact integer inequality `N*energy >= mass^4` is checked. Dividing all
  weights by two gives 674 additional exact rational rescalings
- 258 checks that one, two, or five identical final-coordinate restrictions
  have the same simultaneous-additivity condition
- 12 zero-restriction-family cases on the entire field, not a short interval,
  and the same 12 cases for several different constant parallel restrictions;
  empty domains and zero weights are included
- 27 exact eightfold convolutions checking `N*T_8(E) >= |E|^16`, together
  with the arrangement exponent normalization
- 136 constant-cube cancellations and 32 arbitrary-vertex instances of the
  corrected all-ones identity in dimensions one through eight. Dimension
  zero is explicitly excluded from the cancellation claim
- 73 modal-colour-class selections, illustrating how the same input can give
  a smaller constant good domain; these are not theorem-scale witnesses
- 20,670 affine comparisons on 510 proper arithmetic-progression
  presentations over the fields of sizes three, five, and seven. All starts,
  directions, and possible lengths are considered, including 282 wrapping
  presentations and 30 proper zero-step presentations. Constants are bounded
  using the measured colour maximum; nonconstant affine maps by the alphabet
  size. These words are not claimed to have theorem-threshold balance

The coefficient checker never substitutes the actual
`K = 2^(2^(2^(k+9)))`. Its largest coefficients are ordinary small exact
powers, and it works with Python's integer-to-string safety cap set to 640.
The analytic inequalities for logarithms, the probabilistic existence
argument, the general Cauchy-Schwarz lemma, the source-level compatibility of
all fields, and the all-dimension/all-prime conclusion remain written proofs.

## Source identity and claim boundary

The checker pins these exact bundled data files by literal SHA-256 identities:

- `companion/certificate.json`
- `SOURCE_MANIFEST.json`
- `source_excerpts.json`
- `CURRENT_SOURCE_STATUS.json`
- `provenance/PROOF.md`

It checks 40 recorded complete-source identities and 28 compact, line-ranged
excerpts, including their text hashes and pinned URLs. It checks 34 literal
source anchors and the exact common-base inventory of five data fields and
eight proof fields. The selection field has two mathematical clauses; this
does not make nine proof fields. The contextual quantifier is universal over
common-base witnesses, whereas the constructor only establishes nonemptiness.

The proof pin is commit `130fca9b1131fd983bd0af27565d36e8dfd2865a` in
`VladimirReshetnikov/ProveIt`. The recorded later inspection at
`e40a57b9878f2b20636fe7d1acdc3b2e61796e87` has five matching core identities
(four independently rechecked in the mathematical audit). This is a dated
inspection, not a live branch claim. The audit's recorded SHA-256 is
`cec55c955738b6f965357d3d87ca5f8344f48fe51965709612a3e0c4422cd65c`.

The complete upstream files were checked during preparation. This offline
companion authenticates captured bundled bytes and consistency of their
recorded identities; it does not independently retrieve or authenticate the
unbundled upstream sources. Embedded checksums are integrity checks with the
checker itself as a trust root, not a signature or protection against someone
rewriting the checker and its pins together.

## Read-only and hostile-input design

Each data file is opened once. Its bounded bytes are captured through
no-follow directory/file descriptors, authenticated, and then parsed from
that same immutable `bytes` object. There is no hash-then-reopen step.
Regression tests replace JSON after capture and immediately after its one
read: interpretation still uses the authenticated captured contents, while a
new capture rejects the altered file.

The loader rejects symlinks (including directory ancestors), hard links,
nonregular files, changed-during-read files, and oversized input. The JSON
parser rejects duplicate keys, floating-point or nonfinite numbers, oversized
integers, excessive nesting, and excessive node counts. Arithmetic APIs reject
booleans as integers, negative weights, duplicate residues, composite moduli,
and unbounded test sizes. Runtime guards are explicit exceptions, so they
remain active under `python -O`. Tests also corrupt every pinned data file
under both interpreter modes and verify failure without a success result.
