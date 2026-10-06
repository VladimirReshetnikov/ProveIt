# Report 137: all-orders logarithmic asymptotics for A217057

This offline companion contains the editable article, its PDF, a Python
standard-library-only exact replay, closed typed fixtures, a read-only verifier,
and the complete unchanged final Report135 companion, including Report134.
No research scratch files, raw review reports, third-party PDFs, or network
retrievals are needed. Python 3.10+ is required. PDF builds additionally need
pdfTeX/pdfLaTeX and the packages named in `Report137.tex`.

The theorem and its analytical estimates are in the article. The finite
computations support its algebra; they are not machine-checked proofs of the
uniform estimates or all-orders asymptotic statements. In particular, no
certified decimal value of r_3 or other infinite signed constant, no effective
onset, and no exact integer-threshold rounding rule is supplied.

## Quick start

Use isolated Python (`-I`) for every command. It is mandatory for the new
verifier and code, and remains required in the documented commands for the
unchanged older companions. Normal Python here means isolated Python without
`-O`; optimized Python means the same command with `-O`. Both use explicit
exceptions instead of removable `assert` statements.

Let BUNDLE be the extracted `Report137` directory and OUT an existing real
directory outside it. Each output target below must be absent, and its parent
must already exist. These commands do not overwrite files or write inside the
bundle.

    python -I -B BUNDLE/verify.py check
    python -I -B BUNDLE/verify.py replay --output OUT/replay-normal
    python -I -B -O BUNDLE/verify.py replay --output OUT/replay-optimized
    python -I -B BUNDLE/verify.py selftest --output OUT/selftest
    python -I -B BUNDLE/verify.py build --output OUT/build
    python -I -B BUNDLE/verify.py pack --output OUT/Report137_reproducible.zip

The two `replay-result.json` files must be byte-identical. Replay compares every
computed field with `checks/fixtures.json` after checking the whole package's
integrity and fixture types. `check` validates inventory, hashes, dependencies,
and fixture schema, but does not recompute the mathematical results; `replay`
does that additional work. `build` records the freshly built PDF hash and whether
it matches the frozen article. `pack` produces a deterministic archive.

For the combined release check, including all adversarial self-tests, normal
and optimized replay, two fresh PDF builds, and a fresh-extraction repack:

    python -I -B BUNDLE/verify.py reproduce --output OUT/full-reproduction

Read `OUT/full-reproduction/reproduction-result.json`. It records the two-build
comparison, the frozen-PDF comparison, the archive hash, and self-test count.
The fresh build bytes are required to agree with one another and with the frozen
PDF before this combined release check reports PASS. A different TeX distribution
may produce different bytes; the individual `build` command reports that mismatch
without rejecting it, while `reproduce` rejects it and leaves diagnostic results. `reproduce` requires TeX; `check`,
`replay`, `selftest`, and `pack` need only the Python standard library.

## What the exact replay checks

### Singular models and logarithms

`code/models.py` uses the actual power-series coefficients
b_k(n) = [z^n](1-z)^k log(1-z), including the finite coefficients at n <= k.
It checks the rational falling-factorial formula for 0 <= k <= 12 and
k < n <= 64 (754 checks). It checks every split m = k + l, 0 <= m <= 12,
for m < n <= 64, by direct convolution against
2 b_m(n) (H_m - H_(n-m-1)) (5,096 exact log-square checks).

The same replay verifies triangular model-to-tail matching on eight independent
basis tails, V_3 through V_6, the first four single-log coefficient rows,
the cancellations ell_3 = 40 <U_0,U_0> and ell_4 = 140 <U_0,U_1>,
the inverse avoidance coefficients, and all four fixed-shift weights in

    r_3 = 9^-4/C_0 (c_3 + (59/2)c_2 + (1441/4)c_1 + (37291/16)c_0).

Here U_j denotes the tail arrays in Report137; older notes and source algorithms
may use A_j for the same arrays. The finite scalar coefficients c_j retain the
article's notation.

The falling-factorial kernel rule gives the exact contractions
<C,C> = 1393848 and <C,B> = -52348032. The shift/division correction
67/2 then gives kappa_3 = 43020 sqrt(3)/pi and
kappa_4 = -5041845 sqrt(3)/pi. These are exact rational multiples, not
floating-point approximations.

### Finite Gaussian and character algorithm

`code/gaussian.py` builds phase, Weyl-density, and character Taylor polynomials
with rational coefficients. Wick's recurrence uses the covariance matrix
[[1,-1/2],[-1/2,1]] and the Vandermonde-squared weight. It obtains normalization
81/2 and alpha_0,...,alpha_3 = 1, -11/2, 20, -965/16.

The reusable functions `avoidance_coefficients(order)`,
`boundary_coefficients(p,q,order)`, and `half_coefficients(i,j,order)` implement
the finite algorithm at a specified nonnegative integer order and nonnegative
integer boundary parameters. The last returns U_h(i,j)/C_0. Runtime grows with
order and parameters; the replay makes no complexity or practical high-order
promise. The new verifier loads these modules only from already verified bytes.

The replay also directly checks 1,092 weak-composition falling-factorial moments
through total degree six at p = 0,...,12, boundary symmetry and vacuous
normalizations, finite boundary samples, and shifted half samples through order
three. No optional closed symbolic f_3 formula is included or asserted proved.
The article's finite Gaussian algorithm is sufficient to define the local
coefficients used in the regularized prescription.

### Regularized sums: explicitly synthetic

`code/regularized.py` uses one scalar sequence

    a_n = (2/7)b_3(n) - (3/5)b_4(n) + (5/11)b_5(n) - (7/13)b_6(n)
          + 1/((n+1)(n+2)...(n+8)).

This is a transparent test case, not the actual half-array sequence for
A217057. A beta-integral calculation gives its residual falling moments

    sum n_under_j / ((n+1)...(n+s))
      = (j!)^2 (s-j-2)! / ((s-1)!)^2,  0 <= j < s-1.

With s=8, the corresponding regularized T_j values are known exactly.
The replay checks moments and their certified absolute tail bounds at cutoffs
16, 32, 64, and 128 for j=0,1,2,3. For N >= 12 it uses
|b_k(n)| <= k! 2^(k+1) n^(-k-1) for n>N and the integral bound for a
p-series tail. The bounds strictly decrease when the cutoff doubles.
It checks the exact vanishing moments through order five after subtracting
the residual's Taylor polynomial, and records scaled convolution residuals
at n=32,64,128. Those residual values are finite diagnostics, not uniform error
certificates. The synthetic tail bounds certify only the synthetic sums.

Changing small-index model coefficients would change the regularized constants.
The exact finite convention is preserved. No output in this section is labeled
as a numerical value or bound for R, S, S_2, r_3, or another A217057 constant.

### Inverse expansions

`code/inverse.py` verifies the first two inverse-polynomial cancellations as
identities over Q[z,d,lambda,beta,delta]. It also takes an explicit synthetic
affine-log direct series through order nine, verifies the log-degree bound,
and recursively cancels all inverse residual coefficients through order nine
for two rational formal parameter choices. The second choice treats eta,
which represents log(lambda), as an independent formal constant; it is not a
numerical approximation to log(2). No integer threshold is inferred from these
formal tests. The article proves the eventual inside-ceiling sandwiches.

## Immutable inherited companions

All 20 files under `companion135/` are byte-for-byte the unchanged final
Report135 release, including its eight Report134 files. The frozen manifest
identities are:

- Report135: `27499b894d1f92be6e73cc016da60a4d0b7f65b663eefa561a7fd6c811015251`
- Report134: `87bd951e61b6a51fd8f8ec534b0bf64545535ddd7498f75013ef6656e08ed94b`

The new verifier checks both fixed manifest identities and every dependency
payload against its own original manifest. Neither resealing the top level nor
recomputing its hashes can bless a modified inherited companion. The old
README's statements about what Report135 did not yet establish are historical
scope statements; Report137 supplies the subsequent all-orders result.

To check or replay the earlier work separately, use new output locations:

    python -I -B BUNDLE/companion135/verify.py check
    python -I -B BUNDLE/companion135/verify.py replay --output OUT/report135-replay
    python -I -B BUNDLE/companion135/companion134/verify.py check
    python -I -B BUNDLE/companion135/companion134/verify.py replay --output OUT/report134-replay

The full Report134 replay is slower: it reconstructs its T=40, I=10 exact lower
certificate and includes literal permutation enumeration through n=8. The new
fast replay checks dependency integrity but does not silently rerun those older
computations. Their optional SymPy kernel builder remains optional; the new
replay has no SymPy dependency. Do not run the older maintainers' seal commands
on these frozen copies.

## Integrity, closed schemas, and safe outputs

The hard-coded inventory admits exactly the declared files and directories.
Unknown or missing files, symlinks, nonregular files, duplicate JSON keys,
nonfinite JSON tokens, wrong field types, boolean or floating-point integers,
noncanonical rational strings, undeclared nested fields, bad hashes, and
modified inherited files are rejected. Correctly typed but false mathematical
fixtures are rejected by replay. The manifest covers every payload byte except
itself. This is a reproducibility/integrity seal, not a digital signature or a
substitute for reading and auditing the mathematics.

The entry-point guard uses only built-in `sys` and checks `sys.flags.isolated`
before importing any shadowable module. An unsealed `argparse.py` next to the
verifier cannot execute on a rejected non-isolated invocation. Self-tests
exercise this under both normal and optimized Python. Isolated invocation also
rejects the extra file at inventory validation. The guard does not claim to
secure a compromised Python installation or modified verifier.

Output targets must be absent, outside the whole bundle, and have existing real
directory parents. Parent traversal (including in the verifier's own invocation path), symlink components, existing files,
existing directories, and missing parents are refused for every output command.
Canonical containment is checked after the lexical symlink/traversal checks,
including double-leading-slash path aliases. Opening outputs is exclusive; failed integrity/schema/replay checks create no
output. Builds that fail after starting may leave their new external diagnostic
directory. Path checks are for an ordinary local filesystem, not a hostile
concurrent administrator changing directories or mount points during a command.

Self-tests operate only on fresh external copies. They exercise payload
corruption, fixture and manifest schemas, false rehashed mathematical fixtures,
immutable dependency seals, import shadowing, output guards, normal/-O equality,
and fresh-extraction byte-identical repacking.

ZIP entries have sorted names, fixed timestamps, fixed Unix regular-file modes,
and uncompressed storage to avoid zlib-version dependence. Archives have one
`Report137/` top-level directory. PDF builds copy the article externally, disable
shell escape, fix the date and timezone, use a reduced process environment and
private TeX/home/cache/config directories, initialize a local LaTeX format, and
run two passes. No overfull boxes, missing glyphs, undefined references, changed
labels, or duplicate definitions are accepted. PDF byte identity is expected
within the release toolchain; it is not promised across TeX distributions.

## Maintainer-only resealing

After intentionally preparing and reviewing every payload, use:

    python -I -B BUNDLE/verify.py seal --output OUT/new-manifest.json

This writes a candidate manifest outside the bundle; it does not install it or
change payloads. It checks the exact inventory, fixture schema, and immutable
Report135/134 dependencies but deliberately does not require the previous
top-level hashes to match. Review and install the new manifest manually, then
rerun check, replay, selftest, clean builds, and pack. A seal records bytes, not
a mathematical review verdict. Source or article changes require their own
review; no finite replay turns a pending proof audit into a passed one.
