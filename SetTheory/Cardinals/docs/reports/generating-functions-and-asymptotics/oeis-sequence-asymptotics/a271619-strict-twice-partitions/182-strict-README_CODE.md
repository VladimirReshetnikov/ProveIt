# Exact checks, numerical diagnostics, and deterministic build

## Exact core

All mandatory arithmetic uses Python integers or `fractions.Fraction`.
`code/exact.py` is the adapted computational core, and `code/verify.py` derives
the certificate, checks frozen reference pins, compares all exact data, and
prints a compact PASS object. Every invariant is an explicit runtime check;
none relies on `assert`, which optimization could remove.

The mandatory finite domains are fixed and recorded in the certificate:

- p(0),...,p(10000) from ordinary coin-change DP
- p(0),...,p(600) independently from the divisor-sum recurrence
- a(0),...,a(5000) from descending weighted 0/1 product DP
- a(0),...,a(600) independently from the logarithmic-derivative recurrence
- All 81,156 ordinary partitions of sizes 0 through 35, checking conjugation
  for Q_j with 1 <= j <= 6 and the two q-brackets Q3 and Q2 squared
- The low-hole bijection for 0 <= n <= 28 and 0 <= L <= 5: 174 cases and
  8,898 triples, including exact weights and Frobenius ratio identities
- The explicit first edge coefficients, crossover phase and slope, and
  displayed finite-product normalization coefficients by rational algebra

Strict increase is checked on a(1),...,a(5000). That finite observation is
separate from any general proof. Initial terms and whole stored integer vectors
are compared exactly, not via approximate decimal values.

The q-bracket checks use doubled half-integer coordinates and independent
Eisenstein divisor sums. They check the specified formulas through q^35. The
Laurent-polynomial substitutions are exact rational operations. The second-order supplement described below adds three further finite
bracket certificates. There is no general all-orders symbolic q-bracket engine:
only the displayed finite formulas and arithmetic identities are implemented.

## Separate exact second-order supplement

`code/second_order.py` independently enumerates all 2,714 partitions through
size 20 and computes the brackets of (Q3+7/960)^2, Q2^2(Q3+7/960), and Q2^4.
Within the complete weight-8/10/12 monomial spans in E2,E4,E6, Fraction Gaussian
elimination finds dimensions 4,5,7 and the exact nonzero initial-coefficient
determinants. All 21 coefficients are then checked. Exact Laurent substitution
checks every term, not just its leading power. Sparse rational polynomials
extract A1 and A2 from the five required finite moment terms and verify the
full B2 variance identity. No SymPy or floating library is imported.

The identification of the true brackets in these complete homogeneous spans
uses the Bloch--Okounkov theorem stated in the manuscript. Nonzero determinants
make the initial data determining within those spans; finite agreement alone
would not establish the identities without that analytic input. Transfer and
Taylor remainders remain mathematical inputs, not code-certified theorems.

`code/verify_second_order.py` compares the computation with its separately
frozen `data/second_order_certificate.json` and two earlier independent
reconstructions. Its own literal reference pins and provenance record leave
the original exact certificate unchanged. The frozen independent script uses
SymPy only as a historical source copy; it is not executed by the package.
`second_order_guard_tests.py` corrupts every scalar leaf, checks malformed
certificates and reference pins, exercises singular/malformed matrices and
pivot-swap determinants, and rejects removable assertions and float literals
in the second-order arithmetic core. Both supplemental suites run normally and
under `python -O` in every build.

To recompute the supplement without modifying the package:

```
python -I -S -B code/second_order.py > /tmp/report182-second-order.json
python -I -S -B code/verify_second_order.py --data /tmp/report182-second-order.json
```

## Hole-constant enclosure

Write g(m)=m(m+3)/2. Subset partitions using parts 2 through m+1 give the bound
p(k) >= 2^m for k >= g(m). With N=10000, m0=139, and 132 entries removed from
the first block, exact geometric power sums yield upper bounds on the tails
sum_{k>N} k^s/p(k), for s=0 and s=1. These are rational numbers in the
certificate. The earlier looser geometric bounds are independently reproduced.

The finite product and sums are enclosed by rounding down/up after each
operation on the integer scale 10^100. The product tail uses
exp(T0) <= 1/(1-T0); the energy, count, and count-variance tails use T1, T0,
and T0 respectively. No floating arithmetic or transcendental routine enters
these constant certificates. The resulting decimal endpoints are exact rational
fixed-point endpoints; their number of decimal digits is not a promise that
all those digits are shared by the lower and upper endpoints.

## Certificate integrity and guards

`data/certificates.json` is canonical sorted JSON. It includes every independently
computed result plus explicit negative scope statements. Exact canonical
serialization comparisons distinguish booleans, integers, floats, missing or
extra fields, and altered numerical strings. JSON readers reject duplicate
keys, non-finite constants, invalid syntax, and trailing material.

`guard_tests.py` tests corruption of every category and every scalar leaf of the
certificate, malformed sequence text, frozen pins, symlinked paths, and guarded
regeneration outputs. It also verifies that the mandatory source contains no
removable assertion. The real builder runs the verifier and all guard suites
normally and under `python -O` and requires byte-identical canonical result
objects. Full arithmetic need not be rerun for each corruption: mutation tests
compare against one independently derived expected certificate.

Regenerate to a new file outside the package:

```
python -I -S -B code/regenerate.py --output /tmp/new-certificate.json --compare data/certificates.json
```

Existing output files, symlinked parents, missing parents, paths containing
traversal components, and outputs inside the package are rejected. Regeneration
never replaces the committed certificate.

## Offline build and reproducibility

The builder accepts either the exact source inventory or an intact extracted
release with its exact manifest. It copies only explicitly named source files
to private temporary storage and performs these steps:

1. Check frozen inputs and recompute every finite certificate
2. Run exact verification, corruption guards, and build guards, normally and
   under optimized isolated Python, requiring identical output objects
3. Compile with pdfLaTeX and `-no-shell-escape`, at least twice, until auxiliary
   files stabilize, with a maximum of six passes
4. Reject unresolved or multiply defined labels/citations, rerun requests,
   missing characters, and overfull boxes; check the PDF signature
5. Write generated verification receipts and build-scope metadata
6. Create and verify a complete SHA-256 manifest, then write sorted ZIP entries
   with fixed timestamp, fixed regular-file modes, and no compression
7. Publish the PDF, TeX, ZIP, and their external checksum receipt exclusively
   to a new output directory

The fixed timestamp is 2026-10-03 00:00:00 UTC. `SOURCE_DATE_EPOCH` and
`FORCE_SOURCE_DATE` suppress changing TeX metadata. Home, temporary directories,
and TeX caches are private. Inherited Python and TeX configuration overrides are
removed. The builder never accesses the network or installs dependencies.

The same source and installed Python/TeX stack should produce identical PDF,
TeX, ZIP, and receipt bytes. Cross-version or cross-platform PDF identity is
not promised. Extracted-release rebuild identity is verified before delivery.
The source tree is unchanged by normal verification and building.

The source and trusted executables are not adversarial inputs. The path checks
protect ordinary file integrity and refuse links and nonregular entries; they
are not a complete concurrent-filesystem adversary defense. Disabling shell
escape is not an operating-system sandbox. Hashes detect accidental corruption,
not coordinated replacement of both content and manifest.

## What these checks do not establish

These finite checks do not certify analytic remainders, an effective asymptotic
onset, accurate finite-n coefficient approximations, or a convergent asymptotic
expansion. The optional floating diagnostics explicitly show poor moderate-n
performance of the eventual two-charge formula. Keep those diagnostics separate
from the rigorous fixed-point constant enclosures and the report's proofs.
