Report 113: exact checks and exploratory numerical fits
=====================================================

Requirements
------------
Python 3.12 was used. Exact symbolic checks use SymPy 1.14.0. The optional
numerical fits use mpmath 1.3.0. check_manifest.py and validate.py themselves
use only Python's standard library. No network is required for replay.
The scripts locate their default inputs beside the script, not in the CWD.

Run from any directory (replace CHECKS with this directory):

  python CHECKS/exact_check.py
  python -O CHECKS/exact_check.py
  python CHECKS/validate.py
  python CHECKS/validate.py --with-numerics --output /tmp/report113-validation.json
  python CHECKS/exploratory_fit.py --output /tmp/report113-exploratory.json

Results go to stdout unless an output path is explicitly requested. Baseline
checks and validation do not edit the delivered package. The validation output
may contain local temporary paths in a failure diagnostic; successful recorded
results contain no machine-dependent paths or timestamps.

Package-level manifest
----------------------
The final report package uses one outer MANIFEST.json. No nested manifest is
required. Before distribution, generate it only after all files are frozen:

  python CHECKS/check_manifest.py PACKAGE_ROOT --write
  python CHECKS/check_manifest.py PACKAGE_ROOT
  python -O CHECKS/check_manifest.py PACKAGE_ROOT

The exact schema is:
  {"schema_version": 1, "files": [{"path": "relative/name", "bytes": 123,
                                "sha256": "64 lowercase hexadecimal digits"}]}
MANIFEST.json is the only file omitted from its own inventory. JSON duplicate
keys, duplicate paths, unknown keys, invalid hashes, noncanonical/traversal
paths, symlinks, nonregular files, missing files, and extra files are rejected.
A matching manifest demonstrates byte consistency, not authenticity of a
manifest obtained from an untrusted source. The validation harness makes a
fresh temporary manifest during its own replay; it needs no bundled manifest.

Inputs and outputs
------------------
fixtures.json
  Strict, versioned, exact rational formulas and the 29-term OEIS display.
  Rationals are canonical strings. Q(i sqrt(71)) elements are [a,b] for
  a+b i sqrt(71). The fixture accepts no extra keys and fixed dimensions.
recurrence_terms_0_500.txt
  501 generated integer terms, one index/value pair per line. These are checked
  by default against a fresh recurrence computation. They are NOT an externally
  retrieved OEIS b-file.
exact_results.json
  Frozen exact-check output: checked statements, all nonconstant psi coefficients
  through total degree 8, formal inverse delta coefficients through order 5,
  and SHA-256 of the canonical generated term file. validate.py compares the
  complete computed result with this frozen object normally and under -O.
exploratory_results.json
  Frozen 100-digit computations: 16 fits using four triples of indices and
  truncation degrees 1,2,3,4, plus model residuals on ten indices. A residual at
  n=500 is explicitly marked as in-sample. The other nine residuals are held out
  of the final (400,450,500) fit. These computations certify no decimal digits.
validation_results.json
  Named positive/negative tests, expected diagnostics and exit codes, fresh-CWD
  replay, and identical before/after source hashes. Hash snapshots omit this
  output file and MANIFEST.json to avoid self-reference. The package manifest
  separately covers validation_results.json and every delivered script/data file.

Exact scope
-----------
1. Integer recurrence through h_500; independent ordinary-coefficient EGF
   recurrence through h_80; all 29 externally retrieved display values.
2. Pole coefficient 60 and EGF factorial coefficient 30; exact initial-value
   inequalities used in the analytic comparison bound on rho.
3. Chain-rule normalized flow, exact Lyapunov derivative and its negative sign.
4. Fowler equation, eigenvalues, determinant 74 i sqrt(71), indicial polynomial.
5. The all-degree denominator lower-bound polynomial certificate, scalar
   Catalan functional identity and finite Catalan coefficient checks.
6. Rational quadratic-field psi recursion, a20 and a11, conjugation, and an
   independently multiplied finite PDE residual through total degree 8.
7. Exact generalized-binomial product identity at the checked orders, integer
   diagonal-sector cancellation, Stirling d1 and d2, Bernoulli gamma-ratio
   recurrence through order 6 with an exp/log coefficient crosscheck through 4.
8. The first two Lambert corrections, and the report's formal epsilon inverse
   recurrence through epsilon^5. Full coefficient expressions are delivered.

All verification guards use explicit exceptions, not removable assertions.
Every negative control runs under python -O. A negative control succeeds ONLY
with exit code 2 and its specified diagnostic, without a traceback. Crashes,
timeouts, unrelated diagnostics, and unexpected success are failures.

Sources and limits
------------------
The 29-term display fixture was independently retrieved through the web search
index for https://oeis.org/A333497 on 2026-10-02, with offset 0. The exact terms
were copied as data, not inferred from this implementation. The live page open
failed and the b-file https://oeis.org/A333497/b333497.txt returned HTTP 403 in
this environment. Thus oeis_display_term_count=29 and oeis_bfile_term_count=0
are intentional. --bfile FILE can separately compare a reader-obtained complete
canonical index/value file, but the bundled generated data must not be supplied
under that option and misrepresented as independent source evidence.

The defining equation and B-tree identification are discussed in:
Fabian Burghart and Stephan Wagner, On the histories of B-trees,
Theoretical Computer Science 1070 (2026), 115821,
https://doi.org/10.1016/j.tcs.2026.115821 .

The checks are finite algebraic, implementation, and byte-integrity checks.
They do not prove analytic continuation, stable-surface completeness, singularity
transfer hypotheses, or the asymptotic theorem. The all-degree analytic argument
belongs to the report. The convergent local psi series must not be confused with
convergence of the large-n expansion or permission to sum infinitely many
transferred sectors at fixed n.

The exact analytic comparison bounds are 180^(1/4) <= rho <= 60^(1/3).
Numerical rho about 3.774627575720681804 and C about -0.05169937+0.00209582i
are exploratory fits, not certified intervals. Higher working precision and
agreement of different fits do not provide a rigorous number of correct digits.
