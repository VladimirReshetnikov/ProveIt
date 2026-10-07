# Report189: Minimum-Length Compositions

An authored mathematical report and offline reproducibility package for the
families a_s(n), which count compositions into k parts each at least k+s,
and b_s(n), which count those whose minimum is exactly k+s. The OEIS
normalizations are A098131=a_0 (including n=0), A098132=a_1 (n>=1), and
A098133=b_0 (n>=1).

The report develops a fixed-s, all-fixed-order saddle expansion, its
interlaced half-power difference expansion, and eventual inverse envelopes.
The counting formulas, generating functions, classical Poisson identity,
and standard saddle methods have prior sources. No worldwide priority,
growing-s uniformity, effective onset, convergent transseries, or automatic
single-ceiling inverse formula is asserted.

## Quick start

Python 3.10+ and its standard library suffice for every mandatory exact check:

    python3 -I -S -B code/check_exact.py
    python3 -I -S -B -O code/check_exact.py
    python3 -I -S -B reproduce.py
    python3 -I -S -B test_build.py
    python3 -I -S -B -O test_build.py

The exact checker prints canonical JSON with 12,453 checks, including 87
explicit input rejections. Finite checks are evidence for implementations;
they do not replace the report's proofs of asymptotic statements.
The build guard suite has 258 tests using synthetic packages and a simulated
compiler. Every check remains active with Python optimization enabled.

## Make the complete release

With the report's pdfLaTeX packages and fonts already installed:

    python3 -I -S -B build.py --output "$(dirname "$PWD")/report189-release"

Use a new output directory outside this package, whose parent already exists.
The build does not download dependencies or overwrite outputs. It executes
both isolated exact modes and both guard modes, compiles three TeX passes,
requires a clean settled final log, and writes Report189.pdf,
Report189.tex, Report189_code.zip, and ARTIFACTS.json. The archive has a
closed SHA-256 manifest. Read README_REPRODUCIBILITY.md before rebuilding.

## Mathematical code

- code/compositions.py: exact binomial counts and independently multiplied GFs
- code/coefficients.py: all-order integer/Fraction coefficient generator
- code/independent_coefficients.py: separate derivative-polynomial check through C3
- code/check_exact.py: mandatory finite identities, fixture checks and input guards
- code/diagnose_float.py: optional mpmath forward/inverse experiments
- code/check_symbolic.py: optional SymPy C1/C2 algebra checks

Optional commands deliberately omit -S, so separately installed packages
can be imported. These commands are never called by the release builder:

    python3 -I -B code/diagnose_float.py
    python3 -I -B code/check_symbolic.py

Both optional commands write JSON only to stdout. Floating diagnostics are
not certified enclosures or proofs of remainder estimates.

## Public package scope

The package contains the authored report, authored code and documentation,
72 attributed integer fixture values, and generated release products. It
contains no full OEIS records, third-party articles, source-page downloads,
private research or audit files, bytecode caches, or transient TeX outputs.
DATA_SOURCES.md and data/README.md describe the fixture attribution and
index conventions. code/README.md describes the algorithmic checks.
