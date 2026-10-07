# Report180: modified Entringer numbers and their connection constant

This package accompanies the article on OEIS A386381, the diagonal of the
modified Entringer triangle A386363. It contains the article PDF and editable
LaTeX, a standard-library exact verifier, frozen computational references,
optional SymPy/mpmath reproductions, and an offline deterministic builder.
The original recurrence, previously posted leading equivalent and numerical
amplitude, and classical analytic methods are credited.

## Mathematical content

- An exact boustrophedon reduction to a differential equation and a positive,
  finite connection constant identifying the posted asymptotic amplitude
- All fixed-order scalar and compact-complex-uniform marked asymptotics,
  with explicit coefficient recurrences
- A positive trace-class Green operator, its Fredholm determinant, a limiting
  infinite Bernoulli-sum law, and weighted probability corrections
- Simple negative limiting zeros, eventual escape of finite nonreal zeros
  from bounded sets, and an exact finite counterexample to real-rootedness
- A separate large-positive-real-mark connection asymptotic, with an exact
  optical-length integral and ordinary diagnostic quadrature
- Controlled asymptotic inverse brackets, with exact evaluation still required
  near integer rounding boundaries
- A separate amplitude enclosure obtained from convergent midpoint series,
  proved Taylor-tail bounds, and optional interval arithmetic

These are conventional mathematical arguments, not proof-assistant results.
Asymptotic orders are fixed. No convergence of the full inverse-power series,
complete exponentially small expansion, universal novelty, or finite-polynomial
Bernoulli representation is claimed. The asymptotic and inverse remainder
constants and their starting thresholds are not made into certified finite-N
bounds.

## Quick verification

Use Python 3.10 or newer. From the package root:

```
python -I -S -B code/verify.py
python -I -S -B -O code/verify.py
python -I -S -B guard_tests.py
python -I -S -B test_build.py
```

The core uses exact integer and Fraction arithmetic and no third-party packages.
It compares the original triangle with the ODE for n=0,...,101, including the
21 visible OEIS terms; compares marked polynomial identities for n=2,...,18;
checks formal Frobenius equations and scalar/marked corrections through order
six, with explicit marked audit formulas compared through order four;
checks normalized PGF corrections through order four; proves by an
exact Sturm calculation that P_10 has six real roots; and rechecks the rational
Taylor-tail bound at truncation degree 420. Checks remain active under -O.

The core does not recompute the floating-point or interval series evaluations.
It checks frozen reference integrity and the exact arithmetic surrounding the
interval certificate, including the outward decimal endpoints. Reproducing the
finite interval evaluation requires the optional pinned environment. See
README_CODE.md for the precise evidence boundary and commands.

## Rebuild and check integrity

An installed TeX distribution with pdfLaTeX and the packages used by Report180.tex
is required to build the PDF. The builder installs nothing, uses no network,
disables TeX shell escape, and publishes to a new directory outside the package:

```
python -I -S -B build.py --output /tmp/report180-new
```

The parent directory must already exist and the output path must not exist.
A successful build produces Report180.pdf, Report180.tex, Report180.zip, and
ARTIFACTS.json containing their byte counts and SHA-256 hashes. The same sources
and installed Python/TeX toolchain produce byte-identical PDF and ZIP outputs;
cross-version byte identity is not promised.

After extracting the release ZIP into a clean directory, run there:

```
python -I -S -B verify_manifest.py
```

The authoring source directory does not have a finalized release manifest.
The release manifest detects missing, altered, or unexpected content, including
symlinks and special files. It is an integrity inventory, not a signature or a
general security sandbox.

## Evidence and attribution

The rigorous amplitude interval is a conventional numerical certificate using
mpmath interval arithmetic and mathematically justified truncation bounds.
It trusts the interval library implementation; the package does not independently
prove correct rounding inside that library. Longer decimal diagnostics and
finite-N residuals are not additional certified digits or remainder bounds.

SOURCE_AUDIT.md describes the classical sources, bounded overlap review, and
priority limitations. data/PROVENANCE.json identifies the frozen computational
inputs and their byte hashes. Optional scripts are not run by the core or
builder. Their working-copy instructions are in optional/README.md. No
third-party article/book PDFs or raw research-review dossiers are included.

## Independent large-positive-mark limit

The additional theorem is C(lambda)=exp(L sqrt(lambda))/(2 sqrt(2) pi
sqrt(lambda)) times (1+O(lambda^-1/2)) as real lambda tends to positive infinity.
Here L is the exact integral of sqrt(E(z)/z) from 0 to rho; its short numerical
approximation is 4.2586174557. This theorem is separate from the N-asymptotics
uniform on fixed compact mark sets. No joint growing-lambda/N regime,
complex-sector uniformity, Weyl expansion, or numerically certified
large-mark error constant is claimed. The optional optical-length quadrature
is an ordinary multiprecision diagnostic, not an interval certificate.

## Far tail of the fixed limiting law

For the single limiting Bernoulli law J, the report further proves

```
Pr(J=m) = L^(2m+1) / [sqrt(2) pi C(1) (2m+1)!]
          * (1 + O(m^(-1/2)))
        = K m^(-3/2) [e L/(2m)]^(2m) (1 + O(m^(-1/2)))
K = L / [4 sqrt(2) pi^(3/2) C(1)]
Pr(J>=m)/Pr(J=m) = 1 + L^2/(4m^2) + o(m^(-2))
```

This is an asymptotic factorial comparison, not an exact factorial law.
The rare-tail inverse uses the explicit convention
n(y)=min{m>=0:Pr(J>=m)<=y} and gives a two-sided ceiling enclosure around
a smooth inverse. It does not give an unconditional single-ceiling rule.
These results concern the fixed limiting law only. No simultaneous finite-N/m
tail limit, all-orders mass/tail expansion, effective numerical onset,
complex-sector theorem, or Weyl expansion is claimed. The new conclusions
have conventional analytic proofs; they add no numerical certificates or
new executable checks to this package.
