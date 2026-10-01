# Simultaneous Convolution Divisors of Fabius-Type Laws

A prime-adic Hall criterion, finite certificates, linear rigidity, and a sharp
regularity transition. Research article prepared for the ProveIt project,
29 September 2026.

## Contents

- `article.pdf`: the complete 24-page article, with proofs, examples, source
  provenance, references, and nine proposed further research projects.
- `article.tex`: standalone LaTeX source; it does not import repository files.
- `verify.py`: exact finite certificate routines and reproducible tests.
- `verification.json`: output of the executed companion tests.
- `build.sh`: runs the tests and compiles the article in three direct passes,
  writing everything to `build/`.
- `SOURCES.md`: the full source links underlying the bibliography.

## Main result

Let p be prime and X_p = sum_{k>=0} p^(-k) U_k, with independent U_k uniform
on [-1,1]. A summable family of uniform widths a_j can be removed as an
independent convolution factor exactly when a_j = 1/n_j for positive integers
n_j and, for every K >= 0,

    #{j : v_p(n_j) <= K} <= K + 1.

The same condition is equivalent to entire extensibility of the Fourier quotient.
A nested matching supplies an explicit positive residual. The article extends
this to prime-power targets, gives finite tests for geometric streams, proves
coordinate-direction rigidity in several dimensions, and classifies residual
regularity from a digit-slack sequence.

Normalization matters: X_2 is supported on [-2,2]. The classical Rvachev up-law
on [-1,1] is the law of X_2/2.

## Reproduce the exact tests

Python 3.10 or later; standard library only. No network or package installation
is required.

    py verify.py

Without `--output` the result goes to `verification.rerun.json`; passing
`--output verification.json` overwrites the recorded file.

The recorded execution passed 9,100 finite-family cases, 8,855 geometric-family
cases, 96 uniform partition checks, 1,056 rational moment identities, and
153,390 period-drift identities. It also checked the base-six Laurent identity
and deliberate invalid-input/resource-limit cases.

These are finite implementation tests, not machine verification of the analytic
or infinite theorems. Those theorems are justified by the manuscript's proofs.

### Use the certificate routines

    from verify import Stream, finite_certificate, stream_certificate

    finite_certificate(2, [2, 3])       # accepted: widths 1/2 and 1/3
    finite_certificate(2, [1, 3])       # rejected: zero-order witness at 3*pi
    finite_certificate(2, [2, 3], power=2)  # target base 4, not base 2

    stream_certificate([Stream(1, 2), Stream(1, 2)])
    # Two streams with deadlines 1,3,5,...; accepted and critical.

`finite_certificate` takes the actual positive integer denominators. Its `power`
argument means that the target base is p**power. `stream_certificate` takes
valuation starts and steps for a prime-base target. The optional `finite`
argument contains additional finite deadlines, not denominators.

The finite-window algorithm can have a large least-common-multiple period.
A resource limit raises `ResourceLimitError`; it is never a rejection certificate.
Primality checking in the companion is elementary trial division, intended for
small prime bases rather than cryptographic-size inputs.

## Compile the article

Use a TeX installation with pdfLaTeX, Latin Modern, AMS packages, mathtools,
microtype, booktabs, tabularx, enumitem, fancyhdr, xurl, hyperref, and cleveref.

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

On a Unix-like system, `bash build.sh` runs both the tests and these three passes,
writing `build/verification.json` and `build/article.pdf`.
No bibliography processor or external figures are needed. Rebuilding may change
PDF metadata and binary hashes while preserving mathematical content and layout.

## Proof and novelty status

The article is a proof-bearing research manuscript. It has not been peer reviewed
or checked in Lean. The existing repository's scalar reciprocal-integer
single-copy theorem is explicitly treated as prior work, not as a new discovery.
The proposed extensions were developed after targeted source review; no exhaustive
repository audit or worldwide priority claim is made. The main arguments do not
assume the correctness of unverified repository research claims.

No repository files were modified or uploaded as part of preparing this package.

## Editorial amendments (ProveIt, 2026-09-29)

Made in the editorial pass after batch 56 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-29)`, every change to the programs `ed. (2026-09-29)`.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-29)" is defined in the preamble. One note, at the end of the
  introduction's account of the question, records the uncited predecessor
  `../Arithmetic_Convolution_Factors_Fabius_Type_Laws/` (filed 2026-09-28,
  present at both pinned snapshots): its theorems "Arithmetic convolution
  classification" and "Cross-base classification" contain the one-stream
  case of `thm:streams`, and its periodic-ratio decision theorem and integer
  regularity classification are one-stream cases of `thm:finite-window` and
  `thm:critical`, while it allows composite divisibility-ladder targets that
  this article does not; conversely `thm:hall`, `thm:primepower` and
  `thm:base6` answer its question "Beyond divisibility ladders" for
  prime-power geometric targets, and `thm:vector` and `thm:matrix` treat the
  product-target case of its question "Multivariate arithmetic factors".
  The note also records that the identity `X_2 = X_4 + X_4'/2` (in law) of
  the example "Density is necessary but not sufficient" is machine-checked,
  in the `[0,1]`-digit normalization, as
  `Fabius.ProbabilityRepresentation.geometricUniformDistribution_one_half_conv_one_quarter`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/GeometricUniformMultisection.lean`),
  which the article does not cite. Reciprocal notes now stand at both
  questions of that article and after `conj:general-base` of
  `../Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/`.
- `article.pdf`: rebuilt from the amended source by the amended
  `build.sh` (MiKTeX pdfTeX 1.40.29, three passes): 24 pages (23 as
  delivered), no error, undefined reference or citation, duplicate
  destination, overfull or underfull box; the page carrying the note was
  rendered and inspected.
- `verify.py`: the default output is `verification.rerun.json`, so a plain
  run no longer overwrites the recorded `verification.json`; the JSON is
  written with LF line endings on Windows too (the delivered program wrote
  CRLF there).
- `build.sh`: writes the check output and all LaTeX output to `build/`,
  so it no longer overwrites the recorded `verification.json` or rebuilds
  `article.pdf` in place (and leaves no auxiliary files in the package).
- A rerun on a copy (2026-09-29, `PYTHON=py bash build.sh`, Python 3.14.4,
  standard library) passed with the recorded counts, and
  `build/verification.json` equals the recorded `verification.json` byte
  for byte; the default `py verify.py` gives the same bytes.
- Normalizations, for comparison with neighbouring reports: `X_2` is
  supported on `[-2,2]` and is twice the up-function variable; the law
  `mu^[p]` of `../Arithmetic_Convolution_Factors_Fabius_Type_Laws/` (its
  uniforms live on `[-1/2,1/2]`, its sinc is normalized) is the law of
  `X_p/2`; the product
  `Phi(z) = prod_{n>=0} sinc(pi z/2^n)` of
  `../Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/` is the
  characteristic function of `X_2/2` in the convention `E exp(2 pi i z X)`.
- `README.md`: the page count and the `build.sh` line under "Contents",
  the command and output file under "Reproduce the exact tests", the
  `build.sh` sentence under "Compile the article", and this section.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 69 and 70 of `docs/incoming/` (see
`docs/incoming/README.md`); the change to the source is marked
`% ed. (2026-09-30)`.

- `article.tex`: a second unnumbered environment `ednotelater` ("Editorial
  note (ProveIt, 2026-09-30)") is defined after `ednote`. Under Q6
  ("Stability under approximate factorization") a note records that the
  later unreviewed draft
  `../Arithmetic_Rigidity_off_Resonance_Geometric_Uniform_Laws/` (batch 69)
  gives, in one dimension and for nonresonant geometric targets
  `sum_k q^k U_k` (`U_k` uniform on `[-1/2,1/2]`), an explicit Wasserstein
  lower bound against every law with a factor made of two uniforms of
  lengths `1/N` and `1/M` (its `thm:metric`), and a family near `q = 1/2`
  on which exact factorability fails while that distance tends to zero (its
  `thm:perturbation`); it treats neither the prime-base targets `X_p` of
  this article nor several dimensions. That draft credits and re-proves
  `thm:primepower` (its `lem:hall`) and `thm:base6` (its `prop:base6`).
- Correction to a record outside this package: the draft manifest said that
  this article proves item 1 of `conj:general-base` of
  `../Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/` for prime and
  prime-power bases. It does, but item 1 holds for every integer base, by
  `thm:self-spectrum` of `../Arithmetic_Convolution_Factors_Fabius_Type_Laws/`
  (filed a day earlier); the manifest row and that report now say so.
- `article.pdf`: rebuilt from the amended source with the three `pdflatex`
  passes that `build.sh` runs (MiKTeX 26.2, pdfTeX 1.40.29): 24 pages, as
  before; no error, undefined reference or citation, duplicate destination,
  overfull or underfull box; no Type 3 font. The page carrying the note was
  rendered and inspected.
- `README.md`: this section.
