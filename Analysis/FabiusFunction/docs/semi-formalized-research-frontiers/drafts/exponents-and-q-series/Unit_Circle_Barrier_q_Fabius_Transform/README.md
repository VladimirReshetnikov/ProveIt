# The Unit-Circle Barrier for the q-Fabius Transform

**Natural boundaries, cyclotomic moment poles, and exterior meromorphic divisors**

Research article prepared for Vladimir Reshetnikov, September 30, 2026.
The PDF contains 24 pages (22 as delivered; the editorial notes of 2026-09-30
add two), including complete proofs, a bibliography, a repository
interface audit, computational examples, and further research questions.

## Main result

For every fixed nonzero complex z, the function

    A(q,z) = product_{j>=0} h((1-q) q^j z),     |q| < 1,
    h(w) = (exp(w)-1)/w,                      h(0) = 1,

has the whole unit circle as a natural boundary, even for meromorphic
continuation. The proof combines a nonvanishing root-of-unity cusp coefficient
with a quantitative construction of zeros approaching the boundary.

Other proved results include stability under positive finite products with real
dilations, all-orders radial cusp expansions, exact leading cyclotomic poles of
moment coefficients, a sharper denominator bound, and a complete formula for the
exterior transform's poles and their multiplicities. The functions are not
algebraic or D-finite in q for fixed z != 0.

## Files

- `q_fabius_boundary.pdf`: the article.
- `q_fabius_boundary.tex`: self-contained LaTeX source with embedded bibliography.
- `verify_results.py`: independent exact and high-precision checks.
- `verification_results.json`: recorded verification results of the delivered
  run, including numerical data.
- `verification_run.txt`: console output of that run.
- `requirements.txt`: versions used for verification.
- `build.sh`: PDF build helper for a Unix-like shell.
- `SHA256SUMS` (not kept): the delivered checksum ledger (8 entries) was
  verified in full on filing (batch 65) and not kept; the delivered archive
  remains in the repository history (see `docs/incoming/README.md`, batch 65
  row).

## Rebuild the article

Requires a TeX Live installation providing the packages named in the source
preamble, including newtx, amsmath, amsthm, mathtools, geometry, microtype,
hyperref, xurl, fancyhdr, enumitem, and booktabs. No external figures, BibTeX run,
network access, or font files from this package are required.

    pdflatex -interaction=nonstopmode -halt-on-error q_fabius_boundary.tex
    pdflatex -interaction=nonstopmode -halt-on-error q_fabius_boundary.tex

Or run `bash build.sh` in this directory. Rebuilding creates ordinary TeX
auxiliary files alongside the source.

## Run the checks

Use Python 3.10 or newer; the recorded run used Python 3.13.5, SymPy 1.14.0,
and mpmath 1.3.0.

    python -m pip install -r requirements.txt
    python verify_results.py

The successful run checks:

- agreement of two moment recurrences and the q=0 and q=1 specializations
  through degree 12;
- 46 exact cyclotomic leading-coefficient identities;
- 11 cyclotomic denominator tests, including observed minimality through degree 12;
- 1,800 exact exterior-pole collision counts;
- radial cusp examples at six root orders and zero-condensation examples, using
  85-decimal-digit working precision.

Exact checks use rational arithmetic and cyclotomic quotient rings. Numerical
checks are not interval-arithmetic certificates. The script writes its JSON
results to `rerun/verification_results.json`, or to the file given by
`--output`; only `--output verification_results.json` overwrites the recorded
results (as delivered, every run overwrote them). Its finite checks
supplement, and do not replace, the proofs.

In this repository, on Windows, `uv run --no-project --with sympy==1.14.0
--with mpmath==1.3.0 python verify_results.py` runs the checks without a
virtual environment; bare `python` may not resolve, so use `py` or `uv`.

## Research status and limitations

The main natural-boundary and exterior-divisor results are proved in the article.
The conjecture that the displayed upper denominator is minimal in *every* degree
is not proved; finite computations verify it only through degree 12 (through
degree 20 in an independent computation on filing; see the amendments below).
Neither
nonlinear differential transcendence nor convergence/Borel summability of the
full cusp correction series is asserted.

No Lean file was compiled for this package. These are conventional mathematical
proofs, not machine-certified Lean results. Worldwide publication priority has
not been independently established. The article distinguishes established
q-product methods from its specific arguments and conclusions.

## Repository provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 7747fcfddedeca1a04b6526cdd4836fbfdad1b89
Inspected interface document: Analysis/FabiusFunction/README.md
README blob: 8a19a7c8de8939c4a55ec63fc443ce08d6fe74ce

The audit covers the documented geometric-uniform interfaces relevant to the
article, not every document, incoming archive, or proof in the repository. No
repository files were changed. External mathematical references are given in
the article's bibliography.

## Artifact validation

The delivered PDF compiled without unresolved references, TeX errors, or
underfull/overfull box warnings. All 22 pages were rendered for visual review;
selected formula, table, contents, and audit pages were also inspected at full
page resolution. SHA256SUMS permits checking the delivered file bytes.
(The ledger was retired on filing, and the PDF has since been rebuilt with
editorial notes; see below.)

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batch 65 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`, every change to the program `ed. (2026-09-30)`.
The addressee line ("prepared for Vladimir Reshetnikov") is kept as
delivered, as for the other arrivals of the Fabius drafts tree.

- `q_fabius_boundary.tex`: an unnumbered environment "Editorial note
  (ProveIt, 2026-09-30)" is defined in the preamble (the theorem counter
  is unchanged). Four notes:
  - end of Section 1.1: the article's audit read only the Lean
    documentation. The geometric q-Fabius volume beside it
    (`../geometric_q_fabius_frontiers/`) already proves the natural boundary
    for real or purely imaginary `0 < |z| < pi/2` (`p9:thm:natural-boundary`,
    `p9:cor:germ-natural-boundary`; `A(q,z) = e^{z/2} Phi(q, iz/2)`, and the
    cusp constant `C_L` is minus Part IX's spectral action, checked to 16
    digits on filing); Theorem `thm:main` generalizes it to every `z != 0` and
    so proves the volume's `p7:conj:natural-boundary` for every `t != 0`,
    including the range `|t| >= pi` left open by
    `p7:rem:natural-boundary-status`. The q-Pochhammer monograph
    (`../q_pochhammer_q_binomial_monograph/`, `thm:qF-spectral`) already has
    the factorization `eq:pochhammer` and the exterior pole set, with
    multiplicities only as a count of coincident points; Theorem
    `thm:multiplicity` evaluates them;
  - after Corollary `cor:denominator`: it proves the volume's conjecture
    `p7:conj:Pn-divisibility` (the odd q-integer divisor of `P_n`), which
    the article does not mention. Proof: `P_n = [n]_q! a_n`, and for odd
    `e >= 3` the exponent of `Phi_e` in `[n]_q!/D_n` is
    `floor(n/e) - floor(n/(2e))`, the number of odd multiples of `e` up to
    `n`, which is its exponent in the product of the odd `[d]_q`. Checked on
    filing for `3 <= n <= 20` (the volume checked through 16);
  - after Conjecture `conj:denominator`: an independent computation on filing
    found the reduced denominator equal to `D_n` for every `n <= 20` (the
    article checked 12); it remains a conjecture;
  - after the audit table (Appendix A): the Lean declarations behind the
    table, several uncited:
    `Fabius.hasProdLocallyUniformly_geometricUniformComplexMomentProduct`,
    `Fabius.geometricSincProduct_eq_tprod_complexQPochhammerInf`
    (`RvachevPochhammerFactorization.lean`, not cited; it is
    `eq:pochhammer` at the argument `i(1-q)z/(2 pi)`),
    `Fabius.qFactorial_mul_geometricUniformMomentRatFunc`,
    `Fabius.eval_geometricUniformMomentRatFunc_eq_exteriorComplexMomentGerm_taylorCoefficient`
    and `Fabius.geometricUniformComplexMomentGerm_reciprocity`, all under
    `Analysis/FabiusFunction/Lean/FabiusFunction/`; no natural-boundary,
    pole-order or divisor statement has a Lean counterpart.

  Two marked corrections: in Theorem `thm:moment-pole` the leading
  coefficient printed `R_xi^k/(2k!)`, which reads as `(2k)!`; it now reads
  `R_xi^k/(2 k!)` (from `a_1 = 1/2`). In the audit table the module
  `GeometricUniformExteriorComplexMomentGerm` was printed as two names on
  two lines; it is now one name. No label was renamed or removed.
- `q_fabius_boundary.pdf`: rebuilt from the amended source with `bash
  build.sh` (two `pdflatex` passes, MiKTeX pdfTeX 1.40.29): 24 pages (22 as
  delivered), no error, undefined reference, multiply defined label,
  duplicate destination, or overfull box; every font is embedded and none is
  Type 3. The pages carrying the notes were rendered and inspected.
- `verify_results.py`: new option `--output`, default
  `rerun/verification_results.json`, so a plain run no longer overwrites the
  recorded results; the JSON file is written with LF line endings on every
  platform (as delivered, CRLF on Windows). A rerun of the amended program
  on a copy (2026-09-30, the `uv` command above, which resolved Python
  3.13.5) reproduced `verification_results.json` byte for byte, and its
  console output equals `verification_run.txt` apart from Windows line
  endings.
- `README.md`: the page count, the descriptions of the two recorded files,
  the retired ledger, the output location and the Windows command, the
  degree-20 check, and this section.
- Recorded, not changed: the article calls `verification_results.json` a
  "verification receipt"; it is the program's recorded output. Its `Y_q`
  (uncentred, on `[0,1]`) and `D_n` (the cyclotomic divisor) differ from the
  volume's `Y_q` and from the `D_n` of the volume's problem on the
  arithmetic of `P_n`.
