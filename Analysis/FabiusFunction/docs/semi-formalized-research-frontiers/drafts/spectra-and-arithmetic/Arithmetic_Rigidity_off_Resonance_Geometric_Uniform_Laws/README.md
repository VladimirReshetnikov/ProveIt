# Arithmetic Rigidity off Resonance
## Exact convolution factors of geometric-uniform laws

Research manuscript prepared for Vladimir Reshetnikov, 30 September 2026.

The package contains a standalone article, complete written proofs, nine further
research questions, and exact finite arithmetic certificates. It extends the
Fabius/Rvachev convolution-divisor program in ProveIt to rationally separated
source scales and to prime-power rational-return channels.

### Files

- `article.pdf`: the compiled article (25 pages since the editorial pass below;
  24 as delivered).
- `article.tex`: the standalone LaTeX source, including its bibliography.
- `code/verify.py`: standard-library Python certificates and regression tests.
- `results/verification.json`: the delivered successful verification receipt.
- `results/verification.log`: console summary from the delivered run.
- `results/build_validation.json`: the delivered build record (page, pass,
  warning and box counts of the delivered 24-page PDF, and its hash).
- `SOURCES.md`: source provenance, exact repository paths, and review limits.
- `PROOF_AUDIT.md`: theorem dependency and claim-boundary checklist.
- `build.sh`: verification plus three-pass PDF compilation into `build/`.
- The submitted `SHA256SUMS` was verified in full (10/10) on filing (batch 69
  of `docs/incoming/`) and not kept; the delivered archive remains in the
  repository history (see `docs/incoming/README.md`, batch 69 row).

### Main results

Use U uniform on [-1/2,1/2], and mu_q the law of sum(q^k U_k, k >= 0).
The width of a uniform here is its full interval length.

For positive summable source widths s_k with s_k/s_l irrational whenever k != l,
a finite or countable convolution of uniforms of widths a_j divides the source
law exactly when a_j = s_(k_j)/n_j, with positive integers n_j and DISTINCT
source coordinates k_j. Equivalently, the Fourier quotient extends to an entire
function. A positive remainder is explicitly constructed by interval subdivision.

For q with no positive rational power this gives:

    dilation(c, mu_rho) divides mu_q
    exactly when c=q^a/n and rho=q^m/d,
    with a>=0, m>=1, and positive integers n,d.

Several geometric factors are compatible exactly when their source progressions
a_i + m_i*N are pairwise disjoint. The exact finite pairwise test is

    gcd(m_i, m_j) does not divide (a_i-a_j).

For q=p^(-e/h), p prime and gcd(e,h)=1, each proposed width has the unique
form q^r/n with 0<=r<h. Within each residue class the exact criterion is

    #{j: r_j=r and floor(v_p(n_j)/e)<=K} <= K+1 for every K>=0.

The h=1 Hall ingredient is PRIOR repository work and is explicitly credited.
The article proves the separated-width, geometric-stream, h-channel, and
finite-orbit extensions, as well as an explicit Wasserstein obstruction.

The uniform pair with widths 1/2 and 1/3 divides mu_(1/2), but does not divide
mu_q at any q with no rational positive power. Nevertheless its distance to the
factorable class tends to zero as such q approach 1/2; quantitative upper and
strictly positive lower bounds are proved.

### Proof and originality status

AI-assisted and unrefereed. The new analytic theorems have not been checked in
Lean, Rocq, or another proof assistant. The package is not a claim of certified
worldwide priority or a resolution of every convolution decomposition problem.
The classification concerns factors explicitly presented as sums of independent
uniforms, not arbitrary probability factors.

Existing multisection identities, the prime-power h=1 Hall theorem, the base-six
counterexample, and the golden-ratio Bernoulli singularity mechanism are credited
as prior or classical. All dependencies needed for the results are proved here.
The bibliography is contextual as well as historical; it does not substitute
for the proofs.

No repository files were modified and no pull request was created.

### Verification

Requires Python 3.10 or later. No third-party packages, network, or floating-point
arithmetic are required.

    python3 code/verify.py --output results/verification.rerun.json

(On the ProveIt machine use `py` rather than `python3`, and run the build script
below as `PYTHON=py bash build.sh`. Without `--output` the program writes
`verification.rerun.json` in the current directory; it never touches
`results/` unless told to.)

The executed run passed 156,227 exact finite checks, including CRT comparisons,
Hall conditions versus independent backtracking, colored channels, geometric
orbit cases, exact moment identities, and deliberate invalid inputs.

These are implementation tests, NOT formal verification of the analytic or
infinite statements. The program accepts certified integer parameter forms;
it does not decide whether an arbitrary real parameter is nonresonant.

### Build

Use a TeX installation with pdfLaTeX, Latin Modern, AMS packages, mathtools,
microtype, booktabs, tabularx, enumitem, xcolor, fancyhdr, xurl, hyperref,
and cleveref. No bibliography processor or external figures are needed.

    bash build.sh

This creates `build/article.pdf` and `build/verification.json`, without replacing
the delivered PDF or verification receipt. Set `PYTHON` or `PDFLATEX` in the
environment to choose other executable names. Compilation timestamps may make
PDF bytes differ on rebuilding; they do not affect mathematical content.

### Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 69 and 70 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`. The title-page wording ("AI-assisted", "Prepared for
Vladimir Reshetnikov"), the `pdfauthor` entry and the US Letter page size are
kept as delivered.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble (the theorem counter is unchanged).
  Three notes:
  - in Section 2.1, after the normalization paragraph: the transform identity
    (2.1) is machine-checked for every real `|q| < 1`, in the repository's
    normalized `[0,1]` convention, as
    `Fabius.charFun_geometricUniformDistribution_eq_phase_mul_geometricSincProduct`
    (`Analysis/FabiusFunction/Lean/FabiusFunction/GeometricSincCharacteristicFunction.lean`),
    and the dyadic two-section the article cites by file is
    `Fabius.ProbabilityRepresentation.geometricUniformDistribution_one_half_multisection`
    with its convolution form `..._one_half_conv_one_quarter`
    (`GeometricUniformMultisection.lean`), the case `q = 1/2`, `m = 2` of
    (5.3); no result of the article is formalized;
  - after Proposition 4.5 (`prop:same`): it is `thm:self-spectrum` of
    `../Arithmetic_Convolution_Factors_Fabius_Type_Laws/` (filed 2026-09-28),
    stated there for every `0 < q < 1` in the same normalization and proved
    the same way, which the article does not cite (it read only that
    article's README, which does not list the theorem); with `q = 1/b` it is
    item 1 of `conj:general-base` of
    `../Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/` for every
    integer base, not only the prime-power bases recorded there before;
  - after Remark 8.2: the mechanism of Theorem 8.1 (`thm:metric`) is that of
    `prop:wasserstein` of the same article (divisibility-ladder targets),
    which that article's README lists and this article does not cite; the
    targets differ, so neither statement contains the other.
  One further marked change: the title page no longer sets page anchors, which
  removes the delivered source's one duplicate-destination warning (`page.1`).
- Reciprocal notes now stand in
  `../Arithmetic_Convolution_Factors_Fabius_Type_Laws/article.tex` (after its
  questions "Beyond divisibility ladders", "Two arbitrary geometric ratios",
  which this article answers for all but countably many target ratios, and
  "Optimal approximate factorization"), after `conj:general-base` of
  `../Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/`, and under Q6
  of `../Simultaneous_Convolution_Divisors_Fabius_Type_Laws/`.
- `article.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29): 25 pages (24 as delivered; the notes add
  one), US Letter, with no error, undefined reference, multiply defined label,
  duplicate destination, overfull or underfull box; every font embedded, no
  Type 3 font. The pages carrying the notes were rendered and inspected.
  `results/build_validation.json` is the delivered build record and describes
  the delivered 24-page PDF; its `pdf_hash` is that file's.
- `code/verify.py` and `build.sh` are unchanged: the program already writes
  `verification.rerun.json` (LF) unless `--output` is given, and `build.sh`
  writes only to `build/`. It calls `python3` by default; on the ProveIt
  machine set `PYTHON=py`. A rerun on a copy (2026-09-30, `py code/verify.py`,
  Python 3.14.4, standard library) passed all 156,227 checks; its
  `verification.rerun.json` equals `results/verification.json` byte for byte,
  and its console output equals `results/verification.log` up to the Windows
  console's line endings.
- `README.md`: the file list (page count, build record, retired ledger), the
  note under the verification command, and this section.
