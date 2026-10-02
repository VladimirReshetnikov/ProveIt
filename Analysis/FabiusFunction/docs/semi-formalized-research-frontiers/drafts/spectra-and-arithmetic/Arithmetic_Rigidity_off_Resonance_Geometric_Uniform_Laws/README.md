# Arithmetic Rigidity off Resonance
## Exact convolution factors of geometric-uniform laws

Research manuscript prepared for Vladimir Reshetnikov, 30 September 2026.

The package contains a standalone article, complete written proofs, nine further
research questions, and exact finite arithmetic certificates. It extends the
Fabius/Rvachev convolution-divisor program in ProveIt to rationally separated
source scales and to prime-power rational-return channels.

### Files

- `article.pdf`: the compiled article (26 pages since the editorial passes below;
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

### Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/`; every change
to the source is marked `% ed. (2026-10-01)`. The mathematical text is
unchanged.

- `article.tex`: a second unnumbered environment `ednotelater` ("Editorial
  note (ProveIt, 2026-10-01)") is defined after `ednote`. Two notes, on two
  later unreviewed notes filed in `../../representations/` (batch 72), which
  do not cite this article (nor it them):
  - after Theorem 3.1 (`thm:separated`) and its remark:
    `../../representations/Arithmetic_Geometric_Mask_Order/` compares
    observation masks of independent uniforms of lengths `c q^i` under a
    common tilt by one kernel valid for every total-sum reweighting, which by
    Theorem 1.1 of `../../representations/Universal_Fabius_Mask_Criterion/`
    is convolution divisibility of the observed sums; for `q` in the
    nonresonant set `N`, Theorem 3.1 here forces every target length `c q^j`
    to be `c q^i / n` with distinct `i`, hence `i = j`, `n = 1`, and the order
    is mask inclusion, case 1 of that note's Theorem 2.1. That note proves
    it by the same zero-multiplicity argument, also for ratios with a
    rational but no integer power of `1/q`, and orders the masks for
    `q = M^{-1/d}` by prefix counts in the residue classes modulo `d`, a
    sub-mask analogue of the rationality classes of Theorem 6.2
    (`thm:channels`);
  - after the question "Composite reciprocal returns" and its discussion:
    for finite sources the finite step of the suggested route is carried out
    there. For uniforms of lengths `a_i h` over `b_j h`, divisibility under a
    common tilt is decided by `P(u) = prod [a_i]_u / prod [b_j]_u`: with
    equally many uniforms, `P` must be a polynomial with nonnegative
    coefficients (Theorem 3.1 of the second note); with `r` more source
    uniforms, `P` must be a polynomial whose coefficient measure at spacing
    `h`, convolved with `r` uniforms of length `h`, is nonnegative (Theorem
    1.1 of `../../representations/Uniform_Smoothing_Mask_Stabilization/`). For
    the lengths of Proposition 11.1 (`prop:base6`, `h = 1/6`) the quotient is
    `1 - u + u^2`, and nine further uniforms of length `h` make the factor a
    probability measure, eight do not (Theorem 5.1 there), whereas the tail
    `D_{1/36} mu_{1/6}` (support length `1/30`) leaves the negative central
    mass. The infinite tail of `mu_q` is not treated there.
- `article.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29): 25 pages, as before, 540,279 bytes, US
  Letter, with no error, undefined reference, multiply defined label,
  duplicate destination, overfull or underfull box; every font embedded, no
  Type 3 font. The pages carrying the notes were rendered and inspected.
- `README.md`: this section.

Three further notes of the same date were added in the editorial pass after
batch 73 of `docs/incoming/`, on the later unreviewed draft
`../Wasserstein_Contact_Orders_Uniform_Factor_Resonances/` (batch 73,
2026-10-01), which answers this article's question "Sharp distance to a
resonance" and cites the batch-69 version of this file:

- `article.tex`, after the 2026-09-30 note that follows Remark 8.2: for
  `N = 2`, `M = 3` the exponent is now known near `q = 1/2`. That draft's
  Lemma 2.1 compares Fourier derivatives at the double zero; with `mu_q`
  supported in `[-R_q, R_q]`, `R_q = 1/(2(1-q))`, it gives
  `W_1(mu_q, sigma * nu) >= D_q / (2 pi (1 + 2 pi T R_q))` under the
  hypotheses of Theorem 8.1, linear in `D_q` where (8.4) is quadratic; near
  `q = 1/2`, `D_q ~ |P| |q - 1/2| / 3` with
  `P = prod_{k>=2} sinc(6 pi 2^(-k)) = -0.0462...`, so (8.4) is of order
  `(q - 1/2)^2` and the new bound of the exact order `|q - 1/2|`;
- after Corollary 9.2 and its discussion: the bound (9.2) is improved to
  `Delta(q) <= |q - 1/2| / 4` for every `q` (smaller for every `q`, since
  `2(1-q) < 4`) by adapting the whole remainder,
  `nu_q = Law(D_3 + sum_{k>=2} q^k U_k)`, at coupling cost
  `|q - 1/2| E|U_1|` (that draft's Theorem 1.1); with its lower bound,
  `Delta(q_j)` is of exact order `1/j` along the sequence of Theorem 9.1;
- after the question "Sharp distance to a resonance" and its discussion:
  answered for every approach to `1/2`: `Delta(1/2 +/- t) = c_+/- t + o(t)`
  with `|P|/(6 pi (1 + 12 pi)) <= c_+/- <= 1/4` (about `6.33e-5` below),
  `c_+/-` the `L^1` distances of `+/- v` to the closed cone generated by
  `F_{sigma * nu} - F_{mu_{1/2}}` (not evaluated; `c_+ = c_-` undecided);
  for `U_{1/B} * U_{B^-j}` (fixed integers `B >= 2`, `j >= 1`) the distance
  is of exact order `|q - 1/B|^j` on both sides (its Theorem 1.2), and
  `Delta <= 6259 (q - 1/2)^2` for `U_{1/2} * U_{1/4}` when
  `|q - 1/2| <= 1/100` (its Theorem 1.3).
- `article.pdf`: rebuilt with three `pdflatex` passes (MiKTeX 26.2, pdfTeX
  1.40.29), on a copy: 26 pages (25 before), 550,813 bytes, US Letter, with
  no error, undefined reference, multiply defined label, duplicate
  destination, overfull or underfull box; every font embedded, no Type 3
  font. The pages carrying the notes were rendered and inspected. The source
  is now 1,020 lines/76,262 bytes.
- `README.md`: the page count under "Files", this paragraph and the bullets
  above.
