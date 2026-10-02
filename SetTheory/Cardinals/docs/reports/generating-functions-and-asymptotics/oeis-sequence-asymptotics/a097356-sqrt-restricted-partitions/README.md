# Three Exceptions Before Every Square

**Sharp OEIS partition asymptotics, an all-orders coefficient calculus, and phase-sensitive inverse expansions for A097356 and the quadratic restricted partitions A206226, A206227, A206240**

This research report is dated 1 October 2026. It was built from two manuscripts of ProveIt's incoming-reports intake, written independently of each other: number 38 of batch 73O1, the primary text, and number 02 of batch 74, merged as a second derivation (Section 16, plus a lemma and a theorem in Section 9). Both prove the same three main theorems with the same constants. The author line of manuscript 38, kept on the title page, is "Research report prepared for Vladimir Reshetnikov" and names no assistant; manuscript 02's title page reads "Prepared for Vladimir Reshetnikov" and its PDF metadata names "OpenAI, prepared for Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| primary | batch 73O1, no. 38 | `OEIS_SquareRoot_Partition_Research.zip` (*Three Exceptions Before Every Square*, 27-page PDF, 27 files) | `1f1981f68` | `f8c3a392a` | `9df4ba51a` | Sections 1–15 and Appendices A–B; Appendix C added in the write |
| second derivation | batch 74, no. 02 | `A097356_Sharp_Envelopes_Transseries_Inversion.zip` (*Square-Root Restricted Partitions: Sharp Envelopes, All-Orders Phase Expansions, and Quantized Inversion*, 29-page PDF, 20 files) | `905bdc785` | `c664fc2f0` | `b669cff87` | Section 16; Lemma 9.3 and Theorem 9.4; files prefixed `02-sharp-` |

The pin `1f1981f682b2878bde51a6ad40c22777f362fc05` is the ProveIt commit manuscript 38 inspected (2026-10-01, "Merge origin/main (HilbertTenthProblem research) before pushing the batch-72D placement"). Its delivered `PROVENANCE.md` calls it a "recursive-tree checkpoint"; it is a commit. The pin `905bdc785424922c79fc24f56d27960ecb1085dd` is the commit manuscript 02 inspected (2026-10-01 18:00, "Lower the recoded Tseytin factor frontier by one multiplication throughout"). That commit already held manuscript 38's archive, unopened, in `docs/incoming`; the two texts share 0.7 % of their word 8-grams. Each placement commit deleted its archive from `docs/incoming`; the archives survive in the arrival commits `f8c3a392a` and `c664fc2f0`.

**Status: AI-assisted, unrefereed, not formalized.** The intake recomputed the constants to 60 digits, checked the three-exception pattern by exact integer arithmetic, compared every constant the two manuscripts share, and reran both manuscripts' scripts on copies. It did not re-derive every proof.

## Files

```
README.md                         this guide (replaces both delivered READMEs)
article.tex                       the report (LaTeX, internal bibliography)
article.pdf                       the compiled report, 40 pages
PROVENANCE.md                     manuscript 38's sources, pin and result boundaries, as delivered
VALIDATION.md                     manuscript 38's record of its completed run and PDF checks, as delivered
02-sharp-SOURCES.md               manuscript 02's source and novelty audit, as delivered
02-sharp-VERIFICATION.md          manuscript 02's record of its checks, as delivered
code/partition_asymptotics.py     (38) saddle constants, all-orders coefficient operator, phase polynomials,
                                  inverse coefficients, exact partition DP (mpmath)
code/certificate.py               (38) exact rational sign certificate for kappa_3 < 0 < kappa_4 (standard library)
code/verify.py                    (38) driver: exact counts, numerical comparisons, writes the data files below
code/make_figures.py              (38) recreates the two figures from data/plot_data.json (Matplotlib, NumPy)
code/02-sharp-expansion.py        (02) high-precision coefficient recurrence, evaluation, inverse prediction (mpmath)
code/02-sharp-certify.py          (02) rational interval saddle/sign certificate (fractions; SymPy for Bernoulli numbers)
code/02-sharp-symbolic_checks.py  (02) exact SymPy checks of the closed forms of a, lambda and of the P1, P2 transforms
code/02-sharp-verify.py           (02) exact enumeration to N = 20000, OEIS prefixes, coefficient, boundary, inverse tests
code/02-sharp-Makefile            (02) delivered targets pdf, verify, clean (delivery paths)
data/coefficients.json            (38) saddle constants and coefficients D_j, phase and inverse coefficients
data/sign_certificate.json        (38) the certificate's exact interval enclosures
data/quadratic_checks.csv         (38) square, plus-shift and minus-shift subsequences against the expansion
data/floor_checks.csv             (38) the floor-dependent expansion at sample N
data/endpoint_checks.csv          (38) R((m+1)^2-1)/C_- and the scaled defect at m = 16 ... 256
data/three_exception_checks.csv   (38) the last four indices of the blocks m = 16 ... 256
data/inverse_checks.csv           (38) inverse thresholds: smooth, phase-map and corrected
data/summatory_checks.csv         (38) the summatory law
data/plot_data.json               (38) the figure data
data/verification_summary.json    (38) summary of the completed run (max_m = 256, N <= 66048)
data/run_log.txt                  (38) standard output of that run
data/requirements.txt             (38) mpmath==1.3.0
data/requirements-figures.txt     (38) -r requirements.txt, matplotlib==3.10.8, numpy==2.3.5
data/02-sharp-shell_errors.csv    (02) relative errors of the shell expansion, orders 0-4, m = 10 ... 140, sigma = -1 ... 2
data/02-sharp-phase_checks.csv    (02) the phase-normalized first correction against P_1
data/02-sharp-boundary_defects.csv (02) R(k^2-r)/C_- - 1 and its k-scaling, k = 10 ... 140, r = 1 ... 6
data/02-sharp-inverse_checks.csv  (02) integer thresholds, exact inverse and clipped-phase prediction
data/02-sharp-constants_and_polynomials.json (02) constants and the shell polynomials through order 4 (60 digits)
data/02-sharp-coefficients.txt    (02) standard output of 02-sharp-expansion.py (constants, shell polynomials)
data/02-sharp-certified_signs.txt (02) standard output of 02-sharp-certify.py
data/02-sharp-symbolic_checks.txt (02) standard output of 02-sharp-symbolic_checks.py
data/02-sharp-verification_log.txt (02) standard output of 02-sharp-verify.py
data/02-sharp-requirements.txt    (02) mpmath==1.3.0, sympy==1.14.0
figures/phase_profile.pdf         (38) Figure 1 (included by article.tex)
figures/phase_profile.png         raster preview
figures/inverse_phase.pdf         (38) Figure 2 (included by article.tex)
figures/inverse_phase.png         raster preview
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to its delivery.

- **Manuscript 38, delivery names:** the four scripts were at the package root and are now in `code/`; the eleven files of `results/` and the two requirements files are now in `data/`; `PROVENANCE.md`, `VALIDATION.md` and `figures/` kept their places. Not shipped: its `article.pdf` (replaced by a build of this text) and its checksum ledger `SHA256SUMS` (verified 26/26 at intake, then retired).
- **Manuscript 02, delivery names:** `verification/{expansion,certify,symbolic_checks,verify}.py` → `code/02-sharp-*.py`; `Makefile` → `code/02-sharp-Makefile`; `data/*` → `data/02-sharp-*`; `requirements.txt` → `data/02-sharp-requirements.txt`; `SOURCES.md`, `VERIFICATION.md` → `02-sharp-SOURCES.md`, `02-sharp-VERIFICATION.md` at the root. Not shipped: its `article.tex` (merged into this one), `README.md` and `article.pdf`. It shipped no checksum ledger.
- **Line ends.** The ten CSV files (six of 38, four of 02) are CRLF as delivered and are kept so by `-text` lines in `SetTheory/Cardinals/.gitattributes`. Manuscript 38's four JSON files have no final newline, as delivered.

## Labels and numbering

Every label carries the prefix `srp:`. Manuscript 38's 125 delivered labels keep their names after the prefix, and its write added one (`srp:app:provenance`). The batch-74 write added **44** labels, all with the sub-prefix `srp:se:`: **170** labels in all. No existing label was renamed or removed, and no existing section, statement, equation, table or figure number changed (checked against the `.aux` of the previous build). To keep them, the new material is a Section 16 placed after the Conclusion (Section 15) rather than before the research questions, the lemma and theorem added to Section 9 follow its last numbered item (they are Lemma 9.3 and Theorem 9.4), and Section 16's five tables are numbered 16.1–16.5 so that the appendix table keeps its number 5.

Text added in the writes is marked *[Write note, batch 73O1, 1 October 2026.]* or *[Write note, batch 74, 1 October 2026.]*. Batch-73O1 notes stand after the abstract, after Proposition 11.2, in Sections 13.5 and 14.8, in Appendix B.1 and in Appendix C; batch-74 notes stand after the abstract, after Theorem 2.3, before Lemma 9.3, in Sections 14.1 and 14.7, at the head of Section 16 and in Appendix C. A later reciprocal note at the end of Section 14.6 is the bracketed paragraph "[Added 1 October 2026, batch 74: …]". The 73O1 write also added cleveref type hints (`\label[lemma]`, `\label[proposition]`) to the eleven labels of lemmas and propositions, and `\crefalias{section}{appendix}` after `\appendix`. Bibliography entries added in the writes are marked "[Added in the write.]" (three) and "[Added in the batch-74 write, from manuscript 02.]" (three). No delivered sentence, statement, proof, table or figure of manuscript 38 was changed or removed. Manuscript 02's text is restated in this report's notation, with some proofs condensed; none of its statements was strengthened.

## What is claimed

Let A(N) = p_{⌊√N⌋}(N) count partitions of N into parts at most ⌊√N⌋ (A097356). Let u > 0 solve ∫₀¹ x/(e^{ux} − 1) dx = 1 and set ρ = 1 − e^{−u}, H = 2u − log ρ, d = e^H, C = u/(2π√(2 − 3e^{−u})), C_− = Cρ = 0.0881548837986971165… and β = −log ρ = H − 2u.

Proved by both manuscripts, printed once (Sections 2–12):

- **Phase expansion** (Theorem 2.1): A(N) = C e^{Ht} t^{−2} ρ^θ (Σ_{k≤K} P_k(θ) t^{−k} + O(t^{−K−1})) with t = √N, θ = {√N}, to every fixed order K. The cluster set of N A(N) d^{−√N} is [C_−, C]: Kotesovec's conjectured lower constant in A097356 is the **liminf**.
- **Three exceptions** (Theorem 2.2): for every sufficiently large m, inside the block m² ≤ N < (m+1)², the literal inequality A(N) ≥ C_− d^{√N}/N fails exactly at N = (m+1)² − 3, (m+1)² − 2, (m+1)² − 1. The upper inequality with C holds eventually, and the number of violations up to X is 3√X + O(1). So the literal eventual-inequality reading of the OEIS conjecture is false.
- **Inverse** (Theorem 2.3): with the Lambert-W_{−1} core X(Y) and a piecewise-linear phase map T, √Q(Y) = T(X(Y)) + O(1/X), with exact plateaus.
- The log-uniform limiting law (Theorem 9.2), the first correction (Proposition 5.2), the endpoint signs κ₃ < 0 < κ₄, and the first two inverse coefficients of the square subsequence.

Manuscript 38 only:

- **Uniform all-orders calculus** for p_m(αm² + σm + τ) (Lemma 3.1, Proposition 4.1, Theorem 5.1), with an explicit Gaussian coefficient operator, covering A206226, A206227 and A206240; exact rational sign certificates (Proposition 8.2, Appendix A); a summatory law (Theorem 10.1); all-orders inverse coefficients of the square subsequence (Proposition 11.1); plateaus, interior brackets and an all-orders interior recurrence for the full inverse (Section 12); computations to N = 66048.

Manuscript 02 only (Section 16 and Section 9):

- a second route to first order from the Szekeres–Canfield formula, with G′(μ) = −log(1 − e^{−u(μ^{−2})}) (Proposition 16.1), and a generating-function route to the phase polynomials with an explicit formula for P₂ (Proposition 16.2);
- 0 < u < 1, V = (3ρ − 1)/(uρ) and Li₂(ρ) = u² (Lemma 16.3);
- the exact degree 2k of D_k(1; σ, 0) in σ, with leading coefficient (−1)^k/(k!(2V)^k) (Proposition 16.4);
- closed forms of V, ℓ′, ℓ″, F‴, F⁗ and of the first-correction coefficients a and λ in ξ = 1/(e^u − 1) (Proposition 16.5);
- the **second-order envelope constants** limsup √N(R/C − 1) = a = D₁(0,0) and liminf √N(R/C_− − 1) = κ₁ (Theorem 16.6);
- the forward boundary layer R(k² + r)/C = 1 + (a − βr/2)/k + O(k^{−2}) (Proposition 16.7);
- ordinary steps exp(u/m) against square jumps A(k²)/A(k² − 1) → 1/ρ = 1.7946676740964… (Proposition 16.8);
- the **exact phase loss** of the uncorrected inverse: limsup (Q(Y) − X(Y)²)/log Y = 2β/H² = 0.2385882013…, liminf 0 (Proposition 16.9);
- the ratio form p_m(m² + σm)/p_m(m²) (Proposition 16.10) and A206240 as partitions of m² into exactly m parts (Remark 16.11);
- a Fourier identity for the phase factor ρ^{{√N}} with its square-point correction (Section 16.5);
- the **rate O(M^{−1/2})** in the log-uniform law for Lipschitz test functions (Lemma 9.3, Theorem 9.4), which partly answers the question in Section 14.7;
- an independent second rational sign certificate (Section 16.6), its own computations (Section 16.7) and four further research questions (Section 16.8).

**Not new here:** the leading Szekeres asymptotic (Canfield, Romik) and the OEIS amplitudes of A206226, A206227, A206240 and the constant A258268 are classical and credited by both manuscripts. The discrete threshold transport (Proposition 11.2), the rounding steps of manuscript 02's inverse and interior formula, and its two-term square inverse are instances of the transseries volume's inversion apparatus (see "Relation to neighbouring material"); neither manuscript claims novelty for them.

## What is not claimed

These are both manuscripts' own limits, kept in full: manuscript 38's delivered README ("Attribution and limits"), `PROVENANCE.md` ("Result boundaries"), `VALIDATION.md` ("Remaining boundaries") and article Sections 1.2 and 14; manuscript 02's delivered README ("Scope and provenance"), `02-sharp-VERIFICATION.md` ("What these checks do not establish"), `02-sharp-SOURCES.md` ("Priority boundary"), its title page and its outcome ledger (Section 16.1).

- **No effective m₀**, and no explicit universal constant in the inverse's O(1). The three-exception theorem gives the existence of a cutoff, not a certified smallest one. The shipped data show the pattern is not yet stable at m = 64: in `data/three_exception_checks.csv` the third-last index is still above the envelope at m = 16, 32, 64 (relative defect +0.0031, +0.00059, +0.000030) and below it at m = 128 and 256; manuscript 02's `data/02-sharp-boundary_defects.csv` has it below at m = 79, 99 and 139. A computation made for the batch-74 write (exact counts, comparison in 50-digit arithmetic, not certified, not shipped) found exactly two exceptions for 60 ≤ m ≤ 71 and exactly three for every 72 ≤ m ≤ 200 (note in Section 14.1); that no reversal occurs later is not shown.
- **"All orders" means every fixed truncation order with a proved remainder.** No convergence of the correction series is asserted.
- **"Transseries" is used loosely**, in manuscript 38's subtitle and in manuscript 02's archive name. The floor-dependent expansion is a phase-parametrized Poincaré expansion, "not an ordinary power–logarithmic transseries of a smooth germ" (article §1.2); manuscript 02's own classification (Section 16.5) reaches the same conclusion. No complete exponentially small saddle decomposition, exponentially improved or resurgent transseries, Borel summability or optimal truncation is claimed; noncentral arcs are shown smaller than every algebraic order, but their exponential sectors and Stokes data are not determined.
- No all-orders uniform inverse across the switching layers; the summatory law only to relative order 1/m.
- No global first-discovery priority: both manuscripts' repository and literature searches were bounded, and manuscript 02 states that its results' "novelty as independently published results is not asserted". Manuscript 02 consulted only the metadata and abstract of Romik's article and attributes Szekeres' papers through Canfield's bibliography.
- Both rational certificates certify finite sign inputs using written tail bounds; neither formalizes the contour analysis. The arbitrary-precision tables of both manuscripts are checks, not proofs.
- No Lean or Coq formalization is included or claimed (Section 14.8 sketches a route; manuscript 02 adds that a proof-producing checker for its certificate would certify only the sign claims).
- The OEIS transcription checks (manuscript 38: first 54 terms of A097356 and 17 of A206226, embedded in `code/verify.py`; manuscript 02: 54 terms of A097356 and 24 of each companion, embedded in `code/02-sharp-verify.py`) and every statement about the OEIS entries refer to the entries as inspected on 1 October 2026; the intake did not re-fetch them. Manuscript 02's suggested OEIS statements (Section 16.8) were not submitted, and neither manuscript edited the OEIS or the repository.
- Both reports are unreviewed; manuscript 02 asks for "independent mathematical review before publication or entry updates".

## Relation to neighbouring material

- **Transseries volume** `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`: Proposition 11.2 (`srp:prop:ceil`) and the separation remark after it are the case x_* = x_K(Y), η = δ_K of Theorem `p0:thm:staircase` (`transseries_and_inversion.tex`, "Staircase recovery and the separation condition"), parts (1)–(2). The same parts cover the integer rounding in manuscript 02's global inverse and interior rounding formula, and its two-term square-subsequence inverse is a perturbed inversion around the Lambert core in the sense of `p0:thm:perturbed-inversion`. Only the analytic inputs (Theorem 5.1 and its widths) are specific to A097356. Manuscript 02 is not filed in the transseries tree: its own analysis finds a shellwise, not a transseries, expansion, and a manuscript continuing a collection report goes to that report.
- **Lean.** Placement beside formal developments confers no formal status. The order-theoretic content of `p0:thm:staircase` parts (1)–(2) is formalized in `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean` as `Fabius.staircase_ceil` and `Fabius.staircase_separation` (listed in the transseries volume's README). None of the statements of this report is formalized, including the analytic inputs of Proposition 11.2 and of manuscript 02's inverse.
- **Fabius tree.** Proposition 4.1 (`srp:prop:product`) splits off h(z) = log(z/(1 − e^{−z})) before an Euler–Maclaurin expansion of a finite q-Pochhammer product; manuscript 02's Euler–Maclaurin lemma does the same. The draft `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/combinatorial-coefficient-calculus/Gaussian_Coefficient_Calculus/Gaussian_Coefficient_Calculus.tex`, Theorem `q3:thm:double-scaling`, uses the same device for the Gaussian binomial at real argument. It is a sibling lemma for a different object, not the same theorem.
- **Sibling partition reports** in this directory: [`a022629-distinct-partition-norms`](../a022629-distinct-partition-norms/) (∏(1 + k^α q^k)) and [`a033552-catalan-partitions`](../a033552-catalan-partitions/) (parts in the Catalan numbers). They study different products in different saddle regimes and share only the standard toolkit (exact saddle with an all-orders Edgeworth expansion, Lambert-W inversion with integer staircases); no proposition is proved twice.
- **Cubic boundary** [`a238016-restricted-partitions-cubic-boundary`](../a238016-restricted-partitions-cubic-boundary/) (batch 74, manuscript 05): the same counts p_m(N) at N ≍ m³, the end α → ∞ of Section 14.6's question; there p_m(N) ~ N^(m−1)/(m!(m−1)!) iff N/m³ → ∞ (its Theorem 2.3), which bears on that question without answering it (reciprocal note "[Added 1 October 2026, batch 74: …]" at the end of Section 14.6; no label added). No other repository report treats A097356, A206226, A206227, A206240 or A258268.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build needs `figures/phase_profile.pdf` and `figures/inverse_phase.pdf` beside `article.tex`, and the newtx fonts. pdfLaTeX (MiKTeX 26.2) produced the shipped `article.pdf`: 40 pages, with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`. The two figure PDFs embed Matplotlib Type 3 fonts (DejaVu Sans), as delivered.

## Rerunning the scripts

Run on copies, never in the report directory: both manuscripts' scripts write under their **delivery** names, and manuscript 02's `verify.py` writes into `../data/` relative to its own directory under unprefixed names — run from `code/` it would fail to import its sibling `expansion`, and if made to run it would overwrite manuscript 38's `data/inverse_checks.csv`.

Manuscript 38 (`verify.py --output` defaults to `results/`; `make_figures.py` reads `results/plot_data.json` and writes into `figures/`):

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a097356-sqrt-restricted-partitions
W=$(mktemp -d)
cp "$R"/code/certificate.py "$R"/code/partition_asymptotics.py "$R"/code/verify.py "$R"/code/make_figures.py "$W"/ && cd "$W"
py certificate.py                                                    # exact rational checks; prints JSON, writes nothing
uv run --no-project --with mpmath==1.3.0 python verify.py --max-m 256 --output results   # about 46 s
# optional figures: uv run --no-project --with matplotlib==3.10.8 --with numpy==2.3.5 \
#                     python make_figures.py --data results/plot_data.json --output figs
```

Manuscript 02 (rebuild its delivered layout, `verification/` beside an empty `data/`):

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a097356-sqrt-restricted-partitions
W=$(mktemp -d); mkdir -p "$W"/verification "$W"/data
for f in expansion certify symbolic_checks verify; do cp "$R"/code/02-sharp-$f.py "$W"/verification/$f.py; done
cd "$W"; PY="uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python"
$PY verification/certify.py          > data/certified_signs.txt
$PY verification/symbolic_checks.py  > data/symbolic_checks.txt
$PY verification/verify.py --max-n 20000 > data/verification_log.txt   # writes the four CSVs and the JSON into data/
$PY verification/expansion.py        > data/coefficients.txt
# compare data/X with $R/data/02-sharp-X, ignoring CR bytes
```

Do not run Python with `-O`: both certificates and manuscript 02's checks rely on assertions.

- At the 73O1 intake (Windows, mpmath 1.3.0) manuscript 38's `verify.py --max-m 256` wrote ten files: the six CSV files and `plot_data.json` were byte-identical to the shipped `data/` files, and `coefficients.json`, `sign_certificate.json` and `verification_summary.json` equal apart from CRLF line ends (Windows text mode; the delivery was made with LF). Its standard output equals `data/run_log.txt`, which is a capture of that output, not a file the script writes. The figure script was not rerun; regenerated figures differ in bytes (Matplotlib metadata).
- At the batch-74 write (Windows, Git Bash, mpmath 1.3.0, SymPy 1.14.0) the four commands above took about 10 s in all and reproduced all nine of manuscript 02's recorded outputs: the four CSV files byte for byte (its `csv` writer emits CRLF on every platform, as delivered), and `constants_and_polynomials.json` and the four captured `.txt` outputs apart from CRLF line ends. The last command is not in manuscript 02's Makefile or README: `data/02-sharp-coefficients.txt` is the standard output of `expansion.py` run as a script.

## Disclosures and discrepancies

- The delivered READMEs of both manuscripts are not shipped; this guide replaces them. Manuscript 38's commands (`python certificate.py`, `python verify.py --max-m 256 --output results`, `python make_figures.py`) and file list assume its layout (`results/`, scripts at the root); manuscript 02's (`python verification/certify.py`, `python verification/verify.py --max-n 20000`, `make verify`) assume `verification/` and `data/`.
- `VALIDATION.md` and `PROVENANCE.md` still use manuscript 38's delivery names (`results`, `verify.py` at the root) and describe its delivered 27-page PDF, which is not shipped. `VALIDATION.md`'s statement that the ZIP "contains no build auxiliary files" refers to the delivered archive.
- `02-sharp-VERIFICATION.md` describes manuscript 02's delivered 29-page PDF and its LaTeX checks, not this build, and names `data/symbolic_checks.txt` and `data/certified_signs.txt` (now `data/02-sharp-*`). `code/02-sharp-Makefile` names `verification/*.py`, `data/*` and `article.tex` by their delivery paths; its `pdf` target would build this report, not manuscript 02's article. The docstrings and imports of `code/02-sharp-*.py` (`from expansion import …`, output to `parents[1]/'data'`) assume the delivery layout.
- `02-sharp-SOURCES.md` says that "Indexed GitHub code search for A097356 returned no matches", and manuscript 02's article that searches "did not locate a source stating these particular second-order and inverse formulas". Both are stale: the pinned commit already held manuscript 38's archive (dated note in Section 16.1).
- `02-sharp-requirements.txt` lists `mpmath==1.3.0` and `sympy==1.14.0` (SymPy is needed by `certify.py` for Bernoulli numbers and by `symbolic_checks.py`); manuscript 02 recorded its run with Python 3.13.5.
- The article's Sections 13.5 and Appendix B.1 describe manuscript 38's delivered layout; write notes there give the shipped paths. `code/make_figures.py`'s docstring and defaults name `results/plot_data.json`.
- `PROVENANCE.md` calls manuscript 38's pin a "recursive-tree checkpoint"; it is a commit (above).
- Manuscript 38's subtitle "inverse transseries" and manuscript 02's archive name "…_Transseries_Inversion" are the delivered wording; see "What is not claimed".
- Manuscript 02 indexes a block by its upper square (shell (k − 1)² ≤ n < k²), this report by its lower one (block m); Section 16 converts throughout (m = k − 1).

## Provenance

Appendix C of the article records both sources, their pins, where the merge had to choose, what each write changed and the map from delivery names to shipped paths. The placement commit `9df4ba51a` records the batch-73O1 decisions: no repository report treats these sequences, the manuscript shares no proposition with the batch's other partition manuscripts (39, 40, 48), and Proposition 11.2 is printed as a pointer to the staircase theorem, not as new. The placement commit `b669cff87` records the batch-74 decision: manuscript 02 proves this report's three main theorems in independent text, with every shared constant equal, so it is merged as a second derivation with only its own results added, not as a Part and not in the transseries tree.
