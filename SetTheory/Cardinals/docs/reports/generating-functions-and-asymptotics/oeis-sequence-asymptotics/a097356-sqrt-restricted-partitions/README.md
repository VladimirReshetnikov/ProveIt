# Three Exceptions Before Every Square

**Sharp OEIS partition asymptotics, an all-orders coefficient calculus, and phase-sensitive inverse expansions for A097356 and the quadratic restricted partitions A206226, A206227, A206240**

This research report is dated 1 October 2026. It was built from one manuscript, number 38 of batch 73O1 of ProveIt's incoming-reports intake. Its author line, kept as delivered, is "Research report prepared for Vladimir Reshetnikov"; it names no assistant.

| Source | Batch-73O1 manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| sole | 38 | `OEIS_SquareRoot_Partition_Research.zip` (*Three Exceptions Before Every Square*, 27-page PDF, 27 files) | `1f1981f68` | `f8c3a392a` | `9df4ba51a` | the whole report; Appendix C added in the write |

The pin `1f1981f682b2878bde51a6ad40c22777f362fc05` is the ProveIt commit the manuscript inspected (2026-10-01, "Merge origin/main (HilbertTenthProblem research) before pushing the batch-72D placement"). The delivered `PROVENANCE.md` calls it a "recursive-tree checkpoint"; it is a commit. The placement commit `9df4ba51a` deleted the archive from `docs/incoming`; it survives in the arrival commit `f8c3a392a`.

**Status: AI-assisted, unrefereed, not formalized.** The intake recomputed the constants to 60 digits, checked the three-exception pattern by exact integer arithmetic, and reran both scripts on a copy. It did not re-derive every proof.

## Files

```
README.md                         this guide (replaces the delivered README)
article.tex                       the report (LaTeX, internal bibliography)
article.pdf                       the compiled report, 29 pages
PROVENANCE.md                     the manuscript's sources, pin and result boundaries, as delivered
VALIDATION.md                     the manuscript's record of its completed run and PDF checks, as delivered
code/partition_asymptotics.py     saddle constants, all-orders coefficient operator, phase polynomials,
                                  inverse coefficients, exact partition DP (mpmath)
code/certificate.py               exact rational sign certificate for kappa_3 < 0 < kappa_4 (standard library)
code/verify.py                    driver: exact counts, numerical comparisons, writes the data files below
code/make_figures.py              recreates the two figures from data/plot_data.json (Matplotlib, NumPy)
data/coefficients.json            saddle constants and coefficients D_j, phase and inverse coefficients
data/sign_certificate.json        the certificate's exact interval enclosures
data/quadratic_checks.csv         square, plus-shift and minus-shift subsequences against the expansion
data/floor_checks.csv             the floor-dependent expansion at sample N
data/endpoint_checks.csv          R((m+1)^2-1)/C_- and the scaled defect at m = 16 ... 256
data/three_exception_checks.csv   the last four indices of the blocks m = 16 ... 256
data/inverse_checks.csv           inverse thresholds: smooth, phase-map and corrected
data/summatory_checks.csv         the summatory law
data/plot_data.json               the figure data
data/verification_summary.json    summary of the completed run (max_m = 256, N <= 66048)
data/run_log.txt                  standard output of that run
data/requirements.txt             mpmath==1.3.0
data/requirements-figures.txt     -r requirements.txt, matplotlib==3.10.8, numpy==2.3.5
figures/phase_profile.pdf         Figure 1 (included by article.tex)
figures/phase_profile.png         raster preview
figures/inverse_phase.pdf         Figure 2 (included by article.tex)
figures/inverse_phase.png         raster preview
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to the delivery. Delivery names: the four scripts were at the package root and are now in `code/`; the eleven files of `results/` and the two requirements files are now in `data/`; `PROVENANCE.md`, `VALIDATION.md` and `figures/` kept their places. Not shipped: the delivered `article.pdf` (replaced by a build of this text) and the checksum ledger `SHA256SUMS` (verified 26/26 at intake, then retired). The six CSV files are CRLF as delivered and are kept so by `-text` lines in `SetTheory/Cardinals/.gitattributes`; the four JSON files have no final newline, as delivered.

## Labels and numbering

Every label carries the prefix `srp:`. The 125 delivered labels keep their names after the prefix, and the write added one (`srp:app:provenance`): **126** labels. No section, statement, equation, table or figure number changed. The write also added cleveref type hints (`\label[lemma]`, `\label[proposition]`) to the eleven labels of lemmas and propositions, and `\crefalias{section}{appendix}` after `\appendix`. These environments share counters with theorems and sections, and the delivered PDF printed every reference to them as "theorem" or "section"; only those printed names changed. Text added in the write is marked *[Write note, batch 73O1, 1 October 2026.]*: notes after the abstract, after Proposition 11.2, in Sections 13.5 and 14.8, in Appendix B.1, Appendix C (provenance), and three bibliography entries marked "[Added in the write.]". No delivered sentence, statement, proof, table or figure was changed or removed.

## What is claimed

Let A(N) = p_{⌊√N⌋}(N) count partitions of N into parts at most ⌊√N⌋ (A097356). Let u > 0 solve ∫₀¹ x/(e^{ux} − 1) dx = 1 and set ρ = 1 − e^{−u}, H = 2u − log ρ, d = e^H, C = u/(2π√(2 − 3e^{−u})) and C_− = Cρ = 0.0881548837986971165…

- **Phase expansion** (Theorem 2.1): A(N) = C e^{Ht} t^{−2} ρ^θ (Σ_{k≤K} P_k(θ) t^{−k} + O(t^{−K−1})) with t = √N, θ = {√N}, to every fixed order K. The cluster set of N A(N) d^{−√N} is [C_−, C]: Kotesovec's conjectured lower constant in A097356 is the **liminf**.
- **Three exceptions** (Theorem 2.2): for every sufficiently large m, inside the block m² ≤ N < (m+1)², the literal inequality A(N) ≥ C_− d^{√N}/N fails exactly at N = (m+1)² − 3, (m+1)² − 2, (m+1)² − 1. The upper inequality with C holds eventually, and the number of violations up to X is 3√X + O(1). So the literal eventual-inequality reading of the OEIS conjecture is false.
- **Inverse** (Theorem 2.3): with the Lambert-W_{−1} core X(Y) and a piecewise-linear phase map T, √Q(Y) = T(X(Y)) + O(1/X). Omitting the phase map can cost an index error of order log Y.
- **Uniform all-orders calculus** for p_m(αm² + σm + τ) (Lemma 3.1, Proposition 4.1, Theorem 5.1), with an explicit Gaussian coefficient operator and the closed form of D₁ (Proposition 5.2), covering A206226, A206227 and A206240; endpoint expansion with exact rational sign certificates for κ₃ < 0 < κ₄ (Proposition 8.2, Appendix A); a log-uniform limiting distribution (Theorem 9.2); a summatory law (Theorem 10.1); all-orders inverse coefficients of the square subsequence (Proposition 11.1); plateaus, interior brackets and an all-orders interior recurrence for the full inverse (Section 12).
- **Not new here:** the discrete threshold transport, Proposition 11.2, is an instance of the staircase recovery theorem of the transseries volume (see "Relation to neighbouring material"); it is printed with its proof as a specialization. The leading Szekeres asymptotic (Canfield, Romik) and the OEIS amplitudes of A206226, A206227, A206240 and the constant A258268 are classical and credited, not presented as new.

## What is not claimed

These are the manuscript's own limits (delivered README "Attribution and limits", `PROVENANCE.md` "Result boundaries", `VALIDATION.md` "Remaining boundaries", article Sections 1.2 and 14), kept in full:

- **No effective m₀.** The three-exception theorem gives the existence of a cutoff, not a certified smallest one. The shipped data show the pattern is not yet stable at m = 64: in `data/three_exception_checks.csv` the third-last index is still above the envelope at m = 16, 32, 64 (relative defect +0.0031, +0.00059, +0.000030) and below it at m = 128 and 256. The intake's own exact check agrees: exceptions {−2, −1} at m = 32 and 64, {−3, −2, −1} at m = 128.
- **"All orders" means every fixed truncation order with a proved remainder.** No convergence of the correction series is asserted.
- **"Transseries" in the subtitle is used loosely.** The floor-dependent expansion is a phase-parametrized Poincaré expansion, "not an ordinary power–logarithmic transseries of a smooth germ" (article §1.2). No exponentially improved or resurgent transseries is claimed; noncentral arcs are shown smaller than every algebraic order, but their exponential sectors and Stokes data are not determined.
- No all-orders uniform inverse across the switching layers; the summatory law only to relative order 1/m.
- No global first-discovery priority: the repository and literature searches were bounded.
- The rational certificate certifies the finite sign inputs using the written tail bounds of Appendix A; it does not formalize the contour analysis. The arbitrary-precision tables are checks, not proofs.
- No Lean or Coq formalization is included or claimed (Section 14.8 sketches a route).
- The OEIS transcription checks (first 54 terms of A097356, first 17 of A206226, embedded in `code/verify.py`) and every statement about the OEIS entries refer to the entries as inspected on 1 October 2026; the intake did not re-fetch them.

## Relation to neighbouring material

- **Transseries volume** `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`: Proposition 11.2 (`srp:prop:ceil`) and the separation remark after it are the case x_* = x_K(Y), η = δ_K of Theorem `p0:thm:staircase` (`transseries_and_inversion.tex`, "Staircase recovery and the separation condition"), parts (1)–(2). The manuscript itself credits "ProveIt's remainder-transport and staircase organization" there. Only the analytic width δ_K, from Theorem 5.1, is specific to A097356.
- **Lean.** Placement beside formal developments confers no formal status. The order-theoretic content of `p0:thm:staircase` parts (1)–(2) is formalized in `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean` as `Fabius.staircase_ceil` and `Fabius.staircase_separation` (listed in the transseries volume's README). None of the statements of this report is formalized, including the analytic input of Proposition 11.2.
- **Fabius tree.** Proposition 4.1 (`srp:prop:product`) splits off h(z) = log(z/(1 − e^{−z})) before an Euler–Maclaurin expansion of a finite q-Pochhammer product. The draft `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/combinatorial-coefficient-calculus/Gaussian_Coefficient_Calculus/Gaussian_Coefficient_Calculus.tex`, Theorem `q3:thm:double-scaling`, uses the same device for the Gaussian binomial at real argument. It is a sibling lemma for a different object, not the same theorem.
- **Sibling partition reports of batch 73O1** in this directory: [`a022629-distinct-partition-norms`](../a022629-distinct-partition-norms/) (∏(1 + k^α q^k)) and [`a033552-catalan-partitions`](../a033552-catalan-partitions/) (parts in the Catalan numbers). They study different products in different saddle regimes and share only the standard toolkit (exact saddle with an all-orders Edgeworth expansion, Lambert-W inversion with integer staircases); no proposition is proved twice. No repository report treats A097356, A206226, A206227, A206240 or A258268.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build needs `figures/phase_profile.pdf` and `figures/inverse_phase.pdf` beside `article.tex`, and the newtx fonts. pdfLaTeX (MiKTeX 26.2) produced the shipped `article.pdf`: 29 pages, with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`. The two figure PDFs embed Matplotlib Type 3 fonts (DejaVu Sans), as delivered.

## Rerunning the scripts

The scripts take their output paths relative to the working directory, under the **delivery** names: `verify.py --output` defaults to `results/`, and `make_figures.py` reads `results/plot_data.json` and writes into `figures/`. Run on a copy, never in the report directory, so that the shipped `data/` and `figures/` are not overwritten.

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a097356-sqrt-restricted-partitions
W=$(mktemp -d)
cp "$R"/code/*.py "$W"/ && cd "$W"
py certificate.py                                                    # exact rational checks; prints JSON, writes nothing
uv run --no-project --with mpmath==1.3.0 python verify.py --max-m 256 --output results   # about 46 s
# optional figures: uv run --no-project --with matplotlib==3.10.8 --with numpy==2.3.5 \
#                     python make_figures.py --data results/plot_data.json --output figs
```

Do not run Python with `-O`: the certificate relies on assertions. At intake (Windows, mpmath 1.3.0) `verify.py --max-m 256` wrote ten files: the six CSV files and `plot_data.json` were byte-identical to the shipped `data/` files, and `coefficients.json`, `sign_certificate.json` and `verification_summary.json` equal apart from CRLF line ends (Windows text mode; the delivery was made with LF). Its standard output equals `data/run_log.txt`, which is a capture of that output, not a file the script writes. The figure script was not rerun; regenerated figures differ in bytes (Matplotlib metadata).

## Disclosures and discrepancies

- The delivered README is not shipped; this guide replaces it. Its commands (`python certificate.py`, `python verify.py --max-m 256 --output results`, `python make_figures.py`) and its file list assume the delivered layout (`results/`, scripts at the root).
- `VALIDATION.md` and `PROVENANCE.md` still use the delivery names (`results`, `verify.py` at the root) and describe the delivered 27-page PDF, which is not shipped. `VALIDATION.md`'s statement that the ZIP "contains no build auxiliary files" refers to the delivered archive.
- The article's Sections 13.5 and Appendix B.1 describe the delivered layout; write notes there give the shipped paths. `code/make_figures.py`'s docstring and defaults name `results/plot_data.json`.
- `PROVENANCE.md` calls the pin a "recursive-tree checkpoint"; it is a commit (above).
- The subtitle's "inverse transseries" is the delivered wording; see "What is not claimed".

## Provenance

Appendix C of the article records the source, the pin, what the write changed and the map from delivery names to shipped paths. The placement commit `9df4ba51a` records the batch decisions: no repository report treats these sequences, the manuscript shares no proposition with the batch's other partition manuscripts (39, 40, 48), and Proposition 11.2 is printed as a pointer to the staircase theorem, not as new.
