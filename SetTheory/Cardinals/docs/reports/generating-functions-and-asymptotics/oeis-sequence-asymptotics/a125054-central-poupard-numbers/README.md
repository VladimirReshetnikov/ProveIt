# Central Poupard Numbers

**Two OEIS conjectural statements for A125054, complete asymptotic sectors, and a universal transition for shifted moments**

This research report is dated 1 October 2026. It was built from one manuscript, number 47 of batch 73O1 of ProveIt's incoming-reports intake. Its author line, kept as delivered, is "Research article prepared for Vladimir Reshetnikov"; it names no assistant.

| Source | Batch-73O1 manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| sole | 47 | `Central_Poupard_OEIS.zip` (*Central Poupard Numbers: OEIS Identities and Shifted-Moment Transitions*, 28-page PDF, 16 files) | `ef66df0fd` | `3a9518c52` | `9df4ba51a` | the whole report; Appendix C added in the write |

The pin `ef66df0fdb8fc64cbc80756d622cab0e8e85e262` is the ProveIt commit the manuscript inspected (2026-10-01, "Point power-tower-derivative-term-counts and the A290268 notes to the batch-72A reports"). `PROVENANCE.md` also records a later read of `dc1a7242d2ab4a4496b7dfee63256ee767b21fc9` (2026-10-01), not used for content. The placement commit `9df4ba51a` deleted the archive from `docs/incoming`; it survives in the arrival commit `3a9518c52`.

**Status: AI-assisted, unrefereed, not formalized.** The intake recomputed the tangent numbers by the Seidel boustrophedon, checked Bala's S-fraction exactly to degree 59 and a_n ≡ 3 (mod 9) for n ≤ 400, recomputed s_* and τ_* to 37 digits, checked the leading term with its first three corrections, and reran the verifier on a copy. It did not re-derive every proof.

## Files

```
README.md                    this guide (replaces the delivered README)
article.tex                  the report (LaTeX, internal bibliography; \inputs the data/*.tex fragments)
article.pdf                  the compiled report, 29 pages
PROVENANCE.md                the manuscript's sources, pin, attribution and verification boundaries, as delivered
code/verify.py               exact finite tests, coefficient generation, numerical diagnostics (SymPy, mpmath);
                             writes the six generated files below
code/Makefile                the delivered pdf / verify / clean targets (run from the report root; see below)
data/log_coefficients.tex    logarithmic coefficients h_1 ... (generated; \input by the article)
data/fixed_table.tex         Table 1, fixed-shift accuracy (generated)
data/critical_table.tex      Table 2, explicit-window convergence (generated)
data/inverse_table.tex       Table 3, inverse errors (generated)
data/zeros_table.tex         Table 4, complex-root diagnostics (generated)
data/verification.json       recorded run: versions, exact-check ranges, constants, tables (generated)
data/verification_run.txt    standard output of that run (written by the Makefile's verify target)
data/BUILD_REPORT.json       the delivered build, replay and PDF-inspection record
data/requirements.txt        mpmath==1.3.0, sympy==1.14.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to the delivery. Delivery names: `Makefile` was at the package root and is now `code/Makefile`; `requirements.txt` and `BUILD_REPORT.json` were at the root and are now in `data/`; `code/verify.py`, the seven files of `data/` and `PROVENANCE.md` kept their places. Not shipped: the delivered `article.pdf` (replaced by a build of this text) and the checksum ledger `SHA256SUMS` (verified 15/15 at intake, then retired).

## Labels and numbering

Every label carries the prefix `pou:`. The 108 delivered labels keep their names after the prefix, and the write added one (`pou:app:edition`): **109** labels. The article references with `Theorem~\ref{…}` and similar, not cleveref, so no printed reference name depends on label types. No section, statement, equation or table number changed; the `\input{data/…}` and `\tableinput{data/…}` paths are unchanged. Text added in the write is marked *[Write note, batch 73O1, 1 October 2026.]*: after the abstract, in Section 1 (repository status and the shared constant), in Section 7 (the τ notation clash), in Appendix A (rerun hazards) and Appendix C (provenance). Two bibliography entries are marked "[Added in the write.]". No delivered sentence, statement, proof or table was changed or removed.

## What is claimed

With T_n = (2n+1)! [z^{2n+1}] tan z and A_n(c) = Σ_k C(n,k) c^{n−k} T_k, the central Poupard numbers are a_n = A_n(1), OEIS A125054.

- **Bala's continued fraction** (Theorem 3.3): A(x) = (1 + 2x S(β; x))/(1 − x) with β = 9, 8, 25, 24, 49, 48, …, proving the generating function labelled "Conjectured g.f." by Peter Bala (15 December 2025) in the entry, as an identity of formal power series.
- **Congruence** (Theorem 4.1): a_n ≡ 3 (mod 9) for every n ≥ 1, hence v_3(a_n) = 1. This settles, in stronger form, F. Chapoton's observation (2 August 2021). Corollary 4.2: Σ A_n(c) x^n is rational modulo every m, so the residues are eventually periodic.
- **Fixed shifts** (Theorems 6.1, 6.2): an exact convergent decomposition into odd-pole exponential sectors with a positive tail bound, and arbitrary-order expansions of each fixed sector.
- **Quadratic shifts c = τn²** (Proposition 7.1, Theorem 8.1): a uniform all-order endpoint–saddle expansion; the transition at τ_* = s_*(2 − s_*)/α², α = π/2, 2 − s_* = 2e^{−s_*}, so s_* = 2 + W_0(−2e^{−2}) = 1.5936242600400400923… and τ_* = 0.2624665433684190267…; a coexistence window displaced by a multiple of (log n)/n, the critical mixture law and Gaussian fluctuations (Theorems 9.1–9.3).
- **Universality** (Theorem 10.1): the leading transition for moments of y^p, p > 1, under any probability density with tail C y^β e^{−αy}(1 + O(1/y)), with p − s_p = p e^{−s_p}.
- **Complex zeros** (Theorem 11.1, Corollary 11.2): positivity promotes the real transition to a locally uniform complex limit and locates an array of simple polynomial zeros, for each fixed index j.
- **Inversion** (Theorem 12.2, Propositions 12.3, 12.4): Lambert-W inversion of the fixed-shift growth, an arbitrary-order inverse procedure, and an exponentially small inverse displacement relative to an exact one-sector inverse.
- **Not new here:** the leading asymptotic of a_n (Kotesovec, 2015, recorded in the entry) is re-derived as a consistency check (equation (27), `pou:eq:knownleading`); the tangent and Poupard generating functions (Foata–Han), Bala's 2017 S-fraction machinery, and the moment and Hankel consequences (Section 5) are prior mathematics, included as explanation.

The OEIS labels and dates are as the authors inspected the entry on 1 October 2026; the intake did not re-fetch it.

## What is not claimed

These are the manuscript's own limits (delivered README "Main results and their scope" and "Verification boundary", `PROVENANCE.md` "Claims and attribution" and "Computational record", article Sections 1, 13, 14 and Appendix B), kept in full:

- No worldwide publication priority for the analytic extensions: targeted searches only, and related results may exist under other terminology. The two OEIS statements are resolved; that is not a claim that no unpublished or unlocated proof existed.
- The full all-order assertion is proved for the tangent model only. An arbitrary tail with only a relative O(1/y) description receives a leading transition theorem, not an all-order one; p > 1 is essential for the universal theorem.
- Complex zero locations are for each fixed index j, not for j growing with the degree; no global zero distribution is claimed. The complex-zero convergence is qualitative.
- Floating-point values and root residuals (below 10^−55) are diagnostics, not interval enclosures or proofs of root location or uniqueness; the printed transition constants are numerical values of exact definitions.
- The code checks the fractions through degree 48, the Poupard recurrence through row 24, the congruence through index 256 and the Hankel product formulas through order 6 at shifts 0, 1, 3; all-index statements rest on the proofs.
- No independent peer review, no Lean formalization, no interval certification. Section 14 poses eight research questions and, in Section 14.1, sketches a Lean route.
- Nothing is imported from the Lambert-chart transseries package the article names as methodological precedent.

## Relation to neighbouring material

- **A277364 report** [`a277364-bell-asymptotics`](../a277364-bell-asymptotics/): its constant τ = 2 + W_0(−2e^{−2}) = 1.5936242600400400923…, the root of τ/(1 − e^{−τ}) = 2 governing the omitted tail of the truncated Stirling sum Σ_{k≤n/2} S(n,k) (`A277364_asymptotics.tex`, `eq:taulambert`), is this report's s_*. **Notation:** there the number is called τ; here τ is the shift ratio c/n² and τ_* = s_*(2 − s_*)/α² = 0.26246654… is a different number. Same equation 2 − s = 2e^{−s}, different objects (Stirling tail there, endpoint–saddle balance here); neither report uses the other's argument.
- **Transseries** `Analysis/Transseries/docs/series-and-transseries/Logarithmic_Critical_Endpoint_Lambert_Charts/`: cited by the article (from its README at the pin) as a methodological precedent for all-order expansions, inversion and trust boundaries. Its countable-action model is a different object, and no theorem is imported. This report is not transseries work: its expansions are Poincaré expansions with an exponentially small inverse correction.
- **Other neighbours, no overlap:** `congruences-and-valuations/secant-number-periodicity` (A000364 periodicity; the article uses A000364 only as a second shifted-moment example in Section 10.2) and `enumerative-combinatorics/skew-partition-continued-fractions` (a different sequence; shares only Bala's S-fraction note as a reference). No repository report or formal development treats A125054, A125053, A000182 or the moments A_n(c).
- **Lean.** Placement in the collection confers no formal status, and none of this report's statements is formalized.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build needs the five `data/*.tex` fragments at their paths and Latin Modern fonts. pdfLaTeX (MiKTeX 26.2) produced the shipped `article.pdf`: 29 pages, with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`. (`make -f code/Makefile pdf`, run from a copy's root, does the same.)

## Rerunning the scripts

`code/verify.py` writes by default to the `data/` directory beside `code/`, that is to the shipped data, overwriting the six generated files. The `verify` target of `code/Makefile` (whose paths assume the report root as working directory: `make -f code/Makefile verify`) also overwrites `data/verification_run.txt` with the standard output. So rerun on a copy, or pass `--output-dir`:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a125054-central-poupard-numbers
W=$(mktemp -d)
cp -r "$R"/code "$R"/data "$W"/ && cd "$W"
uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python code/verify.py --max-n 4096 --dps 90   # about 57 s; rewrites $W/data
# shorter: ... python code/verify.py --max-n 512 --dps 90 --output-dir quick   (--max-n >= 256, --dps >= 80)
```

At intake (Windows, Python 3.13.5, mpmath 1.3.0, SymPy 1.14.0) the full command passed, and all six generated files were equal to the shipped ones apart from CRLF line ends (Windows text mode; the delivery was made with LF). Its standard output differed from `data/verification_run.txt` only in the line naming the output directory.

## Disclosures and discrepancies

- The delivered README is not shipped; this guide replaces it. Its commands (`python -m pip install -r requirements.txt`, `python code/verify.py …`, `make verify`) assume the delivered layout, with `requirements.txt` and `Makefile` at the root; its file list names `SHA256SUMS`, which is not shipped.
- `data/verification_run.txt` names the authors' working directory `/mnt/data/oeis_work/poupard_shift_transition/data`, which is not part of the repository (`PROVENANCE.md` says so too).
- `data/BUILD_REPORT.json` describes the delivered 28-page PDF and the delivered `article.tex` (it records their hashes, page-text and raster comparisons); neither is the shipped file any more.
- The article's Appendix A gives the delivered commands ("from the package directory"); a write note there gives the shipped paths and the hazards.
- The article's conclusion speaks of "the fixed-shift transseries"; the expansions are Poincaré expansions (see "Relation to neighbouring material").

## Provenance

Appendix C of the article records the source, the pin, what the write changed and the map from delivery names to shipped paths. The placement commit `9df4ba51a` records the batch decisions: no repository report treats A125054; the report is filed under OEIS-sequence asymptotics by its bulk (Sections 5–12), and its two OEIS identities (Sections 3–4) do not make it a congruences report.
