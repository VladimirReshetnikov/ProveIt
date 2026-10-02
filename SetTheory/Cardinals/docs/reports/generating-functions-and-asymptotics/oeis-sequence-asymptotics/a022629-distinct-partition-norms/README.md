# Five OEIS Asymptotic Conjectures for Distinct-Partition Norms

**Proofs, all-orders logarithmic expansions, exact-saddle corrections, inverse and extreme-value laws for ∏(1 + k^α q^k): A022629, A092484, A265840, A265841, A265842**

This research report is dated 1 October 2026. It was built from two
manuscripts of batch 73O1 (cluster O1 of batch 73) of ProveIt's
incoming-reports intake, written independently on the same day. Both prove
the same theorems for the same real family (source 48's A022629 is source
40's α = 1, and its real exponent `s` is source 40's α), with identical
coefficients. Each shared theorem is printed once and credited to both, with
the other proof as a marked second route. Neither manuscript is superseded:
each has results the other lacks.

| Source | Batch-73O1 manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| base | 40 | `OEIS_Distinct_Partition_Norms.zip` (`f8c3a392a`); `article.tex`, *Five OEIS Asymptotic Conjectures for Distinct-Partition Norms*, 22-page PDF | `1f1981f68` | `9df4ba51a` | the whole text, in its order (Sections 1–14, Appendix A) |
| member | 48 | `A022629_Research_Package.zip` (`3a9518c52`); `article.tex`, *The A022629 Conjecture: All-Orders Logarithmic Asymptotics, Saddle-Point Expansions, Inverse Growth, and the Largest Part of a Weighted Partition*, 20-page PDF | `dc1a7242d` | `9df4ba51a` | second proofs and credits throughout; Section 3.1, Sections 6.1, 7.3, 8.1–8.2, 9.1, 10.3, 12.5, 13.1, part of Appendix B, Appendix C |

Author lines as delivered: source 40, "Research report prepared for Vladimir
Reshetnikov" (no AI wording); source 48, the same, with "Developed with AI
assistance; proofs and computations supplied for review". Both pins are
ProveIt commits of 1 October 2026 (`1f1981f682b2878bde51a6ad40c22777f362fc05`,
`dc1a7242d2ab4a4496b7dfee63256ee767b21fc9`); source 48 calls its identifier a
"tree response" and says it does not pin every later read. Source 40 arrived
first; neither cites the other, and their texts share almost nothing
(8-gram containment 0.004 both ways). The placement commit `9df4ba51a`
staged the files below and deleted both archives, which survive in their
arrival commits.

**Status: AI-assisted (source 48 says so; source 40 does not say), unrefereed,
not formalized.** The intake recomputed the A022629 table to n = 6400,
re-derived P_1–P_8 and the inverse coefficients by a third route (a Sommerfeld
expansion), recomputed source 48's operator series and coordinate change in
exact arithmetic, compared the two Gumbel centrings numerically, and reran
every shipped program on copies. It did not referee every proof.

## Files

```
README.md                                          this guide
article.tex                                        the merged report (pdfLaTeX, internal bibliography)
article.pdf                                        the compiled report, 38 pages (title page, then pages 1-37)
48-a022629-PROVENANCE.md                           source 48's sources and verification record, as delivered
code/40-norm-moments-verify.py                     exact sequences (alpha = 1..5, n <= 5000), recurrence check, saddle/Edgeworth diagnostics
code/40-norm-moments-derive_series.py              symbolic boundary derivatives and P_j (SymPy)
code/40-norm-moments-derive_inverse.py             symbolic reversion through six inverse orders (SymPy)
code/40-norm-moments-check_continuum.py            continuum quadrature check of the P_8 limit (mpmath)
code/40-norm-moments-check_resonances.py           product moduli at the first resonance (reads diagnostics.csv)
code/48-a022629-coefficients.py                    source 48's operator construction of six forward and six inverse coefficients
code/48-a022629-verify.py                          source 48's exact table to n = 6400 and saddle diagnostics
code/48-a022629-Makefile                           source 48's pdf/verify/clean targets (delivery layout; see below)
data/40-norm-moments-A022629_computed.txt          a(n), n = 0..5000, alpha = 1 (and A092484, A265840, A265841, A265842 below)
data/40-norm-moments-A092484_computed.txt
data/40-norm-moments-A265840_computed.txt
data/40-norm-moments-A265841_computed.txt
data/40-norm-moments-A265842_computed.txt
data/40-norm-moments-diagnostics.csv               exact versus saddle comparisons, all five alphas
data/40-norm-moments-diagnostics_alpha1.csv        the same, per alpha (alpha1 ... alpha5)
data/40-norm-moments-diagnostics_alpha2.csv
data/40-norm-moments-diagnostics_alpha3.csv
data/40-norm-moments-diagnostics_alpha4.csv
data/40-norm-moments-diagnostics_alpha5.csv
data/40-norm-moments-continuum_diagnostics.csv     continuum checks of the P_8 limit
data/40-norm-moments-continuum_run.txt             its console transcript
data/40-norm-moments-resonance_diagnostics.csv     product moduli at theta = 2 pi / M
data/40-norm-moments-formal_coefficients.txt       symbolic P_j
data/40-norm-moments-series_run.txt                its console transcript
data/40-norm-moments-inverse_coefficients.txt      symbolic E and E^2
data/40-norm-moments-inverse_run.txt               its console transcript
data/40-norm-moments-run_alpha1.txt                verify transcripts (alpha 1; 2-3; 4-5)
data/40-norm-moments-run_alpha23.txt
data/40-norm-moments-run_alpha45.txt
data/40-norm-moments-requirements.txt              mpmath>=1.3.0, sympy>=1.12
data/48-a022629-exact_coefficients.csv             a(n), n = 0..6400, alpha = 1
data/48-a022629-formal_coefficients.json           six forward and six inverse polynomials
data/48-a022629-numerical_checks.json              saddle, variance, cumulants, residuals, cutoffs, errors (n = 100, 400, 1600, 6400)
data/48-a022629-saddle_table.tex                   generated table fragment (not \input by the article)
data/48-a022629-requirements.txt                   mpmath==1.3.0, sympy==1.14.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. The eight `40-norm-moments-*.csv` files and
`data/48-a022629-exact_coefficients.csv` are CRLF as delivered and are kept
byte for byte by `-text` lines in `SetTheory/Cardinals/.gitattributes`.
Delivered name → shipped path: source 40's `oeis_norm_partitions/X.py` →
`code/40-norm-moments-X.py`, `data/Y` → `data/40-norm-moments-Y`,
`requirements.txt` → `data/40-norm-moments-requirements.txt`, `article.tex` →
`article.tex` (rewritten in the merge), `README.md` → this README; source 48's
`A022629_Research/code/X.py` → `code/48-a022629-X.py`, `Makefile` →
`code/48-a022629-Makefile`, `data/Y` → `data/48-a022629-Y`,
`requirements.txt` → `data/48-a022629-requirements.txt`, `PROVENANCE.md` →
`48-a022629-PROVENANCE.md`. Not shipped: both PDFs, source 48's manuscript and
README, and source 40's `SHA256SUMS.txt` (30/30 verified, retired).

## Labels, structure and notation

Every label carries the prefix `dpn:`. The staged base had **84** labels; all
are kept, unchanged after the prefix. The merge added **44**: 37 of source
48's 83 labels under the sub-prefix `dpn:48:` (source 48's own name after it),
4 new `dpn:48:` names (`sec:operator`, `sec:gumbel`, `eq:sfirst`, `eq:N1`) and
3 new `dpn:` labels (`sec:merge`, `sec:notation`, `app:prov`): **128** in all.
Source 48's other 46 labels named statements and equations that duplicate
source 40's and are printed once.

Section 1.4 says what came from where; Section 1.5 is the notation table.
Source 40's notation is used throughout, and source 48's material is
translated into it. The collisions that matter: source 48's `s` is the power
(here α), while source 40's `s` is the log transition coordinate
−W₋₁(−t/α) (48's `L`); source 48's `r` is the transition site (here M),
while source 40's `r` is log √(2n) (48's λ); source 48's `K`, `M` are
truncation orders (here R, J), while here K = √(2n) and M = e^s; source 48's
`Q_s(n)` (largest weight, here Π_α(n)) and `d_s(λ)` (Gumbel centring, here
β_α(r)) are not source 40's `Q_α(s)` and `d_α(s)`. Source 48's cumulative
Edgeworth sum is written 1 + Σ_{ℓ<J} 𝓔_ℓ. Text added in the merge is marked
"[Merge note, batch 73O1.]"; material only source 48 has is marked
"(source 48)".

## What is claimed

For every fixed real α > 0, with K = √(2n), r = log K, c = π²/(6α²):

- The Kotesovec conjectures log a_α(n) ~ α√(n/2)(log 2n − 2) for A022629,
  A092484, A265840, A265841, A265842 hold, with the sharper additive form
  log a_α(n) = αK(r − 1) + O(K/r) (both sources; source 48's elementary
  upper-bound proof is a second route).
- All fixed orders of log a_α(n) = αK(r − 1 + Σ P_j(c) r^{−j}), with
  P_1–P_7 printed (both sources print P_1–P_6), P_8 computed and checked
  numerically (source 40), and two generating algorithms: source 40's
  Lagrange-inversion route and source 48's differential operator.
- The exact-saddle multiplicative expansion with all fixed Edgeworth orders,
  including control of noncentral arcs (both).
- Lambert-W_0 inversion of the first index with log a_α(n) ≥ Y, through
  R_0^{−6} (both; source 48 displays the order-6 form and the A022629 form).
- Logistic occupation at the boundary, a Gumbel law for the largest part
  with exact-root centring (source 40) and explicit centring in log √(2n)
  (source 48), and L_n/√(2n) → 1 + 1/α (both).
- The fixed-resonance modulus −log|φ_t(2πℓ/M)| ~ 2π⁴ℓ²M/(3α³s³)
  (source 40).
- Source 48 only: the Taylor series of log ∏(1 + k^α q^k) at 0 has radius
  3^{−α/3}; log max weight = αK(r − 1) + O(r); and
  log(a_α(n)/max weight) ~ π²K/(6αr).

## What is not claimed

- No complete multi-saddle coefficient transseries; the resonance theorem
  gives the modulus at a point, not the secondary saddles' contributions
  (source 40). No resolution of the smaller blocks or exponentially small
  contributions; no convergence of the inverse-logarithmic series
  (source 48).
- No uniformity as α ↓ 0 (both); α = 0 is a different regime.
- The finite-size diagnostics are not interval-certified. At n = 5000 the
  central approximation is excellent for α = 1 but fails for α = 3, 4, 5
  (ratio about 1.58 at α = 5); fixed truncations of the logarithmic
  expansion do not improve monotonically at fixed n (source 40). The
  four-term logarithmic approximation is still off by about 3.55 in the
  logarithm at n = 6400 (source 48).
- Gikunda's 2026 dissertation treats a shrinking tilt and is not claimed to
  be superseded; Granovsky–Stark's theorem is not claimed to be
  inapplicable in every form.
- No priority, no Lean or Rocq verification, and no OEIS submission.

## Relation to neighbouring material

- **Sibling reports of batch 73O1** in this collection treat other partition
  products with the same saddle, Edgeworth and Lambert-W toolkit and prove no
  common proposition: [`a033552-catalan-partitions`](../a033552-catalan-partitions/)
  (parts in the Catalan numbers) and
  [`a097356-sqrt-restricted-partitions`](../a097356-sqrt-restricted-partitions/)
  (parts at most √N). [`a039831-two-fourier-peaks`](../a039831-two-fourier-peaks/)
  (batch 73O2) is a further sibling: a Fourier-peak and Lambert-W inverse
  study of another product.
- **Transseries.** The partition-number chapter of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion`
  (`transseries_and_inversion.tex`, label `p3:sec:top`, A000041) is a
  methodological relative. Nothing is imported from it, and neither
  manuscript builds a transseries in that volume's sense.
- **Lean.** Neither manuscript ships or cites Lean or Rocq proofs. No
  statement of this report is formalized, and placement in the collection
  confers no formal status.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX 26.2) produced the shipped `article.pdf`: 38 pages (an
unnumbered title page, then pages 1–37), with no errors, no warnings, no
undefined references or citations, no multiply defined labels, no duplicate
destinations and no overfull or underfull boxes. The build of the delivered
base text had a duplicate `page.1` destination from its title page; the merge
wraps the title page in `\hypersetup{pageanchor=false}` … `pageanchor=true`.
Copy back only `article.pdf`.

## Rerunning the programs

Every program writes its outputs under the **delivered** names, relative to
its own location: source 40's scripts write to `data/` beside themselves (run
from `code/` they would create `code/data/`), and source 48's write to
`../data/` (run from `code/` they would add unprefixed files to the shipped
`data/`). `check_resonances.py` also reads `data/diagnostics.csv`. So rerun on
a copy laid out as delivered:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a022629-distinct-partition-norms
W=$(mktemp -d); mkdir -p "$W/40" "$W/48/code"
for f in "$R"/code/40-norm-moments-*.py; do cp "$f" "$W/40/${f##*/40-norm-moments-}"; done
for f in "$R"/code/48-a022629-*.py;      do cp "$f" "$W/48/code/${f##*/48-a022629-}"; done
U="uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python"
(cd "$W/40" && $U verify.py --max-n 5000 --dps 50 && $U derive_series.py && $U derive_inverse.py \
             && $U check_continuum.py && $U check_resonances.py)    # about 85, 79, 66, 51, 13 s
(cd "$W/48" && $U code/coefficients.py --order 6 && $U code/verify.py --max-n 6400 --dps 45)   # about 83, 46 s
```

Compare `$W/40/data/<name>` with `data/40-norm-moments-<name>` and
`$W/48/data/<name>` with `data/48-a022629-<name>`. The intake's runs matched
every shipped file: the CSVs byte for byte, the text and JSON outputs up to
line endings (on Windows, Python text mode writes CRLF where the delivered
files are LF). The console transcripts `*_run.txt` are the scripts' standard
output. `verify.py --alpha 1 --max-n 300` is a quick partial run, but a subset
run rewrites `data/diagnostics.csv` with that subset only. `make verify` and
`make pdf` in `code/48-a022629-Makefile` assume source 48's delivered layout
(`code/coefficients.py`, `code/verify.py`, `article.tex` beside the Makefile);
`make pdf` would build source 48's unshipped manuscript, so use it only in a
re-extraction of the archive from `3a9518c52`.

## Disclosures and discrepancies

- `code/40-norm-moments-verify.py` says in its docstring "Run: python
  verify.py --max-n 5000 --dps 60", and 60 is its default, while the
  recorded transcripts and source 40's text use `--dps 50`; both are well
  above the 30 the script requires, and the intake's `--dps 50` run
  reproduced the shipped data.
- The two A022629 tables, `data/40-norm-moments-A022629_computed.txt`
  (n ≤ 5000) and `data/48-a022629-exact_coefficients.csv` (n ≤ 6400), agree on
  the common range; both are shipped beside their own verifiers.
- **Delivery names in shipped text.** `48-a022629-PROVENANCE.md` points to
  "requirements.txt and the executable programs" (shipped as
  `data/48-a022629-requirements.txt` and `code/48-a022629-*.py`), and its
  "compiled to a 20-page A4 PDF" describes source 48's delivered PDF, which is
  not shipped. `code/48-a022629-Makefile` names `article.tex`,
  `code/coefficients.py` and `code/verify.py` in source 48's delivered layout.
  `code/40-norm-moments-verify.py` names itself `verify.py` (also in the
  header line it writes into the `*_computed.txt` files), and
  `code/40-norm-moments-derive_series.py` cites "Sections 7 and 8 of
  article.pdf": the section numbers of source 40's text are unchanged in the
  merged article, so that pointer still holds. The scripts' output names are
  the delivered ones (above). The article uses the shipped names; its
  Appendix A records both sources' delivered command lists.
- **External claims.** The A022629 entry's conjecture text (Kotesovec,
  8 May 2018) was confirmed live on 1 October 2026. The other four entries,
  A292189, the Gikunda dissertation, Bridges–Craig, Schneider–Sills,
  Rana–Kaur–Kumar and Granovsky–Stark were not re-checked by the intake.
- **Abstracts and title pages.** The two abstracts were merged into source 40's
  with an added paragraph; source 48's title page and package-contents
  paragraph are replaced by the article's provenance appendix and this README.
