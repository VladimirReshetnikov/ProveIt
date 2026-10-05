# Fixed Forbidden Distances in Involutions

**Uniform expansions over bounded-degree forbidden graphs, two Gaussian
sectors, exact fixed-distance stabilization, and the all-orders law of
adjacent transpositions (OEIS A239144, A170941, A217876)**

A research report dated 2 October 2026, built from two manuscripts of
batch 77. Author lines as delivered: "Research article and reproducibility
companion" (source 19) and "A research note on OEIS A170941 and A217876"
(source 26). Neither delivery names an author or a tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 19 | batch 77, manuscript 19 | `fixed-forbidden-distance-involutions.zip` (wrapper `fixed-forbidden-distance-involutions/`; main file `article.tex`, 13-page PDF), arrival `096ee7b87` | none: no ProveIt commit or path is named | `d0e6008d9` | the base: Sections 1–8 |
| 26 | batch 77, manuscript 26 | `involution-refinements-attribution-revision.zip` (wrapper `involution-refinements/`; main file `report.tex`, 15-page PDF), arrival `096ee7b87` | none | `d0e6008d9` | Section 9 and Appendix A; its credits in Section 1.1 |
| 27 | batch 77, manuscript 27 | `involution-refinements-reproducibility.zip`, arrival `096ee7b87` | none | not placed | not printed: superseded by 26 |

**Status:** AI-assisted (presumed; the deliveries name no author or tool),
unrefereed, **not formalized**. Exact symbolic computation and numerical
replays corroborate the finite algebra; the uniform remainders rest on the
analytic proofs only.

Manuscript 27 is the first edition of 26. Source 26's revision record
(`data/26-adjacent-revision-integrity.json`) holds the SHA-256 of 27's
`report.tex` as `previous_tex_sha256`, and the two manuscripts differ in
four attribution hunks only (26 adds Ganjtabesh–Steyaert 2011 for the
zero-count limit); 15 other files are byte-identical. Nothing of 27 is
shipped; it survives in the arrival commit.

## Why one report, and where the merge chose

Source 26 proves, for the path `P_n` (forbidden distance `r = 1`), the
theorems that source 19 proves for every forbidden graph of bounded degree
and every fixed `r`, with the same coefficients `31/24, −55/48,
1717/1920`. Source 19, the more general, is the base. The merge printed
every result, proof, example, remark, limitation and question of source 26
that is not literally a special case of a statement of source 19 with the
same proof (Section 9): the law of `X_n` with the polynomials `Q_j(ℓ)`, the
total-variation corollary, the exact moments and triangle formula, a
**second proof** of the law (growing-moment summation and a Touchard
transform, instead of matching roots and complex marking), the absolute
and logarithmic avoidance coefficients, a **second exact sector
decomposition** (Chebyshev, with residual `≤ n + 1 + …` instead of `2^n`)
and the sector ratio `1 − 31/(12√n)`, the log-linear inverse with its
explicit chord term `θ(1−θ)/(4x)`, the source's checks, table and six
questions, and its coefficients through order eight (Appendix A). Source
26's smooth root, Lambert-W/Newton algorithm and two-ceiling enclosure have
the same statements and proofs as source 19's Section 6 at `r = 1`; they
are printed once, with a pointer (Section 9.9). The credits of both
sources are stated once (Section 1.1). The cluster dossier proposed to
print fewer of 26's results; the union rule of the intake procedure
(`docs/incoming/README.md` §4.2) was followed instead.

## What it proves

Source 19 (Sections 1–8), for a simple graph `G` on `[n]` of maximum degree
`≤ Δ` (fixed) whose edges are forbidden transpositions, `X = X_G` the
number of forbidden edges used by a uniform involution:

- **Lemma 2.1 (marking and Gaussian duality).** `I_n E(1+w)^X = Σ M_k w^k
  I_{n−2k} = E F_{G,w}(1+Z)`, `Z ~ N(0,1)`; avoidance `A_G = E μ_G(1+Z)`.
  Root moments `a_j(G)` (finite local statistics), `a_1 = m/n`,
  `a_2 = (m/2 + W)/n`; factorial-moment domination `E(X)_k ≤ (Δ/2)^k`.
- **Theorem 3.1 (uniform complex PGF).** `E(1+w)^X = e^{a_1 w}{Σ_{h≤J}
  P_h(w; a(G)) n^{−h/2} + O(n^{−(J+1)/2})}` uniformly over all such `G` and
  `|w| ≤ R`, with universal rational polynomials and the graph's actual
  `a_j(G)`; Corollary 3.2: the same order in every fixed exponentially
  weighted `ℓ^1` norm of the signed law.
- **Theorem 3.3 (two sectors).** Exact split `A_G = K^+ + (−1)^n K^- + C_G`
  at the cutoff `B = 2√max(Δ−1,1)`, each sector with its own all-orders
  expansion (relative weights `e^{±√n}`), and an all-orders rational
  algorithm (Section 3.2).
- **Theorem 5.1 (exact eventual affine statistics).** For a fixed finite
  set `S` of forbidden distances, `a_j(G_n(S)) = α_j(S) + β_j(S)/n` for
  `n > j·max S` (connected-cluster argument), so the column expansions of
  A239144 have constant coefficients: `A_{n,r}/I_n = e^{−r}[1 + r/√n −
  r/(2n) − r(8r²−12r+3)/(24 n^{3/2}) + O(n^{−2})]`, and `log A_{n,r}` to
  every order with `γ_{r,1..3}`.
- **Section 6 (three inverses).** Smooth root with Lambert-W seed and
  `⌈log₂(J+3)⌉` Newton steps; integer threshold between two ceilings
  (Proposition 6.1); the exact log-linear convention and its chord inverse.

Source 26 (Section 9), for `X_n` = number of adjacent transpositions:

- **Theorem 9.1.** `E z^{X_n}` at `z = 1+w` equals `e^w Σ_{j≤J} P_j(w)
  n^{−j/2} + O(n^{−(J+1)/2})`, uniformly on compacts, with explicit
  `P_1, …, P_5`; the point probabilities `e^{−1} Q_j(ℓ)/ℓ!` in every fixed
  weighted `ℓ^1` norm. **Corollary 9.2:** avoidance ratio and
  `d_TV(L(X_n), Poisson(1)) = e^{−1}(n^{−1/2} − n^{−1}/2 + 17 n^{−3/2}/24 −
  …)`, every fixed order.
- Exact moments `E C(X_n, k) = C(n−k,k) I_{n−2k}/I_n ≤ 1/k!`, the A217876
  triangle formula, the Haslinger–Stadler recurrence.
- Absolute and logarithmic avoidance coefficients `d_j`, `β_j` (through
  order eight in Appendix A; `β_j = γ_{1,j}`).
- **Theorem 9.5.** Exact Chebyshev sectors `a_n = 𝒦_n^+ + (−1)^n 𝒦_n^- +
  Ξ_n`, `|Ξ_n| ≤ n + 1 + 2/(√(2π)(n+1))`, separate expansions with
  coefficients `(±1)^m d_m`, and `(a_n − 𝒦_n^+)/𝒦_n^+ = (−1)^n e^{−2√n}(1 −
  31/(12√n) + O(1/n))`.
- **Proposition 9.6.** Log-linear inverse to every fixed order, and the
  explicit chord term showing the smooth and chord inverses differ by
  `O(1/(x log x))` regardless of order.

## What is not claimed

- **Priority.** The shifted Gaussian matching identity (Godsil, via Lass),
  the root-moment technique and high-order structural corrections
  (Godsil–McKay, McLeod's thesis Theorems 4.17–4.18) are prior work; source
  19 makes "no worldwide-priority claim", and a comparison with McLeod's
  final journal text and the full Wanless paper "remains appropriate".
  For the adjacent case: enumeration Haslinger–Stadler (1997 preprint /
  1999 paper; final text not compared), selected-pair formula,
  inclusion–exclusion and the zero-count limit Ganjtabesh–Steyaert (2011),
  full Poisson law Li (2026 manuscript), first correction `31/24`
  Kotěšovec (OEIS, 2014). Source 26 claims neither exhaustive historical
  priority nor optimal truncation; Régnier and Nebel were not inspected.
- **Scope.** Fixed `Δ`, fixed order, fixed `r`; no growing degree or
  growing forbidden range, no triangular diagonal, no convergent series.
  Arbitrary graph sequences keep their moving statistics; constant
  coefficients only for fixed distance sets. The weighted approximation is
  signed; source 19 does not assert a smooth total-variation expansion
  through integer Poisson means in general (source 26's Corollary 9.2
  settles the case of mean 1 by an extra sign argument; a note in Section
  3 says so).
- **Sectors.** The cutoffs are conventions (exact sectors depend on them,
  coefficients do not); a finitely truncated dominant series does not
  resolve the smaller sector; no optimal-truncation, Borel, resurgence or
  Stokes theorem.
- **Inverses.** Constants are proved to exist, not certified at any finite
  input; no unconditional single-ceiling formula.
- **Computations** corroborate and do not prove; the review files are
  human-readable review, not proof-assistant verification. Decimal outputs
  are not interval-certified (the TV routine truncates at `K ≤ 90`).
- **The inversion layer is an instance of repository results; no novelty
  is claimed for the smooth inverse.** A dated note at the end of Section 6
  identifies the seed as `p0:thm:lambert-core` and the reversion as
  `p0:thm:lambert-centered` of *Transseries and Inversion*
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`;
  `t2:thm:balanced-inverse` of *Combinatorial Transseries Inverses* for
  gamma-quotient phases), the `r = 0` dominant-block inverse as
  `t1:thm:ivinverse` of *Combinatorial Transseries Inverses*
  (`Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`),
  and the integer threshold through `p0:thm:staircase` (exact rounding for
  the admissible log-linear interpolant; the separation condition). The
  Gaussian identity `I_n = E(1+Z)^n` and the `r = 0` sector expansion are
  that volume's chapter `ct:ch:involutions` (`t2:eq:involution-A`,
  `t1:thm:ivforward`); notes in Sections 1.1 and 3.1 say so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status. A search
of the tracked `.lean` and `.v` files for the four OEIS numbers and for
matching polynomials finds nothing about these sequences.

**Neighbours.** No other report of the collection treats involutions with
forbidden transposition distances or any of A239144, A170941, A217876.
The only repository material on these objects is the transseries volume
*Combinatorial Transseries Inverses*, chapter `ct:ch:involutions`
(involution numbers A000085: the two Gaussian blocks and their inverses),
which this report's `r = 0` case re-derives, as the notes above say.
Neither volume is edited by this write.

A pointer added in batch 97 (a dated merge note after the proof of
`fdi:thm:affine`): Part IV of
[`a189281-path-forest-expansions`](../a189281-path-forest-expansions/)
proves a uniform all-orders expansion for random bijections between two
path forests by the same connected-cluster locality (its `spf:mg:thm:main`,
`spf:mg:lem:cluster-local` and `spf:mg:prop:log-local`, Theorem 38.1,
Lemma 40.1 and Proposition 48.1); the two reports share a method, not a
theorem. That report's README already points here.

## Notation

Source 19's notation is used throughout. Source 26 reuses many of its
letters (`P_j`, `D`, `K`, `T`, `H`, `F`, `U`, `B`, `r`, `t`, …) with other
meanings; a table in the provenance section (before Section 1) fixes every
symbol of the merged material, with the tempting false reading beside it.
The most important: source 26's `P_j(w)` are constant-coefficient
polynomials after extracting `e^w`, **not** source 19's `P_h(w; a(P_n))`
after extracting `e^{a_1 w}`, `a_1 = 1 − 1/n`; its Chebyshev sectors
`𝒦_n^σ` are **not** source 19's `K_{P_n}^σ` (they differ by the tails
`τ_n^σ`). Renamed from source 26: `t → ε`, `T(n,ℓ) → T^adj(n,ℓ)`,
`G_n(z) → 𝒢_n(z)`, compact radius `B → R`, `r_j → κ_j`, summation and
iteration indices `r → m, i`, Chebyshev `U_n → 𝒰_n`, `H, F, F_J, F_σ →
ℋ, ℱ, ℱ_J, ℱ_σ`, `φ_n → h_n`, `a_σ → g_σ`, `r_{n,σ} → y_{n,σ}`,
`p_{h,σ}, b_{r,σ}, D_{r,σ} → p̂_{h,σ}, b̂_{m,σ}, D̂_{m,σ}`, `K_n^σ, T_n^σ,
R_n → 𝒦_n^σ, τ_n^σ, Ξ_n`, `J_n^± → 𝒥_n^±`, `D_J(ℓ,t) → 𝒟_J`, local
constants `B_J, D_J, M_J, ρ_k, K, L → c_J, c'_J, Ω_J, ϑ_k, k_0, ℓ_0`,
`L_J, x_J, x̃_J, 𝒜, N → L_{1,J}, x_{1,J}, x̃_{1,J}, 𝒜_1, N_1`. No
normalization changed, and no statement, proof or number was altered.
"Kotesovec" in source 19 is printed Kotěšovec.

## Labels

Every label carries the prefix `fdi:`. Source 19's 42 labels were prefixed
`fdi:` before anything cited them (37 references updated). Nine section
labels `fdi:sec:*` were added for the notes. Source 26's material carries
`fdi:adj:` (45 labels: 41 of its 47, the six of its smooth-root, Newton and
two-ceiling displays being printed by pointer, plus four new section and
appendix labels); this also separates the three label names the two
sources shared (`eq:pgf`, `eq:weighted`, `thm:sectors`). Total: **96**
labels, none duplicated.

## Files

```text
README.md                                         this guide (replaces both delivery READMEs)
article.tex                                       the merged report (source 19's article.tex as base)
article.pdf                                       compiled report, 32 pages
19-distance-review.md                             source 19's independent review (of its delivered article.tex, by hash)
19-distance-VALIDATION.md                         source 19's replay and PDF verification record
26-adjacent-REVISION-NOTES.md                     source 26's attribution-revision notes (vs manuscript 27)
26-adjacent-VALIDATION.md                         source 26's validation record
26-adjacent-supplements-coefficients.md           source 26's exact coefficients through order eight (sector d_9, d_10)
26-adjacent-supplements-proof-details.md          source 26's additional proof and computation details
code/19-distance-verify.py                        universal sector/PGF coefficients through order six; numeric checks
code/19-distance-verify_fixed_range.py            fixed-range affine statistics and inverse tests (imports verify)
code/19-distance-check.py                         independent symbolic and finite-graph checks (reads verify.py)
code/19-distance-sector_check.py                  two-sign sector quadrature for disjoint triangles
code/19-distance-stabilization_check.py           100 exact affine-statistic values (reads verify.py)
code/19-distance-compare_results.py               structural comparison, tolerance 1e-40
code/19-distance-verify_manifest.py               checks the delivered MANIFEST.json (not shipped)
code/19-distance-inspect_zip.py                   inspects the delivered zip (not shipped)
code/19-distance-replay.sh                        source 19's replay (delivered layout)
code/19-distance-build_pdf.sh                     source 19's PDF build (expects article.tex beside it)
code/26-adjacent-scripts-derive_coefficients.py   exact Gaussian, logarithm, moment, Touchard and sector extraction
code/26-adjacent-scripts-verify_counts.py         exact triangle rows and large-n count residuals
code/26-adjacent-scripts-verify_law_inversion.py  high-precision law, TV and finite-Newton checks
code/26-adjacent-scripts-verify_sectors.py        independent two-sign sector generator and exact integral checks
code/26-adjacent-scripts-compare_results.py       comparison with the reference JSON (tolerance 1e-60)
code/26-adjacent-replay.sh                        source 26's replay (delivered layout)
code/26-adjacent-build.sh                         source 26's PDF build (expects report.tex)
data/19-distance-expected-coefficients.json       reference outputs of source 19 (six files, no final newline)
data/19-distance-expected-numeric-checks.json
data/19-distance-expected-fixed-range-checks.json
data/19-distance-expected-checks.json
data/19-distance-expected-sector-checks.json
data/19-distance-expected-stabilization-checks.json
data/19-distance-requirements.txt                 sympy==1.14.0, mpmath==1.3.0
data/26-adjacent-involution-coefficients.json     reference outputs of source 26 (four JSON files)
data/26-adjacent-numerical-checks.json
data/26-adjacent-law-inversion-checks.json
data/26-adjacent-sector-checks.json
data/26-adjacent-numerical-table.tex              the table of Section 9.10 (not written by any script)
data/26-adjacent-requirements.txt                 sympy==1.14.0, mpmath==1.3.0
data/26-adjacent-revision-integrity.json          26-vs-27 revision record (hashes, unchanged-file list)
data/26-adjacent-sources.json                     source 26's literature provenance (URLs, hashes of inspected bytes)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Delivery names → shipped names: source
19's `code/<x>.py` → `code/19-distance-<x>.py`, `expected/<x>.json` →
`data/19-distance-expected-<x>.json`, `replay.sh`, `build_pdf.sh` →
`code/19-distance-…`, `requirements.txt` → `data/19-distance-requirements.txt`,
`review.md`, `VALIDATION.md` → `19-distance-…` at the root; source 26's
`scripts/<x>.py` → `code/26-adjacent-scripts-<x>.py`, `replay.sh`,
`build.sh` → `code/26-adjacent-…`, `data/<x>`, `requirements.txt`,
`sources.json`, `revision-integrity.json` → `data/26-adjacent-…`,
`supplements/<x>.md`, `REVISION-NOTES.md`, `VALIDATION.md` →
`26-adjacent-…` at the root. Source 19's `article.tex` is the base of this
`article.tex`; source 26's `report.tex` is printed as Section 9 and
Appendix A.

**Not shipped** (all survive in the arrival commit, e.g.
`git show 096ee7b87:docs/incoming/fixed-forbidden-distance-involutions.zip > <scratch>/19.zip`):
both delivered PDFs, both delivery READMEs, source 26's `report.tex`, the
checksum ledgers `MANIFEST.json` (19, verified 22/22) and `SHA256SUMS` (26,
verified 22/22), and all 21 files of manuscript 27
(`involution-refinements-reproducibility.zip`). No delivered file was
excluded for size; nothing needs reconstructing.

**Delivered text that names the delivery layout or unshipped files:**
`19-distance-VALIDATION.md` (the ZIP, `MANIFEST.json`, `replay.sh`,
`build_pdf.sh`, `review.md`, the 13-page PDF); `19-distance-review.md`
(reviews source 19's delivered `article.tex`, identified there by its
hash, which the write verified; that is not the shipped merged
`article.tex`); `code/19-distance-replay.sh`
(`code/<x>.py`, `expected/`); `code/19-distance-build_pdf.sh`
(`article.tex` in its own directory); `code/19-distance-verify_manifest.py`
and `code/19-distance-inspect_zip.py` (the unshipped manifest and zip);
`code/19-distance-verify_fixed_range.py`, `check.py` and
`stabilization_check.py` (import or read `verify.py` by its delivery
name); `code/26-adjacent-replay.sh` (`sha256sum -c SHA256SUMS`,
`scripts/`, `data/`, then `build.sh`); `code/26-adjacent-build.sh`
(`report.tex`, `involution-refinements.pdf`); `26-adjacent-VALIDATION.md`
and `26-adjacent-REVISION-NOTES.md` (the 15-page PDF, `SHA256SUMS`,
`revision-integrity.json`); `data/26-adjacent-revision-integrity.json`
(paths and hashes in the delivered layout); and the article itself, whose
Sections 8 and 9.10 describe "the companion archive" and "the accompanying
ZIP" (dated notes there give the shipped names). The delivery README of
source 19 (replaced by this guide) also named `expected/` and
`MANIFEST.json`.

## Rerun the checks (on a scratch copy)

The scripts assume the delivered layouts. Source 19's scripts write to
`<parent of code>/results` unless `OUTPUT_DIR` is set, so running them in
`code/` would add a `results/` directory to the repository; source 26's
scripts write their JSON into the **current directory**. On Windows the
outputs have CRLF line endings, so compare structurally (the comparison
scripts do), not byte-wise. Use Python with `sympy==1.14.0` and
`mpmath==1.3.0`, e.g. `uv venv <venv>` and
`uv pip install --python <venv> -r data/19-distance-requirements.txt`, then
`PY=<venv>/Scripts/python.exe` (Windows) or `<venv>/bin/python`.

Source 19 (Git Bash, from this directory; replay as delivered, minus the
manifest check):

```sh
R=$(mktemp -d); mkdir -p "$R/code" "$R/expected"
for f in code/19-distance-*.py; do cp "$f" "$R/code/${f#code/19-distance-}"; done
for f in data/19-distance-expected-*.json; do cp "$f" "$R/expected/${f#data/19-distance-expected-}"; done
cp code/19-distance-replay.sh "$R/replay.sh"
cd "$R" && PYTHONUTF8=1 PYTHON="$PY" bash replay.sh   # ends "All exact and numerical replay checks passed"
```

Source 26 (its `replay.sh` first runs `sha256sum -c SHA256SUMS` and ends
with a PDF build of `report.tex`, neither shipped, so run its steps):

```sh
R=$(mktemp -d); mkdir -p "$R/scripts" "$R/data" "$R/run"
for f in code/26-adjacent-scripts-*.py; do cp "$f" "$R/scripts/${f#code/26-adjacent-scripts-}"; done
for f in involution-coefficients law-inversion-checks numerical-checks sector-checks; do
  cp "data/26-adjacent-$f.json" "$R/data/$f.json"; done
cd "$R/run" && export PYTHONUTF8=1
"$PY" ../scripts/derive_coefficients.py --order 8 > coefficient-output.txt
"$PY" ../scripts/verify_counts.py > count-output.txt
"$PY" ../scripts/verify_law_inversion.py > law-inversion-output.txt
"$PY" ../scripts/verify_sectors.py > sector-output.txt
"$PY" ../scripts/compare_results.py ../data .            # four PASS lines
```

Alternatively, use the delivered layouts unchanged:
`git show 096ee7b87:docs/incoming/<archive>.zip > x.zip`, extract, and run
`bash replay.sh` there (source 19 also `python3 code/verify_manifest.py .`).

Intake replays (on copies, pinned venv with Python 3.13.5, SymPy 1.14.0,
mpmath 1.3.0): source 19 `bash replay.sh`, rc 0 in 147 s, "427 scalar
checks; tolerance 1e-40", six JSON equal to `expected/` up to CRLF; source
26, its four scripts and `compare_results.py`, rc 0 in 62 s, four PASS
lines, four JSON equal to `data/` up to CRLF (PDF build skipped). The
recipes above were run once more at the write, with the shipped names:
source 26 rc 0 in 52 s, four PASS lines; source 19 (on a loaded machine
the replay hit a 300 s cap in `sector_check.py`, which was then rerun
alone, 69 s, followed by `stabilization_check.py` and the comparison with
`OUTPUT_DIR` set) all five scripts rc 0 and "PASS: 6 result files, 427
scalar checks; numerical tolerance 1e-40".
Manuscript 27 was not rerun (same code and data blobs as 26).

## Build the article

The report is standalone pdfLaTeX (no `\input`). Build in a scratch
directory, not here:

```sh
B=$(mktemp -d) && cp article.tex "$B" && cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Result: 32 pages, no errors, no warnings, no undefined or multiply defined
labels, no duplicate destinations, no overfull or underfull boxes. The
delivered build scripts (`code/19-distance-build_pdf.sh`,
`code/26-adjacent-build.sh`) are delivery records; they build the
delivered manuscripts, not this text.

## Provenance

Arrival `096ee7b87` (batch 77, 71 archives); placement `d0e6008d9`
(cluster P4: "Place 13 OEIS-asymptotics manuscripts as eleven new reports;
retire a superseded edition; hand one to cluster P3"), which staged 19's
`article.tex` and `README.md` unprefixed and 19 + 19 support files with the
prefixes `19-distance-` and `26-adjacent-`; write "Write batch 77P4
(2/11)", which replaced the delivery README by this guide, merged source
26 into `article.tex`, and built `article.pdf`.
