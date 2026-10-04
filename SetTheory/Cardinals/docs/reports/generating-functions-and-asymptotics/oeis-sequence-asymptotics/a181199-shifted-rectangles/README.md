# Fixed-Height Shifted Rectangles

**An unconditional proof of the A181199 asymptotic, all-order expansions, and an algebraicity dichotomy**

A research report dated 3 October 2026, built from one manuscript. Its title
page reads "Prepared for Vladimir Reshetnikov" and its PDF author field
"Research report prepared for Vladimir Reshetnikov"; the package names no
human author and no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 85, manuscript 09 | `Shifted_Rectangle_Asymptotics.zip` (wrapper directory `Shifted_Rectangle_Asymptotics/`, 343,338 bytes, 21 files), arrival commit `9d6968c8a`; main file `article.tex` | `6bf7f30d0` (`6bf7f30d0352f7596e70928b3d4f304914075907`, quoted in Section 1.3, the ProveIt bibliography entry and `notes-SOURCES_AND_STATUS.md`) | `ddf8df5d5` (batch 85C) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The manuscript says its
theorems "have not been independently peer reviewed or proof-assistant
verified" and that historical priority is not certified. The exact
computations corroborate the proofs on finite ranges; the numerical tables
are decimal diagnostics, not interval enclosures.

## What it proves

Fix the number of rows `m`. `T_m(n)` counts `m × n` arrays of `1, …, mn`
increasing along rows, columns, diagonals and downward antidiagonals
(OEIS A181196; the rows `m = 3, 4, 5` are A181197, A181198, A181199). Put
`d = C(m,2)`, `J_m = ∏_{j<m} j!`, `M_m(n) = (mn)!/(n!)^m`,
`α_m = (m²−1)/2` and `K_m = √m J_m / (4^d (2π)^((m−1)/2))`.

- **Theorem 2.1 (all orders at fixed height).**
  `T_m(n) = M_m(n) J_m (4n)^(−d) (Σ_{j≤L} c_{m,j} n^(−j) + O(n^(−L−1)))` for
  every fixed `L`, with rational `c_{m,j}` given by the finite moment formula
  of Proposition 5.1; `c_{m,1} = m(m²−1)/12`,
  `c_{m,2} = m²(m²−1)(m²+2)/288`. Equivalently
  `T_m(n) = K_m m^(mn) n^(−α_m) (Σ b_{m,j} n^(−j) + …)`, with
  `b_{m,1} = (m²−1)²/(12m)` and `b_{m,2} = (m²−1)(m⁶+3m²−1)/(288m²)`.
- **Corollary 2.2 (A181199).**
  `T_5(n) = 9·5^(5n+1/2)/(2^17 π² n^12) · (1 + 48/(5n) + 5233/(100n²) +
  1028391/(5000n³) + 60248377/(100000n⁴) + 273939939/(250000n⁵) + O(n⁻⁶))`.
  The leading term is the asymptotic recorded in OEIS A181199 as Vaclav
  Kotesovec's conjecture (27 February 2023, based on Christoph Koutschan's
  guessed recurrence); the proof does not use that recurrence.
- **Theorem 2.3 (algebraicity dichotomy).** `Σ T_m(n) zⁿ` is algebraic over
  `ℚ(z)` (equivalently over `ℂ(z)`) if and only if `m = 1` or `m = 2`: a
  logarithmic singularity at odd `m ≥ 3`, a transcendental Puiseux amplitude
  at even `m ≥ 4` (Section 8).
- **Corollary 2.4.** `T_m(n)/f^(n^m) = 2^(−m(m−1)) (1 + m(m²−1)/(4n) +
  m²(m²−1)(m²−2)/(32n²) + O(n⁻³))`, where `f^(n^m)` counts ordinary standard
  Young tableaux of the `m × n` rectangle.
- **Theorem 4.1 (random-threshold cut):** the exact interior-sum identity
  with nonnegative boundary error at most `m(pⁿ + (1−p)ⁿ)` (at `p = 1/2`,
  `0 ≤ T_m(n) − M_m(n) I_m(n) ≤ 2m 2^(−n) M_m(n)`); Proposition 5.1 (finite
  coefficient formula); Section 6 (the two universal corrections through the
  binomial Vandermonde ensemble and Krawtchouk polynomials); Section 7 (the
  `m = 2` Catalan control, the A181197 and A181198 expansions through `n⁻²`,
  Table 1 of `c_{m,j}` for `m ≤ 6`, `j ≤ 5`, Table 2 of A181199 errors).
- **Theorems 9.1 and 9.2:** Gaussian-Vandermonde (GUE-type) limit laws for
  the intermediate row lengths, at a fixed numerical level and, on the
  trace-zero hyperplane, at a fixed fraction of the labels.
- Section 10: eventual strict monotonicity and log-convexity, and a
  `W_{−1}` inversion of the asymptotic profile with two corrections;
  Appendix A: a direct proof of the shifted hook product; Appendix B: an
  implementation-independent coefficient recipe; Section 12: seven research
  questions.

## What is not claimed

- **Neither guessed recurrence is proved:** not A181198's order-two,
  degree-nine recurrence, nor its conjectured finite-sum solution, nor
  A181199's order-three recurrence. The draft OEIS text says explicitly not
  to mark either as proved.
- The expansion is a Poincaré expansion for fixed `m` and fixed truncation
  order: no growing-height theorem, no Borel summability, Stokes data or
  exponentially improved transseries; the boundary bound `2m 2^(−n)` is not
  claimed sharp.
- Nonalgebraicity is not non-D-finiteness (Remark 8.1); whether `F_m` is
  D-finite for every `m` is Question 7.
- Theorems 9.1 and 9.2 are one-time laws, not process convergence.
- The inverse-index approximations are not integer-threshold certificates,
  and the inversion method is standard (see below); the smallest `n` from
  which monotonicity and log-convexity hold is not identified.
- **Classical material, credited, not new:** the shifted hook product
  (a standard formula, cited from Sun's 2017 article and re-proved in
  Appendix A), the
  order-statistics/order-polytope interpretation (Sun), the A181197
  height-three leading term (Panova, in comments by Joel B. Lewis), Gaussian
  Vandermonde integrals, Krawtchouk polynomials and Lambert-W inversion.
  Chan's periodic P-partitions concern the other orientation (fixed `n`,
  growing `m`).
- The `n = 80` values are OEIS b-file inputs, not regenerated; the
  numerical tables are 90-digit decimals, not certified enclosures.
- Priority rests on the producer's inspected sources only ("not an
  exhaustive priority search"); an OEIS "conjecture" label "is not by itself
  proof that no published proof exists".
- **Nothing was submitted to OEIS**, by the package's author or by the
  intake. `data/notes-PROPOSED_OEIS_ADDITIONS.txt` is a draft marked "DRAFT
  ONLY — NOT SUBMITTED"; any submission is a human editor's decision after
  review.

## Checks made at intake

On 3 October 2026 the intake reran the delivered programs on scratch copies
(Python 3.14.4, Windows; see "Rerun the checks"): `code/verify.py` passed all
471 checks (27 + 238 + 120 + 30 + 12 + 12 + 30 + 2) in 56 s on a loaded
machine (the package recorded 3.9 s), and every data file it writes matched
the shipped one after CR stripping, except the `seconds` field of
`data/verification.json`; its standard output equals `data/verification.txt`
up to the same field. `code/coefficients.py --height 5 --order 5`
reproduced `data/coefficients_m5.json`, and `code/numerics.py` (mpmath 1.3.0)
reproduced `data/numerics.csv` byte for byte and printed `data/numerics.txt`.
The delivered `SHA256SUMS.txt` verified 20/20. The intake also checked
symbolically that `K_5 = 9√5/(2^17 π²)` and, for `m = 2, …, 7`, that
`K_m = 2^(−m(m−1)) C` with the transseries volume's rectangle constant `C`
and that `(2.4)` and the hook product give both printed corrections of
Corollary 2.4.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, no formal development in ProveIt treats shifted tableaux, and the
report's place in the collection confers no formal status. The one formalized
neighbour is general: Theorem J.23 of the transseries volume (below), whose
real branch rules are proved in
`Analysis/FabiusFunction/Lean/FabiusFunction/LinLogCoreInversion.lean`
(rated "Partial" in that volume's register; nothing about shifted rectangles).

**Not new: the comparison constant and the inversion.** Dated `[write]`
notes record:

- the normalizer `f^(n^m)` of Corollary 2.4 is the classical rectangle hook
  count, equation (3.19), `t2:eq:tableaux`, of
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/`
  (Section 3.5, written `T_d(n)` with `d` rows). With its constants (3.20)
  (`t2:eq:tableaux-constants`: `a = m log m`, `β = −α_m`,
  `C = √m (2π)^((1−m)/2) ∏ j!`), `K_m = 2^(−m(m−1)) C` exactly, which is the
  leading term of Corollary 2.4;
- the inversion (10.3) is an instance of Theorem J.23
  (`p0:thm:lambert-core`) of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`,
  with `a = m log m`, `b = −α_m` and its `b < 0` branch rule (`W_{−1}`,
  valid for `L > α_m(1 − log(α_m/(m log m)))`); the integer-threshold
  caution is its staircase theorem J.43 (`p0:thm:staircase`). The manuscript
  itself calls the method standard.

**Neighbouring reports.**

- `oeis-sequence-asymptotics/a189281-path-forest-expansions`: the
  manuscript read its README (one report in three Parts, which the manuscript
  calls "the existing path-forest reports") as an editorial precedent;
  none of its theorems is used. It inverts by the same apparatus
  (`spf:thm:inverse-first`, `spf:thm:inverse-all`).
- Batch-85 siblings: `oeis-sequence-asymptotics/a047874-long-increasing-subsequences`
  (manuscript 08; it shares the rectangle tableau count, its (2.6), but no
  theorem) and `oeis-sequence-asymptotics/a182220-source-boundary`
  (manuscript 07; unrelated).
- Other conjectures of Kauers and Koutschan's 2023 paper, whose Section 6.4
  discusses the guessed A181198/A181199 recurrences, are proved in
  `enumerative-combinatorics/a181280-binary-matrix-formula` (Conjecture 20),
  `enumerative-combinatorics/a195806-hexagonal-lattice` (Conjecture 11) and
  Part IV of `oeis-sequence-asymptotics/a215561-fixed-composition-excursions`
  (Conjecture 15). This report proves none of Section 6.4's recurrences.

**Stale claims.** None. "Identifier searches for A181198 and A181199
returned no matching repository report" is true at the pin and still true:
at placement and again at this writing, a search of the tracked tree for
A181196–A181199, shifted rectangles, shifted tableaux, shifted hook products
and Sun's article found nothing outside the arrival archive except the
sibling a047874, which points here.

## Notation

The manuscript reuses several letters (`T_m(n)` against the volume's
`T_d(n)` for ordinary rectangles; `d = C(m,2)` against the volume's `d` = rows;
`K_m`, `K`, `K_j(X)`; `L`, `L_5(n)`; `h_r(q)` against the norms `h_j`; `λ`;
`R_n`, `R_m`, `R(z)`, `𝓡_{L,n}`; `p` against power sums `p_r`; `q_{ij}`, `q`;
`Z_m(n)`, `Z_i`; `A`, `B`, `𝒜`; `C(z)`, `C_{n−1}`, `C_{m,L}`, `𝒞_n`;
`E_{m,n}`, `𝔼`, `ℰ_z`; `H(λ)`, `H_j`, `H_{20}`; `β_j`). A table in the first
`[write]` note (Section 1.3) fixes each reading and the tempting false one,
notably that `T_m(n)` is **not** the ordinary rectangle count. No symbol was
renamed.

## Labels

Every label carries the prefix `shr:`. The manuscript's 69 labels were
prefixed before anything cited them, and every reference was updated (49
`\eqref`, 11 `\ref`); no label was added or removed, so the report has 69
labels, and no section, theorem, equation or table number changed (checked
against the `.aux` of a build of the delivered source). Corollary 2.4 has no
label and is cited by number.

The writing step also:

- added four dated `[write]` notes: end of Section 1.3 (provenance, pin and
  repository claims, neighbours, the notation table), after Corollary 2.4
  (the comparison constant), end of Section 10.2 (the inversion is an
  instance) and end of Section 11.3 (shipped layout, intake replay, OEIS
  licence, the draft OEIS text);
- defined the `writenote` environment in the preamble, and wrapped the title
  page in `\hypersetup{pageanchor=false}` … `{pageanchor=true}`: the delivered
  source, built as delivered, gives a duplicate `page.1` destination.

No statement, proof, number or table of the manuscript was changed.

## Files

```text
README.md                               this guide (replaces the delivery README)
article.tex                             the report (labels prefixed; four [write] notes)
article.pdf                             compiled report, 24 pages
notes-SOURCES_AND_STATUS.md             the package's source and status audit (delivered as notes/SOURCES_AND_STATUS.md)
code/build.sh                           three pdflatex passes (delivered at the package root; see below)
code/coefficients.py                    exact rational coefficient engine, Proposition 5.1 (standard library)
code/tableaux.py                        row-state and bitmask-poset enumerators, shifted hook product (standard library)
code/verify.py                          the 471 finite checks (standard library; writes into data/)
code/numerics.py                        90-digit diagnostics of Table 2 (mpmath; writes into data/)
data/requirements-numerics.txt          mpmath==1.3.0 (delivered at the package root)
data/oeis_selected.json                 A181198/A181199 terms, n = 1..10, 20, 40, 80 (third-party, CC BY-SA 4.0; see below)
data/exact_regenerated.json             A181198/A181199, n = 1..10, 20, 40, regenerated by the row-state program
data/coefficients_m1_to_m6.json         c_{m,j} and b_{m,j}, m = 1..6, j = 0..5 (Table 1)
data/coefficients_m5.json               m = 5 through order 5, both normalizations
data/numerics.csv                       relative errors for A181198 and A181199 at n = 10, 20, 40, 80 (CRLF)
data/numerics.txt                       standard output of numerics.py
data/verification.json                  recorded run of verify.py (471 checks, PASS)
data/verification.txt                   standard output of verify.py
data/pdf_preflight.json                 the producer's QA record of the delivered PDF (not regenerable)
data/notes-PROPOSED_OEIS_ADDITIONS.txt  draft OEIS text, NOT SUBMITTED (delivered as notes/PROPOSED_OEIS_ADDITIONS.txt)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement moved `build.sh` to `code/`,
`requirements-numerics.txt` and `notes/PROPOSED_OEIS_ADDITIONS.txt` to
`data/` (the latter as `notes-PROPOSED_OEIS_ADDITIONS.txt`), and
`notes/SOURCES_AND_STATUS.md` to the report root as
`notes-SOURCES_AND_STATUS.md`; `code/` and `data/` keep their delivered
contents. Not shipped: the delivered 22-page `article.pdf` (307,362 bytes)
and `SHA256SUMS.txt` (which covers all 20 other files under their delivery
names). Both survive in the archive:
`git show 9d6968c8a:docs/incoming/Shifted_Rectangle_Asymptotics.zip > <scratch>/Shifted_Rectangle_Asymptotics.zip`.
Nothing was excluded as heavy.

**Third-party data.** `data/oeis_selected.json` holds terms of A181198 and
A181199 transcribed from The On-Line Encyclopedia of Integer Sequences
(https://oeis.org/A181198, https://oeis.org/A181199 and their b-files
`b181198.txt`, `b181199.txt`, inspected 3 October 2026 according to the
file). OEIS content is published by The OEIS Foundation Inc. under the
Creative Commons Attribution-ShareAlike 4.0 licence (CC BY-SA 4.0); this
file is third-party data under that licence, **not** MIT-0 like the rest of
the repository. The b-files are by Christoph Koutschan, with earlier terms
by Alois P. Heinz, and the A181199 asymptotic conjecture is Vaclav
Kotesovec's, as attributed in the entries. `data/numerics.*` are computed from these terms. The draft
`data/notes-PROPOSED_OEIS_ADDITIONS.txt` quotes the A181199 formula with its
attribution. No program contacts OEIS.

Delivered text that names the delivery layout or a file not shipped:
Section 11.3 of the article ("From the archive's top-level directory",
`bash build.sh`; a dated note there gives the shipped names); the delivery
README, staged as `README.md` and replaced by this guide; `code/build.sh`
(it runs `cd "$(dirname "$0")"`, so from `code/` it cannot find
`article.tex`); `data/pdf_preflight.json` (22 pages and 307,362 bytes: the delivered PDF,
not the shipped 24-page rebuild); and `data/verification.json`'s
`seconds` field (the producer's machine).

**Byte-level notes.** `data/numerics.csv` is CRLF throughout (Python's `csv`
module); the line
`docs/reports/…/a181199-shifted-rectangles/data/numerics.csv -text` in
`SetTheory/Cardinals/.gitattributes` keeps its bytes. Every other shipped
file is LF. The programs write JSON in text mode, so on Windows a rerun emits
CRLF where the shipped files are LF; compare after stripping `\r`.

## Rerun the checks (on a scratch copy)

Never run `code/verify.py` or `code/numerics.py` in place: they set
`ROOT` to the parent of `code/` and overwrite `data/exact_regenerated.json`,
`data/coefficients_m1_to_m6.json`, `data/verification.json` and
`data/numerics.csv` in this directory, and they have no output option. Copy
`code/` and `data/` (the delivered layout of those two directories) and run
there (Git Bash, from this directory):

```sh
R=$(pwd); T=$(mktemp -d); cp -r code data "$T/"; cd "$T"
py code/verify.py > verify.out                             # standard library; ~1 min
py code/coefficients.py --height 5 --order 5 --output c5.json
uv run --no-project --with mpmath==1.3.0 python code/numerics.py > numerics.out
for f in data/*; do tr -d '\r' < "$f" | cmp -s - <(tr -d '\r' < "$R/$f") \
  && echo "same  $f" || echo "DIFF  $f"; done                # only verification.json (seconds)
tr -d '\r' < c5.json | cmp - "$R/data/coefficients_m5.json" && echo same c5
```

(On a POSIX host use `python3` for `py`. Do not use `python -O`: the checks
are assertions.) Intake results are under "Checks made at intake".

## Build the PDF

pdfLaTeX (fontenc, xcolor, amsmath, amsthm, newtx, geometry, microtype,
mathtools, booktabs, array, longtable, graphicx, enumitem, fancyhdr,
tcolorbox, hyperref). The article is self-contained. Build in a scratch copy
(`code/build.sh` does not work from its shipped place):

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 24 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The delivered
source, built the same way, gives 22 pages with one duplicate `page.1`
destination (the title page).

## Provenance

- Sources cited by the manuscript: OEIS A181196–A181199 and the b-files of
  A181198 and A181199; Kauers–Koutschan, *Some D-finite and some possibly
  D-finite sequences in the OEIS*, J. Integer Seq. 26 (2023) 23.4.5
  (arXiv:2303.02793); P. Sun, Electron. J. Combin. 24(2) (2017) P2.41;
  B. T. Chan, *Periodic P-partitions* (Eur. J. Combin. 2023); Flajolet–Sedgewick,
  *Analytic Combinatorics*; DLMF §§4.13, 5.11, 18.19.
- Repository input: the pin `6bf7f30d0` (3 October 2026), for a bounded
  identifier search and the README of `a189281-path-forest-expansions`; no
  repository theorem is used.
- Batch 85 of `docs/incoming`, manuscript 09; arrival `9d6968c8a`,
  placement `ddf8df5d5` (batch 85C), written in the batch-85 write phase
  (3 October 2026). Single source, so the write made no merge choices.
