# Unlabeled Permutation Graphs to All Orders (OEIS A123448)

**A factorial expansion `a_n = (1/4) Σ_{k<R} h_k (n−k)! + O_R((n−R)!)` for
every fixed `R`, threshold windows that keep the rounding, and an all-orders
comparison of two sampling laws**

A research article dated 3 October 2026 ("Report 153" of a session bundle),
built from one manuscript. Its author line reads "Report 153" and its PDF
author field is empty: it names no person, tool or addressee. It carries no
e-mail address and no personal data.

**"Prepared for private review": none, but the repository is public.** The
placement record (`47fc7a069`) says that this package carries "prepared for
private review" in its README, `.tex` and provenance record. The write
checked every delivered file: the phrase does not occur. The only hits are
packaging negations — "No downloaded paper, private review document,
unrelated earlier report, or research working note is bundled" (delivery
README), "It contains neither unrelated earlier reports nor private review
documents" (Section 11 of the article) and "No complete papers, private
reviews or working notes, or unrelated previous reports are bundled"
(`data/SOURCE_PROVENANCE.json`) — so the flag was a false positive, as for
`a098569-self-modified-ascents`. Two delivered statements do bear on
publication: the article says "No OEIS submission, external publication, or
public repository modification is part of this report", and the delivery
README says the same of the release. This repository is public; filing the
report here is the repository owner's act, not part of the delivered work.
The article's title block is the delivered one ("Report 153", 3 October
2026).

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 153 (batch 106) | `Permutation_Graph_All_Orders_Expansion_Inverses_and_Sampling_Source.zip` (23 files at the archive root, no wrapper directory, 790,477 bytes, SHA-256 `b4b68c55…4397`), arrival commit `60f54ea06`; main file `Report153.tex` (1413 lines, 22 pp.) | none: the package names no ProveIt commit or path | `47fc7a069` (batch 106) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The proofs are
conventional mathematical proofs resting on four cited external theorems
(below). The finite computations certify inputs and rational identities, not
the analytic argument. No constant or onset is effective.

## Trust boundaries

- **External inputs, not re-proved:** Borinsky's factorial composition and
  inversion theorem (EJC 25(4) (2018) P4.1, Theorem 35 and equations
  (62)–(67)); the Albert–Atkinson–Klazar substitution decomposition and
  simple-permutation equation (`S(z) = (z − z²)/(1 + z) − T(z)`, with
  `s_n ~ e⁻² n!`); Habib–Paul's Lemma 20 (strong modules of an inversion graph
  = strong common intervals); and the classical fact that a prime permutation
  graph and its complement each have exactly two transitive orientations. The
  write read none of the first three (the source did); see "Sources" below.
- **Finite inputs:** `a_1, …, a_9` and `r_1, …, r_9` (two independent
  exhaustive enumerations), one-realizer counts `b_j` and marked-context counts
  `c_j` for `j ≤ 8`. The coefficients `h_0, …, h_7`, `g_0, …, g_6` and
  `z_1, …, z_7` are exact functions of these.
- **Quoted, not verified:** the 1990 table values for `n = 15, …, 20`
  (Bayoumi–El-Zahar–Khamis, double precision); they enter no proof.

## What it proves

`a_n` counts unlabeled permutation graphs (inversion graphs of permutations)
on `n` vertices, OEIS A123448; `r_n` counts vertex-rooted classes (vertex
orbits summed over classes, not `n a_n`). Statement numbers are the delivered
ones.

- **Theorem 1.1 (`prg:thm:main`)**: with `F(x) = Σ n! xⁿ`, `T = F^{⟨−1⟩}`,
  `Q = T∘A` and `H = C · xQ′/(Q A′) · exp(1/x − 1/Q) = Σ h_k x^k`, for every
  fixed `R`, `a_n = (1/4) Σ_{k<R} h_k (n−k)! + O_R((n−R)!)`. `h_k` depends only
  on `a_1, …, a_{k+2}` and `r_1, …, r_{k+1}`, and `k! h_k ∈ ℤ` (Corollary
  6.1). `h_0, …, h_7 = 1, −4, −1, −94/3, −769/6, −19969/15, −531812/45,
  −40114096/315`; in ordinary powers
  `a_n = (n!/4)(1 − 4/n − 1/n² − 97/(3n³) + O(n⁻⁴))`.
- **Sections 3–5**: interval exclusion (Lemma 3.1), a unique large simple node
  (Lemma 4.1), strong-module insertion (Lemma 4.2), exact unlabeled context
  recovery (Proposition 4.3), the weighted four-realizer identity
  `f(P) = 4/|Aut P|` (Lemma 2.1), negligible symmetric quotients
  (`exp((n/2) log n + O(n))`, Lemma 5.1), and the finite-polynomial
  approximation `a_n = (1/4)[xⁿ] C_R(x) S(B_R(x)) + O_R((n−R)!)` (Theorem 5.2),
  which is what makes the transfer non-circular.
- **Section 8**: strict monotonicity; Theorem 8.1, a threshold window
  `⌊ν_R − ε_R⌋ + 1 ≤ N(X) ≤ ⌈ν_R + ε_R⌉` with `ε_R = O(ν_R^{−R}/log ν_R)` for
  every fixed `R`; the explicit centre
  `v_* = u − 1/2 − c/D + (97/24 − c²/(2D²))/(uD)`, `u = L/W₀(L/e)`,
  `L = log X`, `D = log u`, `c = ½ log(2π) − log 4`, with a bracket of width
  `O(1/(u²D))`.
- **Section 9**: the exact fiber product (Lemma 9.1), the four-realizer
  expansion `M_{4,n} = (1/4) Σ g_k (n−k)! + …` (Theorem 9.2,
  `g_0, …, g_6 = 1, −8, 22, −230/3, 382/3, −22468/15, −283418/45`), and
  Theorem 9.3: `d_TV(P_n, U_n) = 4/n − 15/n² + 169/(3n³) + 215/(2n⁴) + O(n⁻⁵)`
  between the graph of a uniform permutation and a uniform graph class (seven
  coefficients given).

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Remark 8.2 (`prg:rem:transseries`)**, against the transseries volume:
  (a) `N(X)` is the volume's integer staircase and `p0:thm:staircase`(5)
  applies (every continuous `g` has `sup |N − g| ≥ 1/2`); (b) Theorem 8.1 and
  the explicit bracket are **not** instances of `p0:thm:staircase`(1)–(2): the
  approximant `𝒜_R` is not an interpolation of `a_n` (`𝒜_R(n) = (1/4)
  Σ_{k<R} h_k (n−k)! ≠ a_n`), and the bracket is proved directly at the
  integers; (c) the centre `u` is an instance of `p0:prop:factorial-core`
  (`κ = 1`, `d = −1`, core slope `D = log u`); (d) the two shifts of `v_*` are
  the first two coefficients of the formal reversion `p0:thm:core-reversion`
  after the change of variable `x = u(1 + E)`, `t = 1/u`, with `Λ = D`,
  `h(E) = (1+E) log(1+E) − E` and `c`, `D` as indeterminates — an instance of
  its recurrence, not of its Bell form, and formal only (the error bounds are
  the source's own).
- **`h_8 = −3687969659/2520`** (`8! h_8 = −59,007,514,544`), end of Section 7,
  from the OEIS term `a_10 = 524,572`, which the companion does not
  enumerate; `h_8` is conditional on that term.
- **Johnston's question** (Section 10.3; next section).
- Section 1.1 (provenance, sources as read, relation to the repository,
  reading conventions, collected non-claims), notes on the 1990 table
  (Section 10.1) and on the source's repository search (Section 10.4), and
  Section 12.1 (open questions).

## Johnston's question and what was known

Tom Johnston's blog post "Enumerating permutation graphs", dated 25 October
2020, at <https://tomjohnston.co.uk/blog/2020-10-25-enumerating-permutation-graphs.html>,
enumerated the graphs through `n = 14` (the source of OEIS `a_12`–`a_14`) and
said that its author did not know whether the count is `o(n!)`. Theorem 1.1
gives `a_n ~ n!/4`, so it is not. The placement record says this report
"answers Johnston's 2020 question"; the write qualifies that. The
**qualitative** answer was already in print: Bassino, Bouvel, Féray, Gerin and
Pierrot, arXiv:2402.06394v1 (9 February 2024), Section 4.3, prove
`a_n ≥ n!/30` for all large `n` in the proof of their Theorem 2.1 (every simple
permutation gives a modular-prime graph, which has at most four realizers,
Proposition 4.6; so `a_n ≥ s_n/4 ~ e⁻² n!/4 ≈ 0.0338 n!`). The source quotes
those "coarse bounds" but does not connect them to Johnston. What is new in
the sources read is the constant `1/4` and the expansion to every fixed order.

Priority of the leading term is **not** claimed (the source's own caveat,
kept): El-Zahar and Sauer (Order 5 (1988)) prove that unlabeled
two-dimensional posets number `~ n!/2`, a close classical antecedent of which
the source read only the abstract; Winkler (Order 7 (1990/91)) compares
related random-order models (abstract only); Bayoumi, El-Zahar and Khamis
(1990) gave the exact recurrence and a table through `n = 20`; the 2026
journal version of Bassino et al. (EJP 31, article 110) was not accessible.

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- Every truncation order is fixed: no bound uniform in `R`, no growing-order
  truncation, no convergence or Borel summability of `H`, no exponentially
  small sectors, no optimal truncation (Remark 6.2).
- No effective `K_R`, onset or certified threshold; the floor and ceiling of
  the windows cannot be replaced uniformly by one ceiling.
- Total variation controls events and bounded observables additively; it
  says nothing about unbounded statistics or relative errors of rare events.
- The finite checks certify inputs and identities, not the analytic proof;
  exact verification stops at order nine.
- No first-ever claim for the leading equivalent; the repository search was
  "a bounded absence check, not a universal novelty proof"; "No OEIS
  submission, external publication, or public repository modification is part
  of this report."

The write adds: its numerical comparisons are observations, not bounds.

## Further questions

Section 12.1 (`prg:sec:further`) states every unproved claim as an open
question with its source, sketch and what is missing (Vladimir's standing
rule of 4 October 2026). **Nothing in the source was found to be wrong.**

1. **Effective constants and certified thresholds** (`prg:q:effective`).
2. **Explicit centres of every order** (`prg:q:shifts`): the formal shifts
   exist (Remark 8.2(d)); a bracket around the centre truncated after `m`
   shifts is proved only for `m = 2`.
3. **Growth of `h_k`; orders growing with `n`; Borel summation; exponentially
   small sectors** (`prg:q:growth`).
4. **Efficient recurrences for `r_n`, `b_j`, `c_j`** (`prg:q:recurrence`):
   `h_9` needs `r_10`, `g_7` needs `b_9`, `z_8` needs `g_7`.
5. **Finer fiber laws; unbounded statistics; rare events** (`prg:q:fibers`).
6. **Priority and the quoted table** (`prg:q:priority`): the full texts of
   El-Zahar–Sauer, Winkler and the 2026 Bassino et al.; exactness of the 1990
   values for `n = 15, …, 20`.

## Checks made at intake

On copies (5 October 2026; Windows, Python 3.14, standard library only):

- At placement (batch-106 dossier): all 22 entries of `SHA256SUMS` verify.
  The delivered I/O layer needs POSIX `O_NOFOLLOW`/`O_DIRECTORY`, so the
  replays called `verify.run()` through a read-only shim: the default replay
  (both enumerators through order 6; 0.2 s) and the **full replay** (both
  enumerators, all inputs `a_n, r_n` through 9 and `b_j, c_j` through 8;
  4 min 27 s) reproduced `check-release-normal.json` and
  `check-full-release-normal.json` byte for byte (the `-optimized` twins are
  byte-identical to them). `test_companion.py`, `test_release.py`,
  `build_pdf.py` and `make_zip.py` were not run (Linux-only file calls,
  `/proc/self/fd`, Debian TeX trees).
- At the write: all 21 staged files are byte-identical to a fresh extraction of
  the archive from `60f54ea06`; route B below reproduces both default result
  files (`python -B` and `python -B -O`, about 0.4 s). An independent exact
  program of the write recomputed `Q`, `h_0, …, h_7`, the inverse-power
  coefficients `1, −4, −1, −97/3, −1339/6, −11603/5, −2592529/90,
  −127151851/315`, `g_0, …, g_6` and `z_1, …, z_7` from the printed inputs (all
  agree), and `h_8` from the OEIS `a_10`.
- Against the data: with `S_8(n) = (1/4) Σ_{k<8} h_k (n−k)!`, the relative
  difference `(a_n − S_8(n))/a_n` is 0.1152, 0.0238, 0.0107, 0.00458, 0.00174,
  0.000463, −0.0000604, −0.000238 at `n = 12, 14, 15, …, 20` (OEIS terms to
  14, the quoted 1990 values from 15). The values for `n = 15, …, 19` are
  representable as IEEE doubles; the printed `a_20 = 480,517,922,278,457,424`
  is not (it is `≡ 16 (mod 64)` in `[2⁵⁸, 2⁵⁹)`, where doubles are multiples of
  64). Observations only.
- The dossier read the manuscript in full and spot-checked the proofs; no
  error. It recomputed `k! h_k`, `U⁻¹ − 1 = 4y + 17y² + …`, the
  total-variation coefficient `−15` and the residual `−97/24`.
- Sources read by the write: OEIS A123448 (revision 35, 4 July 2026, now named
  "Number of permutation perfect graphs on n nodes"; the source's bibliography
  uses the older name); Johnston's post; arXiv:2402.06394v1 (Proposition 4.6,
  Section 4.3); the transseries volume. Not read: Borinsky, Albert–Atkinson–
  Klazar, Habib–Paul, Bayoumi–El-Zahar–Khamis (all read by the source),
  El-Zahar–Sauer and Winkler (abstracts only, by the source), the 2026 journal
  text of Bassino et al.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq; no formal file treats permutation graphs or modular decomposition.
Placement in the collection confers no formal status.

**Siblings sharing a pipeline** (same placement commit `47fc7a069`, written
separately in batch 106; paths under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):

- [`a156808-circle-graphs`](../a156808-circle-graphs/) (bundle Reports 150 and
  152, unlabeled circle graphs A156808/A156809, labels `cgr:`), and
- [`a005975-interval-graphs`](../a005975-interval-graphs/) (bundle Report 133,
  unlabeled interval graphs A005975/A005976, labels `ivg:`).

All three count a representation model (permutations here; indexed matchings;
interval orders), show that almost every graph has a recoverable prime core
with bounded decorations whose representations form one full orbit of a
symmetry group (the Klein four-group here; the dihedral group of order `4n`; a
duality of order 2), make the symmetric cores negligible, and invert with
Lambert-W brackets that keep the rounding. They share no statement and no
manuscript cites another; the decomposition theories (modular decomposition
here and for interval graphs, split decomposition for circle graphs), the
external inputs and the normalizations (`n!/4`, `(2n−1)!!/(4n)`, half the
Fishburn numbers) differ. "Prime" means modular-prime here and split-prime in
the circle-graph report; Bassino et al. (2024) is an input of both this report
and the circle-graph one.

**Other neighbours.** `a007716-bipartite-multigraphs` and
`a307316-leafless-multigraphs` use the same rare-symmetry philosophy for
multigraphs (no shared statement). The transseries volume
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`
(`p0:prop:factorial-core`, `p0:thm:core-reversion`, `p0:thm:staircase`): see
Remark 8.2 for what is and is not an instance.

**Stale claims.** The source's "repository-index search found no matching
permutation-graph topic" was true before batch 106; a dated note in Section
10.4 says that this report is now that topic.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with tempting false readings: `r_n` (not `n a_n`); `Q = T∘A` (not a quotient
graph); `h_k` (factorial basis, against the inverse-power coefficients:
`−94/3` against `−97/3`; and the circle-graph sibling's `h_n = (2n−1)!!/(4n)`);
"prime" (modular, not split); `b_R` against `b_j`; `C_R`, `c_j`, `c`; `J_m`
against `J(x)`; `K`, `K(x)` and `K_R` (both a truncation and an error
constant); `E(x)`, `E_k`, `E_n`; `𝒟` against `D`; `U`, `𝖴_n`, `𝒰_R(n)`;
`𝖯_n`, `P`, `P(x)`; `g(v)` against `g_k`; `𝒜_R` (not an interpolation of
`a_n`); `L` (`log X`, and a context graph); `R` (an order, not the ring of
the transseries volume); `Z(y)` against `Z_n`. No symbol was renamed.

## Labels

Every label carries the prefix `prg:` (none existed in the repository). The
manuscript's 72 labels (`eq:` 44, `sec:` 14, `lem:` 6, `thm:` 5, `prop:` 1,
`cor:` 1, `rem:` 1) were prefixed before anything cited them, and every
`\ref`/`\eqref` was updated. The write added 9: `prg:sec:provenance`,
`prg:rem:transseries`, `prg:sec:further` and the questions
`prg:q:effective`, `prg:q:shifts`, `prg:q:growth`, `prg:q:recurrence`,
`prg:q:fibers`, `prg:q:priority`. The report has 81 labels; builds of the
delivered text and of this one give all 72 delivered labels the same numbers
(aux files compared). The added remark is the last numbered statement of its
section and the added displays are unnumbered.

## Files

```text
README.md                                          this guide (replaces the delivery README)
article.tex                                        the report (delivered Report153.tex; labels prefixed, [write] additions)
article.pdf                                        compiled report, 27 pages
companion-README.md                                the companion's guide (delivered companion/README.md)
code/companion-verify.py                           exact checker: claims, algebra, enumeration replay (delivered companion/verify.py)
code/companion-enumeration.py                      two exhaustive graph enumerators (delivered companion/enumeration.py)
code/companion-safe_io.py                          POSIX-only safe I/O helpers (delivered companion/safe_io.py)
code/companion-test_companion.py                   33 companion tests (delivered companion/test_companion.py)
code/build_pdf.py                                  deterministic Linux PDF builder (delivered at the package root)
code/make_zip.py                                   deterministic archive builder (delivered at the root)
code/release_tools.py                              exclusive-output helpers (delivered at the root)
code/test_release.py                               release tests (delivered at the root)
data/SOURCE_PROVENANCE.json                        the source's provenance record (delivered at the root)
data/companion-claims.json                         exact expected values (delivered companion/claims.json)
data/companion-inputs.json                         finite inputs a_n, r_n, b_j, c_j (delivered companion/inputs.json)
data/companion-provenance.json                     companion hashes and policy (delivered companion/provenance.json)
data/companion-results-check-release-normal.json        default replay (delivered companion/results/)
data/companion-results-check-release-optimized.json     the same under -O (byte-identical)
data/companion-results-check-full-release-normal.json   full replay through order 9
data/companion-results-check-full-release-optimized.json  the same under -O (byte-identical)
data/companion-results-tests-release-normal.json        33 tests passed
data/companion-results-tests-release-optimized.json     33 tests passed under -O (differs only in runner_optimization)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery (checked again at the write).

**Not shipped**, recoverable from the arrival commit: `Report153.pdf` (the
delivered 22-page PDF, 455,785 bytes); `SHA256SUMS` (2,038 bytes, 22 entries;
repository policy ships no checksum manifests; verified at placement and at
the write); and the delivery `README.md` (7,217 bytes), staged at placement
and replaced by this guide (summarized under "From the delivery README").

**Delivered text that names the delivery layout or files not shipped.** The
renamed scripts no longer import each other: `companion-verify.py` imports
`safe_io` and `enumeration`, `companion-test_companion.py` imports
`enumeration`, `safe_io` and `verify`, and `build_pdf.py` imports
`release_tools`. `safe_io` takes the package root and `results/` from its own
directory. `build_pdf.py` builds `Report153.tex`; `make_zip.py` and
`test_release.py` check the delivered allowlist, `Report153.pdf` and
`SHA256SUMS`. `companion-README.md`, `data/companion-provenance.json` (file
hashes keyed by delivered names) and `data/SOURCE_PROVENANCE.json` refer to
the delivered layout, and Section 11 of the article to "the source archive"
and "the root README". **None of the scripts runs in this directory**; use the
routes below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Permutation_Graph_All_Orders_Expansion_Inverses_and_Sampling_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # b4b68c5562831ebcc1796a33a7a93d680b5179a2b136ddbd0e12741b03ff4397, 790,477 bytes
mkdir "$T/pkg" && cd "$T/pkg" && unzip -q ../a.zip && sha256sum -c SHA256SUMS
```

The archive has no wrapper directory: unzip it into an empty directory.

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only; no network. Never run anything
in the repository.

**Route A, delivered layout, on a POSIX host** (Linux; the I/O layer needs
`O_NOFOLLOW` and `O_DIRECTORY`). From `"$T/pkg/companion"`:

```sh
python3 -B verify.py > "$T/default.json";    cmp "$T/default.json" results/check-release-normal.json
python3 -B -O verify.py > "$T/default-O.json"; cmp "$T/default-O.json" results/check-release-optimized.json
python3 -B test_companion.py                 # 33 tests
python3 -B verify.py --enumerate-through 9 > "$T/full.json"   # minutes (4.5 min at intake)
cmp "$T/full.json" results/check-full-release-normal.json
```

`test_release.py`, `build_pdf.py` and `make_zip.py` need `/proc/self/fd` and
the recorded Debian TeX trees; they were not run by the intake.

**Route B, from the shipped programs, any platform** (tested at the write on
Windows; it skips the I/O layer and checks the mathematics only):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a123448-permutation-graphs
T=$(mktemp -d); cd "$T"
cp "$R/code/companion-verify.py" verify.py
cp "$R/code/companion-safe_io.py" safe_io.py
cp "$R/code/companion-enumeration.py" enumeration.py
python3 -B -c "import sys, json; sys.path.insert(0, '.'); import verify; R = sys.argv[1]; c = json.load(open(R + '/data/companion-claims.json', encoding='utf-8')); i = json.load(open(R + '/data/companion-inputs.json', encoding='utf-8')); b = (json.dumps(verify.run(c, i, through=6, methods='both'), indent=2, sort_keys=True) + '\n').encode('utf-8'); print(b == open(R + '/data/companion-results-check-release-normal.json', 'rb').read())" "$R"
```

It prints `True` (about 0.4 s); with `-O` compare against
`companion-results-check-release-optimized.json`. With `through=9` and the
`check-full-release-normal.json` file it is the full replay (minutes). Use
`py` where `python3` is not on the path.

## Build the PDF

pdfLaTeX (fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, geometry,
booktabs, longtable, array, microtype, hyperref); the bibliography is
embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 5 October 2026: 27 pages;
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull boxes.
The delivered source built the same way gives 22 pages and is equally clean.
The article keeps the delivered preamble lines that suppress PDF dates and
trailer identifiers; the delivered byte-identity check of the PDF applies to
`Report153.tex` under the delivering toolchain, not to this build.

## From the delivery README

The delivery README (replaced by this guide) described "the complete proof,
editable LaTeX, rendered PDF, and exact computational companion", listed the
results above (the eight coefficients, `k! h_k ∈ ℤ`, the threshold windows,
the second Lambert-W shift, the four-realizer expansion and the
total-variation series) and the observation that nontrivial contexts with
`t = 1` occur at size seven, so the marked-context factor cannot be omitted.
Its "Scope and source boundary" repeated the non-claims above, the prior art
(Bayoumi–El-Zahar–Khamis, El-Zahar–Sauer, Winkler) and that the 1990 values
for `n = 15..20` are not certified. It gave the route-A commands, the full
replay, the PDF builder (Python 3.12.14, pdfTeX 1.40.26, TeX Live 2025, Linux
trees) and the archive builder (stored ZIP, sorted members, timestamp
2026-10-03 00:00:00), and stated that the manifest "proves internal
consistency, not authenticity against simultaneous replacement of payload and
checksums".

## Rights

Repository contents are MIT-0. The article quotes OEIS terms of A123448
(through `a_14`, and `a_10` in the `h_8` note); OEIS content is published by
The OEIS Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and
those terms remain under that licence. The six values for `n = 15, …, 20` are
quoted from Bayoumi–El-Zahar–Khamis (1990) with attribution. Nothing was
submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: Albert–Atkinson–Klazar (JIS 6 (2003));
  Bayoumi–El-Zahar–Khamis (Cairo, 1990); Borinsky (EJC 25(4) (2018));
  Habib–Paul (Comput. Sci. Rev. 4 (2010)); Bassino–Bouvel–Féray–Gerin–Pierrot
  (arXiv:2402.06394v1; EJP 31 (2026)); El-Zahar–Sauer (Order 5 (1988));
  Winkler (Order 7); OEIS A123448; Johnston (blog, 25 October 2020). Added by
  the write: the transseries volume of this repository.
- Repository input: none; the package names no ProveIt commit or path.
- Batch 106 of `docs/incoming`, bundle Report 153; arrival `60f54ea06`,
  placement `47fc7a069`, written 5 October 2026. Single source, so no merge
  choices. The delivered `Report153.tex` is shipped as `article.tex`; the
  delivered programs, data and provenance records as listed above.
