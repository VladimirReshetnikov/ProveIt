# Unlabeled Circle Graphs

**OEIS A156808 and A156809: the leading equivalent with error bounds and inverses, and the first corrections**

This is a research report built on 5 October 2026 (write batch 106) from two
manuscripts of one external research session, Reports 150 and 152 of the
session bundle of Reports 1–243, both dated 3 October 2026. They study one
pair of sequences: the numbers `c_n` of connected and `g_n` of all unlabeled
circle graphs on `n` vertices ([A156808](https://oeis.org/A156808),
[A156809](https://oeis.org/A156809)), through the `m_n = (2n−1)!!` indexed
perfect matchings of `2n` cyclically ordered endpoints, the dihedral group of
order `4n` acting on them, and the normalization `h_n = m_n/(4n)`.

- **Part I** (Report 150, the base): `c_n ~ g_n ~ e^{−3/2} h_n`, by an upper
  bound from reciprocal representation fibres and a matching lower bound from
  asymmetric split-prime cores with canonically recoverable leaf, true-twin and
  false-twin decorations; `g_n − c_n = g_{n−1} + O(m_n/n³)`; relative errors
  `O(1/n)` for both counts and `c_n/g_n = 1 − 1/(2n) + O(n⁻²)`, through a
  self-contained Poisson approximation of local matching patterns with the
  explicit bound `min(1, 200/n)`; independent limiting `Poisson(1/2)` decoration
  counts, a `Poisson(3/2)` core deficit, asymmetry probability `e^{−1}`,
  leafless `e^{−1/2}`, split-prime `e^{−3/2}`; labeled counts
  `~ e^{−2}(2n)!/(2^{n+2}n)`; a Lambert-W inverse with ceiling-safe brackets;
  and the derived value **A156808(13) = 21,593,488,017** (Euler inversion from
  A156809(13)).
- **Part II** (Report 152, a sequel): `c_n = e^{−3/2} h_n (1 − 15/(4n) + O(n⁻²))`,
  `g_n = e^{−3/2} h_n (1 − 13/(4n) + O(n⁻²))`,
  `c_n/g_n = 1 − 1/(2n) − 1/n² + O(n⁻³)`, from a uniform local expansion
  (prime probability `e^{−3}(1 − 5/n + O(n⁻²))`) and a canonical split-tree
  transfer; first corrections for automorphism-weighted and labeled counts and
  for rare automorphism groups; a refined inverse; and a transfer to every
  fixed order that is **conditional** on the corresponding prime expansion, so
  that the second coefficients `β − 277/32` and `β − 297/32` depend on an
  unknown prime constant `β`.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Leading asymptotics of unlabeled circle graphs* (author line "Report 150", 3 October 2026); the base | 150 | `Circle_Graph_Enumeration_Error_Bounds_and_Inverses_Source.zip` (622,124 bytes, 18 files; `Report150.tex`, 1,445 lines, 23 pp.) | none | `47fc7a069` | Part I, Sections 1–13 (13 = its Appendix A) |
| *First corrections for unlabeled circle graphs* (author line "Report 152", 3 October 2026) | 152 | `Circle_Graph_First_Corrections_and_Refined_Inverses_Source.zip` (630,050 bytes, 18 files; `Report152.tex`, 1,200 lines, 19 pp.) | none | `47fc7a069` | Part II, Sections 14–24, plus the write's Section 25 |

Both archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `47fc7a069` (batch 106, cluster 106-GRAPHS) removed them from
`docs/incoming/`. The write is "Write batch 106 (a156808-circle-graphs): new
report, unlabeled circle graphs, leading term and first corrections".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. Neither manuscript names an author, a tool or an addressee,
says it is AI-assisted, or carries "prepared for private review" wording; each
sets an empty PDF author field. Every result, proof, remark, question and
limitation of the two manuscripts is printed.

## Why the Parts are in this order

Report 150 is the base (its `Report150.tex` was staged as `article.tex`) and
comes first: it sets up the model and proves the leading equivalent. Report
152 is a sequel, not a new edition: "The earlier Report 150 established the
leading equivalent and relative O(1/n) bounds; this report identifies the
individual first coefficients." Its archive carries no copy of Report 150 (no
embedded copies in either archive). It re-proves Report 150's symmetry bound
and coarse bound so that its own proof is independent; these restatements are
printed in full with pointer notes (the manuscripts share about 1.5 % / 1.8 %
of their word 8-grams). Dependency order is also the order of writing.

## Files

The directory holds 31 files: 5 at the root, 14 in `code/`, 12 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 150, prefix `150-leading-`** (14 files): the companion README; `code/`:
the exact companion (`circle_companion.py`: enumerations, fibres, constructions,
algebra, evidence generator), its validator, its safe-I/O module and unit
tests, and the release scripts (deterministic PDF and ZIP builders, output
primitives, release tests); `data/`: the source-provenance record, the
deterministic evidence, and the companion's three source snapshots
(third-party data, see "Rights").

```
150-leading-companion-README.md
code/150-leading-build_pdf.py
code/150-leading-companion-circle_companion.py
code/150-leading-companion-safe_io.py
code/150-leading-companion-test_companion.py
code/150-leading-companion-verify.py
code/150-leading-make_zip.py
code/150-leading-release_tools.py
code/150-leading-test_release.py
data/150-leading-SOURCE_PROVENANCE.json
data/150-leading-companion-evidence.json
data/150-leading-companion-sources-danielsen_parker_table3.txt
data/150-leading-companion-sources-oeis_snapshot.json
data/150-leading-companion-sources-provenance.json
```

**Report 152, prefix `152-corr-`** (14 files): the companion README; `code/`:
the exact companion verifier (local atoms and clusters, the three-chord cases,
rooted graph classes, transfer and inverse algebra, automorphism histograms),
its test suite, and the release scripts; `data/`: the source-provenance record,
the companion's expected claims and provenance, and its four recorded results
(the two `check-release` files are byte-identical by design: normal and `-O`
runs).

```
152-corr-companion-README.md
code/152-corr-build_pdf.py
code/152-corr-companion-test_companion.py
code/152-corr-companion-verify.py
code/152-corr-make_zip.py
code/152-corr-release_tools.py
code/152-corr-test_release.py
data/152-corr-SOURCE_PROVENANCE.json
data/152-corr-companion-claims.json
data/152-corr-companion-provenance.json
data/152-corr-companion-results-check-release-normal.json
data/152-corr-companion-results-check-release-optimized.json
data/152-corr-companion-results-tests-release-normal.json
data/152-corr-companion-results-tests-release-optimized.json
```

The release scripts of the two reports are one tool family and differ only in
their report-number strings; each is shipped with its report.

**Not shipped** (all retrievable from `60f54ea06`): the two PDFs;
`Report152.tex` (printed as Part II) and Report 152's delivered README (Report
150's was staged and is replaced by this guide); the two `SHA256SUMS` manifests
(17/17 each, verified at placement; repository policy drops checksum
manifests).

## Labels and numbering

Label prefix **`cgr:`** (none at HEAD before this report): Part I uses
`cgr:ld:` (Report 150's 106 labels), Part II `cgr:fc:` (Report 152's 68). The
manuscripts share bare names (`thm:main`, `sec:inputs`, `sec:inverse`,
`sec:checks`, `eq:prime-prob`); under the Part prefixes they are distinct. The
write added the two Part labels; `cgr:ld:sec:result`, `cgr:ld:sub:poisson`,
`cgr:ld:sub:inspected`, `cgr:ld:sub:aut`, `cgr:ld:sub:companion`,
`cgr:ld:app:dependency`, `cgr:ld:rem:symmetry-credit`; `cgr:fc:sub:symmetry`,
`cgr:fc:sub:priority`, `cgr:fc:sub:rooted`, `cgr:fc:sub:conditional`,
`cgr:fc:sub:second`, `cgr:fc:sub:groups`; the front matter's `cgr:sec:guide`,
`cgr:sec:status`, `cgr:sec:oeis`, `cgr:sec:notation`, `cgr:sec:provenance`,
`cgr:sec:trust`, `cgr:sec:neighbours`; and Section 25's `cgr:sec:further` with
its seven items `cgr:q:beta`, `cgr:q:allorders`, `cgr:q:effective`,
`cgr:q:sources`, `cgr:q:labeled`, `cgr:q:moments`, `cgr:q:data`. 204 labels in
all, all distinct.

| Part | Manuscript | Section here | Statement and equation `k.j` |
|---|---|---|---|
| I | Report 150 | `k` (1–12, unchanged); its Appendix A is 13 | `k.j` (unchanged); Remark 3.3 added |
| II | Report 152 | `k + 13` (14–24); 25 added | `(k+13).j` |

For example Report 152's Theorems 1.1, 1.2, 3.1, 6.1, 10.1 are Theorems 14.1,
14.2, 16.1, 19.1, 23.1 and its Lemma 5.1 is Lemma 18.1. A comparison of the
build's `.aux` with separate builds of the two delivered `.tex` files confirmed
all 174 delivered labels under these offsets and prefixes. The delivered
READMEs, provenance records, code and data use the manuscripts' own numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the two
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a short reading-conventions table. The main
collisions: **`c_r`** (in Part II, Sections 16–17, a coefficient of the
partition polynomial `H_M(u)`, not A156808), **`B`** (Part I's
`B = (3/2)(1 + log 2)` in the Stirling expansion; Part II's inverse constant
`B = (3 + log 2)/2`, which is Part I's `B − log 2`; Part II's conflict sum and
branch polynomial `B_d(z)`), **`q`** (Part I's `q_s = m_s m_{n−s}/m_n`; Part
II's `q_r`, which is Part I's `ρ_r`), **`A`/`D`** (`log(2u)` is Part I's `A`
and Part II's `D`), **`α`, `β`, `η`** (Part I's pattern indices and bracket
errors; Part II's prime coefficients), **`K`**, **`L`**, **`F`**, **`H`**,
**`C`** (Part II's `C_n^lab`, `G_n^lab` are Part I's `c_n^lab`, `g_n^lab`),
**`S`**, **`x, y, z`**, **`d, k, r, s`**, **`P`**, **`W`**, **`ρ`**.

## What the report claims

**Part I (Report 150).**
- Theorem 1.1: `c_n ~ g_n ~ e^{−3/2} h_n ~ e^{−3/2}(2n/e)^n/(2√2 n)`;
  `g_n − c_n = g_{n−1} + O(m_n/n³)`; `c_n/g_n = 1 − 1/(2n) + o(1/n)`.
- Section 2: the published inputs (Bassino–Bouvel–Féray–Gerin–Pierrot's
  Definition 5.3, Proposition 5.5, Lemmas 5.7–5.10, Proposition 5.12;
  Klavík–Zeman) and the limit `P(indecomposable) = e^{−3} + o(1)` (2.6), which
  "follows directly from the preceding lemmas. It is not a new Poisson
  theorem" — a sharpening of the source's stated bound `e^{−4}`
  (Proposition 5.11), by the source's own lemmas, **not claimed as a new
  theorem and not a correction**.
- Lemma 3.1 (`S_n ≤ 4n(2en)^{n/2} e^{√n}`), the fibre identity (3.4) and the coarse bound (3.5), Lemma 3.2
  (bounded deletions), Lemmas 4.1–4.2 (long leaves, shared parents), Lemma 5.1
  (leaf moves, fibre `≥ 4n·2^k`), Lemma 6.1 (canonical recovery).
- Theorem 8.1, Proposition 8.2, (8.6), (8.8): the typical-core laws, the
  automorphism group `(C_2)^{t+f}`, the asymmetric/leafless/split-prime
  probabilities, the labeled equivalent.
- Theorem 9.1 with Lemma 9.2: relative `O(1/n)` errors, the TV bounds, the
  explicit local bound `min(1, 200/n)` for `n ≥ 6`.
- Propositions 10.1–10.2 and (10.14): the smooth inverse
  `φ(x) = u + 1 + (3 + log 2)/(2 log(2u)) + O(1/(u log u))`,
  `u = L/W₀(2L/e)`, and ceiling brackets.
- Section 11: the counts table, and `c_13 = 21,593,488,017` derived by Euler
  inversion (reproduced at intake and at the write; not in the OEIS entry).

**Part II (Report 152).**
- Theorem 14.1: the first corrections of `p_n^a`, `c_n`, `g_n` (and `−91/24`,
  `−79/24` in the Stirling normalization `Q_n`); Theorem 14.2: the second
  connectivity term, unconditionally, and the conditional transfer.
- Theorem 16.1: the uniform local expansion with `F(x,y,z)` and
  `P(X = Y = Z = 0) = e^{−3}(1 − 10/M + O(M⁻²))`, by a hard-core polymer
  expansion with an elementary complex remainder; (18.1), the global
  matching-probability remainder.
- Lemma 18.1 (three-chord interval lemma) and (18.3):
  `P(indecomposable) = e^{−3}(1 − 5/n + O(n⁻²))`.
- Theorem 19.1: the finite canonical split-tree transfer; rooted counts
  `b_0..b_3 = 1, 3, 11, 58`.
- Sections 20–21: the first coefficients, the component transfer,
  `c_n/g_n = 1 − 1/(2n) − 1/n² + O(n⁻³)`, the conditional transfer to every
  fixed order and the conditional second coefficients.
- Section 22: weighted counts `c_n(t)`, `g_n(t)`; labeled counts with
  `−47/(12n)` and `−41/(12n)`; `P(Aut = 1) = e^{−1}(1 − 1/(2n))`;
  `E|Aut|^{−t}`; `P(Aut nonabelian) = 1/(2n) + O(n⁻²)`;
  `P(Aut ≅ S_3 × C_2^k) = e^{−1}/(2n k!) + O(n⁻²)`.
- Theorem 23.1: refined inverse centres `s_a`, `K_c = 103/24`, `K_g = 91/24`,
  width `O(1/(u² log u))`.

**Added by the write** (all marked `[write]`, dated 5 October 2026): the front
matter (including the OEIS entries as read on 5 October 2026 and the inverses
as instances of the transseries volume's factorial core); dated notes marking
what Part II supersedes or answers and what was checked; Section 25 (further
questions); and **Remark 3.3** with its proof: the method of Lemma 3.1 is
that of Bassino et al.'s Proposition 5.14 (proportion `o(n^{−n/3})`), which
neither manuscript cites; that proposition's proof says that a reflection and a
rotation of order two give the same count, which is exact for reflections
through gaps, while a reflection through two endpoints fixes `t_{n−1} < t_n`
matchings (`t_k = k![z^k]exp(z + z²)`, `t_{k+1} = t_k + 2k t_{k−1}`), so the
source's bound is unaffected.

**The inverses.** Both Parts write the threshold through `u`, the solution of
`u(log(2u) − 1) = L`: the factorial core `p0:prop:factorial-core` (`κ = 1`,
`d = log 2 − 1`) of the transseries volume
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`,
which after taking logarithms is its Lambert core `p0:thm:lambert-core` with
`a = b = 1` in the variable `log(2u) − 1`. The corrections to `u` are derived in
the Parts from the explicit Gamma model `H(t)`. The two-ceiling brackets follow
the separation pattern of `p0:thm:staircase` (2) but are **not instances** of
it: the Parts compare `a_n` with the model `H`, which does not interpolate
`a_n`, and prove the brackets directly at the integers. Neither manuscript
cites the volume.

## What the report does not claim

Every limitation is printed in place. In short: no value or conjecture for the
prime second coefficient `β`, so the second graph coefficients are
conditional; no unconditional expansion beyond the first correction, no
convergence, no uniformity in the order, no all-orders inverse; no effective
constants or onsets (only the local bound `200/n` is explicit, and it concerns
local matching patterns only), hence no certified threshold and no
unconditional rounding of an inverse centre; no unbounded automorphism moments;
no separate literature or OEIS audit of the labeled consequences; finite
checks prove no asymptotic statement; checksum manifests establish consistency,
not authenticity. **Priority** is bounded as both manuscripts bound it: the
results were not located in the sources checked (arXiv:2402.06394v1 and a 2024
author copy of Bassino et al., Klavík–Zeman, Gioan–Paul, Danielsen–Parker, the
OEIS entries); the **2026 journal version of Bassino et al.**
(*Electronic Journal of Probability* 31, article 110,
doi:10.1214/26-EJP1570) was **not read at intake or at the write** (its
publisher page refused automated access), Gabor–Supowit–Hsu was read only
through Bassino et al.'s Proposition 5.12, and Arratia–Bollobás–Coppersmith–
Sorkin only at abstract level. No exhaustive priority claim is made.
`152-corr-SOURCE_PROVENANCE.json`'s "independent review" entries are
metadata, as the file itself says, not an independent proof certificate.

## Further questions, and the standing rule

Part I's Section 12 is the manuscript's own; Part II states its limits in
Section 24; Section 25 collects all of them (Vladimir's standing rule of
4 October 2026), with sources, sketches and what is missing:

1. **the prime second coefficient `β`** (Part II) — missing: the next order of
   the polymer, hard-core and matching-probability expansions, and the
   zero-defect matchings with a `k`-decomposition, `4 ≤ k ≤ n − 4`, which are
   `O(n⁻²)` and must be counted at second order;
2. an **unconditional expansion to every fixed order** (Part I item 2, Part II);
3. **effective constants, onsets and certified thresholds** (both);
4. **source reconciliation and priority**: the 2026 journal text,
   Gabor–Supowit–Hsu, Arratia et al. (both);
5. an **audit of the labeled consequences** (both);
6. **unbounded automorphism observables** (both) — the limiting law has
   `E 2^{tP} = exp(2^t − 1)`; convergence of `E|Aut(G)|^t` needs uniform
   integrability;
7. **exact counts beyond order 13** (write): at `n = 13` the counts are still
   10.5 % (`c_13`) and 11.3 % (`g_13`) below the first-corrected
   approximations; an exact split-tree recurrence from prime counts is not
   stated by either manuscript.

**Answered inside the merge**, with a dated note: Part I's item 1 (the first
correction coefficient) by Part II's Theorems 14.1–14.2; Part I's item 2 is
re-scoped by Part II's conditional transfer. **Nothing in the two manuscripts
was found to be wrong**, and no claim was refuted.

**Uncertified evidence.** At intake a Monte Carlo simulation (200,000 uniform
matchings per size, seed 20261005; intake record, not shipped) estimated the
first-order constant of Theorem 16.1: `M(P̂/e^{−3} − 1) = −9.88 ± 0.93`
(`M = 100`), `−9.83 ± 1.9` (`M = 200`), `−4.4 ± 3.9` (`M = 400`), one binomial
standard error. The first two agree with the proved `−10` and exclude `0` by
about 10 and 5 standard errors; the `M = 400` value is within 1.5 standard
errors of both `−10` and `0`. It concerns a proved statement and says nothing
about `β`.

## Relation to neighbouring reports

- No other report of the collection treats circle graphs or A156808/A156809
  (searched 5 October 2026).
- **Siblings sharing a pipeline**, placed in the same commit `47fc7a069` and
  written separately in batch 106:
  [`a123448-permutation-graphs`](../a123448-permutation-graphs/) (bundle Report
  153, unlabeled permutation graphs A123448, labels `prg:`) and
  [`a005975-interval-graphs`](../a005975-interval-graphs/) (bundle Report 133,
  unlabeled interval graphs A005975/A005976, labels `ivg:`). All three count a
  representation model (matchings here; permutations; interval orders), show
  that almost every graph has a recoverable prime core whose representations
  form one full orbit of the representation symmetry group (dihedral of order
  `4n` here; the Klein four-group; a duality of order 2), divide by that
  group's order, make the symmetric cores negligible, and invert with
  ceiling-safe Lambert-W brackets. They share no statement and cite each other
  nowhere; their decomposition theories (split trees here, modular
  decomposition there), external inputs and normalizations (`(2n−1)!!/(4n)`,
  `n!/4`, `F_n/2`) differ, and one report would give several symbols two to
  four meanings, so they were kept apart (placement commit message).
  Bassino et al. also treat permutation graphs.
- [`a007716-bipartite-multigraphs`](../a007716-bipartite-multigraphs/) and
  [`a307316-leafless-multigraphs`](../a307316-leafless-multigraphs/) apply the
  same rare-symmetry philosophy to multigraphs; no shared statement.
- The transseries volume `Transseries_And_Inversion` supplies the factorial
  core of which the leading inverses are instances; the brackets are not
  instances of its staircase theorem (above).

## Relation to formal projects

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file in the repository treats circle
graphs (searched 5 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 28 staged delivered files were
  checked against a fresh extraction from `60f54ea06` at the write: 0
  differences; `article.tex` and this README then replaced the two staged base
  files). Only names changed (tables at the end). The delivered code and
  markdown use delivery paths (`companion/…`, `verify.py`, `evidence.json`,
  `sources/…`, `results/…`, `SHA256SUMS`, `Report150.tex`, `Report152.pdf`,
  `/tmp/…` example outputs), which are shipped under other names or not at all.
- **The renamed scripts no longer import each other.** Report 150's
  `circle_companion.py`, `verify.py` and `test_companion.py` import
  `safe_io`, `circle_companion` and `verify` by module name; Report 152's `test_companion.py` imports `verify`;
  each `build_pdf.py`, `make_zip.py` and `test_release.py` imports
  `release_tools` (and `make_zip`). The release scripts read `SHA256SUMS` and
  `Report15N.tex`, which are not shipped. **None of the scripts runs in this
  directory;** rerun from a fresh extraction (below).
- **POSIX only.** Both companions open files through descriptor-pinned I/O
  with `os.O_DIRECTORY` and `os.O_NOFOLLOW`; on Windows they stop with
  `AttributeError: module 'os' has no attribute 'O_DIRECTORY'` (checked at
  the write). The PDF builders also need Linux `/proc/self/fd` and Debian TeX
  trees.
- `data/150-leading-SOURCE_PROVENANCE.json` and the two companion READMEs
  record the inspected source versions and hashes; the hashes of
  arXiv:2402.06394v1 and of the Klavík–Zeman STACS paper match the files the
  write downloaded on 5 October 2026.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit (each archive unpacks to its own
root):

```
git show 60f54ea06:docs/incoming/Circle_Graph_Enumeration_Error_Bounds_and_Inverses_Source.zip > r150.zip
git show 60f54ea06:docs/incoming/Circle_Graph_First_Corrections_and_Refined_Inverses_Source.zip > r152.zip
mkdir x150 x152 && unzip -q r150.zip -d x150 && unzip -q r152.zip -d x152
```

On Linux or macOS (Python 3.10 or later, standard library only), follow the
delivered READMEs from each root, for example:

```
cd x150 && sha256sum -c SHA256SUMS && mkdir validation
python3 companion/circle_companion.py --output validation/evidence.json
python3 companion/verify.py validation/evidence.json
cmp companion/evidence.json validation/evidence.json
python3 -m unittest discover -s companion -v
cd ../x152 && sha256sum -c SHA256SUMS
python3 -B companion/verify.py
python3 -B -O companion/verify.py
python3 -B companion/test_companion.py
```

Report 152's `--output` accepts only a new `.json` file inside
`companion/results/` of the extraction; Report 150's refuses existing files.
`build_pdf.py`, `make_zip.py` and `test_release.py` need the recorded TeX Live
pdfTeX 1.40.26 toolchain for byte-identical PDFs and were not run.

**Windows.** The safe-I/O layer cannot run. The mathematics can be replayed by
reading the inputs plainly, as the intake did (its shims are not shipped):

```
cd x150/companion
python -B -c "import json,pathlib,safe_io; safe_io.regular_bytes=lambda p: pathlib.Path(p).read_bytes(); import circle_companion as c; c.regular_bytes=safe_io.regular_bytes; e=c.build_evidence(); b=(json.dumps(e,sort_keys=True,indent=2)+'\n').encode(); print(b==pathlib.Path('evidence.json').read_bytes())"
cd ../../x152/companion
python -B -c "import json,pathlib,verify; d=verify.run(json.loads(pathlib.Path('claims.json').read_text('utf-8'))); b=(json.dumps(d,indent=2,sort_keys=True)+'\n').encode(); print(b==pathlib.Path('results/check-release-normal.json').read_bytes())"
```

Each prints `True` when the regenerated evidence or result is byte-identical
to the recorded one.

Results: at placement (5 October 2026, Python 3.14.4, Windows, on copies,
recorded in the batch-106 dossier) both `SHA256SUMS` manifests verified
(17/17 each); Report 150's evidence regenerated byte-identical (46,491 bytes)
and `verify_document` passed, normally and under `-O` (about 6 s each); Report
152's result regenerated byte-identical to both `check-release` files (38,228
bytes, 1.5 s); the unit and release tests were not run (POSIX file calls). At
the write (5 October 2026, fresh extractions, Windows) the same two replays
gave byte-identical output in 3.5 s and 1.9 s, and both delivered verifiers
stopped at the `O_DIRECTORY` call as described. The two delivered `.tex`
files compile with MiKTeX pdfLaTeX to 23 and 19 pages with no warnings.

## Rights

Repository contents are MIT-0, with these third-party data, staged as
delivered with attribution:

- `data/150-leading-companion-sources-oeis_snapshot.json` reproduces the OEIS
  records of A156808 and A156809 (revisions 9 and 16), including OEIS's public
  author line for both entries (Lars Eirik Danielsen) and the extension credit
  to Tom Johnston for A156809(13). OEIS data are available under CC BY-SA 4.0
  ([OEIS license](https://oeis.org/LICENSE)); the OEIS Foundation and the
  named contributors are credited.
- `data/150-leading-companion-sources-danielsen_parker_table3.txt` is a text
  extraction of Table 3 of L. E. Danielsen and M. G. Parker, *Interlace
  Polynomials: Enumeration, Unimodality, and Connections to Codes*,
  arXiv:0804.2576v2 (p. 8): counts of circle graphs and of their
  local-complementation orbits through order 12, credited to its authors
  (checked against the arXiv PDF at the write).

The manuscripts credit Bassino–Bouvel–Féray–Gerin–Pierrot, Klavík–Zeman,
Gioan–Paul (Cunningham's split decomposition), Gabor–Supowit–Hsu, Danielsen–
Parker and the OEIS as they cite them; the write adds the credit for
Bassino et al.'s Proposition 5.14 (Remark 3.3). Nothing was submitted to the
OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The build
(53 pages): no errors, no warnings, no undefined or multiply defined
references or citations, no duplicate destinations, no overfull or underfull
boxes.

## Delivered path → shipped path

Report 150 (`150-leading-`; the archive unpacks to its root):

| Delivered | Shipped |
|---|---|
| `Report150.tex` | `article.tex` (Part I) |
| `README.md` | replaced by this guide |
| `companion/README.md` | `150-leading-companion-README.md` |
| `SOURCE_PROVENANCE.json` | `data/150-leading-SOURCE_PROVENANCE.json` |
| `companion/evidence.json` | `data/150-leading-companion-evidence.json` |
| `companion/sources/<name>` (3 files) | `data/150-leading-companion-sources-<name>` |
| `companion/circle_companion.py`, `safe_io.py`, `test_companion.py`, `verify.py` | `code/150-leading-companion-<name>` |
| `build_pdf.py`, `make_zip.py`, `release_tools.py`, `test_release.py` | `code/150-leading-<name>` |
| `Report150.pdf`, `SHA256SUMS` | not shipped |

Report 152 (`152-corr-`; the archive unpacks to its root):

| Delivered | Shipped |
|---|---|
| `Report152.tex` | not shipped; printed as Part II of `article.tex` |
| `README.md` | not shipped |
| `companion/README.md` | `152-corr-companion-README.md` |
| `SOURCE_PROVENANCE.json` | `data/152-corr-SOURCE_PROVENANCE.json` |
| `companion/claims.json`, `provenance.json` | `data/152-corr-companion-<name>` |
| `companion/results/<name>` (4 files) | `data/152-corr-companion-results-<name>` |
| `companion/test_companion.py`, `verify.py` | `code/152-corr-companion-<name>` |
| `build_pdf.py`, `make_zip.py`, `release_tools.py`, `test_release.py` | `code/152-corr-<name>` |
| `Report152.pdf`, `SHA256SUMS` | not shipped |

## Provenance

Two manuscripts (bundle Reports 150, 152) → one report; base 150, printed as
Part I. Arrival `60f54ea06`, placement `47fc7a069`, write batch 106
(5 October 2026). No manuscript pins a ProveIt commit. Merge choices (base and
dependency order agree, Report 152's restatements printed with pointers, Report
150's appendix as Section 13, the merged bibliography with both annotations of
shared entries) are listed in the article's front matter, "Provenance and
merge decisions".
