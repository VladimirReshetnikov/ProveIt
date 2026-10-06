# Maximal Families of Disjoint Strict Partitions (OEIS A068598)

**`log a(n) = Θ(n log n)`, with `1/5 ≤ liminf ≤ limsup ≤ 1/4` for
`log a(n)/(n log n)`; an explicit elementary upper bound; first-passage
inverses without monotonicity; and two corrections to the OEIS entry: the
graph comment counts *maximal* cliques, and the posted fits `a·exp(b n^c)`,
`c > 1`, are not asymptotic**

A research article ("Report 163" of a session bundle), built from one
manuscript dated 3 October 2026. Its author line reads "Report 163" and its
PDF author field is empty: it names no person, tool or addressee. The package
carries no "prepared for private review" line, no e-mail address and no
personal data. The delivered README used generic sandbox example paths for
its build commands; they are not reproduced here.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 163 (batch 107) | `Maximal_Disjoint_Partition_Families_Growth_and_Inverse_Bounds_Source.zip` (15 files at the archive root, no wrapper directory, 444,037 bytes, SHA-256 `f5a5ce94…050163e3`), arrival commit `60f54ea06`; main file `Report163.tex` (565 lines, 9 pp.) | none: the package names no ProveIt commit and cites nothing in the repository | `3988bf5c4` (batch 107) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository formalizes maximal families of disjoint partitions or queens
counts. No proof uses a computation.

## Trust boundaries

- **What is proved by hand, self-contained.** The upper bound
  `a(n) ≤ 3^{n−1} n^{⌊(n−2)/4⌋}` (`n ≥ 2`), by an injective
  anchor/free-label code and the distinct-parts mass inequality (credited to
  Joel Spencer through Nathanson, and proved where it is used); the
  elementary lower bound `a(n) ≥ 2^k k!`, `k = ⌊(n−1)/7⌋` (`n ≥ 8`), hence
  `liminf ≥ 1/7`; the rejection of every fit `A exp(B n^c)`, `c > 1`; the
  lower inverse constant 4; and the finite Lambert brackets for every real
  `y > 1`.
- **What rests on an external theorem.** The lower constant `1/5`, the
  one-sided linear term `−((log 5 + 3)/5) n` and the upper inverse constant
  5 use the theorem of Luria and Simkin (SODA 2022, arXiv:2105.11431v2,
  Theorem 1.1), `Q(k) ≥ ((1 − o(1)) k/e³)^k` for ordinary labelled queens
  configurations, through an injection of queens permutations into maximal
  families. That proof is cited, not reproduced, and its `o(1)` gives no
  explicit onset.
- **The companion** enumerates `a(n)` exactly for `n ≤ 24`, checks the
  encoding on all 179,455 matchings without the forced singleton through
  `n = 24`, the queens injection through `k = 8`, the greedy construction on
  24 examples and the floor identities through `n = 100000`, and gives exact
  first-passage scans and proved integer brackets. It proves nothing
  asymptotic.

## What it proves

`a(n)` counts inclusion-maximal unordered families of pairwise disjoint
strict partitions of `n` (maximal matchings of the hypergraph `H_n` whose
edges are the strict partitions), `a(0) = 1`. Statement numbers are the
delivered ones.

- **Theorem 1.1 (`mdp:thm:main`)**: `a(n) ≤ 3^{n−1} n^{⌊(n−2)/4⌋}` for
  `n ≥ 2`; `a(n) ≥ Q(⌊(n−1)/5⌋)`; hence
  `1/5 ≤ liminf log a(n)/(n log n) ≤ limsup ≤ 1/4`, and the one-sided
  `log a(n) ≥ (n/5) log n − ((log 5 + 3)/5) n + o(n)`.
- **Lemma 2.1 (`mdp:lem:code`)**: the code `(A, F, f)` (anchors, free
  labels, anchor map) determines the matching.
- **Lemma 3.2 (`mdp:lem:extension`)**: maximal extensions of the queens
  triple bases are distinct for distinct queens permutations.
- **Proposition 4.1 (`mdp:prop:greedy`)**: `a(n) ≥ Π_{i≤k}(m − 2(i−1))`
  when `m ≥ 2k`, `3k + 2m < n`; in particular `a(n) ≥ 2^k k!`.
- **Corollary 5.1 (`mdp:cor:fits`)**: `a(n)/(A exp(B n^c)) → 0` for all
  `A, B > 0`, `c > 1`.
- **Corollary 6.1 (`mdp:cor:inverse`)**: for `N(y) = min{n ≥ 0 : a(n) ≥ y}`,
  `4 ≤ liminf N(y) log log y/log y ≤ limsup ≤ 5`, without monotonicity.
- **Proposition 6.2 (`mdp:prop:finiteinverse`)**: for every real `y > 1`,
  `⌈4(L + log 3)/W(324(L + log 3))⌉ ≤ N(y) ≤ 7⌈L/W(2L/e)⌉ + 1`, `L = log y`.

Added by the write (6 October 2026), with proofs, marked `[write]`:

- **Remark 1.2 (`mdp:rem:cliques`)**: the graph comment, quoted and
  corrected (next section).
- **Remark 3.3 (`mdp:rem:simkin`)**: Simkin's later theorem
  (Adv. Math. 427 (2023) 109127, arXiv:2107.13460v3; read at abstract level),
  `Q(k) = ((1 ± o(1)) k e^{−α})^k` with `α = 1.942 ± 0.003`, improves the
  linear term of the lower bound to `−((log 5 + α)/5) n`, a coefficient in
  `[0.7099, 0.7111]` instead of `0.9219…`; the constant `1/5` is unchanged.
  The source does not cite this theorem.
- **Remark 5.2 (`mdp:rem:fits`)**: the two fits, quoted and refuted as
  asymptotics (next-but-one section).
- **Remark 6.3 (`mdp:rem:transseries`)**: Section 6 against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`).
  The roots `r` and `s` of Proposition 6.2 are **instances**, verbatim, of
  `p0:prop:factorial-core`, with `(κ, d, L) := (1/4, log 3, L + log 3)` and
  `(1, log 2 − 1, L)`. Proposition 6.2 and Corollary 6.1 are **not instances,
  only analogues** of `p0:thm:staircase`: `p0:def:three-inverses` presupposes
  a strictly increasing sequence, and `a(n)` is not known to be monotone; the
  brackets come from two envelopes, not from an inverse of an interpolation.
- **Proposition 9.1 (`mdp:prop:typical`)**: with `v` the number of labels
  used by the non-singleton edges and `Δ` the excess of their sum over
  `v(v+1)/2`, the free-label count is exactly
  `q = (n−1)²/(4n) − (v − (n−1)/2)²/n − 2Δ/n`; families with
  `(v − (n−1)/2)² + 2Δ ≥ t n²` number at most `3^{n−1} n^{(1/4−t)n}`, a
  vanishing proportion for every `t > 1/20`; and if `limsup = 1/4` along a
  sequence, almost all families there use about `n/2` labels in about `n/8`
  edges of average size 4. This locates the families that any proof of the
  constant `1/4` would have to count; it does not show they are numerous.
- **Section 9 (`mdp:sec:further`)**: the open questions.
- Section 1.1 (`mdp:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions), notes at the ends of Sections 7 and 8,
  and two bibliography entries (Simkin; the Wolfram `FindClique`
  documentation).

## Correction 1: the graph comment counts maximal cliques

The live entry A068598 (revision #50, 17 February 2026, read 6 October 2026;
the revision the source inspected), "Number of maximal sets of partitions of
n with property that all parts in all partitions in the set are distinct.",
has the comment

    Also number of cliques in following graph: each strict partition of n represents a vertex, the relation "having no common integer" defines the edges connecting these. - _Wouter Meeussen_, May 27 2002

(quoted verbatim). In this graph `G_n` a vertex set spans a complete
subgraph exactly when its partitions are pairwise disjoint, so `a(n)` is the
number of **maximal** complete subgraphs. **Example, `n = 8`, in full.**
The six vertices are `{8}, {1,7}, {2,6}, {3,5}, {1,2,5}, {1,3,4}`. `{8}` is
adjacent to all others; among the rest the edges are `{1,7}{2,6}`,
`{1,7}{3,5}`, `{2,6}{3,5}`, `{2,6}{1,3,4}` (every other pair shares a part).
Without `{8}` there are 5 + 4 + 1 = 10 nonempty complete subgraphs (vertices,
edges, the triangle `{1,7},{2,6},{3,5}`); with `{8}` adjacent to all, `G_8`
has `2·10 + 1 = 21` nonempty complete subgraphs, but only three maximal ones,
`{{8},{1,7},{2,6},{3,5}}`, `{{8},{1,2,5}}`, `{{8},{1,3,4},{2,6}}`, and
`a(8) = 3`. So with six vertices `G_8` already has at least six cliques in the
usual sense. The first discrepancy is at `n = 3` (3 against `a(3) = 1`); for
`n = 1, …, 12` the nonempty complete subgraphs number
`1, 1, 3, 3, 7, 9, 17, 21, 43, 57, 109, 157` against
`a(n) = 1, 1, 1, 1, 1, 2, 2, 3, 4, 6, 8, 13`.

**What is right.** Under the older convention that a clique is by definition
maximal, the comment is correct as written. That is the Wolfram Language's
convention ("A clique is a maximal set of vertices where the corresponding
subgraph is a complete graph", `FindClique` documentation, read 6 October
2026), and the entry's three programs all count maximal families (the first
Mathematica program tests maximality explicitly; Beregovsky's
`FindClique[…, Infinity, All]`; Chai Wah Wu's `networkx.find_cliques`). The
unambiguous wording is "maximal cliques", as the source says. Recorded only:
**nothing was submitted to the OEIS.**

## Correction 2: the posted fits are not asymptotic

The same entry has, verbatim,

    Conjecture: a(n) asymptotically grows as a*exp(bx^c), where a≈0.57, b≈0.062, c≈1.54. - _Elijah Beregovsky_, Nov 12 2022
    Better parameter values for the above approximation are (a,b,c) = (0.26, 0.129, 1.36) (from correspondence with _Bill McEachen_). - _Elijah Beregovsky_, Feb 17 2026

(`x` is the index `n`). **Proof that neither is asymptotic** (Remark 5.2(a),
from the elementary upper bound alone): for `n ≥ 2`,
`log a(n) ≤ (n−1) log 3 + ⌊(n−2)/4⌋ log n ≤ n log 3 + (n/4) log n`, so

    log( a(n) / (A exp(B n^c)) ) ≤ −n^c ( B − n^{1−c} log 3 − (1/4) n^{1−c} log n ) − log A → −∞

for all `A, B > 0`, `c > 1`, since the bracket tends to `B`. Even
`log a(n) ~ B n^c` fails, because `log a(n) ≤ (1/4 + o(1)) n log n = o(n^c)`.
Exponents `c ≤ 1` fail the other way, by `a(n) ≥ 2^k k!`: no
`A exp(B n^c)` with `A, B, c > 0` is asymptotic to `a(n)`.

**Explicit ranges** (Remark 5.2(b)): `0.57 e^{0.062 n^{1.54}} > a(n)` for
every `n ≥ 1215`, and `0.26 e^{0.129 n^{1.36}} > a(n)` for every
`n ≥ 8579`, because each fit exceeds the proved upper bound there; the
proof is a convexity argument from `n₀ = 1219` (resp. `8587`) plus finitely
many direct evaluations (40-digit mpmath, smallest margin 2.16 resp. 0.93 in
the logarithm; not interval-certified).

**What is not said.** On the data range the fits are fair (at `n = 24, 45,
46` they give 0.487, 0.689, 0.728 times `a(n)` for 2022 and 0.940, 0.907,
0.905 for 2026); their finite-range quality and the fitted values are not
judged. What fails is the asymptotic reading, which the 2026 comment
inherits from the 2022 one: the growth is `exp(Θ(n log n))`. Recorded only:
**nothing was submitted to the OEIS.**

## What is not claimed

From the source, kept in the article (collected at the end of Section 1.1):

- No existence or value of `lim log a(n)/(n log n)`, no multiplicative
  equivalent, no all-orders expansion or transseries; the linear term
  belongs to a lower bound only.
- The constant `1/5` and the inverse constant 5 rest on an external theorem
  without explicit onset; no monotonicity of `a(n)` is assumed or asserted;
  no exact ceiling formula for `N(y)`; floating `W` near an integer
  certifies nothing.
- The fits are rejected only as asymptotic equivalents.
- The quadruple-decomposition direction is unproved.
- A bounded literature check (Filaseta's chapter read at abstract level
  only): "an independently verified proof candidate and application of known
  ingredients, rather than … a certified first proof".
- Finite checks prove nothing asymptotic; PDF byte identity is
  toolchain-specific.

The write adds: Remark 3.3 rests on Simkin's theorem as stated in its
abstract; the explicit ranges of Remark 5.2 use finitely many floating
evaluations of elementary numbers.

## Further questions

Section 9 of the article (`mdp:sec:further`) states every unproved claim as
an open question with its source, sketch and what is missing (Vladimir's
standing rule of 4 October 2026). **Nothing in the source was found to be
wrong**; the two corrections above concern OEIS text.

1. **The limiting coefficient** (`mdp:q:limit`): existence and value of the
   limit, a multiplicative equivalent, the linear term.
2. **Quadruple decompositions** (`mdp:q:quadruples`): with `D(k)` the number
   of decompositions of `[4k]` into `k` quadruples each summing to `8k + 2`,
   *proved at the write:* `D(k) ≥ k^{2k−o(k)}` would give
   `log a(n) ≥ (1/4 − o(1)) n log n` along `n = 8k + 2` (the decomposition is
   recovered from any maximal extension as the edges meeting `[4k]`). Open:
   the bound on `D(k)`; the known constructions give `k!`.
3. **Effective onsets and monotonicity** (`mdp:q:effective`): an explicit
   queens lower bound with onset; and (added by the write, not a claim of the
   source) whether `a(n)` is nondecreasing, strictly increasing for `n ≥ 7`,
   as the data are through `n = 46`.
4. **The literature boundary** (`mdp:q:literature`): Filaseta's 1996 chapter
   (abstract only).

## Checks made at intake

- At placement (batch-107 dossier, 5–6 October 2026; Windows, Python
  3.14.4): the 11 staged files other than `README.md` and `article.tex` are
  byte-identical to the archive, and so were the staged `Report163.tex` and
  README; `SHA256SUMS` 14/14. The dossier read the manuscript in full, found
  no error, rechecked the key steps by hand (forced singleton, free-label
  bound and floor identity, disjoint triple classes, injectivity, the greedy
  product, the linear coefficient, both Lambert roots) and verified both OEIS
  corrections. On copies the companion's `counts`, `verify` and `sources`
  outputs reproduced the frozen data, `threshold --value 1000 --max-n 24`
  gave 22 and `bounds --value 1e20` gave `[26, 127]`; 13 of 14 companion
  tests passed in normal and `-O` mode, and 10 of the 11 release tests
  errored (POSIX descriptor helpers).
- At the write (6 October 2026; same machine): the live entry is still
  revision #50, its 46 data terms equal `data/source_data.json`, and the
  linked b-file adds `a(46) = 4836923613`; an independent enumeration of the
  complete and maximal complete subgraphs of `G_n` for `n ≤ 20` (maximal
  counts equal the OEIS data); the fit ranges of Remark 5.2 (mpmath); the
  companion rerun from a fresh extraction of the archive (route A below,
  Windows): the three outputs equal the frozen files after converting line
  endings, 13 of 14 tests pass (124 s), and the one failure compares raw
  output bytes and sees CRLF; route B's frozen-data tests pass.
- Sources read by the write: the OEIS entry and b-file; the abstracts of
  Luria–Simkin (arXiv:2105.11431v2) and Simkin (arXiv:2107.13460v3; journal
  data from Crossref); the Wolfram `FindClique` documentation; the
  transseries volume (`p0:def:core`, `p0:thm:lambert-core`,
  `p0:prop:factorial-core`, `p0:def:three-inverses`, `p0:thm:staircase`).
  Not read by the write: the full texts of Nathanson, Luria–Simkin, Simkin
  and Filaseta (what the source read is fingerprinted in
  `data/SOURCE_PROVENANCE.json`).

## Relation to the repository

**Formal status.** No statement of this report is formalized, and no Lean or
Rocq development in the repository concerns these families or queens counts.
Placement in the collection confers no formal status.

**The transseries volume.** The two Lambert roots are instances of
`p0:prop:factorial-core`; the first-passage brackets are analogues of
`p0:thm:staircase` only (Remark 6.3). No novelty is claimed for the
inversions.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a005121-strict-partition-chains` (chains of set partitions, a different
object despite the word "strict"); `a271619-strict-twice-partitions`
(strict partitions of partitions); `a201513-sparse-chess-placements`
(nonattacking kings, knights, wazirs and ferses, not queens). None treats
A068598, maximal families of disjoint partitions or queens counts, and none
needs a reciprocal note.

**Stale claims.** Before batch 107 no file of the repository named A068598
or these families; the source made no claim about the repository.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `a(n)` against the comment's coefficient
`a`; the fit parameters `A, B, c` against the anchor set `A`, an edge `B`,
the ranges `A = [1,k]`, `B = [k+1,k+m]`, the parts `c_i` of Proposition 4.1
and the triples `B_i(π)`; `H_n`, `𝒫_n` and the write's `G_n` (with "clique"
in the usual sense); `𝓜, m, v, q, F, f` (and `m` of Proposition 4.1, `v` of
`p0:prop:factorial-core`); `Q(k)`, `k` (two different `k`); `π, σ, α`;
`N(y)` against the staircase `N_*`; `L, W, h, r, s` (the target of
`p0:prop:factorial-core` is `L + log 3` for `r`); the write's `Δ`. No
symbol was renamed.

## Labels

Every label carries the prefix `mdp:` (none existed in the repository). The
manuscript's 28 labels (`eq:` 18, `thm:` 2, `lem:` 2, `prop:` 2, `cor:` 2,
`sec:` 2) were prefixed before anything cited them, and the
20 references to them updated. The write added 11: `mdp:rem:cliques`,
`mdp:sec:provenance`, `mdp:rem:simkin`, `mdp:rem:fits`,
`mdp:rem:transseries`, `mdp:sec:further`, `mdp:prop:typical`, and the
questions `mdp:q:limit`, `mdp:q:quadruples`, `mdp:q:effective`,
`mdp:q:literature`. The report has 39 labels; builds of the delivered text
and of this one give all 28 delivered labels the same numbers (aux files
compared). The added remarks are the last statements of their sections, the
added section follows the last delivered one, and the added displays are
unnumbered.

## Files

```text
README.md                                    this guide (replaces the delivery README)
article.tex                                  the report (delivered Report163.tex; labels prefixed, [write] additions)
article.pdf                                  compiled report, 16 pages
companion-README.md                          the companion's README (delivered companion/README.md)
code/companion-disjoint_partitions.py        bounded exact companion and CLI (delivered companion/disjoint_partitions.py)
code/companion-test_disjoint_partitions.py   14 unit tests (delivered companion/test_disjoint_partitions.py)
code/build_pdf.py                            deterministic PDF build (delivered at the root)
code/make_zip.py                             allowlist-verified source ZIP (delivered at the root)
code/release_tools.py                        descriptor-pinned output helpers (delivered at the root)
code/test_release.py                         11 tests of the release tools (delivered at the root)
data/SOURCE_PROVENANCE.json                  sources, inspection scope, SHA-256 fingerprints (delivered at the root)
data/counts.json                             a(n) for 0 <= n <= 24 (delivered data/)
data/finite_checks.json                      full verification output (delivered data/)
data/source_data.json                        the 46 displayed OEIS terms and snapshot data (delivered data/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report163.pdf` (the delivered 9-page PDF, 345,847 bytes); `SHA256SUMS`
(1,197 bytes, 14 entries, verified at placement; repository policy ships no
checksum manifests); and the delivery `README.md` (7,608 bytes), staged at
placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.**
`companion-README.md` gives its commands as `companion/disjoint_partitions.py`
"from the report directory"; the tests locate the frozen data in `data/`
beside the program's parent directory, so they do not run under the shipped
names. `build_pdf.py` compiles `Report163.tex`; `make_zip.py` checks a closed
allowlist of the 14 delivered names (`Report163.pdf`, `companion/…`, …)
against `SHA256SUMS`, neither of which is shipped. Section 7 of the article
speaks of "the release" with "SHA-256 checksums" and of "earlier independent
checks through n=22" and "a separate direct-enumeration audit through n=24",
which were not part of the package. The release tools also require POSIX
(`/proc/self/fd`, no-follow directory descriptors).

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Maximal_Disjoint_Partition_Families_Growth_and_Inverse_Bounds_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # f5a5ce9462d507f69fe994d3bfd767da9b9fa91569f32d76dfeab37b050163e3, 444,037 bytes
mkdir "$T/pkg" && cd "$T/pkg" && unzip -q ../a.zip     # the 15 files are at the archive root
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only. Never run anything in the
repository.

**Route A, delivered layout** (as the delivery README gives it; at the write
on Windows every line below was run except the `-O` suite and the manifest
check, which the dossier ran at placement):

```sh
cd "$T/pkg"
python3 -B companion/disjoint_partitions.py verify > verify.out    # compare with data/finite_checks.json
python3 -B companion/disjoint_partitions.py threshold --value 1000 --max-n 24   # first_n 22
python3 -B companion/disjoint_partitions.py bounds --value 100000000000000000000  # [26, 127]
python3 -B -m unittest discover -s companion -p 'test_disjoint_partitions.py' -v   # 14 tests
python3 -B -O -m unittest discover -s companion -p 'test_disjoint_partitions.py' -v
sha256sum -c SHA256SUMS
```

On Windows the outputs carry CRLF line endings (they equal the frozen files
after conversion), and `test_cli_normal_optimized_identical_no_writes`,
which compares raw output bytes, fails for that reason; the other 13 pass.
The release tests (`python3 -B -m unittest test_release -v`) and the PDF and
ZIP rebuilds (`build_pdf.py --output-dir`, `make_zip.py --output`, each
refusing existing destinations) need POSIX and pdfTeX and were not run by the
intake on Windows.

**Route B, from the shipped files, any OS** (tested at the write):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a068598-disjoint-partition-families
B=$(mktemp -d); mkdir "$B/companion" "$B/data"; cd "$B"
cp "$R/code/companion-disjoint_partitions.py" companion/disjoint_partitions.py
cp "$R/code/companion-test_disjoint_partitions.py" companion/test_disjoint_partitions.py
cp "$R/data/counts.json" "$R/data/finite_checks.json" "$R/data/source_data.json" data/
python3 -B -m unittest discover -s companion -p 'test_disjoint_partitions.py' -v
```

Use `py` where `python3` is not on the path. The full suite took 124 s on the
intake's loaded laptop (the delivery README reports about 19 s).

## Build the PDF

pdfLaTeX (fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, geometry,
booktabs, array, microtype, hyperref); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026: 16
pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The delivered source builds the same way to 9 pages, also
without warnings. The article keeps the delivered preamble lines that
suppress PDF dates and trailer identifiers; the delivered byte-identity claims
apply to `Report163.tex` under the delivering toolchain (pdfTeX 1.40.26, TeX
Live 2025/dev/Debian), not to this build.

## From the delivery README

The delivery README (replaced by this guide) described `Report163.pdf` as
"the nine-page mathematical report" and the ZIP as packaging the report,
companion, frozen data, tests, provenance and "deterministic local release
tools". It summarized the results as above; gave the quick-verification
commands of Route A; said "All 14 companion tests and 11 release tests pass
in normal and optimized modes" (on its Linux host) and that "Finite
computation is diagnostic"; gave POSIX build and archive commands with
example output directories, two builds to be compared with `cmp`; described
the output helpers' no-clobber guarantees and their limits ("They must not
be treated as a sandbox for hostile code"); called the checksums
"not authenticated signatures"; and ended on source boundaries ("This is a
bounded literature check, not an exhaustive novelty or priority
certificate").

## Rights

Repository contents are MIT-0. The article and the frozen data quote OEIS
terms and comments of A068598; OEIS content is published by The OEIS
Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and those
terms remain under that licence. No third-party PDF is shipped. Nothing was
submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A068598 (revision #50); Nathanson,
  J. Number Theory 17 (1983) 103–112 (Spencer's argument, p. 108); Luria and
  Simkin, SODA 2022 (arXiv:2105.11431v2); Filaseta, in *Number Theory: New
  York Seminar 1991–1995* (1996) 103–113 (abstract only). Added by the write:
  Simkin, Adv. Math. 427 (2023) 109127 (abstract); the Wolfram `FindClique`
  documentation.
- Batch 107 of `docs/incoming`, bundle Report 163; arrival `60f54ea06`,
  placement `3988bf5c4`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report163.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
