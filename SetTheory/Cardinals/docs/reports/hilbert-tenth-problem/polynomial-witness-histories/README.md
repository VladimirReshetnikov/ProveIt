# Polynomial Witness Histories

**Unique linear certificates with finite polynomial unknowns: cellular histories over ℕ[X,Y] and ℕ[X], and linear boundary transport over every commutative ring**

This is a research report dated 2 October 2026, built from three manuscripts
of batch 79 (cluster J1) of ProveIt's incoming reports. They are called
*source 06*, *source 15* and *source 01* after their batch-79 manuscript
numbers, which are also the file prefixes of their shipped programs, data
and notes.

| Source | Manuscript | Archive (arrival commit); title; main file | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 06 (base) | batch 79, manuscript 06 | `unique_polynomial_histories.zip` (`060e08a07`); *Unique Histories from Linear Equations: A canonical cellular-computability compiler over ℕ[X,Y]*; `unique_polynomial_histories/unique_polynomial_histories.tex`, 28-page PDF | `e58b724c2` | `224ca41df` | Part I (Sections 2–19) |
| 15 | batch 79, manuscript 15 | `one_coordinate_certificates.zip` (`ef2fc7990`); *The Price of One Coordinate: Self-sizing quadratic certificates for universal computation*; `one_coordinate_certificates/one_coordinate_certificates.tex`, 30-page PDF | `44983ed7e` | `224ca41df` | Part II (Sections 20–36) |
| 01 | batch 79, manuscript 01 | `Linear_Boundary_Transport_Research.zip` (`060e08a07`); *Linear Quasi-Diophantine Universality: Unique Polynomial Certificates, Boundary Tests, and an Exact Convex Integrality Gap*; `linear_boundary_transport/article.tex`, 22-page PDF | `48ee077c7` | `224ca41df` | Part III (Sections 37–52) |

All three carry the author line "Research report prepared for Vladimir
Reshetnikov" and name no assistant; like the rest of the incoming reports
they are treated as AI-assisted research manuscripts. Source 15 is a sequel
of source 06: it cites source 06's file by name (its bibliography entry
`Precursor`, read as a "user-provided manuscript"; its pin is later than
source 06's arrival) and answers source 06's research question *A
one-coordinate compiler with the same uniqueness guarantees* negatively,
then gives a degree-two replacement whose full witnesses are in bijection
with source 06's. Source 01 is independent of both and shares no lemma
with them. Source 01's title says "Diophantine", but its unknowns are
**polynomial-valued**, with prescribed sorts; it is not about ordinary
integer unknowns.

Every result, proof, example, remark, limitation, research question and
appendix of the three manuscripts is printed. The three share one spine
(Section 1.2 of the article): a fixed number of *finite polynomial*
unknowns, identities linear in them (in source 15, of degree two with every
product through one stride unknown), a clock that makes the whole witness
unique with 0/1 coefficients, and no computable input-only bound on its
degree or support.

**Status: AI-assisted, unrefereed, not formalized.** Nothing in the report
is formalized in Lean or Rocq, and priority is not established for any
Part.

## Already reviewed in the research programme

All three manuscripts were reviewed by the Hilbert's-tenth-problem research
programme, byte for byte the archives placed here. This report links those
reviews and does not present its placement as a first review.

- Source 06:
  [`review_unique_polynomial_histories.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_unique_polynomial_histories.md)
  (commit `e5497072e`), with its checker `review_unique_polynomial_histories.py`
  and receipt `review_unique_polynomial_histories.json`. It accepts the
  written construction on its stated domain and replays all three author
  entry points.
- Source 01:
  [`review_boundary_sandpile_060e08a07.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_boundary_sandpile_060e08a07.md)
  (commit `49bc4c654`, lines 1–64), with its members file, replay and checker.
  It finds the mathematics sound within the stated polynomial and field
  witness domains and reproduces 32,502 checks.
- Both are indexed in
  [`incoming_substrate_review_2a8a39599.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_substrate_review_2a8a39599.md)
  (commit `c00ce825a`), rows *Linear Boundary Transport* and *Unique
  Polynomial Histories*.
- Source 15 was only inventoried as pending (intake commit `b927b2290`) when
  it was placed; it was reviewed afterwards in
  [`review_one_coordinate_aebfa.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_one_coordinate_aebfa.md)
  (commit `a21c86070`), indexed in `incoming_substrate_review_aebfa386e.md`.
  It finds no mathematical defect.

**Defects found by those reviews; the shipped programs are the unpatched originals.**

- *Polynomial-history compiler (source 06).* The ProveIt review of
  2 October 2026 found that accepting symbols `1.0` or `True` pass the
  compiler's validation (Python set containment identifies them with `1`),
  so the compiled system names witnesses `T_1.0` or `T_True` while declaring
  `T_1`, and checking a witness fails with a `KeyError`. The tested repair is
  [`unique_polynomial_histories_exact_domains.patch`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/unique_polynomial_histories_exact_domains.patch).
  The theorems, for exact alphabet symbols, are unaffected; the delivered
  `code/06-polynomial-histories-polynomial_histories.py` is the original.
- *Boundary-transport compiler (source 01).* The review found that
  `compile_system`, `history` and `residual` in
  `code/01-boundary-transport-boundary_transport.py` (lines 161, 171, 233)
  accept non-Boolean clock modes: `clocked=0.5` loses uniqueness (a
  disconnected cycle witness is accepted) and `clocked=2` rejects a true
  history. The intake also saw a third symptom: `history` and `residual`
  with `clocked=0.5` give a nonzero residual on a true halting run. The
  tested repair is
  [`linear_boundary_exact_boolean_guards.patch`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/linear_boundary_exact_boolean_guards.patch);
  with it the suite still passes 32,502 checks (re-verified at the intake).
  The theorems, stated for the two Boolean modes, are unaffected; the
  delivered file is the original.
- *One-coordinate compiler (source 15).* The review found that the
  low-level `System` constructor (`code/15-one-coordinate-compiler.py`,
  line 171) does not validate residual coefficients: with a float
  coefficient `2**60` next to `-1.0`, a false witness is reported as a zero,
  because the `-1` is lost in floating-point rounding; the constructor also
  keeps caller-owned lists, and an accepting set `[1, True]` loses an alias
  before validation. The high-level `compile_system`, the theorems and the
  shipped exports are unaffected. The repair is
  [`one_coordinate_exact_system_inputs.patch`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/one_coordinate_exact_system_inputs.patch);
  the delivered file is the original.

Whether a later commit installs patched copies here is Vladimir's call; the
paragraphs above would then need an update. The same review of source 15
proves a projection of its eleven identities to ten identities on `s³+s+6`
unknowns; the article records it, unverified at the write, under source
15's question *Can the eleven rows be reduced without changing the full
fibre?* (Section 33.1).

## Files

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 92 pages (unnumbered title page, then pages 1–91)
README.md                                            this guide
01-boundary-transport-SOURCE_AUDIT.md                source 01's repository pin, primary sources and claim boundaries, as delivered
code/01-boundary-transport-Makefile                  source 01's make targets (delivered layout; see below)
code/01-boundary-transport-boundary_transport.py     source 01's exact sparse compiler, sort-aware checker and finite-box GF(2) solver (unpatched)
code/01-boundary-transport-verify.py                 source 01's 32,502-check suite; rewrites the examples and the validation record
code/06-polynomial-histories-export_quadratic.py     source 06's exact expansion of the worked sum-of-squares quadratic
code/06-polynomial-histories-feature_verification.py source 06's binary and weighted feature checks; exports both feature systems and quadratics
code/06-polynomial-histories-polynomial_histories.py source 06's sparse-polynomial cellular compiler, feature forms and witness checker (unpatched)
code/06-polynomial-histories-verification.py         source 06's main suite and worked-example export
code/15-one-coordinate-bounded_linear.py             source 15's finite-state bounded-height solver for univariate linear systems
code/15-one-coordinate-compiler.py                   source 15's eleven-identity compiler, feature variants and candidate generator (unpatched)
code/15-one-coordinate-export_example.py             source 15's export of the worked system, witness, quartic and hashes
code/15-one-coordinate-verify.py                     source 15's seven test suites and their receipts
data/01-boundary-transport-test_results.json         source 01's recorded run: 32,502 checks by group, with limitations
data/01-boundary-transport-transfer_certificate.json the transfer-machine instance, trajectory and sparse witness
data/01-boundary-transport-transfer_equation.txt     the emitted tagged scalar equation
data/01-boundary-transport-transfer_witness.txt      the witness polynomials, human-readable
data/06-polynomial-histories-example_binary_system.json   the 12-row binary-feature system of the worked example (73 unknowns)
data/06-polynomial-histories-example_certificate.json     the full accepting witness and its five configuration rows
data/06-polynomial-histories-example_quadratic.json       the expanded worked quadratic: 2,098 unknown monomials, 5,082 terms
data/06-polynomial-histories-example_system.json          every coefficient of the 15-row worked system
data/06-polynomial-histories-example_weighted_system.json the 9-row weighted-feature system of the worked example
data/06-polynomial-histories-feature_results.json         feature-suite counts, invariance, mutation and expansion statistics
data/06-polynomial-histories-quadratic_results.json       expanded-quadratic statistics and the 8 exact evaluation checks
data/06-polynomial-histories-verification_results.json    source 06's recorded main run
data/15-one-coordinate-build_validation.json         source 15's record of its own 30-page PDF build (that PDF is not shipped)
data/15-one-coordinate-example_receipt.json          dimensions and counts of the worked example (75 unknowns, 11 identities, stride 15)
data/15-one-coordinate-example_system.json           every term of the eleven worked residuals
data/15-one-coordinate-example_witness.json          every component of the worked witness
data/15-one-coordinate-export_hashes.json            SHA-256 of three exports, one of them not shipped (see below)
data/15-one-coordinate-test_binary.json              receipt of the binary-rule suite
data/15-one-coordinate-test_bounded_linear.json      receipt of the bounded-linear solver suite
data/15-one-coordinate-test_independent_tiles.json   receipt of the independent tile-assignment suite
data/15-one-coordinate-test_interfaces.json          receipt of the interface-validation suite
data/15-one-coordinate-test_multistate.json          receipt of the multistate suite
data/15-one-coordinate-test_mutations.json           receipt of the mutation suite
data/15-one-coordinate-test_ray_geometry.json        receipt of the ray-geometry suite
data/15-one-coordinate-verification.json             the combined receipt of the seven suites
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md`
is byte-identical to the delivery (`224ca41df` verified all blobs against
fresh extractions). Delivered name → shipped name:

- Source 06 (`unique_polynomial_histories/`): `code/*.py` →
  `code/06-polynomial-histories-*.py`; `results/*.json` →
  `data/06-polynomial-histories-*.json`; `unique_polynomial_histories.tex` →
  Part I of `article.tex`. Its ten `results/*.json` files (eight shipped) have no
  final newline, as delivered. Its delivery `README.md`, staged at placement as
  this directory's `README.md`, is replaced by this guide; it survives in
  the archive and in `224ca41df`.
- Source 15 (`one_coordinate_certificates/`): `code/*.py` →
  `code/15-one-coordinate-*.py`; `results/*.json` →
  `data/15-one-coordinate-*.json`; `one_coordinate_certificates.tex` →
  Part II of `article.tex`.
- Source 01 (`linear_boundary_transport/`): `code/*.py` and `Makefile` →
  `code/01-boundary-transport-*`; `examples/*` and
  `validation/test_results.json` → `data/01-boundary-transport-*`;
  `SOURCE_AUDIT.md` → `01-boundary-transport-SOURCE_AUDIT.md`;
  `article.tex` → Part III of `article.tex`.

Not shipped (all survive in the archives at their arrival commits): the
three PDFs; source 06's `SHA256SUMS.txt` (17/17 verified at the intake) and
source 15's `MANIFEST.sha256` (21/21); the delivery READMEs of sources 15
and 01; and the three heavy exports of the next section.

Delivered files whose text still uses delivery names or names unshipped
files: the article's Parts (each validation section carries a note mapping
the names); `code/01-boundary-transport-Makefile` (runs `python
code/verify.py` and builds `article.tex`, meaning source 01's own
manuscript, not this report); `01-boundary-transport-SOURCE_AUDIT.md`
(describes "the article" and "the report", meaning source 01); all ten
programs (they read and write `results/`, `examples/` and `validation/`
relative to their package root, and import their siblings under their
delivery names); `data/15-one-coordinate-export_hashes.json` (records the
hash of the unshipped `example_quartic.json`); and
`data/15-one-coordinate-build_validation.json` (describes source 15's own
30-page PDF).

## Reconstructing the excluded data

Three expanded-polynomial exports are not stored here because the shipped
code regenerates them exactly (Vladimir, 2 October 2026: "Exclude heavy
regenerable artifacts"). From source 06:
`example_binary_quadratic.json` (1,026,498 bytes, SHA-256
`c43c3a8f9fcac0d1c44a6e937a8a1d347fecd2a9cffa2c38e0d4578e4d95410c`) and
`example_weighted_quadratic.json` (1,031,059 bytes,
`5118044a710caa984070117d071d351e02cf64bdfb2e412f3118bcc705dfc559`). From
source 15: `example_quartic.json` (1,641,389 bytes,
`06b717e6608a3b23d5f74e9c008dcc0c1a65ff0ac7b883b099b424e2bb3ae6d5`).

The programs write to `results/` beside their `code/` directory and import
their siblings by delivery name, so run them in a fresh directory with the
delivered layout, never in this directory:

```sh
R=polynomial-witness-histories          # this directory
mkdir -p /tmp/p06/code /tmp/p15/code
for f in polynomial_histories export_quadratic feature_verification verification; do
  cp "$R/code/06-polynomial-histories-$f.py" /tmp/p06/code/$f.py; done
for f in compiler bounded_linear export_example verify; do
  cp "$R/code/15-one-coordinate-$f.py" /tmp/p15/code/$f.py; done
(cd /tmp/p06 && python code/feature_verification.py)   # writes results/, standard library only
(cd /tmp/p15 && python code/export_example.py)
```

`feature_verification.py` runs the whole feature suite and also writes
`example_binary_system.json`, `example_weighted_system.json` and
`feature_results.json`; it took 43 s and 16 s in two runs on the intake
machine. `export_example.py` takes about 1 s and also writes
`example_system.json`, `example_witness.json`, `example_receipt.json` and
`export_hashes.json`. Both create `results/` themselves. On POSIX the outputs
are byte-identical to the hashes above. On Windows (Python 3.14.4) the files
are written with CRLF line ends; after converting CRLF to LF (for example
`tr -d '\r' < in > out`) they are byte-identical, and so are the other
regenerated files except `export_hashes.json`, which then records the hashes
of the CRLF files. Verified at this write on copies: of the ten files the
two commands write, nine match the delivered bytes after LF normalization
(the three exports by the SHA-256 values above), and `export_hashes.json`
differs only because it hashes the CRLF files.

The delivered files are also in the original archives:

```sh
git show 060e08a07:docs/incoming/unique_polynomial_histories.zip > unique_polynomial_histories.zip    # 434,326 bytes
git show ef2fc7990:docs/incoming/one_coordinate_certificates.zip > one_coordinate_certificates.zip    # 426,821 bytes
```

with members
`unique_polynomial_histories/results/example_binary_quadratic.json`,
`unique_polynomial_histories/results/example_weighted_quadratic.json` and
`one_coordinate_certificates/results/example_quartic.json`. None of the
three is proof-carrying: each is the expansion of a system that a shipped
compiler emits.

## Label prefix

Every label carries the prefix `pwh:`. Source 06's 76 delivered labels are
printed as `pwh:uh:` plus their delivered names, source 15's 75 as
`pwh:oc:` plus theirs, source 01's 65 as `pwh:bt:` plus theirs; none was
dropped or otherwise renamed. Bibliography keys carry `uh:`, `oc:` and `bt:`.
The 34 added labels (250 in all; the placed `article.tex`, source 06 alone,
had 76):

- front matter, Parts and provenance (13): `pwh:sec:front`, `pwh:sec:parts`,
  `pwh:sec:spine`, `pwh:tab:spine`, `pwh:tab:ledger`, `pwh:sec:notation`,
  `pwh:tab:notation`, `pwh:sec:relation`, `pwh:sec:status`, `pwh:part:uh`,
  `pwh:part:oc`, `pwh:part:bt`, `pwh:sec:provenance`;
- Part I (6): `pwh:uh:q:numerical`, `pwh:uh:q:onecoord`, `pwh:uh:q:packing`,
  `pwh:uh:q:kernel`, `pwh:uh:app:ledger`, `pwh:uh:app:trust`;
- Part II (7): `pwh:oc:sec:comparison`, `pwh:oc:q:rows`, `pwh:oc:q:numerical`,
  `pwh:oc:q:packing`, `pwh:oc:q:kernel`, `pwh:oc:app:ledger`,
  `pwh:oc:app:trust`;
- Part III (8): the three unlabelled numbered statements
  `pwh:bt:rem:separation` (Remark 38.3), `pwh:bt:rem:instantiated`
  (Remark 41.4), `pwh:bt:cor:spectral` (Corollary 44.3); `pwh:bt:sec:mrdp`,
  `pwh:bt:q:concrete`, `pwh:bt:q:arithmetic`, `pwh:bt:q:analysis`; and the
  editorial remark `pwh:bt:rem:univariate`.

## What is claimed, and what is not

The report claims conventional mathematical proofs, by its sources, of:
source 06's canonical compiler over ℕ[X,Y] (`s³+s+5` polynomial unknowns;
`3s+3` affine-linear rows, or `3⌈log₂ s⌉+6` unit-coefficient rows, or nine
weighted rows, with identical full solution tuples; a unique
Boolean-coefficient witness exactly at a first singleton acceptance; exact
degrees `h`, `m+2h+1`, `m+3h+1`), its Σ⁰₁-complete fixed matrix, its
degree-bound obstruction, single quadratic, bounded export and
nondeterministic extension; source 15's finite-state decision procedure for
coefficient-bounded univariate linear systems over ℕ[X], the resulting
impossibility of a universal univariate linear compiler with computably
bounded witness heights, its eleven-identity degree-two compiler with the
self-calibrating stride `S = X^(m+2h+2)`, the bijection with source 06's
witnesses, its quartic and bounded export; source 01's ring-uniform
transport theorems, its compiler with `q+d` linear identities in `q+2d`
polynomial unknowns with omitted-variable sorts, the row-tagged single
equation, the integer/rational energy gap and the Hilbert-space range
theorem. One editorial remark (Remark 49.1) is new at the write: source
15's finite-state proof also decides bounded-height univariate systems over
ℤ[X] and all univariate systems over a finite ring, so source 01's 0/1
certificates need at least two indeterminates in this linear syntax.

Not claimed:

- historical priority for any Part or combined normal form (all three
  sources say so); undecidability of linear equations over polynomial
  semirings, or monomial forcing, is older work (Narendran 1996, already in
  one indeterminate). The Narendran attribution is the sources'; the
  research programme could not reread that paper behind its publisher page;
- any ordinary fixed-arity single-fold or finite-fold Diophantine
  representation over ℕ: a fixed number of *polynomial* unknowns is not a
  fixed number of integer unknowns, and coding the tuple through MRDP can
  introduce uncontrolled auxiliary witnesses;
- any change of the repository's 75-operation complete-certificate and
  87-operation universal-polynomial bounds;
- a numerical universal instance (no source instantiates a universal
  machine table; the worked examples are not universal);
- decidability of unrestricted univariate linear systems over ℕ[X];
  optimality of eleven identities or of `s³+s+7` unknowns; sharpness of the
  single quartic;
- undecidability of finite-dimensional convex least squares, or a
  spectral-gap undecidability theorem (source 01);
- refereeing, proof-assistant verification, or a rebuild of the
  repository's Lean or Rocq developments; the finite checks illustrate and
  do not prove.

## Relation to neighbouring reports and to the formal project

- [`canonical-diophantine-certificates`](../canonical-diophantine-certificates/),
  Part IX (*The boundary of fixed-arity compression*): the one-history
  relation `cdc:eq:onehistory`, Theorem `cdc:bd:thm:universal` and
  Proposition `cdc:bd:prop:nobound` are the boundary that all three Parts
  stand outside. Source 01's subsection *Why this is not fixed-arity integer
  MRDP* restates it without citing it, and the three no-bound results
  (Theorem 10.2, Corollaries 26.3 and 41.5) are the bounded-search argument
  of `cdc:bd:prop:nobound` with polynomial degree in place of witness
  height; editorial notes say so and claim no novelty for the argument.
  That report's Part IV, *Polynomial trajectories*, shares only the name.
- [`stochastic-and-thermal-exactness`](../stochastic-and-thermal-exactness/):
  batch-79 manuscripts 10 and 14 were placed there (`bbaf322e5`) for its
  Part V on coercive Green operators, the opposite regime to source 01's
  Hilbert-space operator (uniformly coercive versus zero in the continuous
  spectrum); a note after Theorem 44.2 records this.
- [`smooth-diophantine-finalizers`](../smooth-diophantine-finalizers/),
  opened by the same placement, post-processes ordinary quadratic systems
  over ℕ; it applies here only to the externally bounded exports of
  Proposition 11.3 and Theorem 28.2 (sources 06 and 15), and neither source
  uses it.
- The formal project
  [`Computability/HilbertTenthProblem`](../../../../../../Computability/HilbertTenthProblem/)
  is read-only for this report. Placement beside a Lean/Rocq development
  confers no formal status: **no statement of this report is formalized.**
  The only project declaration a source names is `rePred_dioph`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/Common/RecursivelyEnumerableDioph.lean`,
  line 32, built on `MRDP.mrdp`), which source 01 proposes as the endpoint
  of a future integer bridge; nothing here uses it.

## Build

From this directory (MiKTeX or TeX Live; packages: newtx, mathtools,
tcolorbox, tikz, listings, longtable, xurl, hyperref, bookmark, etoolbox):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Build in a scratch copy to keep auxiliary files out of the repository. The
committed PDF was built with pdfLaTeX (MiKTeX): 92 pages, no errors, no
warnings (no undefined references or citations, no multiply defined labels,
no duplicate destinations), no overfull boxes.

## Rerunning the suites

All ten programs use only the Python standard library (Python 3.10 or
later). They rewrite their recorded outputs in place, so run them only in a
copy with the delivered layout: strip the prefix `NN-slug-` from each
program into `code/`, and for source 01 also create `examples/` and
`validation/` (its `verify.py` does not create them). Then, from each copy's
root:

- source 06: `python code/verification.py` (81 s at the intake),
  `python code/export_quadratic.py` (3 s), `python code/feature_verification.py`
  (16–43 s). Recorded: 59,049 ray-clock flows, 19,200 binary
  rule/input/horizon cases, 840 multistate cases, 16,384 independent tile
  assignments, 373 worked-example mutations and wrong horizons, 8 exact
  quadratic evaluations; the feature suite 7,456 cases in both feature forms
  and 367 mutations per form;
- source 15: `python code/verify.py` (7 s; one suite with
  `--part bounded_linear`, `binary`, `multistate`, `ray_geometry`,
  `independent_tiles`, `mutations` or `interfaces`) and
  `python code/export_example.py` (1 s). Seven suites: 7,168 binary
  candidates (768 admitted), 576 multistate and 576 feature checks (59
  admitted), 6,561 stride prefixes, 432 clock tuples, 4,096 tile
  assignments, 253 coefficient and off-region mutations, 729 scalar linear
  systems plus four edge cases, 12 invalid inputs;
- source 01: `python code/verify.py` (71 s): 32,502 checks.

Use `py` or `python3` where `python` is not available. On Windows the
regenerated files have CRLF line ends; compare after converting to LF. At
the intake every suite passed on copies (Python 3.14.4, Windows), and every
regenerated file matched the delivered bytes after LF normalization, except
the elapsed-time fields of `verification_results.json` (source 06) and
`export_hashes.json` (source 15, which hashes the CRLF files).

## Other discrepancies

- Source 06's text gives the delivery file names (`results/...`) and the
  delivery build commands for `unique_polynomial_histories.tex`; source 15's
  likewise (`results/example_quartic.json`, not shipped); source 01's names
  `examples/` and `validation/`. Notes in the Parts give the shipped names.
- Source 01 abbreviates the path of `RecursivelyEnumerableDioph.lean` as
  `Common/...` (the full path appears only in its bibliography URL); a note
  gives the full path. One `\texttt` path in that paragraph was set as
  `\path` so that it can break.
- Layout changes made at the merge, none of them in a statement or a proof:
  the three title pages became Part openings that print each abstract and
  status box; the appendices are numbered sections at the end of each Part
  ("appendix of source NN") because section numbers run through the
  report; source 01's remarks use the definition style of the other two
  sources; source 01's command `\F` (blackboard F) was renamed `\Fbb`
  because sources 06 and 15 use `\F` for the calligraphic accepting alphabet
  (printed glyphs unchanged); the bibliographies are merged at the end with
  prefixed keys, entries cited by several sources printed once per source.
- The intake's own checks, beyond the reviews: source 15's bijection was
  checked on the shared worked example (packing all 73 components of source
  06's witness by `Y ↦ X^15` gives source 15's components, with `S = X^15`);
  source 01's proofs were re-derived and its kernel, rank and solvability
  claims checked independently on small boxes with no mismatch.
