# Periodic Turmite First Revisits

**First revisit detection and exact pattern queries for finite-defect
periodic turmites: polynomial bit complexity and an executable affine lane
calculus**

This is a research report dated 3 October 2026, built from one manuscript:
"Research Report 38" of the Hilbert's-tenth programme's AI-assisted report
pipeline, batch-83 manuscript 10 of ProveIt's incoming reports (cluster H2).
Its author line is "Mathematical research report"; the archive names no
person or tool.

| Source | Report | Batch 83 | Archive (arrival `3051d1446`) | Pin | Placed | Printed as |
|---|---|---|---|---|---|---|
| sole source | 38 | 10 | `Polynomial_First_Revisit_and_Exact_Pattern_Queries_for_Turmites_Package.zip` (504,531 B, SHA-256 `e5abfdbfbbc9c203bdfafb040cba7f8c280af8b031b02103c989aeb97e085277`; 47 files under `Research_Report38/`; main file `Research_Report38.tex`, 703 lines; 21-page PDF) | `5883b08b7` (see below) | `a51a439cd` | the whole report, with the manuscript's numbering |

**The pin.** The manuscript pins no commit for its mathematics. Its frozen
source audit (`source-packet-boundary-context-source-audit.md`) read two
research-tree notes, `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md`
(lines 305–401, blob `2e762cc5f31e`) and
`Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_TOGGLE_ROUTER_UNIVERSALITY.md`
(lines 1–95, blob `a70af5ccd954`), and pinned its repository searches to
commit `5883b08b7` (3 October 2026). That commit is taken as the pin. Both
blobs are unchanged at the write.

**The result.** For an explicitly listed cyclic L/R turmite rule, an
explicitly listed periodic colour tile, finitely many binary-encoded defects
and a binary start, the first repeated lattice *position* (heading ignored)
is decidable in polynomial bit time: the algorithm returns the exact first
repeated arrival `τ`, an earlier witness and a polynomial-size affine lane
representation of the path, or certifies that no position is ever revisited
and returns a translated periodic tail (Theorem 2.2); `τ ≤ T* = (K+1)(S(2B+1)+1)`
and every intermediate integer has polynomially many bits (Theorem 6.1).
Exact first occurrence of finite unions of heading, coordinate-congruence,
head-site and head-relative colour-stencil clauses on the certified domain
is decidable and implemented (Theorem 7.1), with no polynomial bound. As a
consequence, no undecidable language reduces to globally one-visit runs with
acceptance in that observation language (Corollary 12.1).

**Status: AI-assisted, unrefereed, not formalized.** Conventional proofs
and finite exact replay checks. "In P" refers to the explicit input model of
Section 2 (explicitly listed rule and tile, binary coordinates); succinct
tiles are a different model, and `τ` itself can be exponential in the input
length. No priority is claimed or certified.

**Already reviewed.** After arrival, the Hilbert's-tenth research programme
reviewed the archive: `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_turmite_first_revisit38_intake.md`
(commit `308f14072`), indexed in `Computability/HilbertTenthProblem/README.md`.
It read the proofs and the active source text, and did not run the archived
Python, replay the logs, audit the release verifier or certify the PDF.
Verdict: the first-revisit, polynomial-bit-complexity and exact-observation
arguments "pass this bounded proof read on their stated domains. No
mathematical defect was found." Its scope points, all printed in the article
(editorial preface and `[write]` notes in Sections 7, 11 and 12):

- the certified one-visit portion is decidable and supplies no new universal
  arithmetic bound; the unrestricted turmite substrate is universal;
- the complexity proof bounds every intermediate integer, including discarded
  candidates; the coarse `O(N_in^7)` holds for explicit rule and tile only;
- the **strict first-arrival observation boundary**: colour reconstruction
  holds through the first repeated arrival, not after that site's second
  departure; zero signed count means emptiness only because of the Boolean
  invariant; Boolean expansion can be exponential; eventual periodicity is of
  a head-relative stencil, not of the board;
- **attribution**: turmite universality is due to Maldonado, Gajardo,
  Hellouin de Menibus and Moreira, *Nontrivial Turmites are Turing-universal*,
  arXiv:1702.05547 (Theorems 2.1 and 3.1; Section 5 states the
  at-most-two-visits property); the paper supplies no literal colour atlas,
  ordinary-input loader or iff accepting port for this repository; ordinary
  turmites do not physically halt; no sharp one/two-visit threshold is
  established;
- **a Boolean-DAG occurrence-certificate lead** (membership at a supplied
  lane index, inequality truth bits with residuals, reuse of
  `presburger_congruence_five.md`): an *unimplemented* paid-component lead,
  not a saving or bound, **not a first-hit-minimality certificate**, not a
  certificate for arbitrary supplied lane tables, and **not an
  ordinary-input universal loader**. The article prints it in Section 12 with
  the letters changed to `χ, η, Λ` (the review's `b, s, L` already have
  meanings in the report).

## Files

```
README.md                                                 this guide
article.tex                                               the report: the delivered Research_Report38.tex with ptr: labels, an editorial preface, [write] notes, Appendix C
article.pdf                                               the compiled report, 26 pages
INTEGRITY.md                                              the delivered release's integrity and reproducibility contract
source-packet-PROOF.md                                    proof of the observation extension (signed progression calculus, colour compiler)
source-packet-README.md                                   the frozen source packet's README
source-packet-boundary-context-README.md                  README of the historical boundary context
source-packet-boundary-context-proof.md                   the original first-revisit proof, Presburger formulation, eventual periodicity
source-packet-boundary-context-review.md                  the historical review of the original boundary program
source-packet-boundary-context-source-audit.md            literature and repository source audit (the pin)
source-packet-complexity-review.md                        numerical and intermediate bit bounds for first revisit
source-packet-review.md                                   independent review of the observation code and mathematics (the iterator finding)
code/verify_release.py                                    the release verifier (identity gate, normal/-O replay); does not run here
code/seal_release.py                                      release sealing; rewrites MANIFEST.json, SHA256SUMS and verify_release.py in place
code/build_pdf.py                                         external pdfLaTeX rebuild of the delivered PDF
code/archive_release.py                                   deterministic ZIP creation and safe moved replay
code/archive_regression.py                                hostile-archive regression
code/tamper_regression.py                                 tamper regression on disposable copies
code/source-packet-one_visit.py                           active first-revisit engine (pinned)
code/source-packet-observations.py                        active observation compiler (pinned)
code/source-packet-test_boundary_regression.py            author tests, boundary part (pinned; = historical test_one_visit.py)
code/source-packet-test_observations.py                   author tests, observation part (pinned)
code/source-packet-independent_checks.py                  independent checker, seven groups (pinned)
code/source-packet-example.py                             the 2*10^100 first-hit example (pinned)
code/source-packet-verify_release.py                      the packet's own test gate (inert by design)
code/source-packet-boundary-context-one_visit.py          historical original engine (inert by design)
code/source-packet-boundary-context-review_checks.py      historical review checks (inert by design)
data/MANIFEST.json                                        the release inventory (delivered paths)
data/verification-expected-receipts.json                  stable expected outputs of the replay
data/verification-release-review.json                     the release's own review record (21-page PDF, delivered TeX)
data/verification-replay-plan.json                        the six pinned active programs and the replay commands
data/verification-source-lineage.json                     original/packaged path and SHA-256 of every packet file
data/source-packet-author-normal.log                      original author run, normal Python
data/source-packet-author-optimized.log                   original author run, python -O
data/source-packet-independent-normal.log                 original independent run, normal Python
data/source-packet-independent-optimized.log              original independent run, python -O
data/source-packet-independent-normal.txt                 a second recorded independent run (stream order and timing differ)
data/source-packet-independent-optimized.txt              a second recorded independent run, python -O
data/source-packet-example-result.json                    output of example.py
data/source-packet-release-receipt.json                   receipt of the packet's own test gate
data/source-packet-boundary-context-examples.json         historical examples of the boundary program
data/source-packet-boundary-context-review-check-results.txt   historical review-check counts
data/source-packet-boundary-context-test-results.txt      historical boundary test log
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md` is
byte-identical to the delivery (re-verified at the write against a fresh
extraction). Delivered name (in `Research_Report38/`) → shipped name:

- `evidence/source-packet/X.md` → `source-packet-X.md` at the report root;
  `evidence/source-packet/X.py` → `code/source-packet-X.py`; logs, `.txt`
  and `.json` → `data/source-packet-X`; the nested `boundary-context/`
  becomes the name segment `boundary-context-`; the segment `evidence/` is
  dropped;
- `verification/X.json` → `data/verification-X.json`;
- the six release tools → `code/`; `MANIFEST.json` → `data/MANIFEST.json`;
  `INTEGRITY.md` → `INTEGRITY.md`;
- `Research_Report38.tex` → `article.tex`; `README.md` → replaced by this
  README (its contracts are under "What is claimed" below).

Not shipped: the delivered `Research_Report38.pdf`; `SHA256SUMS` (46/46
verified at placement); `evidence/source-packet/manifest-sha256.json`
(30/30 verified) and `evidence/source-packet/boundary-context/manifest-sha256.json`
(10/10 verified); and `boundary-context/test_one_visit.py`, byte-identical
to `test_boundary_regression.py` (shipped once, as
`code/source-packet-test_boundary_regression.py`). **The article (Section
11.2) and `INTEGRITY.md` print the SHA-256
`7dfd4f270ad7bf667bc123aace7bd97fd13b992949a9dfc8e3dca3f8105cea62` of the
first `manifest-sha256.json`, which is not shipped**; a `[write]` note in the
article says so. All of them survive in the archive of the arrival commit:

```sh
git show 3051d1446:docs/incoming/Polynomial_First_Revisit_and_Exact_Pattern_Queries_for_Turmites_Package.zip > r38.zip
```

No regenerable data were excluded.

**Shipped files whose text uses delivery names or names unshipped files:**
`INTEGRITY.md` (`evidence/source-packet/`, `verification/`, `SHA256SUMS`,
`MANIFEST.json` at the root); `source-packet-README.md`
(`boundary-context/`, `manifest-sha256.json`, unprefixed program names, and
"run from this directory: `python example.py`, `python verify_release.py`");
`source-packet-boundary-context-README.md` and
`source-packet-boundary-context-proof.md` (`test_one_visit.py`);
`code/verify_release.py`, `code/tamper_regression.py`, `code/seal_release.py`,
`code/build_pdf.py`, `code/archive_release.py`, `code/archive_regression.py`
(`Research_Report38/`, `evidence/source-packet/`, `verification/`,
`SHA256SUMS`, `manifest-sha256.json`); `code/source-packet-verify_release.py`
(`manifest-sha256.json`, `boundary-context/`); `data/MANIFEST.json`,
`data/verification-replay-plan.json` and `data/verification-source-lineage.json`
(delivered paths throughout). The Python programs import each other by their
delivered module names (`one_visit`, `observations`), so none runs under its
shipped name. The article's Appendix A names the delivered files; a `[write]`
note there gives the shipped names.

## Labels and numbering

Every label carries the prefix `ptr:`. The manuscript's 59 labels are `ptr:`
plus their delivered names; none was dropped or renamed apart from the
prefix. The write added two: `ptr:sec:preface` (the unnumbered editorial
preface) and `ptr:app:provenance` (Appendix C), 61 in all. Section,
statement and equation numbers are the manuscript's. Text written at the
write is marked `[write]`; text without a marker is the manuscript's own.
The bibliography gained four `[write]` entries (the review, the two
research-tree notes, `canonical-diophantine-certificates`); the delivered
entry for the frozen packet, cited nowhere in the delivered text, is now
cited by the preface.

## Setting and notation

Cyclic L/R turmite: rule word `w ∈ {L,R}^m`, explicitly listed `u×v` tile
`b`, finite defect map `D` (`K = |dom D|`), start `p_0`, heading `h_0`.
Time `t` is the configuration **before departure**; `τ` is the first time
the head stands on a position it occupied before, whatever the heading; the
certified domain is `{0,…,τ}` or all of `N`. `S = 4uv`.

The manuscript reuses letters across sections; no symbol was renamed, and
the preface's notation table lists the collisions: `L, R` (rule letters;
also cycle length, count-interval end, coordinate bound), `A, B` (lanes;
also complexity bounds `A_0`, `B = R+S+1`, threshold `B_F`), `Q` (bound
`S(2B+1)`; also `Q_F`, `Q_obs`), `q` (colour read, residue, coordinate
index, modulus), `a, b, c` (lane base, tile, colour; also rank-one
coefficients, truncation time, congruence, signed coefficients), `s, r`
(earlier and restart times; also Bézout directions and residues),
`C, E, F, H` (collision time, excursion, defect time, history; also an
inequality, the signed indicator, an interval end), `M, N` (bounds and
indices; also the examples' `10^100` and `10^100+7`). The terms most likely
to be misread:

- **revisit** — repetition of the position only; a repeated (position,
  heading) state is not required, and the defect example's repeat has a
  different heading from its earlier occurrence;
- **in P / polynomial** — for the first revisit only, in the explicit input
  model; the observation compiler has no polynomial bound;
- **periodic** — of a finite head-relative observation on a globally fresh
  run, never of the whole board;
- **certified domain** — observations after the first repeated arrival's
  departure are outside every statement.

## What is claimed, and what is not

The report claims conventional mathematical proofs of:

- the total first-revisit algorithm with exact output or a no-revisit
  certificate with periodic tail `1 ≤ L ≤ 4uv`, `0 ≠ δ ∈ uZ × vZ`, at most
  `(K+1)4uv` lanes, polynomial bit complexity (Theorem 2.2), via the static
  shadow (Lemma 3.1), the projected-permutation lemma (Lemma 3.2), the exact
  rank-2/1/0 intersection primitive (Proposition 4.1), event ownership and
  termination (Propositions 5.1, 5.2);
- the numerical and representation bounds `τ ≤ T*`, endpoints `≤ 2B`,
  intermediate bounds `U`, `M`, bit width `β`, coarse `O(N_in^7)`
  (Theorem 6.1, Section 6);
- exact first hit for the observation language (Theorem 7.1), with the
  one-atom projection (Lemma 8.1), the Boolean invariant (Lemma 8.2) and the
  finite exact-minimum bracket (Proposition 8.3); the original Presburger
  route via Cooper (Section 7.2) as a second, unexecuted effective proof;
- eventual `L·Q_obs`-periodicity of finite observations on a fresh run
  (Section 9);
- the examples `τ = 2·10^100 + 2`, first hit `2·10^100`, unseen-defect hit
  `2·10^100 + 14` (Section 10);
- Corollary 12.1 (no reduction through globally one-visit runs).

The report does **not** claim (article Sections 1, 6, 8–12, the delivered
README, `INTEGRITY.md`, the packet's notes, and the review):

- novelty or priority ("The report makes no novelty assertion"; "A limited
  source search is evidence about what was inspected, not a priority proof");
- any polynomial bound for the observation compiler's Boolean expansion or
  for general Presburger elimination; T* does not bound observation first-hit
  times; `U`, `M` are not bounds for arbitrary externally supplied lanes;
- anything about post-revisit dynamics, physical halting of an ordinary ant,
  whole-board translation periodicity, a completed literal two-visit
  universal atlas, input loader or accepting port, or a sharp one/two-visit
  threshold;
- that colour reconstruction holds after the departure at `τ` (the strict
  first-arrival boundary);
- the succinct-tile input model;
- that `first_hit` authenticates a hand-forged or mismatched result, or any
  property of arbitrary mutated Python objects or injected signed
  coefficients;
- that tests prove the theorems: "Tests supplement the proofs"; finite
  prefixes cannot establish infinite nonoccurrence; the complexity review's
  10,000 random bound checks (seed 301003) are historical, not replayable
  and not a premise; replay checks are "strong finite evidence, not machine
  checked proofs";
- that hash verification, test replay and proof validity substitute for one
  another; a hash manifest is not a digital signature; the verifier is "not
  an OS sandbox";
- turmite universality itself (third-party, cited);
- that the Kracht (2002) Presburger exposition read by the source audit is
  usable as an algorithm specification (the audit records reversed bounds
  in its bounded-interval display; it is not cited by the article).

## Relation to neighbouring reports and to the formal project

This report is in the collection's `hilbert-tenth-problem` category, filed
there rather than in `automata-and-formal-languages` because its comparison
targets are the programme's turmite-interface notes and the programme
reviewed it and derived a Diophantine component lead from it.

- **The programme's research tree** (read-only for this report). The notes
  `Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md` (line 394: "choose
  the exact macro-pattern whose occurrence is equivalent to simulated
  halting") and `Papers/1980/EXPLORATION_TOGGLE_ROUTER_UNIVERSALITY.md`
  (line 128: "identifying an actual simulated halt event" as an additional
  compiler obligation), both under `Computability/HilbertTenthProblem/`,
  are answered **only from the negative side**: by Corollary 12.1 such an
  event cannot be read, in the report's observation language, on globally
  one-visit runs, so it must use revisits (as Maldonado et al.'s at most two
  visits do). The report constructs no such event and leaves the notes'
  174-operation count untouched. The source audit read only lines 1–95 of
  the toggle-router note; the line-128 relation is the write's. The
  programme index (`Computability/HilbertTenthProblem/README.md`) still lists
  first-hit minimality and an ordinary-input universal loader as unpaid; the
  review recorded the universal-operation frontier as unchanged, and the
  later record of 84 operations (`20aafb9a5`) does not use this report.
- **[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)**:
  Research Report 35 (batch-83 manuscript 07), placed as source 22 of its
  Part XX (prefix `22-literal-sandpiles-`, labels `cdc:lp:`, placement
  `216bd81e1`), supplies for abelian sandpiles the literal periodic
  background, finite input loader and halting-equivalent acceptance event
  that this report's open question 3 asks for turmites. No shared theorem.
- **`five-particle-binary-automata`, `signal-machine-collision-certificates`**:
  other discrete-dynamics substrates of the category; they cite related work
  of Gajardo and Maldonado on cellular automata and pebble automata, not
  turmites. No shared theorem. No other collection report treats turmites,
  Langton's ant or first revisits.
- **Report 37** (batch-83 manuscript 09, placed in the same commit as Part V
  of `fixed-universal-polynomials`): no relation.
- **The formal project.** **Placement beside a Lean/Rocq development confers
  no formal status**; no statement of this report is formalized. The
  standard theorem it invokes in Section 7.2, decidability of Presburger
  arithmetic by Cooper's quantifier elimination, is formalized in
  `Logic/PresburgerArithmetic`: Lean
  `PresburgerArithmetic.Formula.presburgerArithmetic_decidable` and
  `PresburgerArithmetic.Formula.holds_iff_quantifierEliminate`
  (`Lean/PresburgerArithmetic/Decision.lean`), and an independent Rocq proof
  of the one-variable step, `cooper_finite_criterion` and
  `cooper_step_decidable` (`Coq/Cooper.v`). The report's executable route
  avoids it.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
mathtools, microtype, booktabs, array, longtable, enumitem, fancyhdr, float,
graphicx, hyperref, xurl). The committed build has 26 pages (the delivered
PDF had 21): no errors, no warnings, no undefined references or citations,
no multiply defined labels, no duplicate destinations, no overfull or
underfull boxes. **Do not run `code/build_pdf.py` here**: it rebuilds the
delivered `Research_Report38.tex` against the delivered PDF's bytes.

## Rerunning the programs

The delivered verifier (`code/verify_release.py`) checks POSIX file modes,
the delivered layout and the unshipped checksum files; it refuses to run on
NTFS and on this tree. Two routes:

1. **Full release replay**: re-extract the archive of the arrival commit
   (command above) on a POSIX host, outside the repository, and follow its
   `README.md` there.
2. **The mathematical programs directly**: copy the six pinned active
   programs to a scratch directory outside the repository under their
   delivered names, and run them there (`py` is the Python launcher on this
   machine; any Python ≥ 3.10, standard library only):

```sh
R=SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits
W=/path/outside/the/repository/r38; mkdir -p $W
for f in one_visit observations test_boundary_regression test_observations independent_checks example; do
  cp $R/code/source-packet-$f.py $W/$f.py; done
norm() { tr -d '\r' | sed -E "s/^Ran ([0-9]+) tests in [0-9.]+s$/Ran \1 tests in X/"; }
(cd $W && py -B -m unittest -v test_boundary_regression test_observations > a.out 2> a.err
          py -B independent_checks.py > i.out 2> i.err
          py -B example.py > example.json)
cat $W/a.out $W/a.err | norm | cmp - <(norm < $R/data/source-packet-author-normal.log)
cat $W/i.out $W/i.err | norm | cmp - <(norm < $R/data/source-packet-independent-normal.log)
tr -d '\r' < $W/example.json | cmp - $R/data/source-packet-example-result.json
# repeat with `py -B -O` against the *-optimized.log files
```

Keep stdout and stderr in separate files and concatenate them stdout first:
that is the order of the frozen `.log` files (the release verifier does the
same); a single combined redirect interleaves them differently. The `.txt`
twins of the independent logs record a second run with stderr first. On
Windows the outputs have CRLF line endings, hence the `tr`. At the write
(Windows, Python 3.14.4) all three runs passed in both modes (author tests
about 23 s, independent checks about 17 s), and all six comparisons were
equal after the elapsed-time normalization. The historical programs in
`boundary-context` and the packet's own `verify_release.py` are inert by
design and need not be run; the latter writes its receipt to a directory
of the caller's choice, so never point it into this tree.

## Discrepancies and disclosures

- `data/verification-release-review.json` approves the delivered 21-page
  PDF and the delivered TeX (SHA-256 `d81bc308…`), not this report's
  `article.tex` and 26-page `article.pdf`.
- `code/seal_release.py` rewrites `MANIFEST.json`, `SHA256SUMS` and the
  `MANIFEST_SHA256` line of `verify_release.py` in place; `data/MANIFEST.json`
  records `verify_release.py` with that line zeroed (the documented
  normalized self-pin; 44 of its 45 entries match raw bytes, the 45th after
  normalization). Never run it here.
- The delivered README's replay, PDF and ZIP commands
  (`python -I -B verify_release.py --replay …`, `build_pdf.py`,
  `archive_release.py`, `tamper_regression.py`, `archive_regression.py`)
  assume the delivered layout; they are summarized here, not reproduced.
- The article's Section 11.2 and Appendix A describe the delivered layout;
  `[write]` notes give the shipped names.
- Delivered author wording kept: "Mathematical research report" on the title
  page; the PDF metadata author is empty.
- The archive ships no licence file; the repository's MIT-0 default applies
  to the delivered text and code. Maldonado et al. and Cooper are cited, not
  redistributed; no third-party file is shipped.
