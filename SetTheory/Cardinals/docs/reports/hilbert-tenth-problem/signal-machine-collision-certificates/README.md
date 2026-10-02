# Collision Geometry Is Linear

**Diophantine Certificates for Rational Signal Machines: event-sparse chambers, canonical quadratic and quartic certificates, and two routes to complete chronology**

This is a research report dated 2 October 2026, built from two manuscripts
of batch 78 of ProveIt's incoming reports. Both are AI-assisted research
manuscripts: source 07 is "prepared with ChatGPT for Vladimir Reshetnikov's
ProveIt research program", and source 11's document metadata name "Research
report prepared with OpenAI". They are called *source 07* and *source 11*
after their batch-78 manuscript numbers, which are also the file prefixes of
their shipped programs and data.

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 07 (base) | batch 78, manuscript 07 | `Collision_Geometry_Diophantine_Signal_Machines.zip` (`808b53ed8`); *Collision Geometry Is Linear: Event-Sparse Quadratic Diophantine Certificates for Rational Signal Machines*, main file `collision_geometry/article.tex`, 29-page PDF | `f1edb38f9` (audit blob `cb31d0a10`) | `798b0c5d4` | Part I (Sections 2–16) and Appendices A–B |
| 11 | batch 78, manuscript 11 | `Signal_Machine_Diophantine_Certificates.zip` (`808b53ed8`); *Direct Diophantine Certificates for Rational Signal Machines: Finite collision schemas with unique quadratic witnesses*, main file `signal-diophantine-release/article.tex`, 15-page PDF | none named | `798b0c5d4` | Part II (Sections 17–28) and Appendices C–D |

**The two sources prove one theorem by two routes.** Once a complete finite
collision history of a rational signal machine is fixed, its realizations are
exactly the natural zeros of a sum of squares of integer affine residuals, of
degree two, with exactly one witness tuple per realization. Both use typed
endpoint conditions on maximal adjacency intervals and causal-depth
denominators. Source 07 eliminates every event coordinate (a linear chamber in
the initial gaps, slack witnesses only, signed rational speeds); source 11
keeps batch times and event positions as natural witnesses on a fixed grid
and adds halting semantics. The texts are independent (neither cites the
other). Both are printed in full; Section 1.2 compares the routes (Table 1).

**Status: AI-assisted, unrefereed, not formalized.** Conventional proofs and
finite exact-arithmetic checks. Nothing in the report is formalized in Lean or
Rocq, and no priority is certified.

**Already reviewed.** Both manuscripts were reviewed in the
Hilbert-tenth-problem research tree before this report was written:
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_substrate_review_808b53ed8.md`
and its signal-machine part `incoming_signal_review_808b.md` (commit
`126028588`, with replay script and receipt beside them). That review passed
both reports' stated theorems and examples and proved two certificate-size
reductions that neither source claims (Section 1.4). This intake is not a
first review.

```
article.tex                                                     the report, standalone LaTeX with an internal bibliography
article.pdf                                                     the compiled report, 59 pages (unnumbered title page, then pages 1–58)
README.md                                                       this guide
07-collision-geometry-PROVENANCE.md                             source 07's repository and literature provenance, as delivered
11-signal-certificates-REPRODUCIBILITY.md                       source 11's reproducibility record, as delivered
code/07-collision-geometry-Makefile                             source 07's make targets: test (run_checks.py) and pdf (latexmk)
code/07-collision-geometry-run_checks.py                        source 07's 34,560-assertion regression suite (imports signal_certificates; rewrites data/)
code/07-collision-geometry-signal_certificates.py               source 07's exact simulator, chamber compiler, quartic union (standard library)
code/11-signal-certificates-build.sh                            source 11's three-pass pdflatex build of its own article (delivered layout)
code/11-signal-certificates-run_replay.py                       source 11's isolated replay runner and receipt comparison
code/11-signal-certificates-signal_geometry.py                  source 11's exact simulator, full-layer compiler, rank calculation and checks
code/11-signal-certificates-signal_sparse.py                    source 11's sparse event-coordinate compiler and checks
code/11-signal-certificates-verify_additional.py                source 11's separately seeded edge cases and sharp height checks
code/11-signal-certificates-verify_examples.py                  source 11's worked-example and convention checks
data/07-collision-geometry-checks.json                          source 07's recorded run: PASS, 34,560 assertions, test counts and ledgers
data/07-collision-geometry-first_hit_quartic_union.json         the two-chamber first-hit quartic (all matrices and the selector formula)
data/07-collision-geometry-simultaneous_two_sites.json          the simultaneous two-site certificate (Section 11.3)
data/07-collision-geometry-tournament_left.json                 the tournament chamber AB (Section 11.1)
data/07-collision-geometry-tournament_right.json                the tournament chamber BC
data/07-collision-geometry-tournament_triple.json               the tournament chamber ABC
data/07-collision-geometry-zeno_clock_24_batches.json           the 24-batch prefix of the four-speed clock (Section 12)
data/11-signal-certificates-expected-additional_verification_receipt.json  expected receipt: 506 fixtures, 878 certificates, 2,152 growth checks
data/11-signal-certificates-expected-signal_geometry_receipt.json          expected receipt: 122 full-layer certificates, 4,229 mutations, 625 tuples
data/11-signal-certificates-expected-signal_sparse_receipt.json            expected receipt: 444 sparse certificates, 3,982 lifetimes, 10,102 mutations
data/11-signal-certificates-expected-worked_examples_receipt.json          expected receipt: the worked examples and 64 shuttle batches
data/11-signal-certificates-manifest.json                       source 11's build/replay manifest with payload hashes, as delivered
data/11-signal-certificates-signal_geometry_examples.json       full-layer coefficient dictionaries and witnesses
data/11-signal-certificates-signal_sparse_examples.json         sparse coefficient dictionaries and witnesses
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md`
is byte-identical to the delivery. Delivered name → shipped name:

- Source 07 (`collision_geometry/`): `Makefile`, `code/run_checks.py`,
  `code/signal_certificates.py` → `code/07-collision-geometry-*`;
  `data/*.json` (seven files) → `data/07-collision-geometry-*.json`;
  `PROVENANCE.md` → `07-collision-geometry-PROVENANCE.md`; `article.tex` →
  the base of `article.tex` (Part I); `README.md` → replaced by this README.
- Source 11 (`signal-diophantine-release/`): `build.sh` and `scripts/*.py`
  → `code/11-signal-certificates-*`; `examples/*.json` and `manifest.json`
  → `data/11-signal-certificates-*.json`; `expected_receipts/*_receipt.json`
  → `data/11-signal-certificates-expected-*_receipt.json`;
  `REPRODUCIBILITY.md` → `11-signal-certificates-REPRODUCIBILITY.md`.

Not shipped: source 11's manuscript (`article.tex`, printed as Part II),
both PDFs, source 11's delivered README (this text and `article.tex` replace
it), and both checksum ledgers (source 07's `SHA256SUMS`, 14 of 14 files,
and source 11's `CHECKSUMS.sha256`, 17 of 17, both verified at placement).
They survive in the archives of the arrival commit:

```sh
git show 808b53ed8:docs/incoming/Collision_Geometry_Diophantine_Signal_Machines.zip > cg.zip
git show 808b53ed8:docs/incoming/Signal_Machine_Diophantine_Certificates.zip > sd.zip
```

## Labels and numbering

Every label carries the prefix `smc:`. Source 07's 66 labels are `smc:cg:`
plus their delivered names, and source 11's 26 are `smc:sd:` plus theirs; no
source label was dropped or renamed apart from the prefix. The merge added 51
labels, 143 in all: thirteen `smc:` labels of the front section, the two
Parts and the provenance appendix (`smc:sec:front`, `smc:sec:parts`,
`smc:sec:routes`, `smc:tab:routes`, `smc:sec:notation`, `smc:tab:notation`,
`smc:sec:relation`, `smc:sec:status`, `smc:sec:questions`,
`smc:tab:questions`, `smc:part:cg`, `smc:part:sd`, `smc:app:provenance`);
fifteen `smc:cg:` labels (`lem:endpoint` on source 07's unlabelled endpoint
lemma, `sec:simultaneous`, nine `q:*` on its research directions,
`sec:conclusion`, `app:dependency`, and the two new remarks `rem:singlefold`
and `rem:credit`); and twenty-three `smc:sd:` labels (sixteen `sec:*` on
source 11's sections and subsections, `cor:hessian`, five `q:*` on its
questions, `app:sources`).

Each Part keeps its source's numbering of statements, by section: source
07's Section *n* is Section *n* + 1 here (Sections 2–16), so its Theorem
*n.m* is Theorem (*n* + 1).*m*; source 11's Section *n* is Section *n* + 16
(Sections 17–28). Source 07's two appendices are Appendices A–B, source 11's
are C–D; Appendix E is the provenance. Equations are numbered by section in
both Parts (source 07 numbered them consecutively). Text written in the merge
is marked `[write]`; text without a marker is the source's own.

## Setting and notation

A rational signal machine has finitely many labels, each moving at a fixed
rational speed on a line; a collision consumes its incoming signals and emits
a rule-determined set. A *skeleton* (Part I) or *schema* (Part II) fixes the
ordered batches of simultaneous collisions; a *site* of Part I is an *event*
of Part II. Each Part keeps its source's letters; Table 2 (Section 1.3) lists
every letter used in both. The ones most likely to be misread:

- `B` — Part I: number of batches; Part II: the grid modulus `B = D^K`, **not**
  a number of batches.
- `K` — Part I: `2 + 4V`, and the number of first-hit chambers; Part II: the
  number of batches.
- `D` — the same lcm of nonzero speed differences in both (Part I after
  scaling time by `L`, Part II after a Galilean shift and a scaling by `m`;
  with `m = L` they coincide).
- `L`, `m`, `p`, `q`, `r`, `s`, `R`, `T`, `W` — Part I: speed-clearing
  integer, number of distinct speeds, in/out counts at a site, retained
  equality/strict rows, raw row count, site budget, `3u + 2v`; Part II:
  number of lifetimes, speed multiplier, initial positions, position scale,
  largest arity/fanout, residual count, batch times, number of witnesses.
- **Sparse** — Part I counts conditions (rows may be dense in the gaps);
  Part II's residuals also have bounded width. Neither is an
  arithmetic-operation count.
- **Convex** — Part I's certificate is convex jointly; Part II's is
  *strictly* convex in the witnesses with the input fixed.

No symbol was renamed in the printed text and no normalization changed.
Source 11's TeX macro `\N` is `\NN` in this file because source 07's `\N`
prints `ℕ₀`; both print `{0, 1, 2, …}` as their sources did. Source 11's
bibliography keys `DL09` and `GS66` are cited as source 07's `durandlose` and
`ginsburgspanier` (merged entries).

## Status: what is claimed, and what is not

The report claims conventional mathematical proofs, by its sources, for:

- **The common theorem** (Part I, Theorems 5.3 and 6.1; Part II, Theorem
  18.3): for a fixed machine, initial label word and finite skeleton or
  schema, an effective sum of squares of integer affine residuals of degree
  at most two whose natural zeros are exactly the realizations, with a unique
  witness tuple; typed adjacency-interval endpoints exclude unrecorded
  earlier collisions, omitted simultaneous inputs and omitted simultaneous
  sites.
- **Part I (source 07).** The realizing gap vectors form a relatively open
  rational polyhedral cone with at most `3(n−1) + (3m+1)E` raw conditions;
  the certificate `‖Eg‖² + ‖Gg − 1 − z‖²` with unique slacks; causal-depth
  denominators `D^h` and row heights `2d(1+V)(DK)^h`; a positive integer
  realization of size at most `d^{d/2} A^d`, and real = rational = integer
  realizability; an NP upper bound for bounded synthesis; a certified
  perturbation radius and codimension `rank E`; finite-horizon semilinearity;
  a canonical first-hit quartic with unique selector and slacks; exact
  Ehrhart quasi-polynomial seed counts with rational density; the
  first-collision tournament (`C(H) = ⌊(3H² + 1)/4⌋`, its generating function
  and inverse); a four-speed accumulating clock with denominators exactly
  `2·3^k`; and a convex-quadratic rigidity theorem and compression barrier.
- **Part II (source 11).** The same theorem with batch times and event
  positions as natural witnesses on the grid `D^K`, in prefix and halting
  versions; full column rank of the witness matrix (strict convexity in the
  witnesses); `W ≤ (2s+5)E + 3n₋` and `R ≤ (r+2s+3)E + 3n₋`; a full-layer
  reference construction with exact counts; the canonical-witness height
  bound `60^K max(1, M₀)` for the four-speed interface `{0, 2, 3, 4}` of
  Durand-Lose's universal machine; a bounded shuttle with denominators
  exactly `3^{k−1}`; semilinearity of fixed-schema inputs; positive-witness
  translation.

**Credit (Remark 13.3).** Part I's convex-quadratic rigidity theorem and
compression barrier (Theorem 13.1, Corollary 13.2) are a special case of Part
XI of `canonical-diophantine-certificates` (`cdc:of:lem:affinezero`,
`cdc:of:thm:cubicsemilinear`, `cdc:of:thm:classification`: degree ≤ 3,
nonnegative only on the orthant, `D⁺₂ = D⁺₃ = SL`), which source 07 does not
cite. They are printed with source 07's direct proof as a second route; no
novelty is claimed. Remark 10.3 relates the first-hit quartic to that Part's
single-fold orthant-nonnegative quadratic for semilinear sets
(`cdc:of:thm:singlefoldsl`).

The report does **not** claim:

- historical priority or exhaustive novelty (both sources say so); a general
  linearizability of signal-machine evolution, which source 11 attributes to
  Durand-Lose's linear real-register simulation;
- one fixed-arity polynomial for unbounded halting, a single-fold or
  finite-fold Diophantine representation of c.e. sets, or any improvement of
  the repository's 75- and 87-operation bounds; the skeleton or schema is
  compiler data, and row or residual counts are not operation counts;
- that the published universal machine (13 meta-signals, 21 non-blank rules)
  or its input loader has been transcribed, executed or certified;
- any semantics at or after an accumulation point; that the clock discovers
  accumulation;
- NP-hardness, an efficient first-hit enumerator, or that the denominator
  examples bound arbitrary Diophantine representations (Part II's is a lower
  bound for common-grid encodings);
- that integer scaling of a rational seed keeps a prescribed physical length
  or deadline;
- that the finite checks are exhaustive, or that Part II's two compilers are
  independent (they share a simulator); the code is not a verified compiler
  and source 11's low-level compilers are not hardened parsers;
- novelty for the reductions of the programme's review, which are the
  review's;
- any Lean or Rocq verification.

## Relation to neighbouring reports and to the formal project

This report is in the collection's `hilbert-tenth-problem` category, as a
substrate with low-degree Diophantine certificates; nothing in the repository
treated signal machines before batch 78 apart from the review below.

- **[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)**,
  Part XI: the credit above. Its Part IX proposition `cdc:bd:prop:nobound` is
  the bounded-search argument that Part I uses for a different statement.
- **[`liveness-beyond-halting`](../liveness-beyond-halting)**, Part V: the
  question of its source 11 "Optimal degree under stronger geometric
  restrictions" mentions the "rigid affine geometry" of globally nonnegative
  quadratics; Part I's Theorem 13.1 states that geometry. The question is
  not settled here.
- **[`quadratic-orthant-certificates`](../quadratic-orthant-certificates)**
  (dated note of 2 October 2026, batch 78H3; that report was opened by
  cluster H3 of batch 78 and written in `c51b9880d`): the same format
  family, no shared theorem. Its three Parts compile fixed finite systems
  (maximal-parallel multiset rewriting, timed irreversible races, a fixed
  universal Waterfall program) into one integer polynomial of degree two of
  the form `Σ A_i² + Σ B_j C_j`, with affine `A_i` and with factors `B_j`,
  `C_j` that have nonnegative coefficients, so that it is nonnegative on the
  whole real orthant (its section `qoc:sec:spine`). The common theorem here
  is the case without product terms, a sum of squares of integer affine
  residuals. Both reports therefore sit at the level `D⁺₂ = SL` of
  `cdc:of:thm:classification`, which is why a fixed skeleton, schema or
  horizon gives semilinear projections in both; this report's first-hit
  quartic and that report's degree-four variants lie outside the format.
  The products are where the two differ: that report uses them for
  negative conditions (maximality, earliest completion, inactive
  directions), and its Theorem `qoc:mp:thm:convexno` shows that already the
  deadlock of `A + B → C` has no convex quadratic certificate, whereas the
  sums of squares here are convex. That report names this one in its
  relation section (`qoc:sec:relation`); neither report re-proves a theorem
  of the other.
- **[`probabilistic-quantum-and-continuous-computation`](../probabilistic-quantum-and-continuous-computation)**
  and **[`group-theoretic-substrates`](../group-theoretic-substrates)**: no
  overlap.
- **The Hilbert-tenth-problem research programme** (read-only for this
  report), `Computability/HilbertTenthProblem/Papers/`:
  - `research-wip/native-stream-queue/incoming_substrate_review_808b53ed8.md`
    and `incoming_signal_review_808b.md` (commit `126028588`): the prior
    review of both manuscripts. PASS, no mandatory correction; its Transfer A
    deletes source 11's identically zero same-birth rows and redundant
    same-death rows and erases the initial-order slacks when `K > 0` or
    halting (the worked annihilation goes from 6 residuals and 5 witnesses to
    4 and 4; a natural-integer, not nonnegative-rational, zero-set bijection);
    its Transfer B deletes redundant strict rows from source 07's five
    exported packets. Neither is printed in this report.
  - `1980/REVERSIBLE_FINITE_HISTORY_MODELS.md`: cited by source 07 (blob
    `cb31d0a10`, unchanged at the write).
  - `1980/EXPLORATION_BINARY_BLOCK_CA_AUDIT.md`: notes that finite particles
    "can in principle store unbounded values in their separation" and that a
    new construction would have to establish that interface. Signal machines
    are a candidate (Durand-Lose's halting construction has a finite initial
    configuration), but this report transcribes neither the universal table
    nor a loader, so it does not establish that interface.
- **The formal project.** The report sits in the collection, not in
  `Computability/HilbertTenthProblem`, and **placement beside a Lean/Rocq
  development confers no formal status**. Both sources use MRDP only as an
  imported classical theorem (source 07 cites Matiyasevich and the Isabelle
  AFP entry); the project's formal endpoint is `Diophantine.mrdp`,
  `Diophantine.mrdp_iff` and `Diophantine.mrdp_dioph_iff`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, lines 33,
  42, 26). The project has formalized none of this report's statements: its
  Lean development has no signal-machine, collision-chronology or
  polyhedral-chamber module. The project README
  (`Computability/HilbertTenthProblem/README.md`, line 16) still states the
  75- and 87-operation bounds; neither Part bears on them.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
mathtools, microtype, booktabs, longtable, ragged2e, xcolor, TikZ, enumitem,
fancyhdr, listings, xurl, hyperref). The committed build has 59 pages: no
errors, no undefined references or citations, no multiply defined labels,
no duplicate destinations, no overfull boxes. The log's only box messages
are three underfull lines in the bibliography entry `reversible`, which the
delivered source 07 already produces.

## Rerunning the programs

Both suites import their companion modules by their delivered names, and
source 07's rewrites its seven JSON files in place, relative to its own
directory's parent. **Never run them in place.** Copy the files to a scratch
directory with the delivered layout (`py` is the Python launcher on this
machine; the delivered texts say `python` or `python3`; Python 3.10 or
newer, standard library only, assertions enabled):

```sh
R=SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates
# source 07
mkdir -p r07/code r07/data
cp $R/code/07-collision-geometry-run_checks.py r07/code/run_checks.py
cp $R/code/07-collision-geometry-signal_certificates.py r07/code/signal_certificates.py
(cd r07 && py code/run_checks.py)        # rewrites r07/data/*.json (7 files)
# source 11
mkdir -p r11/scripts r11/examples r11/expected_receipts
for s in run_replay signal_geometry signal_sparse verify_additional verify_examples; do
  cp $R/code/11-signal-certificates-$s.py r11/scripts/$s.py; done
for e in signal_geometry signal_sparse; do
  cp $R/data/11-signal-certificates-${e}_examples.json r11/examples/${e}_examples.json; done
for r in additional_verification signal_geometry signal_sparse worked_examples; do
  cp $R/data/11-signal-certificates-expected-${r}_receipt.json r11/expected_receipts/${r}_receipt.json; done
(cd r11 && py scripts/run_replay.py --output out)   # writes r11/out/
```

At the write (Windows, Python 3.14.4, `PYTHONUTF8=1`) both passed. Source
07's suite reported PASS with 34,560 assertions in about 4 s, and its seven
regenerated JSON files equal the shipped ones apart from line endings: the
Windows run writes CRLF, the shipped files are LF. Source 11's replay (about
18 s) matched all four expected receipts and both coefficient-example files;
it runs the scripts in a temporary directory and writes only its output
directory. The placement-time runs (12.7 s and 39.2 s) and the programme's
review (Python 3.13.14) agree. Running source 11's individual scripts
directly writes their receipts into the current directory.

## Discrepancies and disclosures

- The shipped `code/07-collision-geometry-Makefile` and
  `code/11-signal-certificates-build.sh` keep the delivered layout: the
  Makefile runs `python3 code/run_checks.py` and `latexmk` on `article.tex`
  from the package root, and `build.sh` changes to its own directory and
  runs pdflatex three times on an `article.tex` that is not there. Neither
  builds this report; use the build command above and the rerun recipe.
- Delivered names in shipped and printed text: Part I's Sections 14.1–14.2
  and Appendix A, Part II's Appendix C and source 11's `REPRODUCIBILITY.md`
  name delivered paths (`code/…`, `data/checks.json`, `tournament_left.json`,
  `scripts/…`, `examples/…`, `expected_receipts/…`, `build.sh`); `[write]`
  notes in Section 14.2 and Appendices A and C give the shipped names. Source 11's
  `REPRODUCIBILITY.md` describes `CHECKSUMS.sha256` and the delivered
  `article.tex` and `article.pdf`, and its `manifest.json` lists the
  delivered `README.md`, `article.tex` and `article.pdf` among its payload
  files; none of these is shipped under that name (the map above). Source
  07's `PROVENANCE.md` names no package file.
- Source 11's `manifest.json` author fields read "Jérôme Durand-Lose" in
  correct UTF-8 (bytes `C3 A9`, `C3 B4`); a placement note that suspected
  double-encoded UTF-8 there was checked at the write and is unfounded (a
  console that decodes UTF-8 as a legacy code page displays it garbled).
- Source 07 records its repository snapshot `f1edb38f9` and the audit blob it
  read; the audit is unchanged at the write, and the project README has gained
  text since the pin while still stating the 75/87 bounds. Source 11 names no
  repository snapshot.
- The delivered title pages are replaced by one; each source's title, author
  line, abstract and keywords open its Part verbatim. Credit notes were added
  to source 07's abstract and conclusion, marked `[write]`.
- AI wording kept as delivered: source 07 "prepared with ChatGPT", source 11
  "Research report prepared with OpenAI" (PDF metadata only).
