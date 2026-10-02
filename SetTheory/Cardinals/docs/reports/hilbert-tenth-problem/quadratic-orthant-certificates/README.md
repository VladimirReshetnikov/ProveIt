# Quadratic Orthant Certificates

**Maximal parallelism, timed irreversible races and a fixed Waterfall universal machine: degree-two Diophantine certificates, nonnegative on the real orthant, with negative and selection conditions**

This is a research report dated 2 October 2026, built from three manuscripts
of batch 78 of ProveIt's incoming reports (cluster H3). All three are
AI-assisted research manuscripts. They are called *source 08*, *source 12*
and *source 14* after their batch-78 manuscript numbers, which are also the
file prefixes of their shipped programs and data.

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 08 (base) | batch 78, manuscript 08 | `Maximal_Parallel_Diophantine.zip` (`808b53ed8`); *Quadratic Certificates for Maximal Parallelism: Exact witnesses, sharp growth bounds, and a convexity obstruction*, main file `article.tex`, 25-page PDF; "Research manuscript prepared for Vladimir Reshetnikov", "Developed with ChatGPT" | `db3b377f0` (its search results also showed the older `4cccfa068`) | `41e7f1189` | Part I (Sections 2–16) and Appendices A–C |
| 12 | batch 78, manuscript 12 | `Total_Quadratic_Diophantine_Semantics.zip` (`808b53ed8`); *Total Quadratic Semantics for Irreversible Computation: Exclusive sites, timed self-assembly, and Horn closure without execution histories*, main file `article.tex`, 25-page PDF; "Research prepared for Vladimir Reshetnikov", "Developed with ChatGPT" | `db3b377f0` | `41e7f1189` | Part II (Sections 17–29) and Appendices D–E |
| 14 | batch 78, manuscript 14 | `Waterfall_Diophantine_Certificates.zip` (`24a743255`); *Quadratic Diophantine certificates for a fixed Waterfall universal machine*, main file `paper/waterfall-diophantine.tex` with `paper/affine-gap-table.tex`, 16-page PDF; "Research note prepared with AI assistance for private review" | none (the manuscript names no ProveIt commit) | `41e7f1189` | Part III (Sections 30–38) and Appendices F–G |

Every result, proof, example, remark, research question and limitation of
the three manuscripts is printed. They are not versions of one manuscript
and share no theorem (word 8-gram overlap between 08 and 12 is about 0.5 %,
all boilerplate); none cites another. What they share is one *format*: a
fixed finite system is compiled into one integer polynomial
`P = Σ A_i² + Σ B_j C_j` (affine `A_i`; affine `B_j, C_j` with nonnegative
coefficients), of total degree two, nonnegative on the whole real
nonnegative orthant, whose natural zeros are in bijection with the
semantic objects, and whose unsquared products encode a condition that
balance equations cannot: maximality of a parallel round (Part I), earliest
completion with label priority and certified absence (Part II), and the
strict-minimum events of a fixed Waterfall program compressed into exact
macrosteps (Part III). Section 1 of the article states this spine once,
places it at the level `D⁺₂ = SL` of the degree classification proved in
Part XI of
[`canonical-diophantine-certificates`](../canonical-diophantine-certificates),
and gives tables of notions and letters.

**Status: AI-assisted, unrefereed, not formalized.** Priority is not
certified for any Part. Nothing in the report is formalized in Lean or
Rocq.

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 87 pages (unnumbered title page, then pages 1–86)
README.md                                            this guide
08-maximal-parallel-PROOF_AUDIT.md                   source 08's proof and scope audit, as delivered
08-maximal-parallel-SOURCE_AUDIT.md                  source 08's source audit (repository pin, literature), as delivered
12-total-quadratic-SOURCE_AUDIT.md                   source 12's source audit and claim boundary, as delivered
14-waterfall-LICENSE-PROVENANCE.md                   source 14's licence and provenance statement, as delivered
14-waterfall-SOURCE-PROVENANCE.md                    source 14's provenance of the machine data and primary paper, as delivered
code/08-maximal-parallel-parallel_certificates.py    source 08's exact-integer compiler, evaluator, canonical witnesses, rank and counting routines
code/08-maximal-parallel-verify.py                   source 08's deterministic validation (imports parallel_certificates)
code/12-total-quadratic-build.sh                     source 12's three-pass pdflatex script (delivered layout; see below)
code/12-total-quadratic-quadratic_compiler.py        source 12's event simulator, total and Horn compilers, witness constructor, exporter
code/12-total-quadratic-test_compiler.py             source 12's exhaustive small-instance and regression tests (imports quadratic_compiler)
code/12-total-quadratic-verify_exports.py            source 12's independent re-expansion of the exported polynomials
code/14-waterfall-build.sh                           source 14's PDF build script (delivered layout; see below)
code/14-waterfall-run-replay.sh                      source 14's one-command replay of the eight programs below
code/14-waterfall-verify_matrix_definition.py        rebuilds the compact matrix definition and checks all 2,116 entries
code/14-waterfall-verify_frontend.py                 the 58 macrosteps by 43,065 affine strict-minimum inequalities (64 forms)
code/14-waterfall-verify_frontend_independent.py     the same macrosteps by a second loop parameterization, plus concrete runs
code/14-waterfall-grouped_quadratic.py               builds the 35k-witness quadratic and evaluates the seven-step fixture
code/14-waterfall-verify_quadratic_independent.py    independent formula evaluation from the source machine table
code/14-waterfall-verify_halting_example.py          direct event and countdown simulation of the seven-step example
code/14-waterfall-verify_certificates.py             the common-column class, ledgers and counterexamples
code/14-waterfall-verify_release.py                  cross-checks the receipts and the exported polynomial at its fixture
data/08-maximal-parallel-example_certificate.json    structured and expanded quadratic for A+B→C, A→B, with one witness
data/08-maximal-parallel-verification.txt            source 08's recorded validation run (Python 3.13.5; all PASS)
data/08-maximal-parallel-verification_counts.json    the same counts as JSON
data/12-total-quadratic-huge_delay_chain.json        exported polynomial: four rules with delays near 10^30 (45 witnesses)
data/12-total-quadratic-literal_four_tile_example.json  exported polynomial: the literal four-tile catalogue (58 witnesses)
data/12-total-quadratic-locking_counterexample.json  exported polynomial: the reduced locking example (29 witnesses)
data/12-total-quadratic-timed_race.json              exported polynomial: timed race and blocked cycle (85 witnesses)
data/12-total-quadratic-test_receipt.json            source 12's recorded test run (PASS; seed 20261002)
data/12-total-quadratic-export_verification.json     source 12's recorded export verification (4/4 PASS)
data/14-waterfall-UniversalTM15x2.tm.txt             Iijil's source transition table (third-party data, NOT MIT-0)
data/14-waterfall-UniversalTM15x2.twm.txt            Iijil's 46-clock Waterfall matrix serialization (third-party data, NOT MIT-0)
data/14-waterfall-affine-gap-forms.json              the 64 affine gap forms with activation bounds and multiplicities
data/14-waterfall-frontend-receipt.json              receipt of verify_frontend
data/14-waterfall-grouped-quadratic7-certificate.json  all residuals and product factors of the seven-step quadratic
data/14-waterfall-grouped-quadratic7-fixture.json    its 245 natural witnesses and four parameters
data/14-waterfall-grouped-quadratic-receipt.json     receipt of grouped_quadratic
data/14-waterfall-certificate-receipt.json           receipt of verify_certificates
data/14-waterfall-unit-ledgers.json                  the literal 22/26-operation ledgers of the three-clock instance
data/14-waterfall-matrix-definition.json             receipt of verify_matrix_definition
data/14-waterfall-independent-receipt.json           receipt of verify_frontend_independent
data/14-waterfall-quadratic-independent.json         receipt of verify_quadratic_independent
data/14-waterfall-halting-example.json               the full event and timestamp trace of the seven-step example
data/14-waterfall-release-verification.json          receipt of verify_release (PASS)
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md`
is byte-identical to the delivery. Delivered name → shipped name:

- Source 08 (inner directory `Maximal_Parallel_Diophantine/`):
  `code/*.py` → `code/08-maximal-parallel-*.py`; `data/*` →
  `data/08-maximal-parallel-*`; `PROOF_AUDIT.md`, `SOURCE_AUDIT.md` →
  `08-maximal-parallel-*.md`. Its `article.tex` was placed as this report's
  `article.tex` and is now Part I of the merged text; its `README.md` was
  placed as this README and is replaced by it.
- Source 12 (inner directory `total_quadratic_semantics/`): `code/*.py`
  and `build.sh` → `code/12-total-quadratic-*`; `results/*.json` →
  `data/12-total-quadratic-*.json`; `SOURCE_AUDIT.md` →
  `12-total-quadratic-SOURCE_AUDIT.md`.
- Source 14 (inner directory `waterfall-diophantine/`): `replay/*.py`,
  `run-replay.sh`, `build.sh` → `code/14-waterfall-*`; `replay/*.json` and
  `receipts/*.json` → `data/14-waterfall-*.json`; `source/*` →
  `data/14-waterfall-UniversalTM15x2.*`; `LICENSE-PROVENANCE.md`,
  `SOURCE-PROVENANCE.md` → `14-waterfall-*.md`.

Not shipped: the three PDFs; the manuscripts of sources 12 and 14 (printed
as Parts II and III; source 14's `paper/affine-gap-table.tex` is printed
as Appendix G and carries the same 64 forms as
`data/14-waterfall-affine-gap-forms.json`); the READMEs of sources 12 and
14; and the checksum ledgers of sources 08 (`SHA256SUMS.txt`, 10 of 10
verified at placement) and 14 (`SHA256SUMS`, 30 of 30). Source 12 shipped
no ledger. Nothing was excluded as heavy (the largest shipped file is
127,417 bytes). All of it survives in the arrival commits:

```sh
git show 808b53ed8:docs/incoming/Maximal_Parallel_Diophantine.zip > mpd.zip
git show 808b53ed8:docs/incoming/Total_Quadratic_Diophantine_Semantics.zip > tqs.zip
git show 24a743255:docs/incoming/Waterfall_Diophantine_Certificates.zip > wdc.zip
```

## Labels and numbering

Every label carries the prefix `qoc:`. Source 08's 73 labels are
`qoc:mp:` plus their delivered names, source 12's 40 are `qoc:ts:` plus
theirs, and source 14's 54 are `qoc:wf:` plus theirs; no source label was
dropped or renamed apart from the prefix. The merge added 22 labels, 189 in
all: fifteen of the front section, the three Parts and the provenance
appendix (`qoc:sec:front`, `qoc:sec:parts`, `qoc:sec:spine`,
`qoc:eq:spine`, `qoc:sec:conventions`, `qoc:tab:notions`,
`qoc:tab:letters`, `qoc:sec:gadgets`, `qoc:sec:reproofs`,
`qoc:sec:relation`, `qoc:sec:status`, `qoc:part:mp`, `qoc:part:ts`,
`qoc:part:wf`, `qoc:app:provenance`); six on unlabelled sections of
source 12 (`qoc:ts:sec:intro`, `qoc:ts:sec:selfassembly`,
`qoc:ts:sec:boundary`, `qoc:ts:sec:impl`, `qoc:ts:sec:future`,
`qoc:ts:app:ledger`); and `qoc:wf:sec:results` on source 14's first
section. The CDC report already uses the sub-prefix `cdc:wf:` (its
manuscript 04); it is unrelated to `qoc:wf:`. Bibliography keys carry
`mp:`, `ts:` or `wf:`; the credits added in the merge carry `w:`.

Each Part keeps its source's numbering by section: source 08's Section *n*
is Section *n* + 1 (Sections 2–16), source 12's is *n* + 16 (Sections
17–29) and source 14's is *n* + 29 (Sections 30–38); Theorem *n.m*
shifts the same way. Source 08's appendices A–C keep their letters, source
12's A–B are D–E, source 14's A–B are F–G, and Appendix H is the
provenance. Text written in the merge is marked `[write]`; text without a
marker is the source's own.

## Setting and notation

No symbol is renamed and no normalization changed; each letter keeps its
source's meaning inside its Part. Table 2 of the article lists the letters
the Parts use differently, among them `H` (Part I: species–threshold
pairs, a Hessian, an undecidable set; Part III: residuals and an input),
`M` (Part I: largest coefficient; Part II: the sentinel `S+1`; Part III:
the Waterfall matrix), `D` (retention diagonal / number of prerequisite
literals / direction), `L, R` (affine form / incidences and rules / half
tapes), `B`, `C`, `Q`, `q`, `T`, `W`, `τ`. Table 1 lists the words to read
carefully:

- **maximal** (Part I) is "no feasible one-copy extension", not maximum
  cardinality, and not CDC Part II's maximal commutation or Part XII's
  maximal repetition;
- **flat** (Part I) is flat maximality, unrelated to CDC's flat schemes;
- **rank** (Part I) is the cover rank `ρ(A)`, not CDC Part XI's
  first-arrival ranks or Part XIV's rank function;
- **history-free** (Part II) is CDC Part XIV's sense (outcome instead of
  history), not the sense of *Groups as Diophantine substrates*;
- **single-fold** (Parts II, III) is relative to a fixed catalogue or a
  fixed horizon, not the single-fold problem for all c.e. sets;
- **phase** (Part II) is a timing region; **clock** (Part III) is a
  Waterfall counter, not a computable clock of `liveness-beyond-halting`.

## Status: what is claimed, and what is not

The report claims conventional mathematical proofs, by its sources, for:

- **Part I (source 08).** One maximal parallel multiset-rewriting round as
  a quadratic nonnegative on the real orthant with `d+2m+4H` natural
  auxiliaries (extents included), `2d+2H+m` affine squares and `2H`
  products, zeros in bijection with maximal extents; histories with
  `T(2d+2m+4H)` and exact first halting with `T(2d+2m+4H+1)+4H+m`
  witnesses; guarded, flat (`d+3m+4H`), retaining and fixed-membrane
  variants and a guarded register-machine embedding; the uniform bound
  `O((1+|x|₁)^(m−ρ(A)))` on maximal extents, attained for every `A` along
  an integral ray; eventual quasipolynomiality of fixed-horizon counts with
  degree at most `T(m−ρ(A))`, sharp across systems; a parsimonious
  graph-to-network reduction and `#P`-completeness under Turing
  reductions; no convex quadratic for the deadlock of `A+B→C`; and a
  program-uniform quartic with degree four necessary in the orthant class.
- **Part II (source 12).** A unique capped causal fixed point for
  exclusive-site systems with positive integer delays; one quadratic per
  catalogue with exactly one natural zero for every delay vector, with
  exactly `m(2q+3)+3D+3(L+R₀)+R` witnesses; height and sparsity bounds;
  the Horn compiler with `m+3(L+R₀)+R`; the `37m`/`38m` fixed-candidate tile
  allocation; the four-tile locking counterexample; compatible-box
  uniqueness; the finite polyhedral timing decomposition, the `2^m`
  explicit-outcome lower bound and unbounded nonmonotone timing; an exact
  positive Horn simulation of Turing machines; and the permanent-absence
  obstruction with no computable grounding bound.
- **Part III (source 14).** The exact macrostep word and count
  `c = 6+3Q+r+3Y` of Iijil's fixed 46-clock Waterfall program on every
  input, proved by a finite affine certificate; the halt time
  `τ = 1+2C+7k`; the quadratic `F_k` with `35k` natural witnesses, `5k+4`
  squares and `2k` products whose fibre is empty or a singleton; the
  seven-step example (`C = 189`, `τ = 428`, 245 witnesses); semilinearity
  at fixed `k`; the decidable common-column class with a horizon-free
  `4n`-witness certificate; and the endpoint-count counterexample.

Several statements re-prove or generalize results of
`canonical-diophantine-certificates` Part XI, which sources 08 and 12 knew
only through its README and source 14 not at all. They are printed as
second routes, with `[write]` notes and the table of Section 1.5, and no
novelty is claimed for them: source 08's Lemma 12.1 (cubic semilinearity),
Corollary 12.2, Proposition 13.1, its MRDP-to-quartic paragraph and its
Euclidean penalty (`cdc:of:thm:cubicsemilinear`,
`cdc:of:cor:squares`, `cdc:of:cor:no-cubic-universal`,
`cdc:of:prop:quartic`, `cdc:of:eq:euclidean`); source 12's Theorem 19.2
generalizes `cdc:of:thm:ranks`, and its compatible-union lemma, batch
serialization and the second half of its absence theorem are
`cdc:of:prop:antimatroid`, `cdc:of:lem:closure` and
`cdc:bd:prop:nobound`; source 14's semilinearity proposition has a second
route through `cdc:of:thm:classification`.

The report does **not** claim:

- historical priority for any Part (all three sources searched the
  literature in a targeted, not exhaustive, way), peer review, or
  proof-assistant verification;
- a fixed-arity universal Diophantine equation, a solution of the
  single-fold or finite-fold representation problem, or an improvement of
  the repository's universal arithmetic-operation bounds (the 75- and
  87-operation figures at the sources' pins). Part III's quadratic is for a
  universal machine, but its arity grows with the horizon `k`, which is
  compiler data; Part II's unbounded direction is "there is a grounding
  size", outside every polynomial;
- that finite tests prove the all-input theorems (all three sources say
  their executable checks are implementation and regression checks);
- minimality of any witness count, of the 23-rule maximal-parallel system
  of Alhazov and Verlan, of the Neary–Woods machine or of Iijil's matrix;
- for Part I: efficient computation of `ρ(A)` (the shipped search is
  exponential), a rank theory for guarded systems, convex certificates in
  general, or that guarded/flat histories are implemented (only
  ordinary unguarded retaining histories are);
- for Part II: correctness for zero or negative delays, negative glues,
  inhibition, detachment, consumption, stochastic kinetics or multi-tile
  attachments; an enumeration of all nondeterministic outcomes; a new
  numerical universal tile set; or an improvement over the allocation of
  CDC Part XI (the interfaces differ);
- for Part III: optimality of `35k` or of the four-operation loader, any
  cost for encoding ordinary programs as half tapes, or that the
  universal machine, the matrix or its compiler are new.

## Relation to neighbouring reports and to the formal project

- **[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)**:
  Part XI (`cdc:of:`) classifies exactly the class this report lives in
  (`D⁺₂ = D⁺₃ = SL`, `D⁺₄ = CE`, `cdc:of:thm:classification`); see above
  for the re-proofs. Its Part XIII declines a maximal-parallel reading of
  its reaction networks and cites the same Alhazov–Verlan system; Part I
  supplies certificates for that convention. Part III bears on its
  questions `cdc:q:acceleration` (a canonical factorization preserved by
  the witnesses, realized for one fixed universal Waterfall program at
  each fixed horizon), `cdc:q:restricted` (the decidable common-column
  class) and Part XII's "Canonical macro decompositions" and "A small
  explicit fixed interpreter"; Parts I and II add data points to
  `cdc:q:degree`. None of these questions is answered in general.
- **[`liveness-beyond-halting`](../liveness-beyond-halting)**: Part I's
  guarded register-machine embedding (one round per instruction) appears
  to satisfy the hypotheses of `lbh:thm:transfer` with block length one,
  a partial answer to that report's question "Other unconventional
  substrates with timing certificates"; source 08 does not state this and
  the hypotheses were not checked in detail (`[write]` note in Section 7).
- **[`signal-machine-collision-certificates`](../signal-machine-collision-certificates)**
  (batch 78, cluster H2) uses the same family of degree-two certificates
  for rational signal machines. No theorem is shared.
- **[`group-theoretic-substrates`](../group-theoretic-substrates)**,
  **[`probabilistic-quantum-and-continuous-computation`](../probabilistic-quantum-and-continuous-computation)**,
  **[`stochastic-and-thermal-exactness`](../stochastic-and-thermal-exactness)**:
  no overlap.
- **The Hilbert-tenth-problem research programme** (read-only for this
  report), `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`,
  reviewed all three archives on the day they arrived (see "Reviews and
  patches" below). Its note `neary_woods_explicit_universal_tm.md`
  (added 1 October 2026, commit `f2622a68c`) transcribes the same
  Neary–Woods Table 16 as Part III, entry by entry, and reports the same
  `(u10,b)`/`(u10,c)` inconsistency in the primary paper; source 14 found it
  independently, and the report credits the note.
- **The formal project.** The report sits in the collection, not in
  `Computability/HilbertTenthProblem`, and **placement beside a Lean
  development confers no formal status**. Sources 08 and 12 use MRDP only
  as a classical theorem; the project's formal endpoint is
  `Diophantine.mrdp`, `Diophantine.mrdp_iff` and `Diophantine.mrdp_dioph_iff`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, lines
  33, 42, 26), whose blob `74aea8c5e` is the one source 08 cites. The
  project has formalized none of this report's statements: it has no
  multiset-rewriting, timed-Horn, self-assembly or Waterfall module.

## Reviews and patches by the research programme

These reviews are in another session's tree; nothing there was changed,
and **the shipped programs are the delivered bytes, unpatched**. Applying a
patch to the prefixed copies would need its file names rewritten and is
the research programme's decision.

- Sources 08 and 12: `incoming_substrate_review_808b53ed8.md`, with the
  detailed reviews `incoming_parallel_order_review_808b.md` (source 08)
  and `incoming_convergence_review_808b.md` (source 12), commit
  `126028588`. Both pass mathematical review. Source 08's compiler keeps
  mutable references to its input matrices and guards and accepts a guard
  `Atom(0,1,2)` whose polarity the compiler and the semantic oracle read
  differently; patch `maximal_parallel_immutable_guards.patch`. Source
  12's compiler keeps mutable references to seeds and rules, returns
  aliased export lists and accepts a fractional seed label; patch
  `total_quadratic_immutable_inputs.patch`. No valid polynomial or export
  changes. The review also proves a reduction of source 12's gates to
  `W' = m(2q+3)+2D+2G+R` witnesses (dated note after Theorem 21.2; not
  implemented) and notes the inconsistency below about duplicate literals.
- Source 14: `waterfall_intake_triage_24a743255.md`, then
  `waterfall_report_review_24a743255.md` (commit `f19aaa092`): all eight
  replay commands pass and the theorems are confirmed over natural
  coordinates; the grouped compiler accepts floating-point and Boolean
  inputs and aliases its exported name lists, repaired by
  `waterfall_grouped_exact_domains.patch`. The programme also projected the
  forced first step and the three forced steps before halt
  (`waterfall_forced_boundary_projection.md`, commit `3b8187ea9`): for
  `k ≥ 4`, `35k−138` witnesses, `5k−15` squares and `2k−8` products; at
  `k = 7`, 107 witnesses and a complete 720-operation evaluation instead of
  245 and 1558. Its `waterfall_endpoint_alias.md` shows that the
  endpoint-count shortcut also fails on the actual 46-clock matrix
  (`Mv = 194·1`; `(C,k,τ)` from `(189,7,428)` to `(251,17,622)`). These are
  dated notes in Part III (Sections 34 and 37); source 14's counts are
  printed as delivered.

## Licensing of the third-party machine data

`data/14-waterfall-UniversalTM15x2.tm.txt` (227 bytes) and
`data/14-waterfall-UniversalTM15x2.twm.txt` (5,414 bytes) are Iijil's
machine data from the MTGPrograms repository
(<https://github.com/Iijil1/MTGPrograms>), shipped byte for byte because
the replay needs them; their SHA-256 values are in
`14-waterfall-SOURCE-PROVENANCE.md`. **These two files are not covered by
the repository's MIT-0 licence.** Source 14 observed no upstream licence
and says it "does not claim to relicense any third-party work"
(`14-waterfall-LICENSE-PROVENANCE.md`); they are included as factual
mathematical machine specifications, and anyone redistributing them should
check the upstream terms. The source machine itself is Neary and Woods's;
their paper is cited, not bundled.

The same delivered note also says that no blanket licence is assigned to
source 14's own note and Python checks "in this private review package".
The placement treated those files as repository content; this README
records both statements and does not decide the question.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
bm, microtype, booktabs, longtable, enumitem, tcolorbox, fancyhdr, TikZ,
xurl, hyperref). The committed build has 87 pages, with no undefined
references or citations, no multiply defined labels, no duplicate
destinations, and no overfull or underfull boxes.

The article is generated reproducibly from the three delivered manuscripts
by a merge script with anchored insertions; the script is not shipped, and
`article.tex` is the source of record.

## Rerunning the programs

The programs locate their companions and data by their delivered layout,
and all three suites **write into that layout**: source 08's `verify.py`
rewrites `data/verification_counts.json` (and its README redirects output
over `data/example_certificate.json` and `data/verification.txt`); source
12's `test_compiler.py` rewrites `results/test_receipt.json` and the four
example files; source 14's `run-replay.sh` rewrites all twelve JSON files
of `replay/` and `receipts/` and writes seven logs. Run in place, several
programs would also write new files beside the shipped ones (for example
`code/14-waterfall-grouped_quadratic.py` writes into `code/`). **Never run
them in place.** Recreate the delivered layout in a scratch directory
(`py` is the Python launcher on this machine; the delivered texts say
`python` or `python3`). From this directory:

```sh
# source 08 (standard library; Python 3.10+)
mkdir -p r08/code r08/data
for f in parallel_certificates.py verify.py; do cp code/08-maximal-parallel-$f r08/code/$f; done
for f in example_certificate.json verification.txt verification_counts.json; do cp data/08-maximal-parallel-$f r08/data/$f; done
(cd r08 && py code/verify.py > verification.out && py code/parallel_certificates.py > example.out)

# source 12 (standard library; Python 3.10+)
mkdir -p r12/code r12/results
for f in quadratic_compiler.py test_compiler.py verify_exports.py; do cp code/12-total-quadratic-$f r12/code/$f; done
for f in export_verification huge_delay_chain literal_four_tile_example locking_counterexample test_receipt timed_race; do
  cp data/12-total-quadratic-$f.json r12/results/$f.json; done
(cd r12 && py code/test_compiler.py > test.out && py code/verify_exports.py > export_verification.out)

# source 14 (standard library; Python 3.9+; do not use python -O)
mkdir -p r14/replay r14/receipts r14/source
for f in grouped_quadratic verify_certificates verify_frontend verify_frontend_independent \
         verify_halting_example verify_matrix_definition verify_quadratic_independent verify_release; do
  cp code/14-waterfall-$f.py r14/replay/$f.py; done
cp code/14-waterfall-run-replay.sh r14/run-replay.sh
for f in affine-gap-forms certificate-receipt frontend-receipt grouped-quadratic-receipt \
         grouped-quadratic7-certificate grouped-quadratic7-fixture unit-ledgers; do
  cp data/14-waterfall-$f.json r14/replay/$f.json; done
for f in halting-example independent-receipt matrix-definition quadratic-independent release-verification; do
  cp data/14-waterfall-$f.json r14/receipts/$f.json; done
cp data/14-waterfall-UniversalTM15x2.tm.txt r14/source/UniversalTM15x2.tm.txt
cp data/14-waterfall-UniversalTM15x2.twm.txt r14/source/UniversalTM15x2.twm.txt
(cd r14 && PYTHON=py sh run-replay.sh)
```

At the write (Windows, `PYTHONUTF8=1`, Python 3.14.4) all three passed,
in about 12 s, 23 s and 15 s. Source 08 reproduced its example and counts
files, and its transcript differed only in the Python version and elapsed
time lines; source 12 reproduced its four example polynomials and its
export verification, and its receipt differed only in `runtime_seconds`;
source 14 printed "All Waterfall replays passed." and reproduced all
twelve JSON files. All comparisons are apart from line endings: the
Windows runs write CRLF, and the shipped files are LF. Receipts with run
times or interpreter versions never regenerate byte for byte.

## Discrepancies and disclosures

- The shipped build scripts keep the delivered layout:
  `code/12-total-quadratic-build.sh` changes to its own directory and runs
  pdflatex three times on an `article.tex` that is not there, and
  `code/14-waterfall-build.sh` builds `paper/waterfall-diophantine.tex`,
  which is not shipped. Neither builds this report; use the build command
  above.
- Delivered texts name delivered paths: Part I's validation section and
  appendices (`code/parallel_certificates.py`, `data/...`), Part II's
  implementation section and Appendices D–E (`code/...`, `results/...`,
  `build.sh`, `README.md`, `SOURCE_AUDIT.md`), Part III's replay section;
  `08-maximal-parallel-PROOF_AUDIT.md`/`SOURCE_AUDIT.md`,
  `12-total-quadratic-SOURCE_AUDIT.md` and the two `14-waterfall-*.md`
  notes; `data/12-total-quadratic-export_verification.json` (file names
  without prefix); source 14's receipts. `[write]` notes give the shipped
  names in the article; the map above gives them here. Source 08's title
  page and Part II's Appendix E list the delivered PDFs and READMEs, which
  are not shipped.
- Source 12 says (Section 18.1) that duplicate identical body literals are
  removed during input validation; its compiler rejects them, as its own
  Section 26 says. Noted in a `[write]` note; no theorem is affected.
- Source 12 referred to its self-assembly section as "Section 7"; the
  merged text uses a cross-reference (Section 23) and says so in a
  footnote. Source 14's author line "for private review" is printed only
  in the provenance appendix. No other source sentence was changed.
- Sources 08 and 12 describe the repository at `db3b377f0` and know the
  `canonical-diophantine-certificates` report only through its README;
  source 12 calls its Part XI "manuscript 09" (that report's source 09,
  batch-62 manuscript 02; not batch-78 manuscript 09). The report adds the article's statements by
  label (Section 1.5). Source 14 names no repository commit.
- Credits the sources omit are added in `[write]` notes: Păun (membrane
  systems, 2000) and Burkhard (maximum firing strategy for Petri nets) for
  maximal parallelism, and Matiyasevich, Davis–Putnam–Robinson and Davis
  for MRDP (Part I); Knuth (1977), Gallo–Longo–Pallottino–Nguyen (1993),
  Dowling–Gallier (1984) and Baccelli–Cohen–Olsder–Quadrat (1992) for the
  min/max fixed-point equations, Horn closure and max-plus timing (Part II).
- The three title pages are replaced by one, each Part opening with its
  source's title, subtitle, author line, date, abstract and status
  statement. Fonts, paper size and heading and theorem styles are unified:
  source 08 used the newtx fonts on A4 paper with coloured headings, and
  source 12 printed remarks in the definition style. The appendices of the
  three sources are collected after Part III.
- The receipts of source 08 and source 12 record Python 3.13.5; the
  reruns above used Python 3.14.4.
