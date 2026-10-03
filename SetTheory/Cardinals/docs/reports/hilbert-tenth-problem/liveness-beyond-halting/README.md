# Beyond Halting: Recurrence, Progress Deadlines and Diophantine Liveness

**A progress-modulus hierarchy, quadratic transition laws, and the limits of finite certificates**

This is a research report dated 30 September 2026, built from three
manuscripts in the batch-62 write phase of ProveIt's incoming reports; a
fourth manuscript, dated 2 October 2026, was added as Part VI in the batch-79
write phase. All four are AI-assisted research manuscripts. They are called
*source 10*, *source 03*, *source 11* and *source 12* after the file prefixes
of their shipped programs and data; the numbers 11 and 12 continue this
report's own file sequence and are not batch numbers.

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 10 (base) | batch 62, manuscript 10 | `Beyond_Halting_Diophantine_Liveness` (`b57c0b5ff`); *Beyond Halting: A Progress-Modulus Hierarchy for Diophantine Liveness*, main file `beyond_halting.tex`, 34-page PDF | `b6bf6406a` (MRDP source), `b998f70c6` (MRDP guide, Turing-degree README) | `adeddcecc` | Section 1 and the unmarked sections of Parts I–V (Sections 4–9, 18, 19, 22, 24, 27, 30, 33, 34), Appendices A and E |
| 03 | batch 62, manuscript 03 | `Quadratic_Diophantine_Dynamics` (`b57c0b5ff`); *Quadratic Diophantine Dynamics: Recurrence, computable schedules, and the limits of finite certificates*, 26-page PDF | `4e128356d` | `adeddcecc` | Section 3.2–3.3 and every section or subsection marked `[source 03]`; Appendix B |
| 11 | batch 63, manuscript 01 | `quadratic_infinite_computation` (`a4268e78e`); *Quadratic Laws, Infinite Computation: Exact Diophantine Dynamics, Planar Stack Machines, and the Boundary Created by Recurrence Deadlines*, 27-page PDF | `e18718e83` | `62f1ad07c` | Section 3.4–3.5 and every section or subsection marked `[source 11]`; Appendices C and D |
| 12 | batch 79, manuscript 04 | `clock_spectra_research` (`060e08a07`); *Beyond Enumerable Clock Cones: Limit Computations, Unique-Path Trees, and Quadratic Diophantine Progress*, 23-page PDF; reviewed by the Hilbert's-tenth programme in `2c311e525` (program defect, patch not applied; see below) | `e58b724c2` | `bbaf322e5` | Part VI: Section 38 (written opening), Sections 39–52 marked `[source 12]` (its two appendices are Sections 51–52) |

Every result, proof, example, remark, limitation and research question of
the four manuscripts is printed. Source 10 is the base because it is the
most general: it treats arbitrary computable finitely branching
(binary-controlled) systems and proves the hyperimmune-free characterization
and the exact c.e. deadline spectra. Sources 03 and 11 prove the same
recurrence hierarchy by other routes, through degree-two counter-machine
transition laws of their own. Source 12 was written as an answer to the
report's question `lbh:q:spectra` (deadline spectra beyond c.e. cones) and is
printed whole as Part VI, after Part V, so that no existing Part, section,
theorem or label number changed. The report is AI-assisted and unrefereed, and
**nothing in it is formalized in Lean or Rocq**.

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 129 pages (unnumbered title page, then
                                                     pages 1–128; abstract and contents on pages 1–6)
README.md                                            this guide
03-quadratic-recurrence-PROOF_AUDIT.md               source 03's author-side proof audit, as delivered
03-quadratic-recurrence-SOURCES.md                   source 03's source and provenance notes, as delivered
10-progress-deadlines-source_ledger.md               source 10's source and provenance ledger, as delivered
11-quadratic-laws-SOURCE_NOTES.md                    source 11's source notes, as delivered
12-clock-spectra-source_audit.md                     source 12's source and contribution audit, as delivered
code/03-quadratic-recurrence-Makefile                source 03's Makefile (delivered layout; see below)
code/03-quadratic-recurrence-quadratic_compiler.py   source 03's degree-two compiler
code/03-quadratic-recurrence-verify.py               source 03's exact finite checks
code/10-progress-deadlines-clock_compiler.py         source 10's two-stack quartic compiler and sample export
code/10-progress-deadlines-test_clock_compiler.py    source 10's finite tests
code/11-quadratic-laws-Makefile                      source 11's Makefile (delivered layout; see below)
code/11-quadratic-laws-__init__.py                   source 11's package marker (one docstring line)
code/11-quadratic-laws-quadratic_dynamics.py         source 11's incoming-edge compiler and exact semantics
code/11-quadratic-laws-verify.py                     source 11's exact finite checks
code/12-clock-spectra-build.sh                       source 12's build script (delivered layout; see below)
code/12-clock-spectra-clock_certificates.py          source 12's degree-two compiler and checkers (unpatched; see below)
code/12-clock-spectra-test_all.py                    source 12's exact finite checks
code/12-clock-spectra-verify_export.py               source 12's independent evaluator of the exported polynomial
data/03-quadratic-recurrence-finite_visits.json      source 03's nine-coordinate example (input)
data/03-quadratic-recurrence-finite_visits_polynomial.json   its compiled polynomial: 44 monomials, height 4
data/03-quadratic-recurrence-height_eight.json       source 03's two-parallel-increment example (input)
data/03-quadratic-recurrence-height_eight_polynomial.json    its compiled polynomial: 19 monomials, height 8
data/03-quadratic-recurrence-sample_runs.json        source 03's recorded finite runs
data/03-quadratic-recurrence-report.json             source 03's recorded run: PASS, 302,498 local checks
data/03-quadratic-recurrence-pdf_check.json          source 03's record of its own 26-page PDF build
data/10-progress-deadlines-example_certificate.json  source 10's 52-variable, 137-residual sample and witness
data/10-progress-deadlines-test_report.json          source 10's recorded test run: PASS
data/11-quadratic-laws-countdown_polynomials.json    source 11's budget-example P2 and P4 (88 monomials each)
data/11-quadratic-laws-countdown_prefixes.csv        source 11's finite-prefix table (CRLF line endings, kept)
data/11-quadratic-laws-verification_results.json     source 11's recorded run: PASS, 59,049 state pairs
data/12-clock-spectra-quadratic_certificate.json     source 12's seven-rule example: degree 2, 334 variables,
                                                     1,494 monomials, with its natural zero assignment
data/12-clock-spectra-test_results.json              source 12's recorded run: PASS (Python 3.13.5)
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md` is
byte-identical to the delivery. Delivered name → shipped name:

- Source 10: `code/clock_compiler.py`, `code/test_clock_compiler.py` →
  `code/10-progress-deadlines-*.py`; `artifacts/example_certificate.json`,
  `artifacts/test_report.json` → `data/10-progress-deadlines-*.json`;
  `research/source_ledger.md` → `10-progress-deadlines-source_ledger.md`.
- Source 03: `code/quadratic_compiler.py`, `code/verify.py`, `Makefile` →
  `code/03-quadratic-recurrence-*`; `examples/*.json` and
  `verification/report.json`, `verification/pdf_check.json` →
  `data/03-quadratic-recurrence-*.json`; `PROOF_AUDIT.md`, `SOURCES.md` →
  `03-quadratic-recurrence-*.md`.
- Source 11: `code/quadratic_dynamics.py`, `code/verify.py`,
  `code/__init__.py`, `Makefile` → `code/11-quadratic-laws-*`; `data/*` →
  `data/11-quadratic-laws-*`; `SOURCE_NOTES.md` →
  `11-quadratic-laws-SOURCE_NOTES.md`.
- Source 12: `code/clock_certificates.py`, `code/test_all.py`,
  `code/verify_export.py`, `build.sh` → `code/12-clock-spectra-*`;
  `examples/quadratic_certificate.json`, `test_results.json` →
  `data/12-clock-spectra-*.json`; `source_audit.md` →
  `12-clock-spectra-source_audit.md`.

Not shipped: the four manuscripts (`beyond_halting.tex`, and each member's
`article.tex`), their PDFs and delivered READMEs (this text and
`article.tex` replace them), and the checksum manifests (`SHA256SUMS` of
source 10 and `SHA256SUMS.txt` of source 11, each verified in full at
placement; the packages of sources 03 and 12 had none). These files survive
in the arrival commits' archives (source 12:
`git show 060e08a07:docs/incoming/clock_spectra_research.zip`). Nothing
regenerable was excluded: source 12's 157,768-byte certificate is shipped.

## Labels and numbering

Every label carries the prefix `lbh:`: source 10's 85 labels are `lbh:` plus
their delivered names, source 03's 55 are `lbh:qd:` plus theirs and source
11's 55 are `lbh:ql:` plus theirs; the merge added 32 (`lbh:conv:`,
`lbh:part:`, `lbh:sec:`, `lbh:q:`), 227 in all. No source label was dropped.
The batch-79 write added 70 labels for Part VI, 297 in all: source 12's 55
are `lbh:cs:` plus their delivered names; the write added `lbh:part:spectra`,
six `lbh:cs:sec:` labels for Section 38 and its subsections, and eight
`lbh:cs:q:` labels on source 12's eight questions, which were unlabelled. No
existing label was renamed or removed, and every existing label number is
unchanged (compared in the `.aux`; only page numbers moved).
Where a statement of source 03 or 11 is printed as a second or third proof of
a statement of source 10, its label sits on the printed statement: source 03's
`thm:deadline`, `lem:tree`, `prop:det` and source 11's `thm:deadlinecompact`,
`prop:oraclepath` sit on source 10's compactness theorem, tree normal form,
deterministic boundary and clock–closed-class–degree equivalence, and source
11's `lem:dnr` sits on source 03's `lem:dnc`. The section labels of the
three question sections and of the two deadline sections sit on the printed
section. cleveref type hints (`\label[lemma]{…}` and so on) are on the 42
labels of lemmas, propositions, corollaries, definitions, examples, remarks
and questions, which share the theorem counter; without them cleveref
printed each of them as "theorem".

Text written in the merge is marked `[write]`; section headings from sources
03 and 11 carry `[source 03]` or `[source 11]`, and text without a marker is
source 10's. Sources 03 and 11 wrote their research questions as subsections;
they are printed as question environments with unchanged text. In Part VI,
every section heading of source 12 carries `[source 12]`, unmarked text in
Sections 39–52 is source 12's, and `[write]` marks text of the batch-79 write.

## Status: what is claimed, and what is not

The report claims conventional mathematical proofs for:

- **Compactness.** A shared progress deadline makes recurrence an effectively
  closed condition (Theorem 5.1, proved three times); checking finite
  horizons separately does not (three counterexample machines).
- **Degrees** (source 10). A computable deadline exists iff the accepting
  schedules contain a nonempty effectively closed class iff an accepting
  schedule of hyperimmune-free degree exists (then also a low one); every c.e.
  degree is an exact deadline-oracle spectrum.
- **The hierarchy.** Reachability Σ⁰₁, a fixed deadline Π⁰₁, bounded gaps
  Σ⁰₂, some computable deadline Σ⁰₃, a computable run Σ⁰₃, recurrence Σ¹₁,
  deterministic recurrence Π⁰₂, with the strict chain Comp ⊊ Clock ⊊ Büchi;
  proved for a fixed two-stack machine (source 10), for source 03's fixed
  degree-two counter graph E_U, and for source 11's degree-two law (its Σ⁰₃
  rows across effectively supplied machines). Source 11 adds EFG Σ⁰₂, AGF Π⁰₂,
  AFG Π¹₁; source 03 adds one weak-fairness obligation Σ¹₁. Section 6.7 is the
  one table.
- **Low-degree laws.** An auxiliary-free degree-two polynomial gives a
  counter network's labelled transition relation, with coefficient height ≤ 8
  (source 03's control-vector encoding) or ≤ 6 with a sum-of-squares quartic
  companion (source 11's incoming-edge encoding). **The two heights concern
  different encodings; each is sharp for its own compiler, and neither
  improves or contradicts the other.** A single affine law cannot carry Σ¹₁
  recurrence (signed with bounded branching, source 03; orthant-nonnegative
  with unbounded branching, source 11).
- **Certificates.** Source 10's two-stack quartic has natural zeros in
  bijection with rule-labelled runs meeting prescribed deadlines, with exactly
  H(3+R+G)+k variables and H(4R+E+2G+2)+k residuals; source 11's counter
  deadline certificates stay at degree two. Source 12 (Theorem 45.2) proves
  the same labelled-run bijection for two-stack machines at degree two, with
  3(T+1)+9mT+k natural coordinates for m rules: stronger in degree only (it
  has more coordinates, its rule format and stack code differ, and its
  bijection holds over the naturals only).
- **Clock-degree spectra** (source 12, Part VI; answers `lbh:q:spectra` in
  part). Clock problems are, up to uniform computable transformations, the
  upward effectively closed mass problems of Baire space (Theorem 41.1).
  Every Δ⁰₂ degree is a least clock degree of an input of a fixed two-stack
  system, by a first-matching-stage tree with a unique path (Corollary 42.4;
  `lbh:thm:ce-spectrum` is its c.e. case); so is every degree of a unique path
  through a recursive tree, including 0⁽ʳ⁾ and 0⁽ω⁾ (Theorem 43.1). Unions of
  incomparable cones have no least degree (Corollary 44.2). A least clock
  degree contains a self-modulus and is hyperarithmetic (Theorem 44.4, using
  the classical modulus theorem via Monin–Patey), and no nonzero
  hyperimmune-free degree is least.
- **Realizations and transport.** Exact rational guarded piecewise-affine
  relations on [0,1]³ (source 10) and in a planar strip (source 11); faithful
  block simulations preserve the recurrence notions.
- **Limits.** None of these liveness properties has an ordinary Diophantine
  representation or a total computable reduction to finite polynomial
  solvability; fixed-arity MRDP gives alternating signatures instead.

It does **not** claim:

- any formal verification: no Lean or Rocq proof was built for any statement;
  the proposed `Liveness/*.lean` modules of source 10 do not exist;
- priority: MRDP, the low and hyperimmune-free basis theorems (Jockusch–Soare),
  Σ¹₁-hardness of recurrence (Harel; Harel–Pnueli–Stavi, via
  Esparza–Krasotin; Chodil–Kučera), recursive-tree index sets
  (Cenzer–Marek–Remmel), and, for source 12, unique paths and uniform moduli
  (Gerdes), the limit lemma (Shoenfield), Friedberg–Muchnik and the modulus
  theorem (Solovay, Groszek–Slaman, via Monin–Patey) are classical and
  credited; no source establishes literature-wide priority;
- any finite-fold or single-fold MRDP result: the unique witnesses of the
  finite-horizon certificates do not survive compression to a fixed arity;
- a small or explicit universal machine: no universal edge table, no value of
  source 03's D_U, no expanded fixed universal polynomial is supplied (sources
  03, 10 and 11); source 12's fixed two-stack interpreter is proved to exist
  but not instantiated, and its seven-rule example is not universal;
- (source 12) a fixed universal quadratic Diophantine equation, single-fold or
  finite-fold MRDP, or any improvement of the programme's fixed universal
  operation counts (75 and 87); a complete classification of least clock
  degrees (the equalities in its inclusion chain S ⊆ L ⊆ M ⊆ hyperarithmetic
  are open); a uniform self-modulus from leastness; an implementation of an
  oracle for a Δ⁰₂ set, of the transfinite jump or of an infinite-path solver;
  novelty for the constructions it shares with Parts I–V (its explorer, fixed
  interpreter, compactness step, coherent family and affine coding are this
  report's own, printed with pointers in Section 38.2);
- continuity, noise tolerance, injectivity or physical realizability of the
  piecewise-affine realizations, or extraction of noncomputable information
  from a finite rational input;
- that the finite tests prove any infinite-run, completeness or
  noncomputability statement: they are regression checks of the finite
  constructions.

## Relation to neighbouring reports and to the formal project

This is the third report of the collection's `hilbert-tenth-problem`
category. Neither neighbour treats infinite-path predicates.

- **Report A, [`canonical-diophantine-certificates`](../canonical-diophantine-certificates).**
  Its counter-program remark (label `cdc:eq:zero-guard` and the paragraph
  after it) says that with free initial registers "the uniform-parameter
  presentation is then quartic unless another representation is supplied";
  sources 03 and 11 supply that representation (Section 10). Its Part IX
  concerns single-fold and finite-fold multiplicity, not the quantifier class
  of infinite behaviour; this report's no-go theorems concern the latter. Its
  batch-62 Parts on dynamic heaps (perpetual safety not r.e.) and priority
  pumping (eventual periodicity c.e.-complete) are the lowest levels of this
  hierarchy for other substrates. Questions of Report A are cross-referenced
  by label in Section 33 (`cdc:q:degree`, `cdc:q:verified`, `cdc:q:ski`, and
  "Quantitative universal compilation").
- **Report B, [`probabilistic-quantum-and-continuous-computation`](../probabilistic-quantum-and-continuous-computation).**
  Its Part I shows almost-sure termination Π⁰₂ (`pqc:eq:te`,
  `pqc:thm:unconditionaltable`), the probabilistic analogue of the
  deterministic Π⁰₂ row here. Its Part III has continuous, noise-robust
  realizations; the exact realizations here are discontinuous and not robust.
  Questions of Report B are cross-referenced by label in Section 33
  (`pqc:q:direct`, `pqc:q:smaller`, `pqc:q:continuous`, `pqc:cb:q:extract`,
  `pqc:cb:q:noise`, and "Reduce the three-dimensional realizer").
- **[`quadratic-orthant-certificates`](../quadratic-orthant-certificates)**
  (opened by cluster H3 of batch 78, written in `c51b9880d`; dated note of
  2 October 2026). Research question 33.8, "Other unconventional substrates
  with timing certificates", appears to be answered partly by that report's
  Part I (its source 08, batch-78 manuscript 08): its guarded
  register-machine embedding (`qoc:mp:sec:variants`) simulates a register
  machine by maximal-parallel multiset rewriting with inhibitors, one round
  per instruction. Checked against the definition before
  `lbh:thm:transfer`, it is a computable signal-faithful block simulation
  with block length one, provided the empty rounds that the target's
  semantics allows after a deadlock count as termination (as its
  first-halting certificate `qoc:mp:cor:firsthalt` counts them); the local
  step compiler is its degree-two guarded-round certificate
  (`qoc:mp:prop:guards`). Only register-machine sources and this one class
  of reaction systems are covered: a clock-faithful simulation of this
  report's own universal systems by register machines is not checked, and
  guarded histories are not implemented in that report's code. Source 08
  does not draw the connection. The note is a `[write]` note after the
  question; it added no label, and at that write the article still had 95
  pages and 227 labels, with every label number unchanged (compared in the
  `.aux`).
- **Part VI and Parts I–V (batch 79).** Dated `[write]` notes of 2 October
  2026 record source 12's results where they bear on the earlier Parts: under
  `lbh:q:spectra` (answered in part, re-scoped by source 12's questions
  49.1–49.3), after `lbh:thm:ce-spectrum` (its c.e. case), after the remark
  following `lbh:thm:compiler` and after Section 10's degree comparison (the
  degree-two two-stack form), after `lbh:thm:geometry` (the identical
  coding), after the spectrum remark closing Section 7, and after three
  questions of Section 33 that source 12's questions overlap. Source 12's
  explorer, fixed interpreter, compactness step, coherent family and affine
  coding are printed as this report's own constructions, with pointers.
- **Report A** again: source 12's guard gadget is a compact form of
  `cdc:wf:lem:activation` (canonical branch activation) in
  `canonical-diophantine-certificates`; no novelty is claimed for it.
- **The formal project.** The report sits in the collection, not in
  `Computability/HilbertTenthProblem`, and **placement beside a Lean/Rocq
  development confers no formal status**. It cites, as context only:
  `Diophantine.mrdp`, `Diophantine.mrdp_iff` and `Diophantine.mrdp_dioph_iff`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, lines 33,
  42, 26), whose hypothesis is `REPred`; and `Diophantine.boundedForall_dioph`,
  `Diophantine.exactIter_dioph`, `Diophantine.existsExactIter_dioph`
  (`…/Lean/Diophantine/Common/DiophantineTrace.lean`, lines 52, 60, 71). The
  project has formalized none of this report's statements. The Turing-degree
  project (`Computability/TuringDegrees/README.md`) is cited by source 10 as
  context; it has no hyperimmune-free or low-basis theorem. No statement or
  improvement of an operation count of the project's universal certificate is
  made: the counts here are per local step or per finite horizon.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (New PX fonts, AMS,
microtype, TikZ with the `automata` library, tcolorbox, needspace, xurl,
hyperref, cleveref). The committed build (batch-79 write) has 129 pages and
no LaTeX warnings: no undefined references or citations, no multiply defined
labels, no duplicate destinations, no overfull boxes.

## Rerunning the programs

Every suite writes into its delivered paths, and the programs import one
another by their delivered names, so the prefixed files cannot be run in
place. Run each on a copy with the delivered layout, from this directory
(`py` is the Python launcher here; the delivered texts and Makefiles say
`python` or `python3`):

```sh
mkdir -p r10/code r10/artifacts && cp code/10-progress-deadlines-clock_compiler.py r10/code/clock_compiler.py \
 && cp code/10-progress-deadlines-test_clock_compiler.py r10/code/test_clock_compiler.py \
 && (cd r10 && py code/test_clock_compiler.py && py code/clock_compiler.py)   # writes r10/artifacts/*.json
mkdir -p r03/code r03/examples r03/verification && cp code/03-quadratic-recurrence-quadratic_compiler.py r03/code/quadratic_compiler.py \
 && cp code/03-quadratic-recurrence-verify.py r03/code/verify.py \
 && for f in finite_visits height_eight; do cp data/03-quadratic-recurrence-$f.json r03/examples/$f.json; done \
 && (cd r03 && py code/verify.py)   # writes r03/examples/*_polynomial.json, sample_runs.json, verification/report.json
mkdir -p r11/code r11/data && cp code/11-quadratic-laws-quadratic_dynamics.py r11/code/quadratic_dynamics.py \
 && cp code/11-quadratic-laws-verify.py r11/code/verify.py && cp code/11-quadratic-laws-__init__.py r11/code/__init__.py \
 && (cd r11 && py code/verify.py)   # writes r11/data/{countdown_polynomials.json,countdown_prefixes.csv,verification_results.json}
mkdir -p r12/code r12/examples && cp code/12-clock-spectra-clock_certificates.py r12/code/clock_certificates.py \
 && cp code/12-clock-spectra-test_all.py r12/code/test_all.py && cp code/12-clock-spectra-verify_export.py r12/code/verify_export.py \
 && (cd r12 && PYTHONUTF8=1 py code/test_all.py && py code/verify_export.py examples/quadratic_certificate.json)   # writes r12/examples/quadratic_certificate.json, r12/test_results.json
```

Better still, copy `code/` and `data/` to a scratch directory first and run
there, so that no `r*/` directory is created in the repository. All four
need only the standard library. Source 12's suite takes about two seconds;
compare its outputs with `data/12-clock-spectra-quadratic_certificate.json`
and `data/12-clock-spectra-test_results.json`. At the batch-79 write
(Python 3.14.4, Windows) it passed, the regenerated certificate equals the
shipped one after CRLF→LF normalization, and `test_results.json` differs only
in its `python` field (recorded 3.13.5) and in line endings. Source 12's
recipe runs the unpatched program; to test the programme's repair, apply
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/spectral_repairs_060e08a07/clock_boundaries.patch`
to the copy in `r12/` (the patch addresses `code/clock_certificates.py`),
never to the shipped file. At the write (Python 3.14.4, Windows) all
three passed, and every regenerated file equals the shipped one apart from:
CRLF line endings (the Windows run writes CRLF; the shipped files are LF,
except source 11's CSV, which was delivered with CRLF and is kept that way);
the Python version string in source 10's `test_report.json` and source 03's
`report.json` (recorded 3.13.5); and the elapsed time in source 11's
`verification_results.json`. Source 03's `pdf_check.json` is not
regenerated; it records the build of source 03's own PDF.

## Discrepancies and disclosures

- The shipped Makefiles keep the delivered layout: both build `article.tex`
  (the member's manuscript, which is not shipped; running them here would
  build this report instead) and run `code/verify.py`, a delivered name.
  Source 03's calls `python3`; source 11's defaults to `PYTHON ?= python3`
  and runs pdflatex three times. Use the commands above instead.
- Source 11's delivered README, not shipped, used the programs as a package
  named `code` by delivered names; the recipe above keeps that layout.
- Source 03's `PROOF_AUDIT.md` names `code/verify.py`,
  `verification/pdf_check.json` and the delivered PDF; source 10's
  `source_ledger.md` and the manifest table of Appendix A name
  `beyond_halting.tex`, `beyond_halting.pdf`, `README.md` and the
  `research/` and `artifacts/` paths. These are delivered names (map above);
  the manuscripts and PDFs are not shipped.
- The three shipped source notes describe how each author read the
  repository; the report does not repeat that. Their pins are those of the
  table above. `Computability/` is unchanged from every pin to the write, so
  every repository statement in them and in the report was checked and is
  true at the write.
- The delivered title pages and PDF metadata of sources 10, 03 and 11 named
  the assistant used or the addressee of the manuscripts; the report replaces
  them with the neutral "AI-assisted research manuscript" (Section 37).
  Source 12's author line is quoted as delivered (below).
- Merge notes that complete source text, all marked `[write]`: a pinned
  initial tag for a single-fold version of source 03's finite-horizon
  certificate (Section 14); a textbook reference (Rogers 1967) beside source
  03's citation of a preprint for the non-arithmeticity of Σ¹₁-complete sets;
  the observation that source 10's compactness proof applies verbatim to
  source 11's nondecreasing deadlines. Source 11's citations of
  Cenzer–Marek–Remmel Theorems 2.6(g) and 2.10(e) were checked against
  arXiv:1303.6555 at the write and are correct.
- Bibliography: source 03's key `proveit-mrdp` (the Hilbert's-tenth-problem
  README at `4e128356d`) is printed as `qd-proveit-readme`, since source 10
  uses `proveit-mrdp` for the MRDP source at `b6bf6406a`; source 11's `harel`
  is source 03's `harel1986` (the same paper, printed once); source 11's
  `moore` (Nonlinearity 1991) is `moore1991`, distinct from source 10's
  `moore1990`; source 11's repository entries are `ql-repo-root` and
  `ql-repo-mrdp` (pin `e18718e83`).
- Macros: source 11's unused `\B` (a calligraphic B, clashing with source 10's
  `\B = {0,1}`) and `\F`, and source 03's unused `\INIT`, `\out`, `\sgn`, are
  not defined; `\htp` (source 03's operator and source 11's operatorname) and
  `\dom` are defined once. No printed symbol changed.
- Source 11's stack code η(w) equals source 10's ρ(w) after relabelling
  digits d = 1 + 2a; source 10's η is its scheduler code. Neither was renamed;
  the conventions (Section 2.3) print the warning.
- Research questions: source 10's twelve (the number its delivered README
  gives), source 03's ten and source 11's eight are all printed in Section 33:
  21 question environments, and nine overlapping questions printed unchanged
  as paragraphs after the question they overlap. Which questions overlap is a
  judgement of the merge (Section 37). Source 12's eight questions are
  printed in Part VI (Section 49) as question environments with added labels;
  bracketed `[write]` notes there and in Section 33 mark the overlaps, a
  judgement of the batch-79 write. The report now has 29 question
  environments.

### Source 12 (Part VI, batch 79)

- **Review and patch.** The Hilbert's-tenth programme reviewed source 12 in
  `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_spectral_060e08a07.md`
  (commit `2c311e525`; indexed in `incoming_substrate_review_2a8a39599.md`).
  Its mathematics survives the review. Finding 4 is a program defect: in
  `code/clock_certificates.py` (shipped as
  `code/12-clock-spectra-clock_certificates.py`) a compiled `Machine` keeps
  the caller's mutable rule, initial-state and accepting-state containers, so
  that mutating them after compilation leaves an old zero validating while the
  descriptor and export claim another initial state; and
  `encode_stack([0.0])` returned the float 1.0. The tested repair is
  `spectral_repairs_060e08a07/clock_boundaries.patch` in the same directory.
  **The shipped program is the unpatched original**; neither defect affects a
  theorem. The review's two domain examples (a signed helper with G = 0 and
  D ≠ 0; a nonnegative-rational zero from two identical stay rules with
  selectors ½, ½) are printed in Section 45.
- **Delivered names in shipped text.** `12-clock-spectra-source_audit.md`
  names the report path and blob at the pin `e58b724c2` (the batch-62/63 text
  of Parts I–V); `code/12-clock-spectra-build.sh`
  changes to its own directory, requires `python3` and `pdflatex`, runs
  `code/test_all.py` and `code/verify_export.py` by delivered names and builds
  `article.tex`, source 12's manuscript, which is not shipped. Use the recipe
  above instead. The printed listing in Section 48.4 keeps the delivered
  layout, with a `[write]` note.
- **Rerun hazards.** `test_all.py` overwrites `examples/quadratic_certificate.json`
  and `test_results.json` beside its own `code/` directory; on Windows both are
  written with CRLF line endings, and `test_results.json` records the running
  Python version. Never run it on the shipped files.
- **Notation and macros.** No printed symbol of source 12 was renamed. Its
  `\Clock` (a calligraphic D, the set of adequate deadlines) clashes with
  source 10's `\Clock` (the predicate CD) and is defined as `\csClock`; its
  `\Spec`, `\BS`, `\Cone`, `\degT` and `\zero` are `\csSpec`, `\csBS`,
  `\csCone`, `\csdegT` and `\cszero`; its unused `\rk` is not defined; its
  `\secref` is printed with `\cref`. Section 38.3 tabulates the letters that
  change meaning (𝒟, ρ, f, T, H, m, G, D, E, U, 𝓜 among them).
- **Bibliography.** Source 12's keys carry the prefix `cs-`. Its entry for
  the report itself (`cs-repo-liveness`, at the pin) is kept as provenance,
  with `[write]` pointers to the labels it means; its Matiyasevich entry is
  printed separately from `matiyasevich1970` because it carries source 12's
  annotation.
- **Author line.** Source 12's delivered author line ("Prepared for Vladimir
  Reshetnikov / OpenAI ChatGPT") is quoted as delivered in Section 38.1, as
  the batch-79 records ask; the batch-62 write had replaced the author lines
  of sources 10, 03 and 11 by a neutral description.
- **Repository claims.** Source 12 read the Hilbert's-tenth README on the
  default branch, not at its pin; the README at this write still states the
  75- and 87-operation bounds, which source 12 neither uses nor improves.
  Its statements about this report are true of Parts I–V at this write: the
  only change after its pin is the batch-78 note in Section 33.
- **Placement.** Source 12's two appendices are printed as Sections 51 and
  52 of Part VI, not in the report's appendix, so that Appendices A–E keep
  their letters. The PDF of source 12 was 23 pages; Part VI with its written
  opening is pages 93–121 of the report.
