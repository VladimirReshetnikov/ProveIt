# ZFC closure kernels: intake reconciliation

Intake findings, 16 October 2026. This report now reconciles seventeen manuscripts.
The initial batch 143 combines three manuscripts from
arrival `9e5b610259cd42c88e2cf6c862fb876a7c6d6fcd`, placed in `b07d1a27b`.
This is the reconciliation-note option in `docs/incoming/README.md`, section 2:
the delivered base article is preserved, rather than rewritten as a unified article.
No merged PDF is built. These are ordinary mathematical arguments and finite
regression checks. The deliveries confer no formal status; subsequent Lean
results and their exact scope are listed below.

The user's current machine target is an equivalence **provable in ZFC** between
blank-tape non-halting and Con(ZFC), with fewer than 254 nonhalting states on a
binary, two-way infinite, single tape. The initial sources discuss the stronger
PA metatheory; later deliveries also address the ZFC target. Their missing
proof compilers remain missing; changing our target
does not turn their experiments into a formal equivalence proof.

Batch 146 below supplies a countermodel to the entire intended raw
C/G code calculus, including the variants behind the earlier 252/250/248
experiments. Those artifacts remain compiler benchmarks. The ordinary
first-order closure-theory calibrations remain separate accepted arguments.

## Sources, overlap and base

| Source | Delivered archive | Contribution |
|---|---|---|
| 01, BIC | `zfc_closure_research.zip` | Extensionality + inhabited membership + subset-bounded positive image closure; equality-free QBC using profile congruence; an executable Hilbert certificate checker; deletion diagnostics. |
| 02, seeded closure (base) | `zfc_closure_research (1).zip` | Reflexive point/subset seeds remove the separate inhabitedness axiom; mixed member/subset bounds; two-cycle Pairing and Russell-root Replacement; equality-free subset control; alternative calibrations and implementation questions. |
| 03, exact fibers | `zfc_exact_fiber_hulls.zip` | Extensionality + a transitive rooted hull containing exact output fibers; subset-bounded rooted-closure intermediate; direct equality-free control and deletion diagnostics. |

All three calibrate a closure kernel against ZF with Foundation and Choice
omitted, using functional Replacement, then invoke the usual effective
Foundation/Choice consistency reductions. Their converse arguments collect
**unique exact fibers**, rather than silently choose a family of arbitrary
local bounds. All allow matrices of arbitrary complexity and arbitrary finite
parameter tuples, with fresh auxiliary variables. These are infinite schemas.

02 is the base because its reflexive seed removes 01's separate inhabitedness
sentence. 03 offers a complementary mechanism rather than an improvement of
that same expanded formula. Each manuscript's own definitions and proof route
remain attributable to that source. The following controls and limitations are
retained, without treating formula-size rankings as machine-size rankings:

- 01: guarded images, partial functional images, singleton-decoding Union,
  Infinity from repeated closure, direct profile equality elimination, and
  the certificate format. Removing inhabitedness admits the empty one-object
  structure; removing range purity admits the universal one-object structure;
  removing repetition admits hereditarily finite sets; member-only bounds
  admit the hereditarily countable model. Unrestricted unbounded images are
  inconsistent. Congruence-free RBC0 remains uncalibrated in the source.
- 02: exact constant classes, two-cycle Pairing, membership closure for Union,
  Russell-root Replacement, successor Infinity, exact-fiber converse, a
  reflexive-seed criterion, `Ext + Separation + SBC`, and
  `Ext + nonempty-membership + ISI` calibrations. Its empty-membership one-object model satisfies `Ext + ISI` without
  nonempty membership and `Ext + Separation + set-seeded closure` without
  Power Set; its full-membership model satisfies `Ext + SBC` without
  Separation. These deletion models are preserved in its experiments.
  Membership-arm deletion, congruence deletion, restricted matrix grammars,
  shared seed/fiber code, and proof-certificate engineering are research
  questions in the delivered article. Any subsequent answer belongs to new
  research, not to this intake finding.
- 03: the corrected MathOverflow seed convention, the gated singleton decoder,
  subset-rooted closure, EFH, its equality-free profile interpretation,
  container/subset-image consequences, successor Infinity, and the exact-fiber
  converse. Pure membership bounds and dropping exactness have explicit
  countermodel diagnoses. Removing transitivity and profile congruence are
  not calibrated by the delivered theorem. Finite-class/ground-refutation
  alternatives and full machine compilation remain further work.

No historical priority, global minimality, ZFC inconsistency, finite
first-order axiomatization, serialized PA proof, verified Python checker,
complete bridge certificate, new TM table, or new state bound is claimed.
Source 02 inherits the full raw RCC/bisimulation calibration rather than
reconstructing it; this intake did not reconstruct it either.
No claim was found demonstrably false requiring a repository retraction.

## Current-tree overlap and missing provenance

None of the three deliveries states the ProveIt commit it was written against.
This fails the requested pin provenance; **no pin has been inferred**. Their
`zfc-consistency.zip` input provenance refers to a different attachment, which
is not supplied here. Sources 01/02 instead pin their external machine audit
to `jeff87654/busy-beaver` commit
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`; 03 records an upstream README
blob. Neither is a ProveIt pin or an independently rerun benchmark build.

The current tree already says, in `SetTheory/ClosureAxiomatization/README.md:3`:
“The project proves, independently in Lean and Coq, that the theory retaining
Extensionality, Regularity, Separation, and Powerset while replacing Pairing,
Union, Infinity, and Replacement by a single set-like-relation Closure schema
is exactly ZF.” Its `Lean/ClosureAxiomatization/Equivalence.lean:624` declares `T_iff_ZF`.
The directions at lines 547–555 and 595–597 already use Foundation-free
components; `Lean/ClosureAxiomatization/Forward.lean:7` explicitly notes Regularity is unused.
Thus reconstruction of the linked MathOverflow closure proposal is a
predecessor/control, not a new repository gap. These declarations do not
formalize BIC, seeded positive closure, EFH, their equality-free variants,
the paper-level PA calibration, or a small consistency-search machine.

## Placement and unchanged delivery paths

`article.tex` is source 02's delivered `article/seeded_closure_zfc.tex`, unchanged.
It retains its existing labels, with no common intake label prefix. No labels
were renamed. The source 02 delivery README was staged unchanged in the
placement commit; this reconciliation replaces it afterward.

The other articles, all three PDFs, and original READMEs are recoverable from
the arrival archives. Under the intake placement table they are not duplicated
here. Ancillary files are preserved with `01-bic-`, `02-seeded-`, and
`03-fibers-` prefixes: executable files under `code/`, records under `data/`,
and audit/provenance Markdown at the report root. The exact 53-file rename
map is `data/placement-map.json`. The placement was checked against fresh,
untouched extractions, and all 60 extracted blobs were searched in history
with `git log --all --find-object`; there was no previous placement hit.
Checksums and line endings received no special treatment.

All prefixed scripts retain their delivered import names and directory
assumptions. In particular `*-build.py` expects the original `article/`,
`code/`, and `results/`; the BIC checker imports `logic`, seeded scripts
import `formulas`, and fiber scripts import `syntax` / `prior_templates`.
The prefixed audit notes, provenance files, templates and build/QA records
likewise name the original package paths, PDFs and the unbundled input ZIP.
They describe delivery-time artifacts, not a promise that those paths exist
in this flattened placement. Run from recovered scratch packages as below.

## Verification and reproduction

All advertised Python checks ran on separate copies, without touching the
extractions used for placement:

| Source | Executed evidence |
|---|---|
| 01 | 12 unittest methods; 66,066 graphs and 1,052,740 graph/seed pairs; metrics; a valid identity certificate explicitly **not** a refutation. |
| 02 | 66,066 graphs, 1,052,740 relation/seed pairs, 16,810,248 candidate witnesses, 263,714 point-seed checks; 4,096 HF roots, 531,429 local-bound checks, 555,198 hull members, 65,536 singleton-decoding families; 4,000 randomized expansions and 4,160 model/template expansion checks. |
| 03 | 262,404 membership/matrix pairs; four unittest methods and 5,600 formula-semantics comparisons. |

Source 02 and 03's delivered PDF builders also completed on scratch copies.
This reproduced their builds, not a merged-report PDF or a formal proof.
Expanded metrics differ between sources and normalization policies: 01 gives
QBC 58/56 versus RCC 60/50; 02 gives T_pt 69, T_sub 72, Q_sub 83;
03 gives equality-free EFH control 65 versus prior extensional control 78
(raw nonextensional prior 61). Source 02 excludes variable payloads, arbitrary parameter closure, logical
equality machinery, the proof engine, and the TM backend. These rankings do
not predict machine states. Compare only within a declared metric.

From the repository root, reproduce all Python checks with:

```sh
uv run --no-project python SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/reproduce.py
```

The helper recovers each archive from the committed arrival into its own
new directory **outside** the repository, then runs the delivered commands
using the invoking Python. It reports the scratch location and retains run
logs there. Repository files and the intake extractions stay untouched; regenerated
outputs and logs remain in the recovered scratch packages. To recover the
full manuscripts without running suites, add `--prepare-only`. For a source's
PDF, run its recovered `build.py` there with a suitable TeX installation.

No external machine table, Coq end-to-end development, proof-producing theory
translator, enumerator correctness theorem, or ZFC endpoint was rebuilt here.


## Subsequent minimization research

After intake, [the ZFC machine project](../../../../../../Computability/BusyBeaver/Research/ZFC/README.md)
answered source 02's membership-arm deletion question at the mathematical
level by combining its positive hull with the gated singleton decoder.
`BusyBeaver/ZFC/PositiveClosure.lean` checks the key bootstrap lemmas;
`DeepPositiveClosure.lean` defines the actual equality-free first-order
wrapper and proves its semantic specification. `ProfileCongruence.lean`
checks that the symmetric congruence conclusion can be replaced by one
implication. Subsequently, `PSCCalibration.lean` proved deductive equivalence
of Extensionality plus subset-seeded PSC with first-order ZF without Foundation
or Choice, using actual formula instances in both directions. The remaining
effective Foundation/Choice consistency bridge and small-machine theorem
are open. The delivered source 02
article remains unchanged, including the question it left open.

## Batch 144: pure closure, hereditary saturation and machine experiments

Intake findings, 16 October 2026. Six further manuscripts extend this same
report. The first four arrived in `17d0f2eaa650901cda59764dfcc4661c199e49c8`,
the fifth in `39409c8c921cccdbd6162c8767c84cfb7df65df1`, and the sixth in
`83dec60c249ca0f9e1b2e5ee3cf18fd1ce58c373`. Placement `ac4287e5b` preserves their ancillary files. They answer the base's named
membership-arm/congruence questions or continue its complete-machine cost
question, so all are additions here. The original source 02 remains the
unchanged article base. This is again the reconciliation-note option;
no article or merged PDF is rewritten.

The source numbers below continue this report's local sequence. Batch
manuscript 01 is local source 04, and so on.

| Local source | Archive | Contribution retained |
|---|---|---|
| 04, machine | `zfc_machine_research.zip` | Pure/mixed schema equivalence without Extensionality; factored syntax and capture conditions; attributed upstream 253-state reduction; runtime-only 252 body and exact blank-start classification. |
| 05, subset | `zfc_subset_kernel_research.zip` | General pure/mixed theorem for any logically reflexive seed; separate four-node currying reduction; a bottom-based certificate checker and finite semantic regressions. |
| 06, pure | `zfc_subset_only_machine_research.zip` | Pure-subset calibration, exact bootstrap dependency ledger, certificate grammar and total finite-candidate specification; optional irreflexivity variant. |
| 07, codec | `zfc_tm_pure_subset_research.zip` | Directed Extensionality/congruence and currying controls; a four-tag total codec with genuine bottom; capture-avoiding checker and component cost ledger. |
| 08, schema | `zfc_one_schema_research.zip` | Equality-free PSC alone via hereditary saturation; interpretation of the entire extensional PSC schema; iterative binary checker; 281→269 Wade rebracketing experiment with an independent RM certificate. |
| 09, decoder | `zfc_machine_research (2).zip` | Empty-root decoder bootstrap; cofinal proof padding with retained-data conditions; 203→202 decoder certificate, 267→256 contextual-fold experiment, prepared-tape 252 body; logical-vacuity and CP-transitivity deletion obstructions. |

04–07 and 09 inspect the distinct ProveIt pins `b07d1a27b`, `83ef1da6b`
and `67086c8d8`. Source 08 additionally uses baseline
`6594795e9db81637c30959e42b3bcfc9eb77722f`. The earlier entries are
provenance, not a representation of the current formal status. All use
upstream `297ab8df7e5de329605c3875b4934643b371a5e3` for the original
benchmark. Source 04 separately pins the 253 reduction to
`0d544f2a2e3c18f12278441a74b7879f31cbe856`.

### Mathematical overlap and the new interpretation

04–07 and 09 independently rederive the membership-arm deletion. For every
fixed logically reflexive seed, their pure and mixed schemas are uniformly
equivalent **without Extensionality**: constant instances supply singletons;
a locally subset-bounded singleton decoder supplies a transitive cover of
all members of a bound; that cover absorbs its membership arm. This does
not require choosing a family of bounds. Converse iteration additionally
requires set-sized seed classes. The ZF comparison still retains
Extensionality, arbitrary formulas/parameters and functional Replacement,
and uses unique exact fibers instead of a choice of local bounds.

This is an answer to the historical question in `article.tex:403–406`.
At current HEAD it is a rederivation: `Computability/BusyBeaver/Research/ZFC/subset_only.md:5`
already says “Deleting the membership arm … preserves its calibration”, and
lines 94–102 give the switch proof. `PositiveClosure.positive_decoder_cover`
and `DefinableClosure.transitive_cover_of_model` check the bootstrap;
`PSCCalibration.psc_iff_zf0` and `psc_consistency_iff_zf0` already establish
the actual equality-bearing subset theory's deductive/consistency comparison
with ZF without Foundation or Choice. The explicit general pure/mixed theorem
without Extensionality and the alternate empty-root decoder remain useful
additional formulations; these deliveries contain no Lean implementation.

Source 08 supplies a substantial continuation of the proposal in
`Computability/BusyBeaver/Research/ZFC/raw_psc.md:136`: remove the separate
profile-congruence sentence from the **equality-free** subset PSC theory.
Let D be incoming-profile equivalence and O be incoming plus outgoing
profile equivalence. O is a congruence in pure logic, so O-singletons suffice
for the raw switch, Separation and Union. Raw objects can then be saturated
under D. Define S(a) to say its member extension is closed under D-equivalence, and H(a) to say
S(a) with a transitive cover whose members satisfy S. H is nonempty,
D-invariant and hereditary. If S(a) and all its members are H, separating
H inside any transitive cover proves H(a). This purity-cut argument
simplifies the existing unchecked least-transitive-cover proposal.

For an arbitrary translated matrix, raw PSC on the H-guarded relation
produces a hull containing only H objects. Saturating that hull under D
makes it H; formula invariance preserves its initial closure, recurrent
closure and unrestricted support. This interprets the full extensional
PSC theory on H/D. Our intake found no mathematical gap in that argument.
The delivered calibration is an ordinary proof, including a ZFC-level
set-coded-model/completeness argument and the Foundation/Choice bridge;
it is **not a Lean theorem or an exported proof-code translator**. The
source retains variants with logical equality or added irreflexivity, and
relative atom models showing raw congruence/irreflexivity need not follow.

Source 09 also records a distinct logical bridge for CP/GIC: equality can
be interpreted by two-sided observational profiles O. Its two-argument
membership congruence is purely logical. This does not permit replacing
actual equality by D in the existing bisimulation proof, deleting runtime
equality rules without a compiler argument, or identifying a membership
atom with falsity. Its pure-logic vacuity countermodel concerns that
logical fragment, not independence over CP/GIC. Its CP-without-transitivity
model uses the pseudo-hereditary construction at beth_omega and is a
relative infinite set-model argument, not a finite PSC model. Source 09
credits Greg Oman's construction. The cofinal-padding theorem distinguishes
completeness from arbitrary retained abstract data from soundness, which
requires theorem-valued current/cache/stack entries and an admissible
physical register boundary.

### Syntax and machine costs remain separate

In the common source-02 bottom/implication/forall occurrence metric,
04–07 reproduce mixed point/subset/symmetric-EF totals 69/72/83 and pure
65/68/79. Currying independently gives 61/64/75. Source 07 also directs
Extensionality and mutual-subset congruence, giving 58/61/64 in its declared
basis. The existing `ProfileCongruence.oneWay_iff_full` already justifies
the cheaper one-sided control; 79 is a historical symmetric control, not
the current best syntax. Source 08's unchanged project metric gives 71
for CG+PSC and 52 for PSC alone (56 with irreflexivity). None of these
numbers charges variable payloads, arbitrary parameter closure, the proof
calculus, initialization or the tape backend.

The checkers/codecs are distinct. Source 07's four-tag codec reserves
genuine bottom at code 1 (and bottom aliases), with Truth at 0 and an explicit
normalization of Truth→Truth. Source 08's binary checker has its own
iterative parser and fixed schema interfaces. Source 04's three-label
appendix retains its distinct-slot/freshness conditions and explicit
capture counterexample. These are not the project's experimental base-3
calculus, whose dual-quantifier replacement has a separately documented
logical gap. Source 08's Metamath ax467 lead is valid in its ordinary
negation calculus; it is not by itself a repair for relative falsity
`Rel(0,0)` in that experimental calculus.

Source 04 documents **mira-emmy's existing 253-state reduction**, derived
from Mira-Cult's machine and Jeff's verification, in
[upstream PR 20](https://github.com/jeff87654/busy-beaver/pull/20).
At intake the PR was open and unmerged at the pinned head. Both bundled
tables match the pinned public Git objects. We reproduced its entire
312,975-step blank boot: compact state 33, head −17, gap 40, logical
registers `[5,0,0,0,2,0,0,0,0]`, including all spare-tail data. This differs
from the original 254 boot; the normal register-program prefix and its
runtime invariant must be included in any new proof.
The GitHub job API reports success for
[the verification job](https://github.com/jeff87654/busy-beaver/actions/runs/38829452130/job/116744580063).
The reported 160-module/194-closed-report/coqchk details were not locally
rerun or independently recounted from CI logs (log retrieval returned 403).
No new Coq build was performed. The inspected upstream endpoint is an
external finite-refutation equivalence, with Foundation/Choice comparisons
separate; an internal arithmetized ZFC/PA proof does not follow merely
from that result. This report claims no authorship of that reduction.

The several 252 artifacts must not be conflated:

- Source 04 deletes the 253 initializer to obtain a 252-state **runtime
  body**. All 8,391 affine sites pass its protected-box audit. Of its 252
  blank starts, 234 enter blank rays; 18 reach one common two-one-cell
  frame within 44 steps. That common orbit has no established consistency
  interpretation. Seven longer startup trials and 56,196 direct redirections
  do not solve initialization or prove an impossibility result.
- Source 09's **prepared-tape** 252-state core has no blank initializer.
  Its separately emitted blank-start decoder variants have 267 and 256
  working states. The baseline decoder has 203 nodes, the candidate 202;
  its 2,985-pair RM certificate checks both decrement branches. Eleven
  folds receive affine instruction and finite boot checks under the
  published register-box contracts, not a new kernel proof of those boxes. Its rejected 201-node zero8 candidate,
  certificate and table are not bundled: the reported 3,092-pair/38-failure
  metadata were not independently replayed.
- The project's frozen **experimental blank-start** Wade 252 table changes
  the theory, coding and logic. Its calibration and compiler simulation
  remain unproved. It is neither of those prepared/runtime-only cores.

Source 08 instead rebrackets the existing 219-node recovered Wade program
into 207 nodes, reducing that backend's 281-state output to **269**, not
subtracting twelve states from the optimized 254 benchmark. Its independent
4,533-pair RM certificate matches the actual pinned source DAG, checks both
decrement exits and supports register-program halting equivalence. It proves
neither the Wade binary compiler nor the new PSC search. Its MIT-0 backend
files retain Andrew Wade's license; source 09's unchanged upstream Python
model files retain their attribution and ownership. No intake action
relicenses an upstream table or source.

### Placement, verification and rerunning

The exact 207-file rename map is `data/placement-map-144.json`, using prefixes
`04-machine-`, `05-subset-`, `06-pure-`, `07-codec-`, `08-schema-` and
`09-decoder-`. All copies came from a fresh untouched extraction. All 232
extracted blobs (226 distinct) were searched with `git log --all --find-object`,
and all nine hit records were confirmed in the introducing commit's tree.
The hits are borrowed baseline/backend/source-02 files, not repeated
archives; details are in `data/history-findings-144.json`. No checksum
manifest or line-ending work was done. All six committed ZIPs were retired
in the placement commit; their complete articles, section sources, PDFs and
delivery READMEs remain recoverable from their arrival commits.

The prefixed code retains its delivered imports and paths. In particular,
all build/reproduce scripts, Makefiles, nested engineering/checker READMEs,
provenance and QA records still name their original package layout, articles,
reference data, or external pinned inputs. Those are delivery-time paths,
not shipped unprefixed paths. Run the recovered copies, not the flattened
prefixed scripts. Checks ran only on separate copies:

| Local source | Reproduced evidence |
|---|---|
| 04 | Three standalone checks; all five extended engineering audits/searches, including 8,391 runtime sites, 56,196 redirections and seven two-million-step startup trials. |
| 05 | 28 unit tests, 18,080 schema comparisons, finite graph/HF transports, identity and 10,000-candidate prefix; table audit; scratch 24-page PDF. |
| 06 | 20 unit tests, finite graph/HF and formula/codec checks, identity and 10,000-candidate prefix; table audit; scratch 24-page PDF. |
| 07 | 24 unit tests, 66,066 graphs/1,052,740 graph-seed pairs, 100,000 numeric codes, 1,000 substitution and 72 currying comparisons; identity/schema examples. |
| 08 | 12 checker tests, 131,071-word census, six exact pinned schema comparisons, 530 finite relations; regenerated 269 table and 4,533-pair independent certificate; scratch 28-page PDF. |
| 09 | Exact arithmetic, HF, vacuity and template regressions; 2,985-pair certificate; all four tables' 8,391 affine cases, and the three blank-start tables' exact 264,982-step boots; regenerated tables/eleven folds, 100,000 rotations, 57,375 fold candidates, four C++ boot domains and 256 final boot folds; scratch 25-page PDF. |

Valid examples are explicitly non-refutations; bounded searches and finite
relations prove no consistency statement. Independently regenerated outputs
stay outside the checkout; original records remain unchanged. Sources 05/06/08/09's
scratch PDF builds reproduce their delivered articles, not a merged report.
No new Lean proof, serialized ZFC/PA proof, globally minimal theory/machine,
or completed sub-254 endpoint is supplied by these deliveries. The existing
Lean results listed above remain stated with their narrower proved scope.

From the repository root:

```sh
uv run --no-project python SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/reproduce_144.py
```

The helper recovers each committed archive into its own scratch directory,
runs all core mathematical/checker/table checks and retains logs there.
Use `--prepare-only` to recover without execution, `--sources 5` to select
batch manuscript 05, `--engineering` for source 04's extended diagnostics,
and `--rebuild-variants` for source 09's regeneration and eleven folds.
Manifest-only checks are excluded; source 08's components run directly
because its aggregate driver always checks a checksum manifest. To rebuild
a delivered PDF, run its recovered build command in that scratch package.

## Batch 145: equality erasure and smaller compiler artifacts

Two further additions arrived in `9c98495586c2a3b49e76ccb0d4e29cebc824903b`
and `96836f9eea3540e96322c3d28c7127a582aae223`, respectively. Placement
`3cc6ba5b1` retains their ancillary material under the next local prefixes.
Both continue the existing source-theory, numeric-calculus and complete-machine
questions. The base article is unchanged; this section reconciles the new
material without building a merged article or PDF.

| Local source | Archive | Contribution retained |
|---|---|---|
| 10, twins | `zfc_small_machine_research.zip` | Two-sided equality erasure for CP/GIC; standalone Lean semantic lemmas; canonical base-three codec; cross-variable instantiation diagnostic; 250-state conjunction-reordering experiment and a 348-state translated-equality control. |
| 11, grammar | `zfc_small_machines_20261016.zip` | Reconstruction of PSC-alone and raw CP/GIC calibrations; exact implicational-schema parameter permutation; original-row and dual-row 248-state grammar-compression experiments, each with an independent 3,394-pair register-operation certificate. |

Both use executable ProveIt baseline
`17d0f2eaa650901cda59764dfcc4661c199e49c8`. They inspect the four requested
earlier pins and the later `fa6fcaf09`/`29efd22e` developments; source 11
extends its source audit through `83dec60c249ca0f9e1b2e5ee3cf18fd1ce58c373`.
Their inherited benchmark inputs still use upstream `297ab8df7e5de329605c3875b4934643b371a5e3`,
with the separate attributed 253-state PR head `0d544f2a2e3c18f12278441a74b7879f31cbe856`.
These are provenance cutoffs, not descriptions of today's remaining formal gaps.

### Mathematical and formal reconciliation

Source 10 interprets equality by agreement of **both** incoming and outgoing
membership profiles. This relation is an equivalence and membership congruence
in pure logic. Formula induction and capture-safe equality replacement give an
ordinary conservative interpretation for equality-free conclusions of the
raw CP/GIC theory. Source 09 already records this source-theory bridge; source
10 makes the proof transport and its proposed PA formalizability more explicit.
It does not identify that profile relation with actual identity on raw objects,
incoming-profile equivalence, or the bisimulation equality of another model.
Neither erasure nor its PA formalizability is a delivered proof-code translator.

Its unchanged `formal/AtomicEquality.lean` independently compiled with Lean
4.32.0. All seven printed theorem roots have no axiom dependencies:
`indiscernible_refl`, `indiscernible_symm`, `indiscernible_trans`,
`membership_congr`, `satisfaction_invariant`, `equalityFormula_correct` and
`equality_erasure_correct`. The last three check arbitrary-formula semantic
invariance and the de Bruijn equality erasure in the file's own syntax.
They prove no derivation translation, CP/GIC calibration, quotient construction
or machine theorem. The existing `RawPSCProfile.full_mem_congr` already checks
the basic full-profile congruence in the research library; an explicit syntax
adapter is still needed to reuse the delivery's additional semantic results.

Both papers' canonical base-three account handles code 0 as Truth and excludes
the `Imp(Truth,Truth)` collision. This confirms the existing
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Base3Syntax.lean` results:
`encode_decode`, canonical `decode_encode`, smart implication compatibility
and label freshness, including code 0. Their historical suggestion that only
positive finite syntax has a Lean treatment is superseded by that module.
Codec coverage alone supplies no numeric-calculus completeness theorem.

The papers correctly separate that issue. Identity quantifiers validate the
retained logical rows and same-name instantiation while independent membership
atoms can falsify cross-variable instantiation. This is a logical-fragment
countermodel, not a model of the entire CP/GIC theory or a proof of unconditional
machine nonhalting. Source 11 also reconstructs the original/dual-row distinction
and an arbitrary-added-theory refutation counterexample. It does not settle
refutation equivalence over the actual C/G bundle. Retaining the original row
avoids the additional dual-row change but does not repair the missing equality
rules' instantiation and renaming consequences.

Source 11's PSC-alone and equality-free CP/GIC arguments are ordinary
mathematical reconstructions of the source-08 and source-09 spines, respectively.
Its abstract enumerator theorem is likewise an ordinary proof about its stated
commands and register-boundary invariants. No delivery formally connects that
enumerator, the exact numeric calculus and the binary interpreter. The inherited
PSC reference checker is a separate prototype, not the program executed by either
248-state table. Its bounded census finding no refutation proves no consistency
statement.

### What the state reductions establish

Source 10 commutes internal relative conjunctions and reassociates the outer
C/G/vacuity bundle. Since `And_F(A,B) = F ∨ (A ∧ B)`, these changes preserve
ordinary semantics even when `F = Rel(0,0)` is true, without moving binders.
The full 9,216-choice search reproduces both 250-state minimizers. The selected
table has 188 decision states plus 62 unchanged framework states, 500 rows,
start 0 and terminal target 250. Its normalized table SHA-256 is
`d7af3920268db1c95bf71dc06b77e53c8266086a13043b2fc91f9319c520aff1`.
The rewrite does not resolve the inherited dual-row or full-calculus gaps.
The separate 348-state control retains GEN and all eight original logical rows,
replacing Eq by two-sided profiles; its measured cost is not a lower bound or
a certified endpoint.

Source 11 first permutes the four independent parameters of the implicational
schema. Its two displayed inverse permutations give **literal identical
instance sets**, without a relative-falsity assumption. Weighted Re-Pair,
attributed to source 08, then preserves the expanded 138-macro word while
changing its binary grammar. The fixed original-row seed 122/exponent 2 and
dual-row seed 39/exponent 2 each produce 186 decision plus 62 framework states.
Both complete blank-start tables have 496 rows, start 0, terminal target 248:

| 248-state table | SHA-256 |
|---|---|
| Original quantifier row, recommended | `e9cf9241e0012c56ecf4dc55f969d4c01e988a5c3839c9e4a49b5fae33591d45` |
| Dual quantifier row, comparison | `70d141e1a2872a3080b525a4061b48882131e636c41444f09bc065647a7e4a6c` |

Each independent certificate checks 3,394 related operation sites: 1,902
increment pairs, 1,491 decrement pairs and one halt pair. Register indices and
both decrement exits match, and contracted control paths terminate without
changing registers. This supports the stated ordinary register-program halting
equivalence from **any common register vector**, not just an observed blank run.
The independent checker and eight rejected certificate mutations were replayed.
No finite certificate was checked inside Lean, and no binary compiler theorem
is supplied. The later research `RegisterBisimulation.halts_from_any_registers`
checks the generic exposed-operation theorem only, conditional on instruction
matching; it does not instantiate either certificate or justify control-path
contraction.

All 248 and 250 working states are graph-reachable. Exact step bisimulation and
the radius-4/64-step conservative audit found no safe merge. All three million-step
prefixes end at state 24, head 248, with 223 one-cells; the 250 prefix never enters
the edited AX routine. These are finite diagnostics, not nonhalting proofs or
minimality bounds. The sole missing named backend row is explicitly totalized
by a final move into the terminal state; halting is preserved under that
convention, although the final head may move.

Thus the 248 original-row artifact is the preferred new **compiler experiment**.
Neither it nor the 250/dual-248 alternatives is a proved sub-254 ZFC-consistency
machine. The attributed upstream 253 endpoint remains separate prior work;
no new Coq build or exported internal ZFC/PA proof was performed in this intake.

### Placement, verification and recovery

The exact 90-file map is `data/placement-map-145.json`, with `10-twins-` and
`11-grammar-` prefixes. All 98 extracted blobs (95 distinct) were searched in
history, and all 25 hit records were checked in the relevant commit trees.
They are borrowed project, backend, checker or benchmark files, not previously
placed whole archives; see `data/history-findings-145.json`. No checksum-manifest
or line-ending work was done. Both archives were retired in placement, while
their complete articles, section sources, READMEs and PDFs remain recoverable
from their arrival commits. The unchanged base article still belongs to source 02.

Checks ran only on separate copies. Source 10 passed its logic diagnostic,
100,000-code audit, both complete bounded searches, all eight older backend
measurements, 250-table regeneration/normalization, full-tape named/numeric
lockstep, and 348-control regeneration with 16,384 binder cases. Its standalone
Lean file compiled independently; its scratch PDF has 22 pages. Source 11 passed
11,000 codec cases, 5,712 macro contracts over four AX profiles, both independent
certificates, regeneration of all twelve fixed artifacts, the inherited 12-test
PSC suite and its 131,071-word census, both conservative audits, and all eight
certificate mutations. Its scratch PDF has 27 pages and no reported warnings.
Authored review dossiers and replay records use the `intake-145-` prefix here
and in `data/`; delivered records were not replaced by regenerated outputs.

Recover and replay the Python checks from the repository root:

```sh
uv run --no-project python SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/reproduce_145.py
```

The helper uses committed archives and the source-10 pinned Git objects, with
no network or checkout writes. Use `--prepare-only` to recover the full articles,
`--sources 1` or `--sources 2` to select a batch manuscript, and `--searches` to
repeat source 10's 288- and 9,216-choice searches. The source-11 release-manifest
function is bypassed in memory; its mathematical, table, certificate and fixed
regeneration checks run unchanged. PDF and Lean builds are separate commands
on recovered copies, not part of this Python helper. Prefixed delivered scripts
retain their original imports, layout assumptions and provenance paths; run the
recovered packages rather than those flattened copies.

Source 11's retained `11-grammar-provenance-REBRACKETING_248.md` also names
`TM_ENGINEERING.md`, which is not shipped in that package. This delivery-time
reference is preserved, with no substitute file invented. Since placement,
`Table248.lean` checks the original-row literal table and its actual first
1,024 blank steps; `RawPSCModel.lean` supplies named instances from the actual
equality-free PSC model. Neither adds the missing whole-machine endpoint.

## Batch 146: a full-calculus obstruction and complete-logic alternatives

Four further manuscripts arrived in `47f3a3602946dfe48803a91a910c646e74637ac8`
and `af518abcf8ca2a7c1b795c07973885041aee0d25`. Placement `f31ba244b`
retains their ancillary material under the following local prefixes. The
base article and all delivered claims remain unchanged; the findings here
update their historical research recommendations.

| Local source | Archive | Contribution retained |
|---|---|---|
| 12, sorts | `zfc_consistency_machine_research.zip` | Explicit finite-sort semantics for every raw C/G code axiom and rule; abstract-enumerator nonhalting; conditional literal consequence; 259/264-state diagnostic controls and a separate PSC supplement. |
| 13, tableau | `zfc_consistency_proposal.zip` | Alternative PSC-only bootstrap using incoming-profile fragments and a nonempty monochromatic decoder; ordinary Infinity; complete environment-tableau reference and ten full-original-logic compiler controls. |
| 14, empty | `zfc_empty_seed_research.zip` | Empty-input EPSC deductively equivalent to subset-seeded PSC; reduced-calculus obstructions; a complete-logic reference checker and full-equality 270-state compiler control. |
| 15, modal | `zfc_small_machine_proposal.zip` | Full ordinary equality-free CP/GIC interpretation and designated-theoremhood calibration; exact-word 250/249-state grammar experiments and a bounded nonreflexive-quantifier diagnostic. |

Source 12 freezes compiler inputs at
`83dec60c249ca0f9e1b2e5ee3cf18fd1ce58c373`; its later PSC-only supplement is
separately pinned to `e7c4cadf9b180e4b1801755b09777a7572412360`. Source 13 uses
the numerical pin `17d0f2eaa650901cda59764dfcc4661c199e49c8` and reviews research
through `bda2b4860e6b3664d8ae84978bd7683572f55f49`. Source 14 uses the 83dec60
baseline. Source 15 uses 17d0f2e for numerical replay and e7c4cad for its research
cutoff. Their inherited backend/254 pin is still
`297ab8df7e5de329605c3875b4934643b371a5e3`; the separately attributed public
253-state reference is still PR20 head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`. These provenance statements do not
claim a new remote-status check or proof-assistant rebuild.

### What the finite-sort countermodel changes

Source 12 supplies the previously missing obstruction for the **entire emitted
raw C/G calculus**, beyond the earlier isolated logical-fragment models.
Its finite sorts have sizes `d₀ = 2`, `dᵢ₊₁ = dᵢ + 2^dᵢ`. Diagonal membership
is false; every sort has empty and universal incoming objects for other sorts;
a larger sort represents every subset of a smaller sort. Quantification changes
one coordinate over its own sort. This validates the retained propositional,
distribution, commutation, original and dual quantifier rows, gated membership
vacuity, MP and generalization, while target code 1 is always false.

The numerical support bound applies to **every natural code**, with code 0 as
closed truth and `Imp(0,0) = 0` respected. Matrix code c is independent of labels
c and above. That locality is essential to G when its output label b exceeds c;
when b is smaller, the larger output sort represents the exact finite range.
The proof also covers a=b, the failed c=a/b gates, repeated-binder shadowing,
and matrix codes 0/1. Independent comparison confirmed the exact current C/G
constructor trees, including collisions, and all eight functional compiler
inputs agree with the report's immutable pin and the current tree.

Validity of current formula, old cache and every theorem-stack entry is
preserved by the exact abstract MP/DROP/NIP/AX operations. GEN reads the old
cache; failed MP and failed gates write truth; the zero stack tail is valid.
Thus ZFC proves this exact-arithmetic abstract enumerator never reaches its
incoming-cache-1 halt test. The argument uses no assumption of Con(ZFC).

The obstruction transfers to source 10's 250-state conjunction rewrite and source 11's
original-row/permuted-rho8 248 program: the former only commutes conjunctions
and reorders valid rows, and the latter permutes a propositional schema's
parameters and preserves its macro word. It also covers source 15's two
exact-word raw C/G rewrites and source 12's inspected fresh-label PSC-only
supplement, including primitive Bottom and optional irreflexivity or same-name
specialization. Restoring the original quantifier row alone does not repair it.

This is an ordinary mathematical theorem about the intended numeric calculus
and abstract enumerator, **not a literal-table nonhalting proof**. If its
literal-halting-to-abstract-halting simulation is proved in ZFC, literal
nonhalting follows in ZFC; assuming Con(ZFC), that same machine cannot then
have the requested ZFC-provable equivalence with Con(ZFC). The finite table
facts and source compression certificates do not supply that simulation.

The batch 145 description of the original-row 248 artifact as the preferred
compiler experiment is retained as historical context. Its state savings and
the later 249/250 savings remain reproducible compiler benchmarks. The raw
calculus now needs a complete logical frontend rather than an unproved
calibration of its existing rows. This does **not** retract the ordinary
one-sorted PSC/EPSC or CP/GIC source theories, their mathematical interpretations,
or the full-equality public 253/254 benchmark. The 282-state profile control and
new 259/264-state U/P diagnostics reject this model; rejecting one model proves neither
logical completeness nor a consistency endpoint.

### Ordinary theory results and reference proof engines

Source 13 credits source 08's PSC-only calibration and purity cut. Its
alternative bootstrap uses exact incoming-profile fragments and explicitly
nonempty monochromatic fibers, avoiding global outgoing-profile congruence.
The Russell-root image argument gates its root outside the source set;
unique exact fibers justify the converse without selecting arbitrary local
bounds. Its hereditary interpretation includes a direct ordinary Infinity
construction. The complete six-rule signed tableau uses environments for
bound variables, arbitrary universal instances and fresh existential witnesses.
Its fair certificate search accepts only an actual refutation of logical
Bottom; the supplied valid theorem demonstrations are not refutations.
These are reviewed ordinary arguments and Python references, with no checked
tableau-to-register or binary compiler.

Source 14's new EPSC theorem removes PSC's arbitrary seed parameter: closure
starts from the class of **all raw empty objects**, not a distinguished empty
constant. EPSC and subset-seeded PSC are deductively equivalent through uniform
finite-instance transformations in the same equality-free language. With the
credited source-08 interpretation this gives the same ordinary ZFC-provable
consistency calibration. Its grafted decoder, common subset bounds and support
filter need no separately imposed Extensionality, congruence or irreflexivity.
The theorem remains about an infinite schema with arbitrary matrices and
finite parameters. Its fixed-slot, arbitrary-label and fixed-offset Boolean
interpretations reject the reduced PSC/EPSC proof engines, including the
irreflexive variant. Those particular models are not C/G models; source 12
supplies the stronger C/G result. Its reference checker restores genuine
Bottom and capture-avoiding universal instantiation in a complete ordinary
first-order calculus, with the disclosed Python recursion limits.

Source 15 independently reconstructs the ordinary CP/GIC theory interpretation:
bounded profile-pair codes, exact represented composition, bisimulation equality
and membership congruence, interpreted Power Set, ordinary Infinity and
Replacement unique up to that equality. It calibrates the theory with or
without irreflexivity. Its complete-first-order auxiliary theories S_B/S_D
calibrate **theoremhood of target F** against inconsistency; S_D itself always
has a model and is not an equiconsistent theory. None of that theorem replaces
the restricted logic in the small tables. Its recommendation to settle the
actual C/G target is superseded by source 12's finite-sort result. The bounded
modal search rejects every tested frame already at C; finding no model in
that family gives no evidence of logical completeness.

### Compiler evidence and current Lean boundaries

Source 12 reproduces the frozen raw 252-state table and the 259/264-state U/P
diagnostics.
Its 288-control search comprises 120 bundle layouts per control and 24 logical
orders for each first best layout, not a full Cartesian search or lower bound.
The supplemental PSC 252-state artifact is a different table and calculus
from the frozen C/G 252-state experiment.
Seven fixed PSC recipes were replayed; its historical 144-layout/200-seed
searches were not repeated in this intake.

Source 13's ten base-four controls retain all eight original logical schemas
and separate vacuity gates. All ten regenerate exactly; the smallest measured
point/subset controls have 276/280 states. Dropping the extra theory gate uses
its explicitly checked low-code comparison, not removal of the logical gates.
The optional `optimize_psc_orders.py` referenced in its notes is absent from
the delivery. Its recorded 2,229-order optimization is therefore source evidence,
not a bundled replayable suite; no replacement script was invented.

Source 14's full-equality EPSC control has 208 decision plus 62 framework states,
540 total rows and SHA-256
`54d631fa31f36b02dd41634de8cadeb2cc8fcfae4bc75fea8812af0794b2a136`.
Its independent operation certificate has 3,620 pairs and checks 5,162 successor
pairs. The source is a 266-node plain right-comb EPSC program, **not** the old
C/G program or the best 277-state experiment's DAG; the compressed DAG has
208 nodes. All 2,048 selected grammar choices were rerun, but 2,045 were
heuristically screened and only three emitted. No minimum or end-to-end
calibration follows. Its changed theory, enumerator, binary compiler and
initializer still need proofs.
Its rejected reduced 248-state EPSC and 250-state PSC artifacts are distinct
from the earlier C/G tables with the same state counts. The grammar helper
and operation-verifier adaptations retain their source-08 attribution.

Source 15's original-row 250-state and dual-row 249-state tables have 500/498 rows
and hashes
`2bc151a7ba41fab11a2ebf15c7c9913acf46241843ec12e4bec48417153d8cd0` and
`711d6edf4a523db3d8861387636dbc8fc028eb74a7f4d3f174060a128d04a3a9`.
They preserve their respective 138-call AX words and unchanged program context;
all 19 macros have only normal finite control exits. This establishes the
stated source reassociation property, not arithmetic termination or binary
simulation. Both tables regenerate exactly, have graph-reachable working states
and singleton exact step-bisimulation classes, and match their recorded
million-step prefixes. Their experimental original-row 254-state source is distinct
from Mira-Cult's calibrated 254-state machine.

The present Lean modules already close some historical roadmap items. The
source comments state the remaining scope precisely:

- `Base3Syntax.lean`: “This is a numerical syntax theorem, not a calculus,
  semantic interpretation, compiler simulation or ZFC equiconsistency proof.”
  Total decoding, truth normalization and numerical freshness are checked.
- `CompositionModel.lean`: “This is an interpretation layer, not a coded proof
  compiler or TM endpoint.” Actual equality-free GIC matrices supply composition
  and matching resources; this is more than an assumed semantic composition
  hypothesis, but less than a full interpreted-theory endpoint.
- `RawPSCModel.lean`: “These results do not yet prove the complete hereditary
  interpretation, deductive/consistency calibration or any compiler or machine
  endpoint.” Named represented matrices now supply cover/Separation/Union,
  saturation and purity-cut resources; guarded hull transfer still assumes the
  supplied relation's definability, local bounds and invariance.

All three paths are under `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.
The current 35-module dependency closure passed a fresh serial Lean check;
the delivered countermodel, complete theory interpretations, reference checkers
and new operation certificates have no new kernel calibration. Existing
Table248/Table252/Table253 literal facts and the 248/253 short prefixes retain
their finite scope. No new sub-254 consistency-machine endpoint is claimed.

### Placement, checks and recovery

`data/placement-map-146.json` records 170 retained ancillary files and 48
archive-only manuscript/PDF/section/delivery-README paths. All 218 extracted
files, representing 201 distinct blobs, were searched throughout Git history;
20 borrowed blobs occur among 37 relevant commits, with own/parent tree
occurrences recorded in `data/history-findings-146.json`. They are inherited
sources and artifacts, not previously placed copies of the four full reports.
All archives were retired in placement. Complete packages remain recoverable
from their arrival commits, with their original nested names and layout.

Checks ran on separate copies. Source 12 passed all finite model regressions,
seven table checks, exact 253/raw252 regeneration, all 288 diagnostic controls
and seven fixed PSC recipes; independent AST and source comparisons also passed.
Source 13 passed its tableau/search suites, all 66,066 small decoder graphs,
276 exceptional-row cases, the full 312,975-step literal 253 bootstrap and all ten
compiler controls. Source 14 passed its 11 checker tests/9,216 substitution cases,
coding/logic/model suites, both 192-choice rejected reduced searches, the 192
full-equality arrangements, the 2,048-choice screened grammar search, exact 270-state
regeneration and independent certificate/mutation checks. Source 15 passed its
codec/logic/table suites, both exact fixed grammar replays and bounded modal
diagnostic: all 68 tested relations fail C, with 1,760 C and 512 G evaluator
crosschecks and zero surviving all-matrix G checks. The four scratch PDFs have
34/32/35/41 pages. These are finite evidence and ordinary proof reviews; no
Coq or Lean build was performed as part of these delivered-package suites.

Authored dossiers and replay records use `intake-146-` names; generated outputs
do not replace delivered records. No checksum-manifest or line-ending work was
performed. Recover and replay from the repository root:

```sh
uv run --no-project python SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/reproduce_146.py
```

The helper recovers committed archives and local pinned Git dependencies
without network or checkout writes. `--sources 1` through `--sources 4` select
the batch manuscripts corresponding to local 12 through 15; `--prepare-only`
recovers without execution. `--searches` adds source 12's extended 288-control
and fixed-PSC checks and source 14's bounded search families. Broad manifest
audits are bypassed in memory; table identity and functional compiler pin
contracts remain. PDF and proof-assistant builds are separate. Flattened
retained code keeps its original imports and nested provenance names; execute
the recovered packages rather than renaming paths inside delivered scripts.

## Batch 147: genuine ternary Bottom and a complete reference calculus

Source **16**, `zfc_small_machine_research (2).zip`, arrived in `9439d775aa`
and was placed in `520bcb2a1`. Its main review pin is
`96836f9eea3540e96322c3d28c7127a582aae223`; the inherited machine/backend pin
is `297ab8df7e5de329605c3875b4934643b371a5e3`. It continues this report's
PSC, numerical syntax and proof-language spine. The source 08 PSC calibration
is explicitly credited, as are Mira-Cult, Jeff and Andrew James Wade. No
blanket license is inferred for unlicensed upstream material.

The manuscript independently reconstructs the accepted ordinary raw-PSC
interpretation, including the full incoming/outgoing profile decoder,
hereditary saturation, noncircular local bounds, and the extensional
exact-fiber converse. Its Empty/Power argument excludes finite models without
requiring Extensionality. These overlap source 08 and the later Lean resources;
they do not fill the still-open whole-theory Lean interpretation.

The new numerical codec reserves code 1 as primitive Bottom while moving
membership from `3P(i,j)+1` to `3P(i,j)+4`. Truth 0, implication `3P` and
universal quantification `3P+2` are unchanged. Every natural decodes exactly;
formula round trips recursively contract only Truth→Truth. This is neither
alpha canonicalization nor arbitrary Boolean simplification. Every variable
label, including binders, remains below the matrix code, so `code+2` is fresh.
Subsequent repository work in `830647031`, independently reviewed at intake,
formalizes these all-code round trips, canonical injectivity, freshness and
ordinary semantic preservation in `Bottom3Syntax.lean`. All 36 source units
pass a fresh serial check. The theorem names and exact limits are recorded in
`Computability/BusyBeaver/Research/ZFC/bottom3_codec.md`; no delivered code
acquires formal status merely from this related module.

The complete reference checker uses K/S/C, arbitrary capture-avoiding
cross-variable UI, QD with its free-variable side condition, MP and theorem
GEN. It constructs closed PSC axioms with simultaneous safe slot replacement
and parameter closure. It accepts no arbitrary assumptions or claimed
conclusions. Its flat syntax and fair enumeration of finite byte strings
support the ordinary soundness/completeness and reference-search argument.
This is a separate unbounded algorithm, not the frontend of any supplied table.
The checker and its Python runtime are not kernel verified.

| Source 16 experiment | Decision + framework | Total binary rows |
|---|---|---|
| Original-rho6 C/G/V, relative falsity | 188 + 62 = **250** | 500 |
| Same word, genuine ternary Bottom | 189 + 62 = **251** | 502 |
| Fixed-slot PSC, genuine ternary Bottom | 190 + 62 = **252** | 504 |

These are distinct from earlier artifacts with the same counts. V means
inherited atomic membership vacuity, not a new instantiation rule. The
250 control preserves its exact 138-token macro word; its 254-state
predecessor was an experimental equality-free Wade output, not Mira's
published machine. The overlap-safe weighted grammar handles repeated equal
tokens. All 19 macro roots have no escaping control flow; exact-word
preservation supports the ordinary partial-transformation composition proof.
No operation-bisimulation certificate is included in this source. The Bottom
change makes the existing add-four helper reachable at a one-state cost.
All named tables lack only `1.inc/read1`; normalization adds write1/R/halt
without another working state. All original actions and the unique added
row were independently compared. The count includes initialization.

**The current finite-sort obstruction also covers the new 251 codec.** Its
strict label bound survives the membership offset, Bottom is constantly
false, and the actual C/G ASTs, gates and logical stack are unchanged. Thus
both C/G experiments remain excluded as intended abstract consistency
searches. The source's exact fixed-slot PSC identity-quantifier model also
excludes its 252 frontend, even after adding same-variable specialization
and explosion. Generic identity-quantifier and constant-true diagnostics are
kept at their stated narrower scopes. None is a refutation of ordinary full
first-order PSC. Literal-table nonhalting still requires simulation; no such
unbounded theorem is inferred from the finite tests. The source's historical
recommendation to calibrate its 251 C/G program is retained here as superseded
research advice, with the obstruction explaining why.

Other retained proposals are the finite universal-Horn encoding of a fixed
machine (free term constructors, exact reachable configurations and a halting
denial), finite class-theory and Craig–Vaught expansions, Diophantine coding,
and a total theorem constructor returning Truth on invalid local steps. The
Horn consistency/nonhalting equivalence has a valid ordinary proof; it simply
moves program data into clauses. None of these alternatives supplies a measured
smaller complete machine. The theorem-constructor plan still needs both
refutation transports, totality, capture-safe substitution, canonical
comparison and an implementation that counts all program/data-writing costs.
Weak universality with a periodic infinite background is not a free blank-tape
simulation. All of these are preserved further questions, not omitted results.

Independent scratch verification reproduced:

- Twenty checker tests and a five-line identity certificate, explicitly not a
  refutation; 9,600 substitution and 9,600 UI semantics cases, 1,280 PSC
  comparisons, 10,000 malformed inputs and one huge variable index.
- 200,000 numeric codec round trips, 5,000 formula round trips, 5,000 renamings
  and 20,000 semantic comparisons; 2,000 fixed-slot cases and three exact
  wrapper AST comparisons.
- All nine table/name-map outputs and two sets of 225 constructor contracts;
  2,200 original-row seeds (128 minima 250), and 200 seeds in each Bottom lane
  (eight minima 251; only seed 93 attains 252). Entire recorded search metadata
  match. These are bounded-family minima, not lower bounds.
- Conservative graph/bisimulation/window audits of all three tables and the
  auditor's eleven regression cases; no safe state merge found.
- Three-pass PDF rebuild: 25 pages, nineteen embedded fonts, zero warnings or
  cross-reference defects; all-page contact sheet and four enlarged pages
  visually inspected. The delivered PDF remains recoverable in the archive.

All 74 delivered files (67 distinct Git blobs) were searched in history;
14 previously occurring blobs are borrowed inputs/licenses, not a repeated
manuscript. Placement preserves 64 ancillary files with prefix `16-bot3-`.
The ten article/section/PDF/delivery-README files remain archive-only.
`data/intake-147-placement.json` maps every path, with maximum Windows-prefixed
length 148; `intake-147-placement-check.json` verifies all placed blobs in the
placement commit's own tree against fresh extraction. Original source layout,
imports and paths remain verbatim. In particular the copied upstream notice
refers to a larger historical import, not all files in this subset. No
checksum-manifest or line-ending audit was performed.

Detailed reviews: `intake-147-source-16.md` (theory/checker),
`intake-147-source-16-machine.md`, `intake-147-source-16-article.md`, and
`intake-147-source-16-lean.md`; associated `data/intake-147-*.json` records give
exact evidence. Recover and rerun outside the checkout with:

```sh
uv run --no-project python SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/reproduce_147.py
```

All six default jobs pass. `--searches` additionally repeats the bounded search
families; `--prepare-only` recovers the original layout. The helper excludes
only the delivered source-manifest audit in memory, reporting zero such
verified files; exact functional and generated-table contracts remain. The
base article and all delivered files remain unchanged. The complete internal
ZFC equivalence and binary compiler endpoint remain open.

## Batch 148: PA obstruction and complete ground-clause search

Source **17**, `zfc_consistency_machine_report_20261016.zip`, arrived in
`5e5603303d` and was placed in `30e6d1fd1`. Its audit cutoff is
`47f3a3602946dfe48803a91a910c646e74637ac8`. The PSC interpretation, sorted
countermodel and schema constructor are credited to sources08/12/13;
the full-word grammar tools descend from source 08, with ProveIt helper pin
`17d0f2eaa` and upstream Mira-Cult/Jeff/Wade pin `297ab8df7e`. The attributed
public253 proof is a prior benchmark, not a new result of this manuscript.
No Coq build was repeated at intake.

The report strengthens the ordinary finite-sort obstruction to **PA**.
It encodes assignments in mixed radix with A(n)=product(i<n,d_i), computes
truth tables for all codes k≤n, and bounds their concatenation below
`2^((n+1)A(n))`. Primitive-recursive coordinate updates, table construction
and ambient projection coherence yield one uniform validity predicate Val(k).
All C/G witnesses are bounded arithmetic sums/tests. Induction proves the
validity of every finite proof and every current/cache/stack entry of the
abstract enumerator, while target 1 is false. The argument is accepted as an
ordinary proof of PA provability; neither a PA derivation nor a Lean theorem
is delivered. Entry/read counts are not bit-operation runtime bounds. The
literal-table nonhalting conclusion remains conditional on simulation.

A general fresh-hull theorem isolates the obstruction: for distinct input
and output labels i,j, a hull label k with j<k and k≠i, and a matrix omitting
k, sort k represents its entire finite output range. This validates guarded
closure and support for **any** additional guard and boundedness antecedent.
The argument also works when the guard mentions the hull. Merely changing
that guard, adding same-variable UI or using primitive Bottom cannot restore
a common-domain first-order calculus.

The new complete reference instead compiles finitely many actual PSC instances
to signed Skolem clauses, then checks a ground clausal trace. Universal names
are standardized apart; every existential occurrence receives a fresh symbol
with all active universal dependencies. A dummy constant provides a nonempty
common term domain. Ground substitutions check exact arities and permit
identification of different variables. Two instructions extend by a ground
clause or close the newest literal against a complementary ancestor; every
pending sibling must close. Empty clauses, empty conjunctions, shadowing,
trailing instructions and malformed references have their stated treatment.

The ordinary proof combines equisatisfiable clausification, Herbrand's theorem,
propositional branching completeness and fair enumeration of finite matrix
lists, terms and traces with strictly decreasing child codes. Closing at the
first complementary pair justifies the newest-literal restriction. The actual
PSC entry point reconstructs every axiom from its matrix and admits no generic
extra-theory input. Its ideal unbounded algorithm has the intended refutation
contract and ordinary ZFC calibration. Host resource exhaustion is an error,
not a refutation; the Python runtime, whole compiler and binary state cost
remain unverified. Its generic inconsistent example and specialization
certificates are **not PSC refutations**. This is a complete reference frontend
and a concrete replacement to measure, not the algorithm compiled by its
separate 270-state control.

That control retains **all original equality, logical and theory rows**.
It preserves a 186-token expansion of the original AX word, with seventeen
used closed macros, and transforms 219 decision nodes to 208. The public
framework contributes 62, so the actual output has **270 named working states,
539 partial rows**, start `0.boot.A`, and only `1.inc/read1` undefined. No total
numbered table is delivered. The 4,000-choice search (1,000 seeds at each
exponents 1/2/4/8) reproduces every histogram and all six output artifacts.
The selected recipe is exponent 4 / seed 287, with 26 productions and 78 residual
tokens. Its independent register certificate verifies 4,533 operation pairs
(2,601 increments, 1,931 decrements, one halt), both decrement exits, all related
sites and entry, and finite contracted control paths. Both unfolded programs
have 6,460 sites. Six certificate mutations are rejected. This is an ordinary
register correspondence, not a binary simulation or an instance of the Lean
register theorem. The prior source 08 recipe was also reproduced at 269 states:
its coarser 185-token word expands to the same 186-token word. The new control
is therefore a comparison, not a new state record or lower bound.

The article retains finite predicative class theory (with set Choice), its
possible 15-axiom presentation and proof-elimination obligations, and the
artificial SK carrier route. Neither provides a free small interpreter or
expanded fixed payload. A primitive-recursive external proof transformer
alone is not a PA proof of its correctness. Equality/nontriviality, full
initialization, term coding and program-writing costs remain part of every
proposed machine. The six-interface roadmap and further questions remain open
where they require full translation, enumeration, runtime or consistency proofs.

One local external inference is corrected. We inspected the primary
[Friedman manuscript](https://bpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2020/09/NBGAxioms091520.pdf),
Theorem 3.21, printed page 19. Let A={0,2}, with witnesses (0,1) and (2,3).
The family containing only `{0,{0,1}}=A` covers A by union, although input 2
is covered through another input's second component; its double union omits
witness 3. Thus the displayed untagged extraction does not follow from Capture.
This refutes that step, not Capture or the theorem's global NBG equivalence.
The supplied repair tags inputs `<0,x>` and outputs `<1,y>`. The tagged input
set is bounded in a double power set, without Replacement; disjoint tags force
correct extraction, and triple Union bounds the witnesses. Extensionality,
Pairing, Union, Power Set, limited comprehension, subclass-of-set and distinct
tags are explicit assumptions. No Choice, Collection, Foundation or Infinity
is used beyond those resources. No current repository assertion of the faulty
step needed a pre-placement retraction.

Independent finite checks reproduce 159 formulas / 2,862 finite
structure-Skolem comparisons, all 20,854 relevant three-atom clause families
and 4,613 refutations, 15 invalid traces, 200 actual PSC matrices (2,167 clauses,
1,326 Skolem symbols, maximum arity 5), 5,000 round trips for each of three
codecs, and both cross-variable/diagonal specialization examples. The inherited
countermodel suite and the Capture counterexample/tagged regression pass.
A 1,000-candidate search prefix rejects every candidate and proves no consistency
statement. The scratch PDF rebuild has 25 pages, 18 embedded fonts and zero
warnings or cross-reference defects; all-page contact sheet and five enlarged
pages were inspected, as was the primary external page.

Historical roadmap gaps have been checked against the current tree:
`RawPSCModel` already supplies actual formula-level decoder and purity-cut
resources; `CompositionModel`/`QuotientModel` already supply their stated
CP/GIC model steps; `Bottom3Syntax` now supplies the new ternary codec layer.
The arbitrary-formula hereditary translation, all local-bound/invariance
obligations, proof-predicate calibration and full machine endpoint remain.
These partial advances do not certify the new Python frontend or table.

Placement preserves 46 ancillary files under `17-clause-`; four main/experimental
TeX, PDF and delivery-README files remain archive-only. All 50 files / 49 distinct
Git blobs were searched in history; 16 borrowed blobs do not constitute a prior
placement of this manuscript. The placement map and fresh-extraction/own-tree
check are `data/intake-148-placement{,-check}.json`, with maximum Windows path
length 141. Borrowed notices retain larger historical-package references;
flattened imports and paths are intentionally unchanged. No manifests or
line endings were audited. Full independent reviews are
`intake-148-source-17{,-article,-machine}.md`, with `data/intake-148-*.json`
evidence. Recover and reproduce all six finite jobs, including the full grammar
search and independent certificate check, with:

```sh
uv run --no-project python SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/reproduce_148.py
```

The helper passes from a fresh scratch recovery; `--prepare-only` restores the
original layout. The base article and every delivered file remain unchanged.
