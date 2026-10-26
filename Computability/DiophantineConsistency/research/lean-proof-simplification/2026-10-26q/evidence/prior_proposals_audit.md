# Prior-proposal exclusion audit

## Scope and standard

Snapshot: `9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9` (main at retrieval, 26 October 2026).
The exclusion corpus comprises all six placed packets under
`Computability/DiophantineConsistency/research/lean-proof-simplification/`
and all five ZIP files currently in `docs/incoming/`. The placed tree has 323
files. The five ZIPs have 400 members in total and contain no nested archives.
`prior_corpus_manifest.json` records file identities and ZIP membership.

The review inspected the main report proposal sections, source-review notes,
README summaries, inventories of proposed Lean modules and patches, existing
novelty audits, and candidate-specific searches across report/note/Lean text.
The long incoming README was screened for relevant proof-simplification entries;
it also contains historical intake summaries for many unrelated projects. We do
not claim a fresh semantic review of all remotely linked historical manuscripts.
Their visible generic proof-engineering summaries (shared recursion and quotient
syntax, implication bases, semantic boundaries, automatic certificates) are not
presented as new ideas.

The user's counterfactual baseline is stronger than the adoption ledger:
**every idea in this corpus is treated as already applied**, including pending,
deferred, rejected-default, uncompiled, optional, and notes-only proposals.
A compiler receipt for one of them is new validation work, not a new proposal.
A different helper name or a further instance of the same advertised interface
is not enough. A candidate should remove a different obligation, exploit a
materially different invariant, or strengthen the actual theorem contract in a
way the old mechanism does not already supply.

This is a scoped nonduplication screen, not a claim of novelty in Lean literature.

## Reference key

All repository paths are at the snapshot above. For a placed packet, the main
report is `report.tex` unless otherwise stated.

| Key | Corpus source |
| --- | --- |
| A | `research/lean-proof-simplification/2026-10-26a/` |
| B | `research/lean-proof-simplification/2026-10-26b/` |
| C | `research/lean-proof-simplification/2026-10-26c/` |
| D | `research/lean-proof-simplification/2026-10-26d/` |
| E | `research/lean-proof-simplification/2026-10-26e/`; report is `report/report.tex` |
| F | `research/lean-proof-simplification/2026-10-26f/`; report is `report/proof_simplification_report.tex` plus `report/sections/` |
| I1 | `docs/incoming/diophantine-lean-simplification-2026-10-26(1).zip`; root `diophantine-lean-simplification/` |
| I2 | `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip`; root `diophantine-lean-new-ideas-2026-10-26/` |
| I3 | `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip`; root `diophantine-lean-additional-simplifications-2026-10-26/` |
| I4 | `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip`; root `new-lean-simplification-2026-10-26/` |
| I5 | `docs/incoming/lean-proof-simplification-review-2026-10-26.zip`; root `lean-proof-simplification-review/`; report `lean-proof-simplification-review.tex` |

The `research/...` paths above are relative to `Computability/DiophantineConsistency/`.

## Excluded mechanisms: syntax, programs, and checkers

| ID | Already proposed mechanism and actual scope | Sufficient prior evidence |
| --- | --- | --- |
| S01 | Transport pointwise equations through `Nat.rec`; replace `Realizes.prec` and optimizer comparison inductions by `simp` or reusable axiom-free recursor congruence. | A, “Rewrite under primitive recursion”; `lean/RecursorCore.lean`. |
| S02 | Replace optional-lookup/membership inductions by core List lemmas; use `Option.map_injective` for annotated parents. | A, “Use the core list-lookup API”; E, sections 6 and checker cleanup patch. |
| S03 | Fixed-state, zero-absorption, successor, invariant and encoded-list simulation laws shared by numeric scanners, with arbitrary-raw-code soundness retained. | A scanner section; B “Checked histories and numeric scanners”; C scanner section; E sections 7–8; I1 “One simulation kernel”. |
| S04 | Generic guarded/validated history fold, `run_append`, invariant preservation, separate input-row and stored-judgment types, reusable proof fragments. | B, “One invariant-preserving history fold”; C syntax notes; E section 8; I5 “Reuse scanner and validated-history proofs”. |
| S05 | Dynamic-seed/input-dependent PR iterator accepting actual seed/fuel/step realizers, preserving executable `.val` and counts. | B, “A better primitive-recursive iterator interface”; C notes/syntax.txt. |
| S06 | Normalize eight-tag threshold dispatch and derive exact numeric Boolean output from range plus acceptance equivalence. | A/B numeric Boolean sections; E section 8. |
| S07 | Fuse decoder quote recovery and depth bounds into one exact graph theorem on arbitrary input codes; alternatively simplify successful Option branches separately to preserve axiom footprint. | I3 “Describe the tree decoder by its exact graph”; I4 first proposal; I5 decoder section and rejected-default fusion patch. |
| S08 | Automate extensional primitive-recursiveness composition using `fun_prop`-style registered rules; distinguish propositions about functions from explicit realizers/costs. | I3 “Automate extensional primitive-recursiveness composition”; notes/checker.md. |
| S09 | Share Direct/Native graph-enumerator control-flow templates with explicit backend combinators, preserving different witness counts. | E section 14. |
| S10 | Derive inverse graphs by product equivalence and projection; normalize tuple coordinates separately; also proposed for Cantor encoding. | I2 “Derive inverse graphs from a product equivalence” and first further question. |
| S11 | Factor affine composition budgets and remove unnecessary nonempty arity premises; synthesize max-plus representation-depth certificates. | I2 arithmetic-budget section/further questions; I4 “Synthesize representation-depth bounds”. |
| S12 | Normalize `AnnotatedSchemaMaps.rsep/rf1/rf2/ri` renaming chains using algebra of index maps. This is notes-only but still excluded. | I4 `evidence/semantic_review.md` section 5; `evidence/prior_ideas.md` candidate 8. |
| S13 | Support-restricted evaluator congruence and overwrite/frame rules; notes acknowledge that `WitnessCompaction.eval_congr` already implements the natural-expression core. | I4 `evidence/prior_ideas.md` candidate 7. |

## Excluded mechanisms: witnesses, polynomials, and circuits

| ID | Already proposed mechanism and actual scope | Sufficient prior evidence |
| --- | --- | --- |
| R01 | Assignment naturality under `Sum.map`, moving variable renaming outside evaluation, shared finite witness splitting via `Fin.addCases`, and earlier constructor projection/count laws. | A assignment patch; B “Witness layouts”; D assignment section; I1 first local proposal. |
| R02 | Shared syntax and finite sum-of-squares evaluation, zero criterion, degree and operation-count bounds across signed/natural DAG and register compilers. | A SOS section; B residual/gate section; C/D compiler sections; I5 residual section. |
| R03 | Obtain natural gate completeness/soundness from existing semiring semantics after splitting data from proofs. | B “The semiring theorem already subsumes the natural induction”; C/D architecture; E combines add/mul proof branches. |
| R04 | Move structural/weighted syntax-degree machinery earlier; specialize weight one; preserve cancellation normal forms and exact-degree distinctions. | A translation/degree section; B/C/D compiler sections; F ShortSystem degree prefix. |
| R05 | Replace 193 generated power chains by existing `run_power` certificates, reuse parent labels, factor circuit-specific node equations, expose indexed or lazy facades, preserve useful public cuts. | A/B generated-circuit sections; F section 04 and circuit notes; I1/I5 circuit sections. |
| R06 | One indexed topological invariant for uniqueness, nonnegativity, degree, range and other register properties; extend local labels to support/invariant metadata. | A `CircuitInvariant`; C/D DAG sections and D further questions. |
| R07 | General positive/natural circuit simulation; `NodeRel` permits commuted add/mul operands while subtraction stays ordered. | A translation section; C general-translation section; I1 factor-translation section. |
| R08 | Generic append topology/allowed-node/evaluation invariants for NaturalRegisterProgram. | A “Package append invariants locally” and circuits source notes. |
| R09 | Reuse semantic register cuts in generated clients; share the identical 99-node free-carrier circuit tail, the scalar `ratioValue` tail, and later its correctness glue. | C “Use established register facts” and “Extract the shared 99-node free-carrier tail”; E sections 9 and 11. |
| R10 | Sparse quadratic row normalization/reflection bound to independently specified source residuals; coefficient-table naturality and syntax unification; finite majorant/sign-basis certificates for coefficient envelopes. | C coefficient and row-normalizer sections; D further questions; F coefficient section; I1 coefficient-envelope tactic; I5 eight-term coefficient-basis proposal. |
| R11 | Elementary row addition and surjective row reindexing preserve zero sets; general invertible linear combinations are also mentioned as a later option. | C “Represent elementary row operations once”. |
| R12 | Guarded solution-existence transport and composition, without demanding witness bijections; lift pointwise zero-set equivalences once. | E section 10 and `SolutionTransport.lean`; I1 local zero-set-lifting section. |
| R13 | Share exact nine-coordinate packaging, named conjunction/port-bound accessors, preserve the unshifted coordinate 7. | F `03_architecture.tex`, nine-coordinate/accessor sections. |
| R14 | Parameterize Split/Gap numerical degree profiles and source domination with exact inequalities and sharp output exponents. | F “Abstract the degree profile but retain sharp hypotheses”. |
| R15 | Checked-circuit/typed-safe-node views with exact erasure to literal lists; block semantic certificates with existing whole-DAG binding. | F `04_circuits.tex`, final two architectural proposals. |
| R16 | First prove polynomial support envelopes by degree arithmetic, then bound only supported coefficients. | I3 “Prove the support envelope before individual coefficients”. |

## Excluded mechanisms: native digits, carries, finite data

| ID | Already proposed mechanism and actual scope | Sufficient prior evidence |
| --- | --- | --- |
| N01 | Exact half-radix scaled division/remainder identity and its bound/parity corollaries. | A–D arithmetic sections; I1 local proposal. |
| N02 | Derive weaker moduli from strongest available coefficient congruence, notably 2048 to 16. | A modulus-reuse patch; C window section; I1 local proposal. |
| N03 | Derive quotient, remainder, zero-carry and modular projection from exact local decomposition; make redundant carry recurrence a method instead of a stored field. | A normalization section; B CarryCertificate; C/D/E current-window sections. |
| N04 | Conditional padding witnesses under the phase guard, eliminating dummy witnesses. | A conditional-padding patch and digits notes section 1. |
| N05 | Shared arbitrary-shift cyclic field residues and off-origin mask facts; aligned cells as `ZMod N`; reuse actual cell translation and preserve wraparound and N=1. | B native geometry; A digits notes section 5; E section 12; I1 field geometry. |
| N06 | One coherent restored source/window witness for low/high masks; small views of existing Facts and source positivity/bounds; extract CurrentCarrierBase below completeness. | A digits notes section 8; E section 12; F source/window/base sections. |
| N07 | Generic origin no-borrow decrement for cyclic words; common mask-block lookup/length/bound library; direct physical selector-sum interface. | A digits notes sections 6–7; E section 13; I1 origin-correction section. |
| N08 | Finite pushforward/fiber sum identity separating arbitrary folding with collisions from injective sparse placement. | D “One finite-fiber identity for folded stencils”; I1 folding section. |
| N09 | Generic finite-block/tail dispatcher and checked sum assembly, keeping kernel-checked leaves; shared copied-field descriptors and four field bounds. | B finite data section; E section 13. |
| N10 | Use `Finset.sum_le_one_iff` for exact zero-or-singleton support classification. | I1 local sum-at-most-one section; I2 first proposal; I5 local support section. |
| N11 | Use finiteness/surjectivity to obtain an invariant predecessor instead of periodic-orbit bookkeeping in the offset-19 exclusion. | I3 finite invariant predecessor section and notes/finite-invariant.md. |
| N12 | Rotation as convolution with a point mass. | I3 corresponding section. |
| N13 | Carry uniqueness via finite maximum principle; derive uniqueness of digit vectors from exact full packed words; preserve the exceptional ambiguity. | I3 “Canonical normalization from a finite maximum principle”. |
| N14 | Explicit least/greatest cyclic carry formulas using rotated weighted sums; characterize exactly the one/two-solution boundary and budget-selected least carries. | I4 “An optional structural alternative: explicit cyclic carries”; evidence/algebra_review.md and peer_review_carry.md. |
| N15 | Cyclic packing as a monoid-algebra homomorphism into `ZMod (radix^n-1)`, deriving convolution/product and rotation/monomial laws by a universal property. Notes-only but explicit. | I4 `evidence/algebra_review.md`, final optional direction; `evidence/prior_ideas.md` candidate 9. |
| N16 | Selected local source cleanups: finite-set support/singleton identities, keep huge powers symbolic, natural-subtraction/modulo library facts, linear cast handling, final finite-sum factorization. | F `02_local.tex` and tactics findings; I5 local arithmetic section. |

## Excluded mechanisms: Pell, integer arithmetic, object models

| ID | Already proposed mechanism and actual scope | Sufficient prior evidence |
| --- | --- | --- |
| M01 | Decode literal source/Pell register identities once, then expose appropriate integer and natural corollaries. | B “Decode source-register equations once”; C arithmetic notes. |
| M02 | Reuse an existing Pell parity criterion instead of reproving oddness. | I2 corresponding section and native-proofs findings. |
| M03 | Congruence up to sign as a transitive relation, with multiplication, powers, natAbs transport, and guarded half-interval uniqueness. | I2 final mathematical proposal; I4 second proposal and algebra notes. |
| M04 | Preserve exact rational roots while descending to integer roots through denominator arguments; transfer the entire witness tuple rather than recovering signs in four cases. | I3 rational-root descent section and arithmetic notes. |
| M05 | Decompose integer-product units in one pass, keeping conditional sign exclusions; earlier simple units and sum-of-squares replacements. | E sections 3–4; I3 “Decompose the product's units once”. |
| M06 | Share the positive-denominator quotient/remainder/slack certificate between quadratic and register backends; uniqueness of the triple; uniqueness-based coherence of composed witnesses. | E section 6; I2 Euclidean-certificate section and second further question. |
| O01 | Definable induction transport with an actual formula and satisfaction equivalence, preserving arbitrary nonstandard models. | A object-language section; C/D object sections. |
| O02 | One all-model validity-to-sealed-provability bridge, common model-axiom extraction, arity-polymorphic closed-sentence transport. | A/B object sections; C arity improvement; I5 object endpoint section. |
| O03 | Model-independent finite-index/row-family and existing internal-semiring transport; do not claim the already-existing semiring as new. | C object section; I1 finite-index section; D further questions. |
| O04 | Constructor views/no-confusion for internal code graphs, and fused unique-existence induction for bound codes. | I4 “Constructor views and one internal unique-existence induction”; semantic notes sections 2 and 4. |
| O05 | Definable preservation and fusion laws for internal recursive graphs `ThetaG`, with genuine formula witnesses. | I4 “Preservation and fusion for internal recursive graphs”; semantic notes section 3. |

## Notes-only warnings that matter

I4's `evidence/prior_ideas.md` lists support/frame rules, schema renaming-chain
normalization, and cyclic packing algebra as *promising candidates not found in
its older audit*. That phrase does not make them new to the present task: the
ideas are now present in the requested exclusion corpus.

I2's `novelty-audit.md` also mentions broad exploratory search directions:
functional-graph uniqueness, split-encoding projections, relation algebra for
solvability endpoints, natural-difference/order-embedding bounds, and specialized
syntax-recursive pair induction. These are not complete theorem interfaces. A
new concrete construction can still differ, but it should state the nearest
previous direction instead of claiming the surrounding subject was untouched.

General suggestions about profiling, `simp only`, imports, axiom audits, certificate
sharding, generator synchronization, regression tests, and counting helper costs
appear throughout the corpus. They are supporting methodology, not fresh proposals.

## Candidate-specific novelty checks in this review

These judgments concern overlap only. Mathematical correctness and Lean replay
are separate obligations.

### Consecutive Pell negative-norm obstruction

Searches for `ConsecutivePell`, `norm_ne_neg_one`, continued fractions, period two,
square-gap descent and the transformed coordinate `x-n*y` found no prior proposed
simplification of `ConsecutivePell.norm_ne_neg_one`. Hits are unchanged imports
and uses in copied ShortSystem modules. The selected construction instead squares a hypothetical negative-norm solution
and uses the first-coordinate congruence of powers of the positive fundamental
unit. This is distinct from M01–M04. The broad order-
arithmetic search prompt above is not such a theorem.

### Equality at heterogeneous lower bounds

No proposal for `MinimumNorm.minima76_zero_iff`, saturation of a sum of lower
bounds, or `Finset.sum_eq_sum_iff_of_le` was found. This can be distinct from R02
if the substantive mechanism treats different/coupled minima and exact equality
conditions, rather than merely renaming the old zero-sum-of-squares argument.
A general finite-sum equality lemma alone is conventional library reuse; the
source-specific reduction and handling of dependencies are the contribution.

### Monotone certificate closure for internal syntax relations

No explicit empty/union/insert certificate-closure calculus was found. The
current proposed direct client is ObjectCodeBound; other clients are future
possibilities, not established source savings. The nearest predecessors are
O04 constructor inversion/unique existence, O05 recursive-graph preservation,
and S04 checked-history folds. A common theorem about monotone relational
certificates and closure under coded set operations removes a different proof
obligation if it derives the repeated union/insert results themselves. It must
not quietly assume an internal set is a finite external list, nor simply rename
the already-proposed internal recursive invariant theorem.

### Finite residue obstruction transport

No new generic finite-residue obstruction transport proposal was found, but
`ShortSystem` already has an actual `ZMod 4` obstruction proof in archived
unchanged source. A proposed general wrapper should be described as extending
that existing method to genuinely different clients; a claim that finite residue
checking is absent would be false.

## Practical interpretation of the adoption ledger

`ADOPTION.md` reports adopted/in-validation recursor congruence, assignment
naturality, core lookup cleanup, NatIterate scanner laws, shared model extraction,
coefficient bounds, ArithmeticDAG/FirstPellCarrier cleanups and Option injectivity.
It marks other proposed changes pending or deferred and notes independent use of
`TotalDegreeBound` for ShortSystem/ShortFrontier/ShortReducedStrong.

These statuses do not shrink the exclusion set. Under the user's instruction,
the report should reason from the end of that entire roadmap rather than offering
to implement old uncompiled items as if their ideas had just been discovered.

## Two additional candidate-specific checks

### Remove unused induction in internal zero-product reasoning

No proposed change mentioning `ObjectNaturalZero`, `zeroProductStage`,
`mulRel_zero_iff`, `nat_zero_or_succ`, or unused induction hypotheses was found
in the full report/note/Lean corpus. In the maintained proof, the successor
branch discards its induction hypothesis. Replacing the entire definable
induction with one internal zero/successor case split would remove a different
obligation from O01/O05: the formula, satisfaction lemma and induction transport
become unnecessary. The replacement must quantify over arbitrary internal omega
and retain the existing totality, successor and uniqueness arguments. It must
not use external natural-number induction as a substitute.

### Unify negative-norm obstructions by a discriminant normal form

No prior proposal for `MinimumNorm.main_norm_ne_neg_one`,
`square_auxiliary_ne_neg_one`, or a common discriminant normal form was found.
The candidate theorem `X^2 - (A^2 - 1)*Y^2 != -1` over integers and its concrete
substitutions could consolidate the existing residue calculations. Bespoke
`ZMod 4` checks already occur in ShortSystem; the fresh contribution would be
the single shared mathematical obstruction and explicit substitutions, not
finite residue checking itself. This should be presented as a focused local
mechanism whose net benefit includes the shared theorem's cost.


### Addition companion to unused-induction elimination

The same novelty check covers `ObjectAdditionCancellation.addRel_zero_iff` and
its private `zeroSumStage` formula. No previous proposal was found; the only
ObjectAdditionCancellation corpus matches were inventory paths. The exact
patch preserves the independent `cancellationStage` induction. Source savings
reported in `internal/metrics.json` compare against the raw pinned snapshot,
not a synthesized baseline with every earlier proposal applied.
