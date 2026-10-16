# Smaller machines for Con(ZFC)

The goal is a binary, single-tape machine with fewer than 254 nonhalting
states whose blank-tape non-halting is provably in ZFC equivalent to
Con(ZFC). The goal remains open. All new formal work uses Lean.
An intended set-theoretic meaning is optional: any effectively presented
theory or proof calculus is eligible once its consistency calibration is proved.
The complete compiled search, including its data and initialization, is the
cost measure that decides whether a candidate improves the baseline.

The [attributed upstream baseline](../../../../lib/jeff-busy-beaver-zfc254/README.proveit.md)
is imported at commit `297ab8df7e5de329605c3875b4934643b371a5e3`.
Mira-Cult designed the machine; Jeff supplies the published verification.
Its exact table has 254 working states, two symbols and terminal label 254.
Our new Lean representation proves finite table facts; the upstream
end-to-end consistency equivalence has not been ported to Lean.

The frozen [experimental table](raw_candidate_252.md) has **252 working
states and 504 total binary transition rows**. Its generator reproduces the
frozen table byte for byte. The finite-sort argument in
[typed_countermodel.md](typed_countermodel.md) rules out the intended abstract
calculus as a consistency-search target. Its consequence for the literal table
still requires the missing compiler simulation. The experiment
uses equality-free theory rows, base-3 formula coding, a dual quantifier
schema and shared code. [theory_backend_experiment.md](theory_backend_experiment.md)
records the exact recipe and competing measurements. The
[dual-quantifier gap](dual_quantifier_gap.md) gives a counterexample to the
generic calculus replacement used in this experiment. The stronger finite-sort
model satisfies the actual C/G bundle with either quantifier row. The later
250- and 248-state rewrites preserve that obstruction; their state savings remain
compiler measurements. Full ordinary equality-free PSC and CP/GIC retain their
separate mathematical consistency calibrations.

## Intake and theory minimization

[Intake batch 143](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md)
was completed before this research: placement `b07d1a27b`, reconciliation
`83ef1da6b`, catalogue `1ce7ab050`. The three source archives remain
recoverable from arrival `9e5b610259cd42c88e2cf6c862fb876a7c6d6fcd`.

Batch 144 adds six later reports to the same host (placement `ac4287e5b`,
reconciliation `6d8bc7f1b`), including arrivals `39409c8c9` and `83dec60c2`.
The accepted ordinary PSC-only hereditary-saturation argument is local source
08; the new `PSCSaturation` module checks its semantic hull transfer under
explicit resources. The host also attributes the existing 253 reduction to
mira-emmy/Mira-Cult/Jeff and distinguishes all prepared/runtime-only and
experimental 252 artifacts. The delivered claims have no automatic Lean status.

Batches 145/146 add six more reports to that host: exact 250/248 compiler
artifacts, the finite-sort obstruction, an incoming-profile PSC alternative,
empty-input EPSC equivalent to seeded PSC, and complete reference proof engines.
The unchanged reduced C/G calculus is retired by `59b78a0d9`; placements
`3cc6ba5b1`/`f31ba244b` and reconciliations `5ae03164f`/`9d9e128cc` preserve
all fifteen sources. EPSC is a new ordinary simplification, with a 270-state
full-equality control; its uniform Lean interpretation and machine bridge
remain open. The opt-in formal library now includes actual raw-PSC model
adapters, generic register bisimulation and finite facts about the attributed
248 table. All 35 source units passed a fresh serial check.

Batches 147/148 add two further sources (arrivals `9439d775aa` and
`5e5603303d`): the [primitive-Bottom ternary codec](bottom3_codec.md), a
complete Hilbert reference, an ordinary PA strengthening of the sorted
obstruction, and a [complete ground-clause reference](clausal_reference.md).
The new codec now has Lean proofs for all-code round trips, freshness and
ordinary semantic preservation; all 36 source units pass a fresh serial
check (`830647031`). The new 251-state reduced C/G encoding retains the
countermodel. A separate 270-state complete-original-word comparison is
reproducible but does not improve the prior 269. These reference algorithms
still need complete binary implementations and the requested internal proof.

Batch149 adds sources18/19 (placement `a9a313b79`, reconciliation
`81bcbe6a7`): complete binding-witness and shared-template PSC references,
a formal fixed-slot obstruction and a stronger composite-instantiation
diagnostic. Both delivered standalone Lean modules compile; their claims
cover the specified weak calculus and syntax identities, not either Python
checker. The source19 **268-state control** retains all original logical rows
and uses a separately justified conjunction rewrite. Its full53,760-choice
grid and8,192 PSC controls reproduce. Source18's fixed269/283 tables reproduce,
and all1,024 PSC trials reproduce the full histogram when the actual
depth-dependent dispatcher cost is charged. Our earlier six-versus-five
finding was a review error, explicitly withdrawn in the host; three larger
historical sweeps still lack full drivers. The
[logical-engine continuation](logical_engine_completeness.md#batch149-composite-collisions-and-two-complete-references)
records the practical interface requirements. No new literal-machine consistency
endpoint follows from these controls or finite checks.

Batch 150 adds sources 20–23 (placement `a6823de93`, reconciliation
`ad685a601`): low-code falsity calibration and captured closures, a
**two-parameter EPSC** interpretation, equivalent native protected-witness
rules, and quantified-NAND tableaux. All advertised functional checks and
bounded searches reproduce. The new 255/271 and 341/343 tables are separate
compiler/initializer controls; none implements these new complete frontends
or improves public 253. The 269 grammar control survives full-cost repricing.
[Raw PSC notes](raw_psc.md#batch-150-two-slots-and-native-rules),
[logical interfaces](logical_engine_completeness.md#batch-150-three-further-complete-interfaces)
and [initializer controls](mira_backend.md#batch-150-initializer-controls)
record their actionable consequences. The host had 23 sources after that batch.
The reviewed compact initializer is also integrated into the clean assembler:
`compile_dag(..., initializer="compact")` reproduces the exact 341/343 tables
with all runtime rows preserved; `--initializer compact` selects it on the CLI.

Batch 151 adds sources 24–25 (placement `65c776f4be`, reconciliation
`9c8242c78f`), bringing the host to 25 sources. Outgoing equality and reserved-zero
falsity receive ordinary proofs and a new [Lean semantic component](outgoing_profile.md).
An explicit SK carrier preserves the entire large input term; intake records a
negative-start parser counterexample while accepting the frozen start-zero payload.
Exact-hull EFPC is equivalent to full EPSC, with a single-instance obstruction
and separately checked local Lean resources. All 264/20,480 compiler recipes
and 148,368 fusion records reproduce. The 288/271 controls supply no state
improvement; fusion fuel/abstraction outcomes remain unresolved. See the host's
full dossiers and offline `code/reproduce_151.py` helper.

[subset_only.md](subset_only.md) proves, at the mathematical level, that
the membership arm can be removed from source 02's mixed local bound.
A positive singleton-decoder hull covers the root's members without
containing the root. This recovers Separation and Union noncircularly.
The candidate remains an infinite schema, with arbitrary parameters and
matrices. Lean now proves that Extensionality plus its subset-seeded version
is deductively equivalent to ZF without Foundation or Choice. The effective
consistency bridge from that comparison theory to ZFC remains unformalized.

[Mira's container comparison](mira_containers.md) records the user-supplied
insight and its independent mathematical audit. Mere transitive containment
and power-bounding transitive containment have different strength.
One-sided profile congruence suffices: universally swapping its two variables
recovers the other direction. [rejected_deletions.md](rejected_deletions.md)
gives a `V_{ω₁}` countermodel to deleting transitivity from EFH.

`kernel_metrics.py` compares all candidates in declared common formula
bases and emits actual example-instance RPN/binary encodings. In source 02's
unchanged falsity/implication metric, deleting the membership arm saves four
nodes: point control 69→65, subset control 72→68, and symmetric equality-free
control 83→79. Replacing symmetric congruence by one-sided congruence takes
the last count to 71; in the unary-negation metric it is 58 raw / 56 after
double-negation cancellation. These are formula measures. An example matrix
`Mem(0,1)` is one instance, not the whole schema.

## Lean results

The opt-in umbrella is `BusyBeaver.ZFC`. Its current components are:

| Module under `../../Lean/BusyBeaver/ZFC/` | Proved scope |
|---|---|
| `ProfileCongruence.lean` | One-sided/full profile congruence equivalence; equality erasure and formula invariance for the existing `SetTheory.Form` syntax. |
| `ProfilePairs.lean` | Equality-free pair-code endpoint uniqueness up to raw profiles, without profile congruence. |
| `ProfileCollection.lean` | Empty/profile-pair/code existence and bisimulation reflexivity/symmetry under named collection instances and container resources. |
| `ProfileSyntax.lean` | Equality-free first-order profile/pair/App/bisimilarity predicates and GIC wrapper, with checked satisfaction specifications. |
| `ProfileModel.lean` | Initial pair/code/reflexivity/symmetry constructions obtained from actual equality-free Form-indexed CP/GIC instances. |
| `ProfileComposition.lean` | Exact App composition, bisimilarity transitivity and quotient Extensionality under named collection-instance families. |
| `CompositionModel.lean` | All composition and matching matrices adapted to actual equality-free CP/GIC; bisimilarity transitivity and quotient Extensionality for these models. |
| `QuotientModel.lean` | Actual quotient domain and membership congruence; computable equality-free formula translation, its satisfaction bridge and quotient Extensionality. |
| `ProfileAxioms.lean` | Interpreted Empty, Pairing, Union, Separation, Power and partial Replacement under explicit instances/invariance hypotheses; singleton-closed containers, with ordinary Infinity still separate. |
| `PowerSyntax.lean` | Fixed equality-free SubD/Power-filter matrices obtained from actual Form-indexed CP/GIC, including the bound for copies outside a transitive container. |
| `RawPSCProfile.lean` | Full incoming/outgoing profile equivalence, twin singletons, the equality-free decoder, transitive covers, Separation and Union under explicit PSC instances; actual formula adapters remain separate. |
| `PSCSaturation.lean` | Hereditary incoming-profile saturation, the purity cut and guarded PSC hull transfer under explicit per-instance semantic resources; no full first-order interpretation theorem yet. |
| `PositiveClosure.lean` | Exact constant fibers, singletons, Power Set, gated decoder root coverage, Separation and Union, under explicit per-relation semantic closure instances. |
| `Bootstrap.lean` | Pairing, Russell-root partial Replacement and Infinity under explicit per-relation instances and the earlier set constructions; Infinity needs no Extensionality. |
| `DeepPositiveClosure.lean` | Actual `SetTheory.Form` wrapper with checked binder renamings, preserving equality-freeness; satisfaction equals the intended definable closure instance. |
| `DefinableClosure.lean` | Every forward set-existence construction connected to an actual first-order matrix, with formula-level Separation and functional Replacement. |
| `PSCCalibration.lean` | Extensionality plus subset-seeded PSC and ZF without Foundation or Choice have the same models and the same sentence theorems in the existing `BProv` calculus. |
| `StateReduction.lean` | A valid transition quotient preserves every finite run, arbitrary/blank halting and exact final score in the existing machine model. |
| `Table254.lean` | Literal baseline table, bounds, halt-edge count and initial action, checked by kernel `decide`. |
| `Table248.lean` | Attributed original-rho6 source-11 experimental table: all 496 actions, 248 working states, both halt edges and actual first 1,024 blank steps checked by kernel reduction; no calculus or full simulation theorem. |
| `RegisterBisimulation.lean` | Actual increment/decrement/halt semantics: matching instruction/index/both-exit bisimulation preserves finite halting from every common register vector, including exact counts of attempted steps; no submitted certificate instance yet. |
| `RawPSCModel.lean` | Raw PSC model indexed by `EqualityFreeForm`: named definable instances supply cover/Separation/Union, semantic saturation and purity-cut resources; guarded hull transfer retains explicit local-bound and invariance hypotheses. |
| `Table253.lean` | Attributed literal mira-emmy 253-state table and actual first 1,024 blank-tape steps, checked by kernel reduction. |
| `FiniteZipper.lean` | Generic zero-exterior tape representation; one-step and balanced-block simulation to the existing Core semantics, every integer tape read and earlier activity from an active endpoint. |
| `Boot253.lean` | Full312,975-step actual blank bootstrap of the attributed253 table, state33/head−17 and complete tape frame including158 spare blocks; arbitrary runtime and consistency bridge remain open. |
| `Table252.lean` | Literal experimental table, 252-state/504-row bounds, both halt edges and the normalized row, checked by kernel `decide`. |
| `FormulaRPN.lean` | Three-constructor NAND formula syntax; exact prefix-token parsing in both directions; De Bruijn scope check and a closed semantic contradiction. |
| `Base3Encoding.lean` | Finite named membership/implication/forall code tags and label freshness; excludes cyclic truth code 0. |
| `Base3Syntax.lean` | Complete numerical decoder including the truth alias at code 0; encode/decode round trips on canonical syntax and code freshness. This is not a calculus interpretation. |
| `PartialTotalization.lean` | Filling undefined transitions with a tape-preserving halt action preserves halting and final score under an explicit partial-step convention. |
| `WadeMachine.lean` | Actual literal-table INC execution from state 13 through its return to state 55, for a nonempty preceding-register prefix and gap of at least two zeros; selected unary register increments and every other tape cell is preserved. |
| `Kalmar.lean` | Generic classical implication calculus and its deduction, consistency and maximal-theory tools. |
| `TarskiCalculus.lean`, `TarskiDerived.lean`, `TarskiLeibniz.lean`, `TarskiClean.lean`, `TarskiComplete.lean` | Soundness and conditional completeness of the full named-variable calculus, with primitive Bottom, genuine equality, all eight logical rows and both gated atomic vacuity families; capture-safe specialization and clean-form model construction. |
| `Lukasiewicz.lean` | Attributed port of 107 upstream implication certificates; derives K/S/Peirce and rho6-based ex falso, constructs `Tarski.classical`, and proves `Tarski.complete` without the conditional theorem's extra basis hypotheses. An independent condensed-detachment search regenerates exactly the same 106 derived formulas ([tarski_logic_layer.md](tarski_logic_layer.md)). |
| `RegisterPath.lean` | Exact upstream RM path semantics including truncate/zero-extend, break/continue and infinite registers; finite-list execution proves the same runs. |
| `Prog254.lean` | All 6,459 original decoder rows, with a verified balanced lookup equal to flat lookup for every index; no replacement by the different structured DAG. |
| `Prefix330.lean` | Exact 330-step public register prefix from the original initial vector to path 000 and logical registers [5,0,0,0,2,0,0,0,0], with the entire remaining register tail zero. |
| `TarskiFalsity.lean` | The machines' relative falsity `F = Rel(0,0)`: the literal row set `ThmG (rel 0 0)` is sound for irreflexive models and complete for ⊥-free theories and targets; the comparison axiom IR is a generalized identity, not a row. |
| `Code254.lean` | All-natural base-four decoder and original numerical calculus; soundness for decoded bundles, completeness under no nonempty model of literal encodable bundles. The corrected statement explicitly requires a valuation; comparing the two bundle theories remains open. |
| `OutgoingProfile.lean` | Four-node outgoing equality from exact full-profile singletons, actual raw-PSC model corollaries and reserved-zero named semantic translation at one false point. Source equality denotes full observational classes. |
| `Numeric254.lean`, `NamedNumeric254.lean` | Exact original four-tag numerical rules and gated C/G/vacuity bundle; named proof transport and refutation equivalence for the explicitly defined encoded-numerical-theorem theory Q. Q/ZFC calibration remains open. |
| `BootstrapFrame253.lean` | The actual 312,975-step binary bootstrap realizes the actual 330-step register endpoint, with all nine permuted registers, 158 spare blocks and exterior blanks retained. |
| `Code254Containers.lean` | A literal gated bundle gives the existing transitive, powerset-bounding container resource in an irreflexive model with an explicit valuation. |
| `ZipperRuns.lean`, `RegisterBoxes253.lean` | Generic whole-tape sequential execution and preserving scans; actual public253 zero-decrement box for arbitrary preceding and following registers, in exactly twice the prefix width plus five steps. No PC-update or complete instruction simulation claim. |
| `Code254GIC.lean`, `Code254Models.lean` | Hygienic actual Form matrices and padded gated bundles give the CP/GIC model interface; semantic encoding/decoding gives the decoded-to-encodable model implication. The reverse implication and full ZFC calibration remain separate. |
| `NumericCode254.lean` | Exact equality of the two pairing/encoding definitions and equivalence of their twelve-constructor numerical derivability relations, including zero and all actual gates. |
| `RegisterMark253.lean`, `RegisterIncrement253.lean` | Actual public253 marking and increment excursions, with arbitrary register values and spares, exact step counts and whole-tape output. PC updates, positive decrement and general dispatch remain separate. |

The [Tarski audit](tarski_calculus_review.md) and subsequent
[propositional certificate port](lukasiewicz_basis.md) now establish full
named-calculus completeness. The seven added modules and updated umbrella
pass scoped direct Lean checks against the source-verified dependency cache.
The basis and ex-falso derivations use no axioms; completeness uses only
`propext`, `Classical.choice` and `Quot.sound`. Numerical syntax, relative
runtime falsity, the literal theory bundle and the machine remain separate
proof obligations.

The calibration uses the repository's first-order internal recursion theorem
for the reverse construction, then its generic completeness theorem for
deductive equivalence; [psc_calibration.md](psc_calibration.md) gives the exact
statements and comparison theory. It is not a computable proof-code translator verified
in arithmetic. No theorem here supplies a proof-producing theory translator, a complete
refutation checker, an enumerator compiler, a verified executing decoder, or
the final ZFC machine endpoint. `PositiveClosure` deliberately assumes the
specific closure instances used by each lemma, rather than silently assert
all second-order relations form an implemented first-order schema.

The Lean prefix/de Bruijn codec and Python postfix/named-variable bit codec
are distinct encodings. Only the stated Lean token codec has a Lean theorem.
Three token forms still carry natural-number atom payloads. Axiom audits
show no custom axioms or `sorryAx`; only the repository's ordinary Lean
foundational axioms occur. The literal finite table facts have no axioms.

Rebuild the entire small dependency closure **serially from source**:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/check_lean.py
```

This compiles 62 source units: the first-order logic, calculus and completeness
modules, `ZF.Zf`, `BusyBeaver.Core`, 56 research modules and the umbrella into a
fresh scratch directory, without shared oleans or Lake's
worker pool. [results/lean-verification.json](results/lean-verification.json)
records the prior 38-unit fresh source check and axiom outputs. The seven
subsequent modules and updated umbrella have separate scoped evidence in
`results/tarski-verification.json` and `results/lukasiewicz-verification.json`;
the expensive finite bootstrap was reused in those checks. The pinned Lean toolchain must
be installed. Source SHA-256 pins are included for each checked module.
The three RM-prefix modules also passed a separate fresh source closure;
`results/rm330-verification.json` records their exact data audit and checks.
The [numerical adapter](numeric254_lean.md) and
[bootstrap-frame bridge](bootstrap_frame253.md) have separate scoped
Lean 4.32.0 checks and axiom audits in their linked evidence files.
`results/integration-151-verification.json` checks the newly merged relative-falsity
module and the complete updated umbrella against those source-verified caches.
The subsequent [code-calculus review](code254_review.md) and
[outgoing equality development](outgoing_profile.md) are integrated into the
runner. Their separate source and axiom checks are linked in those
notes; `results/code-outgoing-integration-verification.json` records the
corrected numerical module and updated umbrella check with reused dependencies.
The [encoded container adapter](code254_containers.md) and
[arbitrary-length zero-decrement box](register_boxes253.md) add three more
modules. Their separate source and caller checks are linked in those notes;
`results/containers-boxes-integration-verification.json` records their joint
integration with the 57-unit umbrella, reusing the previously verified dependencies.
The [GIC model bridge](code254_gic.md), [model comparison](code254_models.md),
[calculus identification](numeric_code254.md) and
[marking/increment proofs](register_mark_increment253.md) add five further
modules. `results/gic-boxes-integration-verification.json` records their serial
source and 62-unit umbrella checks with the earlier dependencies reused.
The standalone BusyBeaver Lake package declares its FirstOrder and ZF path
dependencies; the ZFC umbrella is opt-in.

The separate [NoQuotient254 result](no_quotient254.md) proves every exact
step-preserving state quotient of this literal machine is injective. Its
13-round finite certificate is checked by Lean kernel `decide`. This is a
narrow obstruction to one reduction method, not a lower bound for other
equivalent machines. It is an expensive opt-in check:
`check_lean.py --include-no-quotient` (about two minutes and several GiB
in the recorded run). It is excluded from the small umbrella.

## Executable experiments and reusable repository ideas

`audit_tm.py` checks the literal table and searches conservative reductions.
The recorded [baseline audit](baseline-254-audit.json) finds all 254 states
graph-reachable and all distinct after step-bisimulation refinement.
A radius-four window abstraction, 64 steps per side and 64,262 ordered
pairs finds no certified single-state merge. The 264,982-step boot prefix
reaches state 96 at head −8 with 149 ones. This finite trace proves no
future invariant; failed reduction searches prove no global lower bound.
The generic exact quotient rule and the literal no-quotient obstruction are
formalized; the Python implementation
and window/macro argument are not formalized.

Useful repository material is recorded with exact source declarations in:

- [repository_ideas_set_theory.md](repository_ideas_set_theory.md): lightweight syntax, data-valued proof trees, proof transport, internal recursion and choice-free certificates.
- [repository_ideas_surreal.md](repository_ideas_surreal.md): exact parser/scope validation already adapted here; arithmetic guards and the limits of surreal round-trip axiom schemes.
- [repository_ideas_diophantine.md](repository_ideas_diophantine.md): stream codes, exact trace certificates, simultaneous witness packing and their true costs.

`stream_encoding.py` tests a 2-adic natural-field stream. For the concrete
NAND example it uses 2,831 fairly framed bits versus 3,080 in the gamma-field
encoding (249 saved). In a natural register the unframed payload is 2,789
bits with the register boundary supplied by the machine model. This is an
encoding experiment, not a state improvement or a verified Lean bit codec.

The [public compiler route](compiler_route.md) reconstructs the published
219-node register DAG offline as a 281-state table using Andrew Wade’s
licensed backend. Replacing its recursive Cantor pair/unpair helpers with
naive 2-adic helpers increases the count to 305. This compiled experiment
shows why the smaller flat stream needs a backend suited to streaming;
the whole-program calibration and compiler simulation remain unproved.
The [clean single-marker assembler](mira_backend.md) now reconstructs an
editable engine from the published phase interface. It emits 408 states for
the original DAG from zero registers, including a 122-state initializer;
its generated instruction checks pass. Recovering the optimized original
bootstrap and decoder remains a separate compression task.

The editable theory-generator experiment reproduces the original 281-state
public-backend result before replacing its theory rows. A fixed-binder
Extensionality/point-PSC variant takes 317 states; the equality-free route
reaches 252 after the additional coding and compiler changes. The formal
subset-seeded control calibrates neither changed enumerator. Their distinct
freshness, falsity and logical-completeness obligations remain.

[wade_compiler_proof.md](wade_compiler_proof.md) records the checked local INC
execution. PC carry/selector relocation, decrement, dispatch, bootstrap and
whole-program simulation remain separate from that theorem.

[equality_free_bisimulation.md](equality_free_bisimulation.md) gives a proposed
interpretation for equality-free CP/GIC, carefully separating raw profile
equality from bisimilarity. The Lean profile-pair and collection results
now extend through composition and an actual extensional quotient, with checked
first-order matrix adapters for those steps. The remaining set-existence lemmas
are checked under explicit semantic instances. Their complete first-order
adapters, the ordinary Infinity bridge and the ZFC consistency reduction remain.

[The logical-engine audit](logical_engine_completeness.md) locates the
original equality machinery's role in substitution and alpha conversion.
Quantifier-only repairs do not supply cross-variable atomic transport. A
control keeping all nine original logical outputs and four formula tags
compiles raw PSC to 279 states with fixed grammar sharing; it retains the
complete logical frontend specification, with its changed theory/enumerator
and binary simulation still unproved. Its exact baseline and controls reproduce.
[The finite 253-state Lean layer](finite253_lean.md) records the attributed
table and its complete312,975-step actual blank bootstrap. All83 computation
blocks use kernel `decide`, through a faster transition lookup proved equal
to all506 literal actions. The theorem specifies every integer tape position
and activity throughout the prefix. The fresh38-module checked closure passes;
no first-dispatch-arrival, arbitrary runtime or consistency endpoint is claimed.

The [separate register prefix](rm330_lean.md) is now also checked in Lean:
330 actual path instructions reach the same primary register values, with
all higher logical registers zero. Its 6,459-row literal program is imported
exactly, and finite execution transfers to infinite-register semantics.
The two finite certificates still require a general binary/register
representation and instruction-simulation bridge.

[The PSC-only compiler control](psc_backend_experiment.md) tests the new
schema with original rho6, a fresh `code+2` binder and genuine bottom. Exact
macro-word sharing reaches a different 252-state partial table. An algebraic
counterinterpretation proves this control's reduced quantifier calculus is
incomplete, so it is not an eligible consistency-machine result. The same
counterinterpretation fails the frozen candidate's actual existential C/G
bundle. Adapter, constructor, codec and grammar measurements are reproducible.

[raw_psc.md](raw_psc.md) reconciles the earlier saturation proposal with
[batch 144 source 08](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-144-source-08.md).
That report supplies an accepted ordinary mathematical ZFC consistency
calibration for equality-free subset PSC alone. `PSCSaturation.lean` checks
its hereditary saturation and hull-transfer core under explicit resources;
the equality-free bootstrap, full Form adapters and whole-theory/proof-code
calibration remain to be connected in Lean. [bootstrap.md](bootstrap.md)
details the earlier checked forward existence arguments.

Run the Python regressions with:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/test_kernel_metrics.py
uv run --no-project python Computability/BusyBeaver/Research/ZFC/test_stream_encoding.py
uv run --no-project python Computability/BusyBeaver/Research/ZFC/audit_tm.py --self-test
```

Regeneration of `kernel_metrics.json` and `stream_encoding.json` is explicit
by running their respective generators. Delivered intake files stay unchanged.

[The complete-frontend grammar experiment](full_grammar_experiment.md) applies
source16's overlap-safe counting to both original full-word tokenizations.
Across 32,000 paired DAG evaluations it still reaches 269 states, matching
rather than improving the prior control. The fixed winner regenerates and its
operation certificate passes independent checks and six mutations. The full
equality/theory frontend is retained; binary simulation remains open.

[The revised-layout grammar experiment](layout_grammar_experiment.md) preserves
source 19's complete word and matches its 268-state control across 56,000 DAG
evaluations. Both searches charge the compiled dispatcher depth; their
framework cost varies from 61 to 65 states. Exact-word certificates pass,
without a new state bound or binary simulation theorem.

## Next proof and compiler work

1. Complete the equality-free interpretation and its Foundation/Choice
   consistency bridge, using the calibrated subset-PSC theory as a control.
   Keep alternative and artificial calculi eligible by complete compiler cost.
2. Supply a complete logical frontend with a proved cross-variable substitution
   or refutation interface. The finite-sort model rules out calibrating the
   existing reduced C/G calculus. Preserve the attributed 253 construction as
   the implementation baseline while measuring complete alternatives.
3. Prove the selected enumerator, compiler and actual initializer simulations.
   The existing generic totalization result covers one normalization step,
   and register bisimulation covers exposed operations; neither covers the
   complete binary interpreter.
4. Establish the required ZFC-provable nonhalting/consistency equivalence before
   claiming the numerical candidate as an improvement on the benchmark.

The [public 253-state fold complement](public253_fold_search.md) tests all 504
folds of the two additional old states 5 and 84 while preserving every protected
register-box row. Only the known 5→64 runtime fold survives all 8,391 affine
cases; it does not reach the exact bootstrap frame within 2,000,000 steps.
Fuel exhaustion remains unresolved. This bounded experiment supplies no new
blank-start consistency machine or general minimality result.

The distinct [public253 local-window search](public253_macro_search.md) checks
all 63,756 ordered deletions at radii 4 and 5, with 64 steps per side. Neither
run produces a certificate. The larger window removes 447 projected patterns
across 26 states, but both abstractions still allow both symbols in every
working state. These bounded results supply no minimality theorem.

The [whole-cost grammar beam search](grammar_beam_experiment.md) scores 103,596
DAGs while retaining the same complete revised word. Its selected 269-state
candidate has an independently checked 4,533-pair RM certificate; it does not
improve the retained 268-state control. The bounded beam and coarse pruning
key make no optimality claim.
