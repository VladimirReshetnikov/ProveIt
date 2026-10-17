# Smaller machines for Con(ZFC)

The goal is a binary, single-tape machine with fewer than 254 nonhalting
states whose blank-tape non-halting is provably in ZFC equivalent to
Con(ZFC). The goal remains open. All new formal work uses Lean.
An intended set-theoretic meaning is optional: any effectively presented
theory or proof calculus is eligible once its consistency calibration is proved.
The complete compiled search, including its data and initialization, is the
cost measure that decides whether a candidate improves the baseline.

The [252-state register-permutation machine](candidate-permutation252/README.md)
now has a [closed Lean endpoint](binary_perm252.md): its literal blank-tape
nonhalting is equivalent to consistency of ordinary ZF, including Foundation
and Power. It retains the complete original proof-search program. The proof
includes all 82,552 bootstrap steps, all 8,391 decoder guard cases, unbounded
register operations and both directions of global binary simulation. No
coverage or register-operation premise remains. The exact table, full startup
tape and independent regeneration are preserved. This is distinct from the
older reduced-calculus 252-state experiment below.

The [direct well-founded-model construction](wf_model.md) now proves in Lean
that the exact native/numerical calculus is equiconsistent with ordinary ZF,
including Foundation and Power. It uses the quotient's existing collection
resource. Choice removal remains assigned to the constructible-class lane;
[PA internalization](pa_internalization.md) requires an explicit arithmetic
proof-code bridge. The original request asks for a PA proof, which is stronger
than the later goal record's ZFC metatheory target.

The complete binary endpoint passed a
[153-unit source-verified integration](results/binary-perm252-integration-verification.json):
all151 reused source identities match successful scoped builds, with fresh
standard-theory bounds, umbrella and joint callers. This is not a full153-module
rebuild. The closed theorem also proves Con(ZFC) implies nonhalting; the reverse
ZFC implication and the internal PA proof remain open.

The later merged `SatSupport` module also passed a
[154-unit integration](results/sat-support-integration-verification.json).
It proves uniform internally finite support for satisfaction on every internal
formula code, including nonstandard codes. The independent
[Choice-route review](constructible_choice_review.md) records its scope; the
internal well-order and Choice arguments remain open.

The [156-unit integration](results/history-abs-integration-verification.json)
freshly checks `ConstructibleAbs`, `Code254History` and the umbrella, with153
source-matched reused units. Satisfaction is now compared on constructible
data with a genuine environment and code validity in both models; formula-code,
Def/hierarchy absoluteness and Choice remain separate. The
[numeric history checker](code254_history.md) agrees with the original proof
validator on every natural input, including invalid codes. It is the next
concrete evaluator for the PA representation work, not an internal PA theorem.

A measured attempt to save a register by changing Cantor pairing to a
[power-of-two encoding](register_lifetime.md) retained the full calculus but
cost 306 states; its tested hybrids cost at least293. The current 252-state
table remains unchanged. Fewer registers alone do not guarantee a smaller
complete machine.

An independent [GEN-elimination presentation](gen_free.md) prefix-closes the
axiom families and recovers generalization by induction using QI and MP. Its
best tested complete control costs285 states. This sound ordinary
admissibility idea also failed to improve the current machine.

A [phase-invariant diagnostic](permutation252_phase_analysis.md) excludes six
source-program guards from the zero-register start and re-tests503 affected
fold recipes. None passes the bounded checker; fuel and abstraction stops
remain distinct from counterexamples. Three literal continuation probes also
show why different program counters need a proved semantic relation.

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

Batch 152 adds sources 26–34 from `da6dabcd89` (placement `b123527ff4`,
reconciliation `f6fdf828af`), bringing the host to 34 sources. Its ordinary
theory candidates are EPSC1 plus fixed adjunction, contraction/ground-epsilon
engines, shared subworld SR₂⁺ and finite assignment/class FAK12. A 253-state
variant saves 40 bootstrap steps with the same whole tape; it does not reduce
the state count. Reproduced clean initializer quotients remain at least 309,
and a new protected-basis replay matches the existing 268 control. The host
keeps the code 0/free-variable correction, exact bounded-search limits,
archived Lean audit scope and current post-pin overlaps. Full dossiers and
`code/reproduce_152.py` provide offline recovery and finite replay. None of
these new frontends has a kernel-checked full consistency-machine endpoint.

Batch153 adds sources35–36 from `4e720ccbbf` (placement `6135ffef4b`,
reconciliation `837b30d620`), bringing the host to36 sources. Checked dirty-root
absorption permits six arbitrary nonformula fields at a valid root with safe
formula data. An ordinary EPSC1 counterinterpretation rules out the old
Pairing/hereditary-domain shortcut, while its consistency strength remains
open. An actually reached scanner counterexample strengthens the earlier
prepared-frame obstruction. Same-count253 rewrites,597080 transition checks,
a290-state outgoing-equality control and unchanged268 grammar controls retain
their exact finite scopes. Both reports have complete dossiers and offline
replay through `code/reproduce_153.py`; they supply no new sub253 machine or
complete internal-ZFC endpoint.

Batch154 adds sources 37–41 (placement `d1636c9af8`, reconciliation
`9f4efefcff`, catalogue `21880d20b6`). Finite GIC/EPSC fusion, the EPSC1 plus
BinaryUnion repair, stronger support countermodels, finite assignment/class
and cyclic-algebra kernels continue the theory search. All advertised finite
suites and the fresh 26-source Lean closure pass; the guarded shortcut keeps
253 states. The algebraic ZFC query and complete new frontends remain
unexpanded. These reports supply no strict EPSC1 consistency separation or
new closed binary endpoint. Their preserved evidence and offline recovery are
in the host's batch154 appendix and `code/reproduce_154.py`.

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
| `Code254.lean` | All-natural base-four decoder and original numerical calculus; soundness for decoded bundles, completeness under no nonempty model of literal encodable bundles. The corrected statement explicitly requires a valuation; `NativeDecoded254` now compares the two bundle model classes. |
| `Code254Proof.lean`, `Code254ProofCompiler.lean` | Finite raw proof trees, a total natural-number checker and `C254 n ↔ ∃ code, check code n = true`; a structural compiler to the existing enumerator with exact block contracts and an explicit refutation command word. These external coding theorems are prerequisites for PA representation, not that representation itself ([checker](code254_proof.md), [compiler](code254_proof_compiler.md)). |
| `Code254History.lean` | Numeric12-rule course-of-values evaluator; `accepts_iff_check` covers all codes/conclusions and `c254_iff_history` gives exact derivability. Ordinary Nat/list computation; arithmetic representation and internal PA totality remain open. |
| `Enum254.lean` | The abstract six-register enumerator halts from zero iff code 1 is `C254`-derivable. Every candidate is reached unless an earlier one halts; proof blocks handle arbitrary retained registers. Model corollaries explicitly require a valuation. Its literal Prog254/RegisterPath simulation and the permutation252 complete binary composition are checked. |
| `RMDag.lean`, `Dag254.lean`, `L2Lib254.lean`, `L2Macros254.lean`, `L2Control254.lean`, `L2Axioms254.lean`, `L2AxiomsEval254.lean`, `L2Root254.lean` | L2 for the shared 219-node register program (attributed data port of the pinned `Dag254.v`, used by the 253- and 254-state tables): Wade's structured semantics with determinism; every loop, `pair`, the unpair walk, all stack/formula macros, the equality test, fetch, MP/NIP/DROP and the generated `axioms()` closed forms; `root_step` (one root run is one `enumStep`, halting included), `iter_halts_boot` and `program_halts_iff : IterHalts dag254 (nextproof = 2) ↔ C254 1`. |
| `RMEquiv.lean`, `RMEquiv254.lean` | L3: Wade's path semantics and the structured semantics agree for every well-formed DAG (`halts_iff_iterHalts`, forward and backward simulation up to trailing zero bits, Boolean well-formedness check); the 219-node program is well-formed (kernel-checked tables), giving `path_halts_iff : Halts pathDag254 (nextproof = 2) ↔ C254 1`. |
| `RMBisim.lean`, `Bisim254.lean` | L4: segment bisimulations transfer path halting for every register file (symmetric relation defined by certificate lookup, so one check gives both directions); 3010 related test-site pairs between the literal 6459-row `Prog254` and the 219-node DAG, kernel-checked in 16 chunks, giving `literal_halts_iff : Halts Prog254.program Prog254.initial ↔ C254 1` ([tarski_logic_layer.md](tarski_logic_layer.md)). |
| `NamedZF.lean`, `InternalOrd.lean`, `InternalRank.lean`, `ZFRank.lean`, `ZFNative.lean`, `Endpoint254.lean` | ZF proves the native axioms: named formulas over `Form` with named Separation/Replacement; inside any model of the ZFAxioms bundle with Power and set Regularity (no external well-foundedness), ordinals with trichotomy, the cumulative hierarchy by transfinite recursion, the rank theorem, Collection for every matrix and power containers; hence every `ZFax_s` model satisfies `NativeAx`, `zf_refutation_of_native` by `theory_transfer`, and `literal_nonhalting_of_zfc_consistent : Con(ZFC) → ¬ Halts Prog254.program Prog254.initial` ([tarski_logic_layer.md](tarski_logic_layer.md)). The reverse ZF comparison is now checked in `WFTheory`; Choice remains open. |
| `TransRec.lean`, `ConstructibleDef.lean`, `Constructible.lean`, `ConstructibleReflect.lean`, `ConstructibleZF.lean` | Gödel's L inside any ZF model (no external well-foundedness): transfinite recursion for a definable stage operation; `Def(X)` through BoundedZFCConsistency's certificate satisfaction of coded formulas, with the truth bridge for standard formulas; `L_a ∩ Ord = a`; pairing, union and power in L; the reflection theorem for the L-hierarchy (closed limits by ω-iteration of a definable closing step); Separation and Replacement in L; `L_models_ZF`: the constructible substructure satisfies `ZFax_s`. AC in L (hence the Choice transport) remains ([tarski_logic_layer.md](tarski_logic_layer.md)). |
| `OutgoingProfile.lean` | Four-node outgoing equality from exact full-profile singletons, actual raw-PSC model corollaries and reserved-zero named semantic translation at one false point. Source equality denotes full observational classes. |
| `ConstructibleAbs.lean` | Basic operations, internal omega, recorded application, environments and certificate relations agree on constructible data; `satIn_iff` requires formula-code validity in both models and a genuine environment. `memRel_iff` compares encoded membership. This first part does not prove formula-code/Def/hierarchy absoluteness, V=L or Choice. |
| `Numeric254.lean`, `NamedNumeric254.lean` | Exact original four-tag numerical rules and gated C/G/vacuity bundle; named proof transport and refutation equivalence for the explicitly defined encoded-numerical-theorem theory Q. Q/ZFC calibration remains open. |
| `BootstrapFrame253.lean` | The actual 312,975-step binary bootstrap realizes the actual 330-step register endpoint, with all nine permuted registers, 158 spare blocks and exterior blanks retained. |
| `Code254Containers.lean` | A literal gated bundle gives the existing transitive, powerset-bounding container resource in an irreflexive model with an explicit valuation. |
| `ZipperRuns.lean`, `RegisterBoxes253.lean` | Generic whole-tape sequential execution and preserving scans; actual public253 zero-decrement box for arbitrary preceding and following registers, in exactly twice the prefix width plus five steps. No PC-update or complete instruction simulation claim. |
| `Code254GIC.lean`, `Code254Models.lean` | Hygienic actual Form matrices and padded gated bundles give the CP/GIC model interface; semantic encoding/decoding gives the decoded-to-encodable model implication. The reverse implication is now supplied by `NativeDecoded254`; full ZFC calibration remains separate. |
| `NumericCode254.lean` | Exact equality of the two pairing/encoding definitions and equivalence of their twelve-constructor numerical derivability relations, including zero and all actual gates. |
| `RegisterMark253.lean`, `RegisterIncrement253.lean` | Actual public253 marking and increment excursions, with arbitrary register values and spares, exact step counts and whole-tape output. PC updates and general dispatch remain separate. |
| `QuotientSeparation.lean` | The full quotient satisfies the actual `Sep_form` schema for arbitrary formulas and quotient parameter valuations, using a literal equality-free GIC matrix. Other ZF axioms remain separate. |
| `QuotientPower.lean`, `QuotientReplacement.lean` | Actual quotient `Pow_form` and all `Repl_form` instances, using literal trace/filter and guarded translated matrices; quotient subsets and parameter valuations are unrestricted. |
| `RegisterDecrement253.lean` | Positive decrement of the actual public253 table: arbitrary register values, exact twice-old-file-width-plus-three duration, all spare data preserved and the additional zero spare retained. All four register boxes are now proved; PC and general dispatch remain separate. |
| `QuotientBasic.lean` | Actual quotient Empty Set, Pairing, Union and an empty-root singleton-closed container; ordinary Infinity is a separate construction. |
| `SingletonInfinity.lean` | A literal Separation cut gives the least singleton-closed index, with induction over represented sets and formulas; Infinity is not an assumption. |
| `BreakSite253.lean` | Complete actual PC site001→1 with unchanged registers/spares and whole-tape DispatchFrame, in 2×gap+34 steps. General dispatch remains open. |
| `FiniteSets.lean`, `InductiveAttempts.lean` | Actual finite graph objects and formula atoms construct an ordinary inductive set in the CP/GIC quotient, using three specific Separation matrices and one Replacement matrix, with no prior Infinity. |
| `QuotientZF0.lean` | The complete quotient satisfies ZF without Foundation or Choice; a refutation of that theory forces the abstract enumerator to halt. `WFTheory` supplies the full ZF comparison and `BinaryPerm252` the literal binary endpoint. |
| `DecodeFresh254.lean`, `NamedForm254.lean` | Every-code semantic freshness, including truth code0, and exact named-to-de-Bruijn matrices including shadowed/colliding names. Native equality is retained explicitly. |
| `DuplicateProfiles.lean` | A conditional duplicate-model obstruction: equality-free CP/GIC and IR can hold while the actual native-equality numerical bundle fails. No starting-model existence is asserted. |
| `WritingRuns.lean` | Exact arbitrary-length scans that overwrite the read bit, with whole-tape Core corollaries and explicit actual-transition premises. |
| `ZeroSite253.lean` | Complete actual000 zero branch preserves the full dispatch frame; the checked blank run extends to313429 binary steps and matches RM331, with all158spares retained. |
| `EqualityGIC.lean` | Explicit outgoing-profile faithfulness, supplied for example by native Pairing, permits equality erasure and extends equality-free GIC to all actual Form matrices. |
| `QuotientCPGIC.lean` | A literal output-guarded trace gives CP in the same raw container's quotient; translated actual Form matrices give full native-equality GIC. Quotient IR is not inferred. |
| `ProgramZF0.lean` | A ZF0 refutation forces the actual 219-node structured program to halt from nextproof = 2; structured non-halting implies Con(ZF0). The subsequent `BinaryPerm252` endpoint includes literal blank execution and Foundation; Choice remains open. |
| `NativeDecoded254.lean` | Native CP + full actual-Form GIC + raw IR satisfy every decoded bundle, including coincident binders and truth code 0. With an explicit valuation, ModelsEncodable and ModelsDecoded are equivalent. |
| `NativeTheory254.lean` | Numerical falsity and actual 219-node structured-program halting are each equivalent to refutability of the explicit sentence theory CP + full native-Form GIC + IR. ZFC calibration and binary execution remain separate. |
| `EnumSafeStart254.lean`, `DirtyRoot254.lean`, `DirtyProgram254.lean` | Attributed arbitrary-cutoff enumeration and dirty-root absorption, composed with the actual structured219/path program. Six numerical fields are unrestricted; top/cache/stack retain their exact theorem invariant and logical registers beyond8 remain zero. |
| `SeedInvariant254.lean` | Six constructors certify nonzero initial theorem codes, unshifted stacks, and the resulting dirty-start/native-refutation equivalence. This gives a larger sufficient initializer target; no binary startup is inferred. |
| `WellFoundedPart.lean`, `WFRelativization.lean`, `WFModel.lean`, `WFTheory.lean` | One actual GIC instance supplies closure of internal well-foundedness. Actual translated Separation/Replacement, Infinity and Power make its subtype a ZF model, yielding `C254 F ↔ BProv ZFax_s [] Bot` and native/ZF equiconsistency. Choice and internal PA proof codes remain open ([direct route](wf_model.md)). |
| `RMBisim.lean` | Merged generic segment bisimulation with symmetric halting transport and a sound finite checker on explicit decoder trees. No concrete certificate instance is included in this module. |
| `SitesPerm252Checks0–7.lean`, `SitesPerm252.lean` | All233 decoder chunks and8,391 guarded instruction cases, composed against the complete literal tree. No external coverage premise remains. |
| `BinaryPerm252.lean`, `ZFCBoundPerm252.lean` | Actual blank252 halting iff numerical/native/ZF refutation, also iff an accepted finite proof code. Con(ZFC) implies blank nonhalting. Choice removal and internal PA formalization remain open. |

The [Tarski audit](tarski_calculus_review.md) and subsequent
[propositional certificate port](lukasiewicz_basis.md) now establish full
named-calculus completeness. The seven added modules and updated umbrella
pass scoped direct Lean checks against the source-verified dependency cache.
The basis and ex-falso derivations use no axioms; completeness uses only
`propext`, `Classical.choice` and `Quot.sound`. The later numerical, native-theory
and binary modules listed above discharge the corresponding obligations for
the complete original calculus and the252-state permutation machine.

The calibration uses the repository's first-order internal recursion theorem
for the reverse construction, then its generic completeness theorem for
deductive equivalence; [psc_calibration.md](psc_calibration.md) gives the exact
statements and comparison theory. That semantic calibration is not a proof-code
translator verified in arithmetic. The current binary and proof-data modules
supply an external checker/compiler endpoint, while internal arithmetic theory
transport and the final ZFC comparison remain open. `PositiveClosure`
deliberately assumes the specific closure instances used by each lemma;
arbitrary second-order relations are not silently treated as a first-order
schema.

The Lean prefix/de Bruijn codec and Python postfix/named-variable bit codec
are distinct encodings. Only the stated Lean token codec has a Lean theorem.
Three token forms still carry natural-number atom payloads. Axiom audits
show no custom axioms or `sorryAx`; only the repository's ordinary Lean
foundational axioms occur. The literal finite table facts have no axioms.

Rebuild the dependency closure **serially from source**:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/check_lean.py
```

This compiles 99 source units: the first-order logic, calculus and completeness
modules, `ZF.Zf`, `BusyBeaver.Core`, 93 research modules and the umbrella into a
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
The [abstract enumerator audit](enum254_review.md) and
[quotient Separation](quotient_separation.md) extend the runner to 64 units.
`results/enum-separation-integration-verification.json` records the corrected
enumerator, Separation and umbrella checks with previously verified dependencies.
The [Power Set](quotient_power.md), [Replacement](quotient_replacement.md) and
[positive-decrement](register_decrement253.md) developments bring the runner
to 67 units. Their scoped source, caller and axiom checks are linked in those
notes; `results/power-replacement-decrement-integration-verification.json`
records the joint source and umbrella check with the earlier dependencies reused.
The [basic quotient axioms](quotient_basic.md), [singleton index](singleton_infinity.md)
and [first complete PC site](break_site253.md) extend the runner to 70 units.
Their independent checks are supplemented by
`results/singleton-break-integration-verification.json`: three source builds,
the umbrella, seven axiom audits and a caller, reusing the verified67 cache.
This integration does not rebuild the expensive finite bootstrap.
The [finite set atoms](finite_sets.md), [ordinary Infinity proof](inductive_attempts.md),
[full quotient comparison](quotient_zf0.md) and five merged
[structured-program modules](l2_component_review.md) extend the runner to78 units.
`results/infinity-l2-integration-verification.json` records all eight source
builds and the umbrella. `results/quotient-zf0-verification.json` records the
final quotient module's additional abstract-enumerator consequence and renewed
umbrella/audit checks. Previously verified dependencies are reused.
The [all-code freshness proof](decode_fresh254.md), [named matrix adapter](named_form254.md),
[duplicate-model obstruction](duplicate_profiles.md), [overwriting scans](writing_runs.md)
and generated AX subtree extend the runner to83 units. Their five source
checks, umbrella, fourteen axiom audits and three callers are recorded in
`results/decoder-duplicate-integration-verification.json`, with the earlier
dependencies reused. This record also checks the duplicate module's final
comment-only clarification after its separate source audit.
The [000 zero branch and RM331 endpoint](zero_site253.md) bring the runner to84 units;
`results/zero331-integration-verification.json` reuses its matching checked olean
and rebuilds the umbrella with three axiom audits and an endpoint caller.
The [conditional equality-schema adapter](equality_gic.md) brings it to85;
`results/equality85-integration-verification.json` checks its source and the
final umbrella. Neither integration recomputes the finite bootstrap.
The merged AX evaluation and complete L2 root correspondence, together with
[the structured-program ZF0 consequence](program_zf0.md), extend this to 88 units.
`results/l2-program88-integration-verification.json` records five scoped source
builds, nine axiom audits and three callers; both AX generators reproduce their
current sources. [CP and native-form GIC in the quotient](quotient_cpgic.md)
bring the runner to 89; `results/quotient89-integration-verification.json`
checks that source, the umbrella and four joint axiom audits. Dependencies are
reused, with no fresh full-closure or bootstrap rerun.
The [native decoded-model adapter](native_decoded254.md) brings it to 90 units
and closes the encoded/decoded model-class gap under raw IR and a supplied
valuation. Its source has 14 axiom audits and six callers; the joint source,
umbrella and five additional audits pass in
`results/native90-integration-verification.json`. No full dependency or
bootstrap rebuild is claimed.
The [explicit native theory](native_theory254.md) brings the runner to 91
units. Its exact CP/GIC/IR refutation predicate is equivalent to numerical
falsity and to actual structured-program halting from nextproof = 2. The
source and final umbrella check, joint axiom audits and endpoint callers are
recorded in `results/native91-integration-verification.json`, reusing the
verified dependencies. This equivalence does not yet calibrate the theory
to ZFC or connect the structured DAG to binary-tape execution.
The merged `RMEquiv` and `RMEquiv254` extend the runner to 93 units.
`results/rmequiv93-integration-verification.json` records their scoped
source checks, regenerated height/escape tables, the final umbrella, nine
axiom audits and three callers. The 219-node DAG's path semantics is now
equivalent to its structured semantics for every register vector. This
still leaves the separate 6,459-node literal `Prog254` correspondence and
binary runtime proof; the public 3,010-pair certificate is the next bridge.
The [dirty-start composition](dirty_program254.md),
[safe initializer families](safe_initializer_families.md),
[internal well-founded part](well_founded_part.md), and merged generic
`RMBisim` bring the runner to 99 units. The scoped verification record
`results/breakthrough99-integration-verification.json` checks all source
identities and import order, the two newly built modules and umbrella,
12 axiom audits and three callers. The four other new modules have matching
separate scoped build records. No full dependency or bootstrap rerun is claimed.
The safe-seed certificate language proves that startup formula fields need
not be zero: even code60 is the theorem `Rel(1,0) → Truth`, while stack60
contains falsity and is unsafe. This motivates changing physical register
roles during initialization. The first36 permutations pass all selected
instruction contracts but produce no safe startup in their stated finite
blank runs; three controls were independently replayed. The
[functional subset-closure experiment](functional_subset_closure.md) is
a separate ordinary theory alternative whose measured retained compiler
cost increases to347. Neither experiment supplies a new state bound.
The separate [target-permutation obstruction](quotient_ir_obstruction.md)
shows at the ordinary mathematical level why raw IR cannot simply be passed
through this bisimulation quotient, even when native equality and Pairing are
available. It is conditional on an actual ZF model and is not a Lean theorem.
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

1. Complete the Choice transport from the checked native/ZF comparison through
   the constructible-class lane. The complete252 binary simulation is checked.
2. Represent the exact proof checker, proof-data compiler and finite binary
   traces inside PA, and prove the required arithmetic comparison. The external
   Lean equivalence does not settle this stronger requirement.
3. Continue minimizing complete machines. Alternative and artificial calculi
   remain eligible once their consistency comparison is justified; preserve
   the complete252 machine as the current implementation baseline.
4. Preserve the finite-sort countermodel when evaluating reduced logical
   engines. A smaller compiled table without a sound consistency calibration
   does not establish the requested record.

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

The [faster253 mixed-row search](variant253_search.md) tests 1,338 new
fusion recipes around source27's three reassociated decoder states. All
fail affected affine checks; seven have literal prepared-frame halt
witnesses, while the other failures remain bounded diagnostics. An
independent replay reproduces every functional result, the 8,391-case
baseline and its complete 312,935-step bootstrap frame. No smaller table
is accepted.

The [whole-cost grammar beam search](grammar_beam_experiment.md) scores 103,596
DAGs while retaining the same complete revised word. Its selected 269-state
candidate has an independently checked 4,533-pair RM certificate; it does not
improve the retained 268-state control. The bounded beam and coarse pruning
key make no optimality claim.

The [incoming-edge deletion search](public253_context_search.md) tests 502 new
nonuniform old107 removals and two uniform controls, preserving the full original
frontend and all55 protected pairs. No recipe survives the bounded affine
filter; no modified table proceeds to bootstrap testing. The complete per-recipe
ledger distinguishes fuel exhaustion, abstraction limits and unexpected halts.

The [safe initializer experiment](safe_initializer_families.md) uses the checked
nonzero seed certificates to permit many more startup configurations. All64
stack-containing swaps/three-cycles retain the8,391 conditional instruction
contracts, but none reaches the sufficient root target within its literal
bound. Exact first-write analysis reduces all252 possible starts to seven
nonblank classes and12 starts that remain blank; the455 class/table runs are
finite observations. An independent interpreter replays all252 prefixes and
six full normalized controls. Interior frames and short gaps remain separate
from the sufficient root criterion.

The [ground-equational proof generator](equational_generator_cost.md) removes
formula matching and freshness by constructing only valid ground equalities.
Its measured complete control is299 working states after bounded sharing,
before a ZFC-specific query and writer. The isolated171-state axiom emitter is
a component count. This first complete control is larger than the existing
runtime; it supplies a reproducible cost baseline for a different architecture.
