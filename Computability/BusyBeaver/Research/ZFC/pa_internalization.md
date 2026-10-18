# Internalizing the machine comparison in arithmetic

Research inventory begun 16 October 2026 against
`7b1e56dbc59f746695a7fb375546422f91de3a96`, updated with the explicitly linked
Lean checks below. The full PA equivalence is still open. The represented
checker and actual machine-run evaluator have PA totality theorems. The
forward validator consistency implication is now also proved in IΣ₁ and PA.

The request and active goal require an equivalence provable in **PA**.
A Lean theorem comparing halting and `BProv` is an ordinary metatheorem until
the intended arithmetic sentence and an object-theory proof are connected to
it. Completing the PA version would also serve the ZFC requirement, after
checking the chosen arithmetic interpretation in ZFC.

The [246-state endpoint](prefix246_binary.md) now closes the external Lean
theorem for the exact contextual-fold machine: blank nonhalting iff Con(ZFC).
It reuses the earlier [Choice calibration](choice_calibration254.md), including
Choice in L and external first-order completeness. This discharges the
external consistency comparison; it does not implement the represented proof
translations or prove their correctness for every internal code in every PA
model. The remaining obligations are recorded below.

The current arithmetic checkpoints are:

* [Accepted-proof soundness](../../../../Logic/Interpretability/ZFCinPA/model_coded_decoder_accepted254.md)
  sends every accepted internal numerical conclusion to an actual internal ZF
  proof. It covers all twelve rows, both bundle gates and arbitrary
  nonstandard proof codes, using Σ₁ order induction.
* [The fixed forward sentences](../../../../Logic/Interpretability/ZFCinPA/validator_consistency_forward254.md)
  have actual IΣ₁ and PA proofs:
  `Con(ZF) → ¬∃code, value(code)=2` and
  `Con(ZFC) → ¬∃code, value(code)=2`.
  The all-internal soundness theorem supplies the model-wise premise before
  arithmetic completeness is applied to these fixed sentences.
* [Internal relative interpretation](internal_relativization_refresh.md)
  now includes domain-side discharge and the function-free set-language
  adapter. The [constructible interpretation](../../../../Logic/Interpretability/ZFCinPA/constructible_interpretation.md)
  supplies the fixed L-domain formula, its nonemptiness, the quotation bridge,
  and the finite equality, fixed ZF and Choice axiom obligations. The uniform
  internal Separation/Replacement hypothesis `hSchema` remains open.
* [Internal validator provability](../../../../Logic/Interpretability/ZFCinPA/validator_provability254.md)
  supplies the twelve literal rule closures and a classical propositional
  interface. The [formula encoder](../../../../Logic/Interpretability/ZFCinPA/validator_formula_encoder254.md)
  has total, fixed arithmetic graphs with depth-sensitive variable labels.
  The [quantifier interface](../../../../Logic/Interpretability/ZFCinPA/validator_quantifier_core254.md)
  proves finite quantifier and vacuity laws, including a two-binder bridge
  with four explicit vacuity premises. The [equality interface](../../../../Logic/Interpretability/ZFCinPA/validator_equality_core254.md)
  supplies reflexivity, symmetry, transitivity and atomic congruence. The
  [configurable environment encoder](../../../../Logic/Interpretability/ZFCinPA/validator_environment_labels254.md)
  proves exact internal term, vector and formula SHIFT laws through nested
  quantifiers. [Binder opening](../../../../Logic/Interpretability/ZFCinPA/validator_environment_opening254.md)
  now gives exact term/vector/formula substitution identities and opened
  ALL/EXS matrix equations for arbitrary internal depths. The
  [vacuity proof](../../../../Logic/Interpretability/ZFCinPA/validator_environment_vacuity254.md)
  supplies generalization witnesses for every internal encoded formula when
  its free, bound and future binder labels avoid the generalized variable;
  its uniform environment invariant uses Π₂ induction in IΣ₂. The
  [represented equality context](../../../../Logic/Interpretability/ZFCinPA/validator_equality_context254.md)
  supplies coordinate projection and the binder-cons interface. Its
  [vacuity theorem](../../../../Logic/Interpretability/ZFCinPA/validator_equality_context_vacuity254.md)
  derives both context-vacuity resources from avoidance of equal-length
  stacks, using Σ₁ induction in IΣ₁. The
  [alpha transport](../../../../Logic/Interpretability/ZFCinPA/validator_environment_alpha254.md)
  now proves both implications between encodings of every internal formula
  under the same equality context, using Π₂ induction in IΣ₂ and explicit
  disjoint fresh streams. [Concrete stream selection](../../../../Logic/Interpretability/ZFCinPA/validator_environment_streams254.md)
  now compares encodings at any two free-safe starts, including overlapping
  starts `s` and `s+2`, through a represented opposite-parity intermediate.
  Source-proof translation remains open and can use the configurable encoder
  directly, since its falsity code is already `1`; comparison with the earlier
  fixed encoder is optional. Arbitrary accepted proofs are not assumed closed
  under variable renaming.
* [Both actual reads](arithmetic_control_read_template254.md) are checked on
  every internal register file with its scratch fields zero. They reach the
  actual dispatch control 38, retain the whole register file in their
  endpoint, and give a positive internal logical runtime.
* [Actual dispatch](arithmetic_control_dispatch254.md) and the
  [complete NIP branch](arithmetic_control_unpair254.md) are checked for
  arbitrary internal values. With both scratches zero, cache1 halts;
  otherwise NIP writes the two Cantor projections of WS to cache and WS,
  then returns to fetch. The AC2 dispatcher composition additionally clears
  AC. The [pairing routines](arithmetic_control_pair254.md) now have terminating
  all-internal contracts, including both actual DROP and MP occurrences and
  whole-file preservation. The [complete DROP branch](arithmetic_control_drop254.md)
  pushes the old TW/WS pair, restores TW from the cache and returns to fetch;
  its AC1 dispatcher composition is also checked. The
  [MP comparison](arithmetic_control_compare254.md) clears scratch1 and cache,
  reaches success exactly when their original values agree, and has the
  exact internal logical clock `3*a+2*distance(a,b)+2`. Both
  [MP parameter pushes and the comparison-to-fetch tail](arithmetic_control_param_push254.md)
  are now checked. Each push preserves param1 while setting TW to param1
  and WS to the pair of the original TW and WS. The
  [short MP unpair](arithmetic_control_unpair_core254.md) and its composition
  with the initial push now restore the original WS, put old TW in scratch1,
  and put param1 in TW. The [complete MP branch](arithmetic_control_mp254.md)
  now composes the actual constructor, fourfold transfer and comparison tail.
  It returns to fetch, sets TW to param1 and pushes a zero on success, clears
  TW and preserves WS on failure, and clears cache in both cases. Its AC0
  dispatch composition is also checked. The [first AX parameter push and
  classifier](arithmetic_control_ax_prefix254.md) now have all-internal
  whole-file contracts. The [second AX parameter push](arithmetic_control_ax_cache_push254.md)
  now covers controls 67–93 and composes both pushes from control 41.
  It puts the old cache in TW and saves the previous TW on WS, preserving
  all other fields. Its copy/restore tail has exact internal clock
  `7*cache+2`; the complete push assumes both scratch registers zero.
  Eight axiom probes and twelve callers pass with zero warnings. The
  GEN constructor and remaining AX bundle are still open.

The remaining major steps are the reverse internal ZF-to-validator proof
translation, the internal L-specific Separation/Replacement proofs, and the complete
interpreter-to-Enum connection. The forward validator sentence alone does
not yet imply the requested PA theorem about the literal binary machine.

The active binary target is the exact 246-state machine. Its table, logical
seed, whole-tape instruction contracts, complete decoder coverage and blank
startup now compose into the checked external ZF/ZFC consistency endpoint.
That theorem still does not supply an internal PA proof.
The [fixed arithmetic lookup for its exact table](arithmetic_machine_graph_prefix246.md)
is now checked in every IOpen model and agrees with all 492 typed transitions.
The [exact step graph](arithmetic_machine_step_prefix246.md) now defines the
numeric operation on every IOpen configuration code, including inactive and
invalid states. Its [fixed run graph](arithmetic_machine_run_prefix246.md)
is total and unique at every internal IΣ1 time index; the separate Nat theorem
compares every ordinary runtime to this literal binary machine. The
[bootstrap transport](arithmetic_bootstrap_prefix246.md) proves the fixed
410,735-step arithmetic startup sentence in IΣ1 and PA. Its numeral-transfer
lemma applies to external natural times, not arbitrary internal times.
The unbounded internal register/binary comparison still needs its own proof.

The [arbitrary-start iterator](arithmetic_machine_run_from_prefix246.md)
now has fixed Σ₁/Δ₁ graphs, totality, time-addition laws and whole-configuration
halt absorption for every internal initial code and time in every IΣ1 model.
The [prefix-removal theorem](arithmetic_machine_prefix_prefix246.md)
proves halting equivalence before and after any internal prefix, including
halting inside that prefix. Its `boot_halts_iff` specialization removes the
checked 410,735-step startup using its complete numeric tape code. The two
modules passed 23 axiom probes and 29 typed callers with zero warnings.
This closes arithmetic startup removal; the post-startup register/binary
simulation and its connection to the seeded scheduler remain open.

The [seeded arithmetic scheduler](arithmetic_enumerator_seed246.md) now
proves the validator/scheduler equivalence at candidate 3, pointer 0 and
working fields `TW=WS=H=0,D=3`, in every IΣ1 model. Both proof-code and
runtime witnesses range over all internal values. The represented refutation
word has raw candidate at least 3, and the initial working state is certified
even with `D=3`. The resulting fixed sentence has IΣ1 and PA proofs. This
closes the arithmetic scheduler's seed adjustment; its identification with
the exact246 binary run and the reverse ZF-to-validator proof translation
remain open.

Source review of the merged arithmetic work through `70f2e7a57b` identifies
three further reusable pieces in `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/`:
`LGlueCodes.lean` proves environment opening/free-variable and binder code
identities for arbitrary internal formulas; `LMatch.lean` supplies the
primitive-recursive, Sigma-one-definable matching formula `MT(j)` and its
zero/successor equations for every internal index; `LGlueT.lean` contains
`funTemplate_provable`, `slot0Template_provable` and
`slotSTemplate_provable`. These fixed templates prove functionality and
slot-reading steps and can be instantiated by the existing internal
`compileT_provable` interface. This paragraph records source inspection,
not a new compiler run of those upstream files.

Commit `2285ff6c00107552a50b988fc71a56a7f2df9b88` adds
[LGlueT2](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LGlueT2.lean),
with fixed-template derivability for the Boolean constructors, quantifiers,
and equality/membership atoms. These templates can be specialized at typed
internal formula codes, including nonstandard codes, using
`LTemplate.compileT_provable`; their explicit premises must still be discharged.

Commit `ce89d875857e59e147becd7f34a7c5ea8d18180b` adds
[LGlue1](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LGlue1.lean),
closing internal matching functionality and slot reading. `fun_MT` gives an
internal ZF proof of functionality for every internal matching length `j`;
`slot_MT` gives the corresponding reading of every slot `a < j`. Both use
represented Sigma-one induction in an arbitrary IΣ1 model, with explicit
formula-code and shift/substitution identities. The numeral-naturalness
premise is discharged by the existing `LNumOK.numOK`.

Commit `ccdebc892a922881b299455c53bb75c32d3e2ae4` adds
[LGlue2](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LGlue2.lean).
`shift_envForm` proves `shift (envForm n p) = envForm n p` for every
internal semiformula code and depth in an arbitrary IΣ1 model, including
nonstandard codes. The transformed predicate retains its bound environment
slot; the identity concerns free-variable shifting. `tr_gS`, `tr_qHyp`,
`tr_relAll` and `tr_envAll` identify the translated glue and universal-step
templates. `QX_free` identifies the opened quantifier premise with the
successor matching clause; with `LGlue1.MT_succ`, the matching length becomes
`j + 1`. Its sole extra premise, that the environment predicate is shift-fixed,
is supplied by `shift_envForm`.

These are code identities needed to assemble the internal glue derivation.
This module does not yet declare the general `glue` theorem, matching-environment
existence or `hSchema`. Specializing the template derivations, completing the
free-based formula induction and connecting matching environments to the
relativized schema closures remain. This update records source review only,
without a new compilation or axiom-audit claim; the reverse validator comparison
and actual 246-state arithmetic runtime remain separate obligations. The
[pinned source review](results/upstream-ccdebc892a-source-review.json) records
the declarations and remaining obligations.

Commit `e6b5769ba46ca018085414df212968273022531b` adds
[LGlue3](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LGlue3.lean).
`glue_atom` supplies the atomic compiled-glue client: for all internal
indices `a,b < j` in any IΣ1 model, internal ZF proves that the membership
or equality atom agrees with its environment encoding under `MT j`.
It discharges the slot, numeral-correctness, functionality, uniqueness and
atom-definition premises; `eAtomT_val` identifies the encoded atom body.
The [independent source review](results/upstream-e6b5769ba4-source-review.json)
finds no issue within that scope, without claiming a fresh compilation.
The matching antecedent remains. At that stage, general formula glue and its
internal induction, matching-environment existence, and the schema
closure/domain-side adapter to `hSchema` remained open.

Commit `116aa35087a8a37b57b3e07bb0de72a891218a35` adds
[LGlue4](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LGlue4.lean).
Its `glue` theorem supplies the general formula induction in every IΣ1 model:
for an internal formula `q` with free variables below `j`, internal ZF proves
that `relativize domL q` agrees with `envForm 0 q` under the matching
antecedent `MT j`. The explicit budget `j + formulaComplexity q ≤ C` bounds
the quantifier over `j`, keeping the induction predicate Σ₁; each binder
uses the freed formula at matching length `j+1`. This budget can be chosen
as `j + formulaComplexity q`, so it does not restrict formulas to standard
codes or externally bounded complexity.
The connective and quantifier clients now discharge the corresponding
compiled-template premises. At that stage, matching-environment existence,
the final Separation/Replacement combinations and the universal-closure/domain-side
adapter to `hSchema` remained open. The
[pinned review](results/upstream-116aa35087-source-review.json) records source
inspection of the new module and its ten-probe audit; this integration makes
no fresh compilation or executed-audit claim.

Commit `cc42edb2547a0d14c31bab552e629412ad6440f2` adds
[LFvBound](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LFvBound.lean).
In every IΣ₁ model, opening a shift-fixed internal body and binding its free
variables back recovers that body. This derives the free-variable bound on
its opened instance. A second internal induction transfers such a bound back
through a bound-variable substitution. Reading the Separation and Replacement
skeletons then bounds their cores: `FvLt (m+1) (free K)` for Separation, and
`IsSemiformula (m+2) (bindFreeAt 2 K)` for Replacement. The recognizer supplies
the needed shift-fixed body, its level and the equality with the schema body,
so these bounds require no restriction to standard formula codes.
This closes the core-bound prerequisite at source level. At that stage,
matching-environment existence, the exact final schema combinations and the
universal-closure/domain adapter to `hSchema` remained. The Replacement
conclusion still needs its precise depth-two opening adapter for the
zero-level glue interface.
This integration records source review only: the new module has not been
compiled or axiom-audited in this review, and the existing `LGlueAudit` does
not probe it.
The [pinned source review](results/upstream-cc42edb254-source-review.json)
records the internal quantifiers, exact recognizer premises and remaining adapters.

Commit `014b9618729e6d3e8bbfe95eeb0fdfecae7e2d0d` adds
[LPeel](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LPeel.lean).
In every IΣ₁ model, `peel` turns an internal ZF proof of the opened-body
statement `pVal m (rel (subst (fvarVec m) b))` into one of
`pVal 0 (rel (qqAlls b m))`, for arbitrary internal `m,b`, assuming
`IsSemiformula m b` and `shift b = b`. Its Σ₁ successor induction uses
`peel_step`, the matching-code successor equation and a fixed template for
extending a stage environment by a constructible element. `peel_close` then
removes the zero-match antecedent using a functional base environment.
This supplies the closure mechanism without separately constructing an
environment matching every internal parameter tuple. The opened-body proof
remains an explicit premise. The exact schema/template combinations,
Replacement's depth-two opening adapter and final recognizer/domain-side
integration remain. The [pinned review](results/upstream-014b961872-source-review.json)
records source inspection only: no fresh compilation or executed axiom audit
is claimed, and the existing `LGlueAudit` does not probe `LPeel`.

## What is already available

The following declarations identify mathematical inputs, not represented
proof-code transformations.

| Existing interface | Precise boundary |
| --- | --- |
| `Code254.C254` (`Lean/BusyBeaver/ZFC/Code254.lean:102`) | Twelve code-level inference constructors, including the two freshness inequalities on `bundle`; the relation lives in `Prop`. Code 0 decodes as truth and code 1 as membership `(0,0)`, so native Bottom needs IR. |
| `NativeTheory254.c254_refutation_iff` (`NativeTheory254.lean:76`) | Exact `C254 1 ↔ BProv NativeAx [] Bottom`, where `NativeAx` is sealed CP, every **native Form** GIC instance, and IR. Both directions use semantic completeness/soundness; an explicit valuation prevents the former empty-domain error. |
| `ZFNative.zf_refutation_of_native` (`ZFNative.lean:63`) | Native refutation implies ordinary ZF refutation, through `theory_transfer` and the arbitrary-model rank construction. ZF here includes Foundation and Power. |
| `Enum254.build`, `complete`, `enum_halts_iff` (`Enum254.lean:662,684,701`) | Proof construction and exhaustive enumeration at the ordinary metatheoretic level. The command blocks are explicit, but `build` returns an existential from a `Prop` derivation. |
| `NumericCode254.numThm_iff_c254` (`NumericCode254.lean:133`) | The two local exact numerical calculi agree; this is useful for avoiding a third arithmetic coding. It is not an internal PA proof of that agreement. |
| `Code254.c254_of_thmG` (`Code254.lean:425`) and `NamedNumeric254.transport` (`NamedNumeric254.lean:37`) | Existing constructor-by-constructor named/numerical transports provide templates for data-level compilers. Their current premises and results remain proposition-valued. |
| `WFModel`, `WFTheory` | The freshly checked internally-WF interpretation supplies the reverse comparison with ordinary ZF, including Foundation and Power, using actual Form instances. `WFTheory.c254_refutation_iff_zf`/`native_refutation_iff_zf` close the ordinary two-way comparison. The scoped audit checked all three WF modules, 23 axiom reports and six callers; see `results/wf-model-theory-verification.json`. Choice and internal PA formalization remain separate. |
| `BinaryPerm252` | The closed blank-machine endpoint includes the completed actual-sites certificate and literal/structured program correspondence. It proves the actual machine's nonhalting iff ordinary ZF consistency, with no coverage or startup premise. |
| `ChoiceCalibration254` | The constructible subtype satisfies all sealed ZFC axioms. External completeness transfers ZFC refutations to ZF refutations, closing the actual machine's nonhalting iff Con(ZFC). This does not expose a represented proof-code compiler. |

`Logic/FirstOrder/Lean/FirstOrder/Calculus.lean:33` defines the seventeen-rule
natural-deduction relation in `Prop`. `Completeness.lean:1105` defines
`theory_transfer` by semantic completeness and soundness. Consequently the
current semantic bridges do not expose an algorithm that inspects a proof tree.
This is a representation boundary, not a defect in those theorems.

## Local arithmetic resources worth reusing

All paths in this table are repository paths. The Foundation gitlink is pinned
to `32e1a0956a8622fad067328ca1959729a7634428`; its source directory is unpopulated
in this worktree. The local clients below were read, but their external
dependency closure was not rebuilt or newly audited here.

| Resource | Concrete reusable API and remaining adapter |
| --- | --- |
| `Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/Basic.lean:200` | A `Type`-valued `ProvTree`, its erasure, and `provTree_complete : Prov → Nonempty ProvTree` at line370 give the right pattern for a data-carrying mirror. This one is for PA syntax, not BusyBeaver's Form or C254. |
| `Logic/Interpretability/PAHF/Lean/PAHF/Interpretation.lean:8208,8226` | `TheoryInterpretation` and its composition package syntactic formula translation, axiom discharge and theorem transfer. They still use `Prop` provability, rather than an internally represented proof-code map. |
| `Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/TypedTemplateProofCompiler.lean:47,203,270,280` | `TypedTemplateTranslation`, `compileDerivation`, `compileProof`, and `compileProof_isProof` instantiate a **fixed standard proof template** at typed, possibly nonstandard model-coded formulas. Translation equations for binders, substitution and shifting are explicit. The output's `.val` is accepted by Foundation's represented `Proof` predicate. |
| `Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/PrimitiveRecursiveTruthCertificate.lean:120,170` | `PrimitiveRecursivePackage` and `paRestrictedConsistencyProofSelectorIn_of_primitiveRecursivePackage` illustrate represented `PR.Construction` iteration and correctness in arbitrary arithmetic models. They do not provide the needed BusyBeaver blueprint. |
| `Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/UniformProofPackage.lean:67` | Sigma-one definable existential packages can be iterated by internal induction without a canonical choice function. This is an alternative to demanding a primitive-recursive output selector. |
| `Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/UniformInternalProvability.lean:131,157` | A statement about proof witnesses at **every element of every PA model** is turned into an actual `Peano ⊢ sentence` theorem. Using arithmetic completeness here is legitimate because the obligation is already about represented proofs, including nonstandard codes. |
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/Instances.lean:52` and `ZFDelta1.lean:75,83` | The set language has symbol recognizers, and Foundation's actual ZF/ZFC axiom theories have `Theory.Δ₁`, enabling its represented `Proof`/`Provable` machinery. These are not yet instances for the local `NativeAx`/`ZFax_s` codings. |
| `.../Translation.lean:77,113` and `UniformStatement.lean:142` | `toSet`, `eval_toSet`, and `toNat_toSet_congr` already handle local flat De Bruijn Form, Foundation syntax, and quotation depth. `Translation` explicitly transfers semantic results rather than source derivations; a proof-code/coded-syntax correctness adapter is still needed. |
| `.../SetPlaceholderQuotient.lean:160` and `SetCongruence.lean:1322` | Existing placeholder-language equality/congruence completion and translated congruence proofs can support finite templates with inserted formulas. Equality cannot be silently assumed to respect an arbitrary replacement predicate. |

For the revised **ZFC** metatheory, also inspect
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/CodedDerivation.lean`:
it has ranked set-coded certificates for the same seventeen ND rules, actual
`fDerivesF`, and internal induction rather than circular closure certificates.
`AxiomCode.lean:1054,1063` supplies `IsZFCAxiomCode`/`fZFCAxiomCodeF`.
These offer a set-coded route, but matching the chosen natural-number proof
and machine-trace predicates, and proving the unrestricted translation theorem,
remain work. Its bounded-consistency endpoint is not that theorem.

The bounded-consistency projects do **not** supply unrestricted `Con(ZFC)` or
this machine's internal endpoint. In particular, a family indexed by external
`Nat` is not automatically the corresponding internally quantified sentence.
`ZFCinPA/README.md` also keeps its stronger uniform ZFC-provability target
conditional on its own nonstandard-index obligations; those are not needed
merely to reuse its syntax and proof constructors.

## Finite-proof blueprints in the attributed snapshot

The read-only snapshot is pinned to upstream
`297ab8df7e5de329605c3875b4934643b371a5e3`. Its following interfaces are better
guides for proof transport than a new appeal to semantic completeness:

* `lib/jeff-busy-beaver-zfc254/ZF/m254/coq/settheory/S_qt.v:88,125` proves
  `qt_prv`/`qt_tprv` by induction on the finite natural-deduction derivation;
  atomic membership/equality are replaced by their interpreting formulas.
* `ZF/stdzf_r3/regcon/Rel.v:22,49,102` defines relativization, proves its
  substitution law, and transports derivations with `rel_prv`.
* `ZF/m254/coq/settheory/S_ax.v:239,284,303` supplies the parameterized Sep,
  Repl and combined interpreted-axiom derivations. `S_main.v:23` composes the
  quotient interpretation with a finite source refutation.
* `ZF/m254/coq/logic/Comp_Bundle254.v:128,208,291` gives native CP/GIC
  derivations in the numerical-theorem theory and `SIR_to_thm`.
  `logic/L1_Comp254.v:289` displays the twelve-case command-block compiler.
* `ZF/stdzf_r3/zfc/Z_main.v:38,78,83` gives finite-refutation Choice removal
  by relativizing to L. The last theorem includes Regularity; upstream
  `Std_iface.ZFc` alone omits it. The local logical-equality calculus and
  `Choice_form` still need their actual presentation adapter.

These are object-theory derivability results inside Coq, useful as source for a
Lean proof compiler. They are **not** an exported PA arithmetization theorem,
nor permission to infer one from the upstream end-to-end theorem's closed
global assumptions. No Coq work is proposed here.

## Smallest concrete next checkpoint

The external finite-data checkpoint below is now checked in
`Code254Proof.lean`: unindexed `RawProof`, structural validity/conclusion,
positive Nat quotation, total fuel parser, and `c254_iff_checked`. Its scoped
verification is [recorded separately](results/code254-proof-verification.json).
That finite-data checkpoint alone does not represent the checker; the later
arithmetic history extension below now supplies that representation.

The staged route starts with this finite syntax, rather than arithmetizing model theory:

1. Mirror C254 as finite data, quote it into natural numbers, and implement a
   total Boolean checker for its twelve rules. Record axiom parameters and
   premise indices explicitly; all premise indices must be earlier. Prove
   erasure and `C254 n ↔ ∃ p, checkC254 p n = true`.
2. Make the existing explicit `leaf`, `genBlock`, and `mpBlock` constructors
   consume that data and return command lists. Prove the same contract as
   `Enum254.build`, now with an explicit computed result. This is a useful
   executable checkpoint before any PA theorem, and can be compared directly
   with upstream `L1_Comp254.compile`.
3. Represent that checker, pairing/list operations and compiler in the
   Foundation arithmetic layer, with correctness over **all internal codes**
   in arbitrary PA models. Invalid inputs must be rejected or have a specified
   harmless result. Quotations of ordinary Lean trees alone do not cover this.

For native/ZF proofs, similarly carry axiom tags and the source matrix as
finite data. An axiom node can check literal equality with `sealF(gicForm phi)`,
or with the appropriate Sep/Repl instance. This avoids using an unbounded
search for the matrix hidden in `NativeAx`'s existential definition. The
ordinary equivalence with `BProv` must still be proved. Native equality,
code0/code1 aliases, gate collisions `a=b`, and the freshness inequalities
retain their current exact semantics.

There is a further concrete coding boundary in the convenient semantic
notation: `NamedZF.NForm.atom` (`NamedZF.lean:39`) stores `args : Nat → Nat`.
Arbitrary such functions are not finite syntax. A coded adapter must retain
only the finitely many entries below the embedded formula's variable bound,
or use a finite substitution representation. The existing explicitly given
slot maps can be treated this way; no arbitrary environment function should
be presented as a natural-number code.

The next bridge should be **uniform finite proof templates**, one per axiom
family and logical rule. The semantic results identify which templates to
seek; a finite template may first be found with ordinary completeness or proof
search and then supplied as a literal checked proof. Its matrix substitution
must be represented and proved correct for arbitrary internal formulas. A
chosen proof for each *standard* matrix is not enough. Predicate congruence,
domain guards, freshness and nonemptiness have to appear in this adapter.

The new [finite core compiler](model_coded_core_compiler.md) specializes a
standard proof at an arbitrary internal arithmetic matrix, including its free
parameters, without requiring `S.shift = S`. It compiles Foundation's existing
proof core and discharges the finite translated axiom list with supplied
target proof witnesses. The result satisfies the represented `Proof` predicate.
This removes the free-parameter restriction for fixed templates; represented
translation of arbitrary internal source proofs remains open. The L schema
step still needs syntax-sensitive relativization of the actual set-language
matrix, rather than a generic uninterpreted-predicate substitution.
The [fixed-template graph extension](model_coded_template_graph.md) now
represents substitution into each standard source formula by fixed Σ1/Δ1
graphs, and proves an actual IΣ1/PA sentence asserting provability for every
well-formed internal matrix when a standard lifted-PA source proof is given.
This closes the graph-selection step for fixed templates; it does not yet
represent a translator for arbitrary internal source proof codes.

## Exact eventual endpoint

Fix Boolean checkers for closed proofs and finite machine traces. Let
`PrfT(p)` abbreviate the arithmetic formula saying that `p` is an accepted
T-proof of Bottom, and `HaltTrace252(t)` the actual canonical table's accepting
blank trace. The intended arithmetic obligations are:

```text
PA ⊢ ∀t (HaltTrace252(t) → ∃p PrfZFC(p))
PA ⊢ ∀p (PrfZFC(p) → ∃t HaltTrace252(t))
```

Negating gives the desired PA-provable nonhalting/consistency equivalence.
An adequate modular interface is the analogous pair of proof-translation
sentences for C254/Native, Native/ZF, and ZFC/ZF, plus C254/actual-machine
traces. The reverse ZFC/ZF direction must represent the now externally checked
Choice comparison;
Foundation is addressed by the internally-WF route rather than a false claim
that raw IR descends to the bisimulation quotient.

Primitive-recursive total translators are a sufficient implementation choice,
not a necessary requirement. It is enough to prove in PA that each accepted
source refutation has some accepted target refutation. A proof-search function
can be partial away from valid inputs. External termination on valid standard
inputs, however, supplies no PA totality/correctness proof by itself.

For the binary side, use a finite coded zipper/trace predicate and prove its
equivalence with the actual Core blank-run semantics. Register and tape
simulations then need internally total finite-trace construction and the
positive-progress arguments already exposed in the runtime interfaces. A
finite bootstrap computation or certificate can supply checked constants;
the generic executor/checker soundness and unbounded trace composition still
need their arithmetic proofs.

`Classical.choice`, quotient types and completeness in an ordinary Lean proof
neither invalidate the result nor establish its strength over PA. A fixed
chosen finite proof can become a checked numeral. Uniform selections,
structural recursion on proofs and quantified code correctness require the
additional interfaces above. Conversely, proving the represented endpoint in
every PA model and applying **arithmetic** completeness, as the local arithmetic
projects do, is a valid way to obtain the actual PA proof without claiming a
primitive-recursive extractor for the original semantic Lean proof.

The next finite-data checkpoint is also checked: `Code254ProofCompiler`
structurally maps every valid raw proof into the existing `Enum254` command
blocks and proves their exact result contract. Its explicit refutation word
halts from any working state; the existing fair scheduler yields the external
enumerator-halting corollary. See [the compiler note](code254_proof_compiler.md).
This removes proof-existence extraction from the compiler function itself;
the subsequent arithmetic word history and correctness modules now represent
that computation and establish its contract in every IΣ1 model. The internal
scheduler and proof-system comparisons remain open.

The [numeric command-word adapter](command_word254.md) now supplies a total
shifted encoding of the actual command lists, exact tail replacement, and
numeric concatenation with all-input list agreement. Empty word0 is distinct
from the actual raw candidate0 (`MP0`). This provides the finite-data operations
for a compiled-word history; it does not itself represent that
history or prove the compiler's internal execution contract. Invalid proof
code0 must remain separate from either command-code convention.
The subsequent [bounded command-tail graphs](arithmetic_command_word254.md)
now represent the raw tail and replacement functions in every IOpen model,
with all-natural identification. The subsequent
[represented concatenation](arithmetic_command_append254.md) now proves its
exact recurrence at every internal index, all-Nat word agreement and actual
PA unique totality. The [compiler-block circuits](arithmetic_command_blocks254.md)
now represent all actual leaf, MP and GEN blocks using those operations,
with symbolic equality to the existing command-list encoding on natural
inputs. Their syntax and repetition counts are fixed external data; their
numeric operands may be internal model elements.
The [internal word laws](arithmetic_command_word_laws254.md)
now prove exact replacement, right identity and associativity, without
assuming an external finite-list interpretation of internal codes.

The simpler compiler design keeps an unconditional history of raw compiled
words and uses the already checked `ArithmeticHistory254.value` once as the
public validity gate. Invalid public inputs return empty word 0. This avoids
duplicating the twelve-rule validator in a paired history. For an accepted
parent, the validator's internal recurrence must imply acceptance of the
actual MP/GEN children; only then may their raw words be used with the
validity-conditional execution induction. The
[internal history recurrence](arithmetic_history_recurrence254.md) now proves
this MP/GEN validity inversion, including the actual child bounds and
whole-tail GEN convention. The [word-history extension](arithmetic_proof_word254.md)
now implements the unconditional row/history and final validator gate, with
exact internal recurrence and PA-provable unique totality. The
[quotation adapter](arithmetic_proof_word_adapters254.md) now proves agreement
with the structural compiler on every ordinary finite quoted proof tree,
including invalid trees. The accompanying all-internal nonemptiness theorem
identifies empty public output exactly with rejection by the original
validator. The later [correctness theorem](arithmetic_proof_word_correct254.md)
now proves its accepted-proof execution contract.

The [command-step graph](arithmetic_command_step254.md) now represents the
exact MP, DROP, NIP and AX effects on every internal IOpen input, agrees with
the actual `Enum254.cstep` on all ordinary inputs, and is invariant under
rest-pointer replacement. Success is encoded as working-state code plus one;
zero is reserved for a halting NIP. These facts supply the local command
semantics needed for internal word execution and composition.
The [internal iterator](arithmetic_command_run254.md) now has exact
zero/successor and semigroup laws at every internal time. A pointwise Σ1
induction proves that every shifted word halts or completes by the numerical
bound given by its own code, with no bound on changing working registers.
PA proves the resulting evaluator's unique totality. The
[execution adapters](arithmetic_command_execution254.md) now identify it with
the actual natural executor and prove successor/append execution at every
internal input. The [Π1 contract interface](arithmetic_proof_word_contract254.md)
uses the total Δ1 functions to retain universal top/stack quantifiers inside
a Π1 induction hypothesis. Thus the MP major can use its changed saved stack
without a register-growth bound. The [fixed block contracts](arithmetic_command_block_execution254.md)
and [correctness theorem](arithmetic_proof_word_correct254.md) now discharge
the exact twelve-case successor premise using the actual validator recurrence.
The [represented refutation word](arithmetic_refutation_word254.md) then
resets arbitrary working registers and halts whenever the validator accepts
falsity. This closes the compiler-to-word direction in every IΣ1 model.
The scheduler comparison below is now checked; binary traces and internal
C254/ZFC proof transformations remain to be connected.

The [arithmetic scheduler step](arithmetic_enumerator_step254.md) now covers
every internal six-register configuration and has an exact ordinary-Nat
`Enum254.enumStep` adapter. Its [internal iterator](arithmetic_enumerator_run254.md)
uses a Σ1 invariant retaining an earlier stopped-word witness, since a
completed word and a scheduler boundary have different next steps. It proves
internal fairness and schedules every positive word halting from all working
states. The raw candidate for shifted word `w` is `w-1`. This supplies the
forward scheduling argument. Complete binary transport and the internal
ZFC proof comparison remain separate.
The subsequent [composition theorem](arithmetic_enumerator_refutation254.md)
now states this forward direction as one fixed arithmetic sentence and proves
its IΣ1 and PA derivability. Its hypothesis is the actual represented C254
validator returning 2; its conclusion uses the actual start and run graphs.
It does not yet translate a ZFC proof code or a binary machine trace.
The [ordinary-Nat adapter](arithmetic_enumerator_run_nat254.md) separately
proves exact equality with the existing native scheduler at every ordinary
time and state, including its blank-halting predicate. This identifies the
standard interpretation of the run graph while keeping the all-internal
proof obligations explicit.
For the reverse direction, the [bounded-stack plan](arithmetic_enumerator_soundness_plan254.md)
keeps one existential bound on proof witnesses for the current stack and
registers. This gives the checked Σ1 time invariant. The required
[actual proof-constructor equations](arithmetic_proof_constructors254.md)
are now checked. The subsequent
[tail-drain](arithmetic_stack_tail254.md) and
[certificate](arithmetic_stack_certificate254.md) modules now close the
stack representation and local push/pop obligations.
[Command preservation](arithmetic_command_preservation254.md) and Σ1 time
induction now supply the reverse implication from every certified start.
The [fixed equivalence theorem](arithmetic_enumerator_equivalence254.md)
proves in IΣ1 and PA that the actual validator accepts a falsity code iff
the actual arithmetic scheduler halts from scalar1. The proof establishes
that scalar1 is precisely `liveValue 0 0 0`. All quantified codes and times
are internal model elements. This completes the numerical validator/scheduler
comparison, with binary execution and internal C254/ZFC proof transformations
still open.
The [internal positive-clock transport](arithmetic_positive_simulation254.md)
now handles the final conditional trace-composition argument by Σ1 induction.
It needs only positive local clock increments, not a global upper clock
bound. The actual binary run and simulation relation must still satisfy
its explicit local premises in every IΣ1 model.
The [arbitrary-initial binary run](arithmetic_machine_run_from_perm252.md)
now supplies the concrete run's addition and halt-persistence laws, and the
[fixed bootstrap lift](arithmetic_bootstrap_perm252.md) proves the exact
82,552-step endpoint in every IΣ1 model and in PA. Unbounded instruction
simulation and its arithmetic frame relation remain open.

For proof-system transport, [internal axiom-proof substitution](internal_axiom_proof_transport.md)
now composes existential target proofs through arbitrary internal source
derivations in a shared language. It uses Σ1 induction and needs no selected
proof compiler. Its explicit hypothesis is target provability of every
well-formed internal source axiom. This implements a weaker sufficient
interface already permitted by this plan; it does not supply the missing
C254/Foundation syntax map or the WF/L axiom translations. The accompanying
note identifies represented closed-matrix Separation/Replacement constructors
as a concrete next client, while preserving the additional free-parameter
closure obligation.

The [numeric history-checker construction](code254_arithmetic_checker.md)
specifies a concrete next adapter: represent the exact Cantor pairing and its
bounded projections, then use the existing arithmetic history iterator to
evaluate all twelve proof rules. The pinned arithmetic library uses a different
pairing for its own data, so that adapter cannot be omitted. The note gives the
exact MP and gate tests, the fixed formula interface and all-input equivalence
target. The plan is now implemented by the arithmetic history extension below,
including an actual PA theorem of unique Boolean evaluation.

## Intake156 proof-coding continuations

The [three new reports](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md#batch156-sparse-certificates-reset-synchronization-and-the-zfc-comparison)
separate three useful specifications. Source47 reconstructs an ordinary
set-coded ZFC proof for the existing machine. Source48 supplies explicit sparse
acceptance/rejection arithmetic graphs with bounded certificate-size arguments.
Source49 specifies HOD descriptions, the exact selector Choice adapter and an
internal-natural decoder covering every recognized formula tree, including
nonstandard codes. The HOD construction is classical and attributed; the
project-specific all-code adapters remain to be implemented. Its PA transport
requires an actual primitive-recursive proof compiler and verified axiom-proof
generators, not merely external semantic equivalence. None of these reports
closes the requested internal PA theorem.


The subsequent [ArithmeticCantor adapter](arithmetic_cantor.md) now supplies the
literal Cantor polynomial graph, bounded inverse graphs and all-natural
identification with `Code254.P`/`Cantor.ofNat`, in arbitrary IOpen models.
Its semantic representation uses weaker arithmetic than full PA. The history
extension below now represents the checker; finite proof/trace translation
remains open. This local definability theorem is not the whole-machine PA proof.

The [constructor extension](arithmetic_code254.md) now supplies fixed bounded
graphs for the four live numerical constructors and the rho1 payload branch.
It proves parameter-free formula correctness in arbitrary IOpen models and
exact all-natural implementation agreement. Output bounds justify those
constructor witnesses; they do not by themselves bound the intermediate values
of a rejected MP row with output0. The later row extension below handles that case.

The subsequent [fixed-template graphs](arithmetic_templates254.md) cover the
remaining rho2–8 and exact C/G/full-bundle expressions. Their generic circuit
compiler yields a fixed parameter-free graph for each finite template, with
all-natural equality to the live functions. This completes the positive
template library. The subsequent [complete row graph](arithmetic_row254.md)
adds both gates, exact rejected-row behavior and every invalid tag, with bounded
witnesses justified separately for failed and successful branches. It agrees
with `Code254History.row` on every natural input, using explicit child-result
values, and its fixed graph works in every IOpen model. The four-module chain
passes 114 axiom probes and 120 callers.

The [represented history checker](arithmetic_history254.md) completes the
selector, actual child lookups and history iteration. Its fixed Σ1/Δ1 graphs
are total at all internal codes in every IΣ1 model. `history_lookup_nat` covers
every lookup index, including out-of-range zero, and `checkDef_nat` identifies
the fixed formula with the actual `Code254Proof.check` for every natural input.
The fixed `totalitySentence` also has actual IΣ1 and PA derivations. This closes
checker representation and totality; internally coded proof and machine-trace
translations remain open.

The [numeric binary-machine adapter](arithmetic_machine_perm252.md) now gives
an exact two-natural tape simulation of the frozen 252-state table. Its
`numericRun_sound` theorem constrains the entire actual tape and head at every
natural time; state zero is equivalent to actual halting, with the final write
and move retained. This Std-only checkpoint closes the ordinary finite-data
machine adapter. The subsequent
[arithmetic machine extension](arithmetic_machine252.md) now supplies the
fixed bounded action/step graphs and fixed Σ1/Δ1 run graphs, with unique
evaluation at every time in every IΣ1 model. Its all-Nat bridge identifies a
closed Σ1 halting sentence with the actual Core blank-run endpoint. IΣ1 and PA
prove unique totality of the evaluator. What remains is the internally coded
proof/command/trace transport between this sentence, the represented C254
checker, and ZFC refutations; the run representation alone does not prove it.

Intake157's [canonical term certificates](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md#batch157-canonical-term-certificates-for-the-full-calculus)
provide ordinary exact checker reductions and constructor-only derivations.
Their small-witness and forward-equation arguments can guide internal sequence
predicates, but those predicates and their all-code proof are not delivered.
The manuscript follows the later goal record when calling PA stronger than
requested; the original user request explicitly requires PA, and remains the
target here. Avoiding arithmetic inside a future verifier does not remove the
arithmetic proof obligation relating its finite traces to Con(ZFC).

## Claude lane: represented relativization (L-interpretation core)

The ZFC-refutation → ZF-refutation direction (Choice) and the WF comparison
both need a *syntax-sensitive* interpretation in arithmetic. Its generic core
is now **checked** (standard axioms only), in
`Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/InternalRelativization.lean`
(any language) and `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/SetRelativization.lean`
(the set language), with `…Audit` modules:

1. `relativize L d p`: relativization of every internal formula code to the
   class defined by an internal domain formula `d` with one bound variable
   (one `UformulaRec1` construction: atoms unchanged, `∀q ↦ ∀(¬δ ∨ q^δ)`,
   `∃q ↦ ∃(δ ∧ q^δ)`), with Σ₁ graph and constructor equations.
2. Formula laws: preservation of (semi)formulas; commutation with negation,
   with shift (for shift-fixed `d`), and with substitution of terms for bound
   variables (`subst_eq_self_of_prefix` generalizes Foundation's
   `subst_eq_self` to longer vectors).
3. `derivable_relSet`: every internal T-derivation of a sequent `s` (in every
   IΣ₁ model, nonstandard derivations included) yields a U-derivation of
   `s^δ ∪ {¬δ(&i) | i < m}` for some `m`, by one `Derivation.induction1` pass
   with a Σ₁ predicate. Hypotheses: U derives the relativized T-axioms (with
   side formulas), and closed terms are variables.
4. `derivable_of_domSet`, `provable_relativize`, `provable_falsum_of_relativize`:
   the side formulas are discharged from `U ⊢ ∃x δ(x)` (∀-rule on `¬δ(&0)`,
   cut against `∃x δ(x)`, internal induction on `m`), so
   `Prov_T(⊥) → Prov_U(⊥)` holds in every IΣ₁ model.
5. `SetRelativization.isTerm_eq_fvar`: in the set language every closed
   internal term is a free variable (its function-symbol recognizer is `⊥`),
   and `provable_falsum_of_relativize_set` packages item 4 for set theories.

6. `ZFCinPA/ConstructibleInterpretation.lean`: the L-specific obligations
   with `T = 𝗭𝗙𝗖`, `U = 𝗭𝗙`, `d = ⌜x ∈ L⌝`, except the schemata.
   * `inLSyn`/`domL`: one model-independent formula for `x ∈ L` (the
     repository's `Constructible.inLF` with its operation bundle unfolded;
     `inLSyn_eq` is `rfl`), translated to a Foundation semisentence with
     `eval_domL` in every model of `𝗭𝗙`.
   * `relF`: external relativization, clause for clause the internal one;
     `eval_relF` evaluates it in the carved-out substructure, and
     `quote_relF`/`quote_relF_sentence` prove `⌜σ^L⌝ = relativize ⌜δ⌝ ⌜σ⌝`.
   * `L_models`: the constructible class of a Foundation model of `𝗭𝗙`
     satisfies the equality axioms, the seven fixed axioms and `𝗔𝗖` (Gödel,
     via `BusyBeaver.ZFC.ConstructibleZF`/`ConstructibleOrder`, with the
     bundle extracted by `zfAxioms_of_modelsZF`). Completeness gives
     `𝗭𝗙 ⊢ σ^L` (`zf_proves_relL`) and `𝗭𝗙 ⊢ ∃x (x ∈ L)`.
   * `mem_ZFC_class` splits the internal `𝗭𝗙𝗖` axiom class into its five
     `Δ₁` parts; codes in the three finite parts are standard numerals
     (`standard_of_mem_class`), so `standard_obligation` discharges them by
     D1 with no side formulas.
   * `provable_falsum_ZF_of_ZFC`: in every model of `IΣ₁`,
     `Prov_ZFC(⊥) → Prov_ZF(⊥)`, **assuming** `hSchema`: every internal
     separation or replacement axiom code `p` has an internal
     `𝗭𝗙`-derivation of `p^L` with side formulas.

**Remaining for the Choice transport in PA** (this lane, next): `hSchema`.
An internal schema code is `∀^m (Fval K)` for an internal (possibly
nonstandard) core `K` (`SchemaClosure.SchemaRecognizer`), so no finite
template set covers it: `L ⊨ Sep_K` is *not* a theorem of `ZF(P)` for an
arbitrary predicate `P`, and needs an argument by internal induction on `K`.

### Design of the `hSchema` generator (Claude lane)

The invariant avoids relativization to `L_β`, diagonal intersections and
parameter guards by putting ZF's *own* satisfaction relation for set-sized
structures (`InternalSatTotality.SatIn`, whose Tarski clauses
`satIn_memAtom` … `satIn_ex` hold semantically in every model of ZF for every
code) into the induction, and by reading every variable from one assignment
`s : ω → L_β` (`applyV`, `econs`), so that internal formulas with
nonstandardly many free variables never need a nonstandard quantifier block.

* `K⟦s⟧_d`: a represented transform (one `UformulaRec1` construction with the
  depth `d` as its changing parameter) replacing bound `#k` by `s(k)` and free
  `&i` by `s(d+i)`, each quantifier becoming a quantifier over `econs y s`;
  atoms read entries through ZF numerals (Codex's numeral code builders).
  **Checked** as `ZFCinPA/EnvTransform.lean` (`envForm d K`, its equations,
  and `isSemiformula_envForm`: the output has bound-variable arity at most
  one). The typing theorem alone does not assert absence of free variables;
  `LGlue2.shift_envForm` now supplies shift-fixity for every internal code.
  `LGlueCodes.envForm_free` separately identifies opening with a depth change.
* Reflecting stages are the limit **closure points of a function** `f_K`
  (a placeholder-definable graph, existentially supplied by the induction):
  successor for atoms, `max(f₁, f₂)` for `⋏`/`⋎` (closure points of the
  max are closure points of both, so no club intersection or iteration is
  needed), and `max(f', g_{P'})` for `∃`/`∀`, where `g_{P'}(α)` bounds the
  `L`-ranks of witnesses for environments on `L_α` (the planned Collection
  template). The current invariant quantifies over **environments on an
  earlier stage** `L_α`, with `α ∈ β`. Extending such an environment by one
  element of `L_β` keeps it on a common earlier stage. The source no longer
  requires finite support or a locality argument.
* **Invariant** `Θ(K, d)`: `ZF ⊢ Total(f) ∧ ∃c ∈ Fml. ∀β (β limit closure
  point of f) ∀α ∈ β, ∀ env s on L_α:
  envForm d K (s) ↔ SatIn(L_β, c, s)`, by semiformula induction with the depth
  as parameter (exactly the shape of the construction, so `free` never
  appears).
* Templates use the **full** Separation/Replacement schemata over the
  enlarged language (Codex's `separationProof`/`replacementProof` are generic
  in the matrix) and `congruenceProof₁/₂` for the placeholders, so the
  semantic proofs may use any instance they need. ω-iteration is needed only
  once, in the final templates: a generic "limit closure points are
  unbounded" lemma.
* The only `free`-based induction is the final **glue** (`envForm` versus
  Foundation's `relativize` on the schema core), done by induction on formula
  rank in models of PA (the endpoint's arithmetic).
* Each inductive step is **one fixed template** over `ℒₛₑₜ` with placeholders
  for the component predicates (`P'`, `f'`, numerals), proved semantically
  from `SatIn`'s Tarski clauses and the constructible hierarchy of
  `BusyBeaver.ZFC` in every template structure, and compiled at the internal
  components by Codex's `OpenSetTemplateCompiler.compileOpenTemplate` (the
  `CollectionTemplate254`/`CompiledCollection254` pattern). The internal
  induction on `K` then only chains `Derivable` facts.
* **Final templates**: `Sep^L(P)` from `Θ` (choose a limit closure point `β` of `f_K` above `a` and
  the parameters: the separated set is `{x ∈ a | SatIn(L_β, c, x::s)}`,
  definable over `L_β`, hence in `L_{β+1}`); `Repl^L(P)` from `Sep^L` and the
  `P`-independent `Coll^L` template.
* **Glue**: the assignment `s` with `s(i) = &i` (`i < m`) exists in ZF, and
  `K⟦s⟧ ↔ K` under it (two small generators by internal induction on `m` and
  on `K`); `relativize` commutes with the `∀^m` closure of `SchemaRecognizer`.

**Progress (checked, standard axioms only).** The template toolkit
(`LTemplate`: template theory with the full enlarged schemata, a universal
axiom callback, `compileT`; `LPieces`; `LTransVal`: translated codes are `Σ₁`
in the placeholder codes) and **every inductive step** are theorems of the
template theory, over one six-placeholder language with the common conclusion
`totS F₅ ⋏ reflS P₄ F₅`: `LStepAnd` (`⋏`), `LStepBasic` (`⋎`, negated atoms,
`⊤`, `⊥`), `LStepAtom` (membership and equality atoms read through numeral
placeholders), `LStepEx`/`LStepExT` (`∃`, `∀`, with the witness-bounding
function obtained from Replacement and Separation in every template model).
Two design refinements were forced on the way: `reflS` quantifies over
environments on *earlier stages* (no finiteness argument is needed anywhere),
and `EnvTransform`'s fixed pieces are embeddings of closed semisentences, so
each template's definitional hypotheses translate to literal tautologies.

**Final templates (checked).** `LIterate`/`LClosure` prove, in every template
model, that limits closed under a total `F₅` are unbounded (ω-iteration with
every Separation/Replacement use discharged by `sep_iff`/`repl_iff`).
`LFinalSep.sepTemplate_provable` and `LFinalRepl.replTemplate_provable` turn
the invariant `totS F₅ ⋏ reflS P₄ F₅` into `L`-separation for `P₄` at
`z :: t` and `L`-replacement for `P₄` at `x :: y :: t` (the slot orders of
the schema matrices `φ z` and `ψ x y`), for every environment `t` over a
stage. Replacement needs no code-level shift: the image is bounded in a
stage, and the domain `X` is stored at a slot `n` beyond a support bound of
the reflecting code (`SatSupport.sat_support`) by patching the environment.

**Driver (checked).** `LDriver.driver`: for every internal semiformula code
`p` of level `n` (nonstandard included), some function code `f` makes
`𝗭𝗙 ⊢ totS f ⋏ reflS (envForm n p) f`. The induction is Foundation's
`IsSemiformula.sigma1_structural_induction`, whose binder level is exactly
`envForm`'s depth; each case is one compiled step (`LDriverSteps`) whose new
function code is the translation of the template's own defining matrix, so
every definitional hypothesis is the internal tautology `∀(A ↔ A)`. Atoms
use `LNumOK.numOK` (every numeral chain defines one natural, in `𝗭𝗙`).

**Remaining for `hSchema`** (superseding the historical next-step notes below):
the reflection driver producing `Θ` is already available. `LGlue1` provides
matching functionality and slot reading; `LGlue2` supplies shift-fixity and the
opened quantifier-premise identity; `LGlue3` supplies the atomic compiled-glue
client. The merged `LGlue4` now supplies the remaining connective/quantifier
clients and internal formula induction, as source-reviewed above. `LFvBound`
adds the recognizer-derived core free-variable bounds, also source-reviewed.
`LPeel` supplies the internal universal-closure induction and zero-match
discharge; constructing a matching environment for an arbitrary internal
tuple is no longer a separate prerequisite on this route. The remaining
work is to combine the final Separation/Replacement templates with the
driver and glue to prove the exact opened-body `pVal` premises, including
Replacement's depth-two core adapter. Then identify each recognized axiom
with `qqAlls b m`, establish the required formula typing, and convert the
resulting internal ZF proof to the `Derivable`/`domSet` conclusion required
by `hSchema`. Empty domain side formulas suffice once that exact proof is
obtained. These source-reviewed additions still require focused compilation
and axiom/caller audits.

Feeding `hSchema` into `ConstructibleInterpretation.provable_falsum_ZF_of_ZFC`
and the result into the C254/ZF comparison then gives the Choice half of the
PA endpoint.

The merged `efa3142e2d` supplies those quantifier resources:
`LStepExT.wb_tot` obtains a total witness bound by Replacement over a set
containing all environments on the earlier stage, then uses Separation and
regularity to select the least bound. `exTemplate_provable` and
`allTemplate_provable` consume it in the fixed template theory. This source
review covers the 429-line module and its six-probe audit; it does not claim
a new local compiler run of the upstream modules. The represented compiler
clients, the internal induction producing `Θ`, and the final schema/glue
arguments remain open. The atomic clients must also discharge their
`numOK` premises in ZF. These templates do not yet discharge `hSchema`.

`LIterate.orbit_closure` constructs a nonzero limit closure point by taking
the union of an ordinal orbit. The merged `3c6917845f` adds
`LClosure.closure_point`, which constructs its image set, two Separation
resources and orbit set from concrete enlarged-language formulas in every
template model. The image and orbit relations are totalized outside the
ordinals and naturals respectively to meet the Replacement interface.
This supplies the semantic closure-point resource; final schema templates
and their internal compiler/induction clients remain separate. The review
of these upstream sources does not claim a local compiler rerun.

The merged `4be44bc3fe` adds `LFinalSep.sepTemplate_provable`: totality and
reflection for a placeholder predicate imply its Separation instance in L,
at extended environments. A concrete satisfaction formula supplies the
definable subset of a closed stage. The final Replacement template and the
internal instantiation/induction driver are still needed before `hSchema`
is discharged. This update records source review, without a local rerun.
