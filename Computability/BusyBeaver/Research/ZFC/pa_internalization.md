# Internalizing the machine comparison in arithmetic

Research inventory begun 16 October 2026 against
`7b1e56dbc59f746695a7fb375546422f91de3a96`, updated with the explicitly linked
Lean checks below. The PA equivalence for the exact 240-state binary machine
remains open. Upstream commit `e1ff9636d5` now supplies the complete arithmetic
[validator comparison](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorConsistencyEquivalence.lean):
IΣ₂, hence PA, proves `Con(ZF) ↔ validatorConsistencySentence`
and `Con(ZFC) ↔ validatorConsistencySentence`, where the fixed sentence says
that no internal code has `ArithmeticHistory254.value = 2`. The represented
checker and machine-run evaluator already have PA totality theorems.

This update records source review of the upstream R2/R3 composition. Its commit
reports a successful facade build and a 15-probe standard-axiom audit; this
review did not locate a dedicated fresh R2/equivalence verification record in
the maintained results and did not run Lean. Existing linked forward-validator
records retain their separate actual-check status.
The [source review](results/upstream-r2-review.json) and
[preserved review history](results/upstream-r2-review-history.json.gz) record
the scope and the available evidence.

A subsequent [fresh R2 context check](../../../../Logic/Interpretability/ZFCinPA/r2ctx.md)
passes six probes and ten callers on the unchanged upstream source, with one
unused-variable warning. Replaying the remaining R2 composition is separate.

The request and active goal require an equivalence provable in **PA**.
A Lean theorem comparing halting and `BProv` is an ordinary metatheorem until
the intended arithmetic sentence and an object-theory proof are connected to
it. Completing the PA version would also serve the ZFC requirement, after
checking the chosen arithmetic interpretation in ZFC.

The [exact 240-state endpoint](rotation240_binary.md) is now the closed
external Lean baseline: blank nonhalting iff the specified ZFC proof calculus
is consistent. The [compensated244](compensated244_binary.md) and
[245-state](routing245_binary.md) endpoints remain earlier baselines. The
[rotated source calibration](calibrated_rotation240.md) reuses the
[Choice calibration](choice_calibration254.md), including Choice in L and
external first-order completeness. This closes the external consistency
comparison for the literal 240-state machine. It does not supply the PA proof
connecting that machine's arithmetic run graph to validator consistency.
The arithmetic work and its current status are recorded below.

The [exact 240-state arithmetic run](arithmetic_machine_run_rotation240.md)
now has a fresh Lean check (14 probes, 16 typed callers, zero warnings). Its
fixed Σ₁/Δ₁ graph is total at every internal IΣ₁ time; its ordinary-natural
interpretation agrees with the literal machine run at every time. IΣ₁ and PA
prove its closed totality sentence. The parameter-free Σ₁ halting sentence
therefore has the intended standard interpretation, while the internal
simulation and consistency equivalence remain to be connected.
The [arbitrary-initial run](arithmetic_machine_run_from_rotation240.md) also
passes a fresh 19-probe/23-caller check with zero warnings, supplying internal
run composition, full halted-code absorption and recovery of that blank graph.
The [finite arithmetic startup](arithmetic_bootstrap_rotation240.md) passes
seven further probes and nine callers with zero warnings. Its fixed sentence,
provable in IΣ₁ and PA, gives the complete boot code after 409,691 steps.
The [startup-removal theorem](arithmetic_startup_rotation240.md) passes 12 probes
and 14 callers with zero warnings. IΣ₁ and PA prove the equivalence of the fixed
blank- and seed-halting sentences. Its general shift theorem covers arbitrary
internal offsets and configurations, including prefixes that extend past a
halt. The unbounded internal binary-to-register simulation remains open.
The [actual 240-state scan layer](arithmetic_scans_rotation240.md) now passes
13 probes and 15 callers with zero warnings. It supplies bidirectional writing
and unchanged scans over arbitrary internal lengths, plus exact single-row
effects. The register-box and dispatch-frame composition remains to be proved.
The [internal one-valued spare codec](arithmetic_one_blocks_rotation240.md)
passes nine probes and eleven callers with zero warnings. It supplies total
Σ₁/Δ₁ repetition, concatenation and append laws for `011`, matching the proposed
167-plus-increments spare invariant. Machine preservation of that invariant
is a remaining register-box obligation.

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
  internal Separation/Replacement hypothesis `hSchema` is discharged
  (`LSchema.hSchema`, 2026-10-17), so the Choice transport is unconditional:
  `𝗜𝚺₁ ⊢ Con(ZF) → Con(ZFC)` and `𝗣𝗔 ⊢ Con(ZF) → Con(ZFC)`
  (`LSchema.iSigma1_proves_con_ZF_imp_con_ZFC`,
  `LSchema.peano_proves_con_ZF_imp_con_ZFC`; axioms `propext`,
  `Classical.choice`, `Quot.sound` only). With the internal inclusion of
  `𝗭𝗙`'s axiom class in `𝗭𝗙𝗖`'s, the ZFC/ZF pair is two-way:
  `𝗣𝗔 ⊢ Con(ZF) ↔ Con(ZFC)` (`LSchema.peano_proves_con_ZF_iff_con_ZFC`).
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
  The upstream `R2Main`/`R2Native` source now completes internal source-proof
  translation with this configurable encoder, whose falsity code is `1`.
  It uses Π₂ induction in IΣ₂ and discharges the native-axiom callback; no
  comparison with the earlier fixed encoder is required. Arbitrary accepted
  proofs are not assumed closed under variable renaming.
  [Native GIC matrix slots](../../../../Logic/Interpretability/ZFCinPA/validator_native_gic_slots254.md)
  now identify both internal substitution orders and derive padded-matrix
  vacancy from odd labels under IΣ₂. The literal padded GIC instance passed
  eight probes and ten typed callers with zero warnings. Upstream `R2Gic` and
  `R2Ax` now supply the complete encoded native body and arbitrary internal
  universal closure. These arithmetic results concern the numerical validator;
  their connection to the exact 240-state binary machine remains separate.
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
  [GEN constructor](arithmetic_control_gen254.md) now reaches control 122 from
  93; composed with both pushes, it reaches 122 from 41 with
  TW=`wal oldP1 oldCache` and WS=`cantor oldTW oldWS`. The separate
  [cache read](arithmetic_control_ax_read_cache254.md) reaches 136 from 122,
  adding `first oldPL` to cache and replacing PL with `second oldPL`.
  Both fragments require initially zero scratch registers and preserve every
  other field, with positive internal runtimes. Their audits pass 16 probes
  and 24 typed callers with zero warnings. Their
  [41→136 composition](arithmetic_control_ax_gen_read254.md) also passes nine
  probes and eleven callers, preserving the original cache inside the GEN
  result while updating cache and PL afterward. The remaining AX bundle is
  still open.
  Later checked contracts extend this frontier: the
  [third implication composition](arithmetic_control_ax_third_imp254.md)
  reaches control 354 from 41. The subsequent
  [cache push](arithmetic_control_ax_next_cache_push254.md),
  [AC push](arithmetic_control_ax_next_ac_push254.md), and constructors at
  [406](arithmetic_control_ax_next_constructor254.md),
  [433](arithmetic_control_ax_constructor433254.md) and
  [460](arithmetic_control_ax_constructor460254.md) reach 487 in successive
  whole-file contracts. These six existing units passed 28 probes and 38
  callers with zero warnings. Their combined 41→487 contract and the
  subsequent AX operations still require their own checks.

The remaining major steps are the complete interpreter-to-Enum connection
and the unbounded internal register/binary simulation for the exact 240-state
machine. The upstream R2/R3 source closes the reverse internal ZF-to-validator
translation in IΣ₂, and the internal L-schema theorem supplies Choice transport.
The validator biconditionals do not by themselves identify the literal binary
run with the arithmetic scheduler.

The active arithmetic target remains the [rotation240 machine](candidate-rotation240/README.md).
Its [external binary endpoint](rotation240_binary.md) now passes nine probes
and nine typed callers with zero warnings. It composes the
[complete decoder coverage](rotation240_coverage_complete.md),
[runtime contracts](rotation240_runtime.md), [409,691-step blank bootstrap](rotation240_bootstrap.md),
[full startup frame](rotation240_tree_frame.md), and
[source consistency calibration](calibrated_rotation240.md). This closes the
external Lean endpoint for the exact table; the internal register/binary
simulation and PA composition remain separate. Earlier compensated244,
combined243 and rotation244 results are retained as provenance.
The [exact 240-state arithmetic lookup](arithmetic_machine_graph_rotation240.md)
now passes eight probes and eight typed callers, defining all 480 actions in
every IOpen model. The [240-state arithmetic step](arithmetic_machine_step_rotation240.md)
also passes seven probes and ten callers, identifying its action on every
natural configuration code. The iteration and arithmetic startup results below
still concern the earlier 246-state machine. Specializing those results and
proving the all-internal comparison remain obligations.
The [fixed arithmetic lookup for the 246-state table](arithmetic_machine_graph_prefix246.md)
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
closes the arithmetic scheduler's seed adjustment. Its identification with
the actual register interpreter and the active exact240 binary run remains
open; the upstream R2/R3 source now supplies the separate reverse validator
comparison.

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
remains an explicit premise. At that stage, the exact schema/template
combinations, Replacement's depth-two opening adapter and final
recognizer/domain-side integration remained. The
[pinned review](results/upstream-014b961872-source-review.json)
records source inspection only: no fresh compilation or executed axiom audit
is claimed, and the existing `LGlueAudit` does not probe `LPeel`.

Commit `dd85eb4a47` adds
[LSepBase](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LSepBase.lean).
Its `sep_base` combines the final Separation template with the reflection
driver and glue, obtaining the exact opened-body `pVal` proof. Then
`sep_obligation` takes only `SepR p` and produces an internal
`Provable ZF (rel p)` in every IΣ₁ model. The recognized code `p`, closure
length `m`, matrix `b`, and core `K` are internal model elements. The proof
derives the core free-variable bound from the recognizer and uses `peel`
and `peel_close` for the arbitrary internal closure length. No matching
environment existence or `hSchema` premise remains on this Separation route.
At that stage, Replacement's level-two base/glue combination and the final
membership/`Derivable`/`domSet` adapter remained. The
[pinned review](results/upstream-dd85eb4a47-source-review.json) records source
inspection only. The new `LSchemaAudit` lists 11 axiom probes, including
`sep_obligation`, but supplies no typed callers; no fresh compilation or
executed audit is claimed by this integration.

Commit `11b8f3efb6`, merged through `de330b4037`, adds
[LReplBase](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LReplBase.lean)
and [LSchema](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LSchema.lean).
The level-two glue reads the core at `x :: y :: t`; the compiled Replacement
template and existing peel close every internally recognized `RepR` code.
`LSchema.hSchema` combines both schemata, identifies their internal axiom
classes with their recognizers, and takes the domain-side length to be zero.
Consequently the internal refutation transfer has no schema premise. Arithmetic
completeness yields `IΣ₁ ⊢ Con(ZF) → Con(ZFC)` and its PA corollary for the
represented `Theory.consistent` sentences. All formula codes and closure
lengths in the schema obligations range over the ambient arithmetic model.
The [pinned source review](results/upstream-11b8f3efb6-source-review.json)
finds no mathematical or API-scope issue. This review performs no fresh
compilation or axiom audit: the upstream audit contains 20 axiom probes,
one `#check`, and no typed caller examples. The closed Choice transport
does not by itself close the validator/interpreter or binary-machine bridges.

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

## Historical decomposition of the reverse ZF-to-validator translation

The proposal below records the earlier obligations and its intended IΣ₁
bound. The later `R2Native` and `ValidatorConsistencyEquivalence` source
discharges the comparison in IΣ₂, hence PA; the R3 interpretation remains in
IΣ₁. Keep the original proposal as chronology, rather than reading its open
items or IΣ₁ target as the current frontier.

*Proposal (Claude lane, 2026-10-17), with the R1 theory-construction sources
supplied in `f368d4ff11` and the generic R3 interpretation core supplied in
`ec37dd933a` on 18 October; the remaining obligations are below.*
With `𝗣𝗔 ⊢ Con(ZF) ↔ Con(ZFC)` closed and the forward
validator sentence `Con(ZF) → ¬∃code, value(code)=2` already proved, the
remaining arithmetic comparison between ZF and the validator is the reverse
implication: in every IΣ₁ model, `Provable 𝗭𝗙 ⊥ → CProv 1`. The external
proof (`WFTheory.c254_of_zf_refutation`) is semantic: the internally
well-founded part of every CP/GIC quotient models ZF. A represented version
splits into three pieces with a narrow interface:

1. **(R1) The native theory as a Foundation theory.** A `Δ₁` theory `𝗡`
   over `ℒₛₑₜ` mirroring `NativeTheory254.NativeAx`: the sealed container
   axiom, the GIC instance at every formula (a schema, recognized like
   `SepR`), and irreflexivity. External sanity check: for standard sentences,
   `𝗡 ⊢ σ ↔ BProv NativeAx [] σ` through the existing completeness adapters.
2. **(R2) Calculus translation (validator side).** In every IΣ₁ model,
   `Provable 𝗡 ⊥ → CProv 1`: internal Foundation derivations from `𝗡` are
   translated into C254 code proofs, using the configurable encoder,
   opening, vacuity, alpha-transport and fresh-stream interfaces already
   built for source-proof translation. Each GIC instance at an internal
   matrix goes to the corresponding `bundle` instance.
3. **(R3) The WF interpretation (set side).** In every IΣ₁ model,
   `Provable 𝗭𝗙 ⊥ → Provable 𝗡 ⊥`, by
   `InternalInterpretation.provable_falsum_of_interp` with target theory
   `𝗡`. This core permits defined equality and membership. Concrete raw
   formulas are available: domain
   `QuotientModel.translate (WellFoundedPart.wfForm 0)`, equality
   `ProfileSyntax.eqvForm 0 1`, and membership
   `QuotientModel.memberForm 0 1`. The domain describes the internally
   well-founded part of the definable quotient: its minimal-element
   condition quantifies over represented sets, not arbitrary external
   subsets. The [explicitly closed parameter](native_wf_closed_parameters.md)
   now has checked `Good` arity/shift conditions in every IΣ₁ model.
   Its identification with the semantic interpretation remains to be
   checked. Then prove native domain nonemptiness and
   transport of every internal ZF axiom code, including interpreted
   equality axioms and nonstandard Separation/Replacement matrices.
   Existing semantic proofs and completeness can supply fixed ordinary
   sentences; they do not discharge this uniform internal-code callback.
   A native adaptation of `LTemplate`'s proof-template compiler must
   supply GIC introduction and preserve quotient congruence for its
   interpreted matrix placeholders. The generic core alone does not
   establish these obligations.

The [source-only R3 review](results/upstream-internal-interpretation-ec37dd933a-review.json)
records the exact supplied core and existing quotient/WF formulas. The
[reduced-import core](internal_interpretation_core.md) subsequently passed
its source check and expanded audit: seven probes, thirteen typed callers,
and zero warnings. Its public declarations are unchanged; the import repair
adds a private arity lemma and redirects seven uses to it. The historical
source and audit remain available. The set-language term
premise is supplied by `SetRelativization.isTerm_eq_fvar`, while `Good`,
domain nonemptiness and internal axiom transport remain hypotheses of the
generic core. The separate closed-parameter audit passed seven probes and
ten typed callers without warnings. Its quotation helper passed five
probes and eight callers with two retained style warnings. These syntax
results do not supply the remaining semantic or arbitrary-code transport
steps.
A finite-fragment alternative would still need a uniform
transformation of arbitrary internal refutations; a result restricted to a
proper definable cut would need an additional bridge to full consistency.

The upstream [NativeFixed](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeFixed.lean)
now supplies source-level proofs for the interpreted equality and seven
fixed ZF axioms, together with domain nonemptiness for `NativeInterp.PN`.
Its [source/API review](results/upstream-native-fixed-b8b8397f3c-review.json)
found no mathematical blocker; no fresh compiler or typed audit is claimed.
`provable_domain` has the required nonemptiness shape in every IΣ₁ model.
`provable_interp_fixed` still takes an ordinary sentence and external
membership proof. Turning that result into a case split on arbitrary
internal axiom codes, handling internal Separation/Replacement matrices,
and identifying the checked closed parameter with `PN` remain separate
obligations.

The supplied [NativeGicDelta1](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeGicDelta1.lean)
and [NativeTheory](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeTheory.lean)
define the Δ₁ schema recognizer and `NativeSet.nativeTheory`.
`NativeSet.models_cpgic` supplies an external model bridge useful for R3.
The [source review](results/upstream-native-theory-f368d4ff11-review.json)
found no mathematical blocker; it did not run a fresh compiler or audit.
A subsequent [focused recognizer check](native_gic_delta1.md) compiled the
unchanged `NativeGicDelta1` and passed seven probes and ten typed callers
with zero warnings. It covers arbitrary-internal schema recognition; it
does not compile `NativeTheory` or prove the R2 translation into `CProv`.
The original five-probe audit, which has no typed callers, is retained as
history. The later R3 result is described below.

**R3 closed (Claude lane, 18 October).**
[`NativeSchema`](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeSchema.lean)
proves, in every IΣ₁ model, `Provable 𝗭𝗙 ⊥ → Provable nativeTheory ⊥`
(`provable_falsum_native_of_ZF`), hence
`𝗣𝗔 ⊢ Con(nativeTheory) → Con(𝗭𝗙)` (`peano_proves_con_native_imp_con_ZF`),
with standard axioms only (`NativeSchemaAudit`). The internal axiom callback
of `provable_falsum_of_interp` is discharged for every internal ZF code by a
case split on the axiom class (`mem_ZF_class`): equality and fixed axioms by
`NativeFixed`; Separation and Replacement at arbitrary, including
nonstandard, cores by

* `NTemplate`: `LTemplate` over `nativeTheory` with GIC, including GIC
  introduction at every internal matrix (`nativeGicProof`) and the compiler
  `compileN`;
* `NTInterp.interp_translate`: `interp PN` commutes with template
  translation, which settles every interpreted code identity at once;
* `NativeSchemaSem`: two fixed template sentences
  `intT(congruence of R) → intT(Separation/Replacement body for R)`, proved
  in every template model through the domain structure `SD` and `eval_intT`
  (GIC at `u ∈ x ∧ v = u ∧ R u`, respectively `u ∈ X ∧ D v ∧ R u v`, WF
  closure, functionality up to bisimilarity);
* quotient congruence of interpreted matrices: the congruence law of the
  core is a theorem of pure equality logic (`SetCongruence.congruenceProof₁/₂`
  over `𝗘𝗤`), transported to `nativeTheory` by `derivable_iSet`;
* `NativePeel.peel`: guarded generalization over the nonstandard parameter
  count.

The parameter is `NativeInterp.PN` itself (`good_PN`), so no identification
with the separately checked closed parameter is needed. The remaining
arithmetic piece of the reverse comparison is (R2),
`Provable nativeTheory ⊥ → CProv 1`.

The [literal GIC introduction](../../../../Logic/Interpretability/ZFCinPA/validator_native_gic254.md)
now supplies a validator proof for every internal matrix value after
double-negation padding, including zero: eight probes and ten typed callers
passed with no warnings. This closes the literal bundle side conditions;
the configurable Foundation-body encoding, arbitrary universal closure and
internal derivation translation required by R2 remain open.

[Fixed-label matrix congruence](../../../../Logic/Interpretability/ZFCinPA/validator_native_gic_congruence254.md)
now transports both validator implications through the literal GIC circuit
in every IΣ₁ model. It removes padding from the matrix while retaining the
witness label `pad p`, and derives
`CProv (wal 3 (internalGic 1 3 (pad p) p))` for every internal matrix value.
Eight probes and eleven typed callers passed with zero warnings. Configurable
native-body encoding, alpha identification, arbitrary universal closure and
internal derivation translation remain separate R2 obligations.

**R2 closed (Claude lane, 18 October).**
[`R2Native`](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Native.lean)
proves, in every IΣ₂ model, `Provable nativeTheory ⊥ → CProv 1`
(`cProv_falsum_of_native`), and with R3 `Provable 𝗭𝗙 ⊥ → CProv 1`
(`cProv_falsum_of_ZF`), hence
`𝗣𝗔 ⊢ ¬∃code, value(code)=2 → Con(𝗭𝗙)` (`peano_proves_validator_imp_con_ZF`).
The translation is generic (`R2Main.cProv_falsum_of_provable`): a Tait
sequent `Γ` is encoded, at an odd free environment `F` and an even binder
stream `s`, as the validator implication chain from the negated encodings of
`Γ` to falsum, and a Π₂ order induction over internal derivations (hence
IΣ₂, not IΣ₁) shows that every enumeration of every derivable sequent is a
validator theorem at every such `F` and `s`. Free labels are odd and binder
streams even throughout, so every rename targets a label absent from its
source and no bound-variable vacuity is needed. The axiom callback
`axOK_native` is a case split on the class of `nativeTheory`:

* `R2Fixed`: the `𝗘𝗤` axioms and irreflexivity through Codex's equality,
  Leibniz and Kalmár tautology interfaces, and the container axiom from the
  validator's bundle container clause;
* `R2Gic`/`R2Ax`: `gic_bridge_core` turns the literal GIC clause (through
  `cProv_internalGic` and the fixed-label congruence above) into the encoded
  GIC body at any odd labels, and `gic_axiom` peels the arbitrary internal
  universal closure.

Composing (R3), (R2) and the forward sentence,
[`ValidatorConsistencyEquivalence`](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorConsistencyEquivalence.lean)
states `𝗣𝗔 ⊢ Con(𝗭𝗙) ↔ validatorConsistencySentence`
(`peano_proves_con_ZF_iff_validator`) and, with `LSchema`, the same for
`𝗭𝗙𝗖` (`peano_proves_con_ZFC_iff_validator`); both already hold in `𝗜𝚺₂`.
`R2Audit` reports the axioms. The binary-machine side (exact246/routed245
runs against the arithmetic scheduler) is independent of all three.

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

**Historical obstacle for the Choice transport in PA**, now discharged by
`LSchema.hSchema`:
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

**`hSchema` is closed (2026-10-17).** `LSepBase.sep_obligation` and
`LReplBase.repl_obligation` give, for every code recognized by `SepR` or
`RepR`, an internal `𝗭𝗙`-proof of its relativization to `L` with empty
domain side formulas; `LSchema.hSchema` feeds them to
`ConstructibleInterpretation.provable_falsum_ZF_of_ZFC`, and completeness
gives `𝗜𝚺₁ ⊢ Con(ZF) → Con(ZFC)` (`LSchema.iSigma1_proves_con_ZF_imp_con_ZFC`)
and its `𝗣𝗔` corollary. The route:

* separation: the L6 template `LSepBase.sepComb` combines the reflection
  invariant (driver) with the glue premise `qPremise` at `m + 1` for
  `free K`; the code identity `relSep_val` matches the translated body with
  `relativize dL (sepBodyVal K)`;
* replacement: the core is read at `x :: y :: t`, so the glue premise is
  needed at level two; `LReplBase.qPremise2` obtains it from the glue at
  `m + 2` for the twice-opened core and one more generalization
  (`QX2_free`), and `replComb` places the relativized core in the binary
  slot `F₁`;
* both: `LFvBound` reads the core's free-variable bound off the recognizer
  data, and `LPeel` peels the opened body back to `qqAlls b m` and closes
  at zero matched variables with a functional environment.

The paragraph below is the pre-closure plan, kept for history.

**Remaining for `hSchema`** (historical, superseded by the paragraph above):
the reflection driver producing `Θ` is already available. `LGlue1` provides
matching functionality and slot reading; `LGlue2` supplies shift-fixity and the
opened quantifier-premise identity; `LGlue3` supplies the atomic compiled-glue
client. The merged `LGlue4` now supplies the remaining connective/quantifier
clients and internal formula induction, as source-reviewed above. `LFvBound`
adds the recognizer-derived core free-variable bounds, also source-reviewed.
`LPeel` supplies the internal universal-closure induction and zero-match
discharge; constructing a matching environment for an arbitrary internal
tuple is no longer a separate prerequisite on this route. `LSepBase` now
discharges the exact Separation opened-body premise and closes every internal
recognized Separation code through `sep_obligation`. The remaining schema
work is the Replacement depth-two core/glue adapter and its exact opened-body
`pVal` proof, followed by recognizer typing and the same closure mechanism.
The two schema proofs must then be connected to class membership and the
`Derivable`/`domSet` conclusion required by `hSchema`. Empty domain side
formulas suffice once each internal proof is obtained. These source-reviewed
additions still require focused compilation and axiom/caller audits.

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

## Claude lane: PA endpoint for the exact 240-state machine (claimed 2026-10-18)

Vladimir asked the Claude lane on 2026-10-18 to complete the PA formalization
for the [rotation240 candidate](candidate-rotation240/README.md). The intended
final statement is `𝗣𝗔 ⊢ (∃t, blank240 halts by t) ↔ ¬Con(𝗭𝗙𝗖)` for the fixed
arithmetic run graph of `machineRotation240`, with an all-Nat bridge to the
actual Core run. The validator half is closed (`ValidatorConsistencyEquivalence`,
`ArithmeticEnumeratorSeed246`). The remaining chain, in every IΣ₁ model, is

```text
binary240 halts from blank
  ⟺ (fixed 409,691-step bootstrap)  binary240 halts from the seed frame
  ⟺ (W6: per-site simulation)       Rotation240 control interpreter halts from the seed
  ⟺ (W1+W3: internal bisimulation)  Prog254 control interpreter halts from the seed
  ⟺ (W4+W5: control contracts)      arithmetic scheduler halts from seedValue
  ⟺ validator accepts falsity  ⟺  ¬Con(ZFC).
```

Planned work items (Claude lane; new modules only, Codex modules are not edited):

* **W1** a catalogue-generic statement of the represented control step and an
  internal *offset segment bisimulation*: related test sites agree on the tested
  register, untested registers may differ by a fixed standard offset (this covers
  both transfer-plus-one rotations as well as the routing245 re-association), and
  both clocks are positive per segment. Soundness is proved once for every IΣ₁
  model; certificates are external finite data checked by `decide`.
* **W2** the Rotation240 catalogue (6,455 leaves from `TreeRotation240`) and its
  represented step, mirroring `FiniteControlTable254`/`ArithmeticControlStep254`.
* **W3** the Prog254 ↔ Rotation240 certificate and its kernel check.
* **W4** the scheduler-state encoding into the Prog254 register file and the
  fetch-to-fetch composition for MP, DROP and NIP (contracts already exist).
* **W5** the remaining AX bundle (controls 487 → the gate), via macro contracts
  proved once per macro shape and instantiated at each occurrence.
* **W6** the arithmetic port of the 252 binary chain to the 240 table
  (`ArithmeticControlRun254.halts_iff_blank` analogue) and the 240 bootstrap.
  It consumes the external 240 decoder coverage, which stays with the Codex lane.
* **W7** the final composition, PA theorem, audit and documentation.

Because W3 bisimulates Rotation240 against Prog254, the existing Prog254
contracts (and W4/W5) also serve the 252-state machine's PA endpoint.

Upstream `3d62be4cbf` adds the source of `ArithmeticControlBisim`.
Its `halts_iff_of_check` transports halting at arbitrary internal times in
IΣ₁, conditional on both represented interpreter specifications and run
laws, a common definable nine-register algebra, nonzero live states, and a
passing closed certificate with positive A-controls and a zero-offset
initial entry. The [source review](rotation240_pa/upstream-review-3d62be4cbf/README.md)
records no local compilation, typed audit or concrete certificate check.
The source explicitly sets recursion depth 8,192 and heartbeats 4,000,000.

W2/W3 must reconcile register numbering: the Python catalogues use logical
registers, while `ArithmeticControlData254.sourceRegister` applies `physOf`
(logical register 0 is physical register 6). Use a common logical view of
the register operations, or permute both catalogues and their offsets
consistently. The concrete Lean certificate also needs successor indices
`s0`/`s1`, start/closure facts, and enough fuel for the terminal lookup.
These integration obligations and W4–W7 remain open at this source-review
checkpoint; the exact binary240 PA endpoint is not established by W1 alone.

Upstream `c0b55cdc4a` changes the proposed W2–W5 route to the unfolding of
`ofDag dag254 219`, instead of the Prog254 numbered interpreter in the earlier
diagram. Its tree-generic represented interpreter applies `physOf`, and the
certificate emitter permutes both catalogues before computing offsets. The
[source review](rotation240_pa/upstream-review-c0b55cdc4a/README.md) confirms
that this addresses the register-coordinate mismatch for the new data path.
It statically counts 3,862 certificate entries, ten with unit offsets; this
is not verification of their semantic obligations. The concrete wrapper
currently checks only entries 0–9, with no all-entry check or concrete
`halts_iff`. Its introductory claims have been corrected accordingly.

The new DAG unfolding has 6,459 internal binary nodes and 6,460 leaves,
including one halt. Its structured-semantics connection to the internal
scheduler remains to be proved; the older Prog254 contracts cannot be applied
to these new control numbers without a bridge. Full certificate checking,
that internal connection, the binary240 simulation/startup, and final PA
composition remain open. No local compiler or axiom audit was run for this
upstream review; its nondefault and unlimited-heartbeat settings are recorded
explicitly. The separate external 240-state coverage work remains unchanged.

**Claude-lane status, `9f2276a8c3` (W3 closed).** `ControlBisimRotation240.halts_iff`
now holds in every IΣ₁ model from every internal register file: the dag254
and Rotation240 represented interpreters halt together. All 3,862 certificate
entries are kernel-checked in four chunks (about 90 s); axioms `propext`,
`Classical.choice`, `Quot.sound` only. Both interpreters are now instances of
`ArithmeticControlTable` at packed literal row tables (`PackedTables`), so the
dag254 side needs no decoder-tree evaluation; only the Rotation240 table must
later be identified with `TreeRotation240.tree`, for the binary simulation (W6).
W4/W5 (scheduler link) will be proved on the dag254 interpreter by an internal
structured semantics (`ArithmeticDagRun`: block occurrences with exit maps, the
`RMDag.Run` constructors as composition lemmas, internal `Σ₁` iteration) and a
constructor-by-constructor port of L2; one root-occurrence check against the
packed table replaces any per-occurrence contract. The Prog254 contracts are not
on this route.

The [packed W3 source review](rotation240_pa/upstream-review-9f2276a8c3/README.md)
confirms the concrete interpreter theorem and independently compares all 3,862
certificate entries and 12,915 packed rows with their source data. This was a
source/data review, without a local Lean replay. The reported upstream timing
and axiom audit remain attributed claims; the wrapper uses unlimited heartbeats.
The packed-table identification with the binary decoder is still required.

Upstream `e4f8bd1762` adds `ArithmeticDagRun` and `ArithmeticL2Lib254`.
The [source review](rotation240_pa/upstream-review-e4f8bd1762/README.md) finds no
substantive mathematical blocker in the internal structured composition,
19 primitive loops and pairing contract. Its iteration proof fixes an external
occurrence before Σ₁ induction, allowing arbitrary internal counters. These
contracts remain conditional on occurrence facts; at that checkpoint the
concrete root binding, unpairing and remaining macros, scheduler link and
reverse halting argument were still needed. Both modules use recursion depth 8,192 and 4,000,000
heartbeats. No local compiler replay or axiom audit is claimed by this review.

The subsequent `85acb1bd28` and `ef744dd6d6` add internal unpairing and 22
stack/formula macro contracts. Their [successor source review](rotation240_pa/upstream-review-ef744dd6d6/README.md)
finds no substantive blocker and confirms the arbitrary-internal counters,
full-file effects and clean-scratch hypotheses. Root occurrence, equality/fetch,
dispatch/AX/root composition, the scheduler/seed relation and both directions
of internal halting equivalence remain open, alongside W6/W7. Upstream compile
claims retain their attributed status; this review did not run Lean.

**W6 interface (Claude lane, 2026-10-19).** The register side of the PA chain
meets the binary side at the represented Rotation240 interpreter
`ArithmeticControlTable.controlRun ControlBisimRotation240.tableR`, started at
`liveValue 1 (ArithmeticL2.enc seed)` with the logical seed of
`LogicalSeed246` (`np = 3`, `p1 = 3`, all other registers zero; `enc` places
logical register `r` in physical field `physOf r`). W6 must show, in every
IΣ₁ model, that blank240 halts iff this run reaches `0`. That needs (i) the
agreement of the packed table `tableR` with `TreeRotation240.tree` (successor
resolution as in the binary dispatcher; a chunked kernel check), (ii) a
per-control binary frame/step simulation for the 240 table (the analogue of
`ArithmeticControlFrame254`/`ArithmeticControlSimulation254`), and (iii) the
bootstrap now provided by `ArithmeticBootstrapRotation240`. The Claude lane is
currently on W4/W5 (L2 port: `ArithmeticDagRun`, `ArithmeticL2Lib254`,
`ArithmeticL2Macros254`, `ArithmeticL2Control254` landed); Codex-lane work on
(i)–(ii) is welcome and should target this interface.

The [control/AX source review through `8fa0f5b48e`](rotation240_pa/upstream-review-8fa0f5b48e/README.md)
finds no substantive blocker in the new equality, fetch, MP/NIP and complete
structured AX contracts. The AX evaluation module supplies 110 closed-form
transformer equalities. Execution still requires its stated cleanliness and
finite-occurrence hypotheses; the concrete root occurrence, identification
with the validator's AX operation, scheduler/seed composition and reverse
halting argument remain to be joined. These are upstream source additions
with explicit nondefault limits and attributed compile claims, not a new
local Lean audit. W6/W7 remain open.

The [W6 implementation route](rotation240_pa/w6-route/README.md) now fixes the
exact numeric frame: state 85, 64-cell PC margin, 167 initial one-valued spares,
and seed gap 117. Its independent static comparison finds all 6,455 packed
four-field rows equal to the decoder catalogue, including both successor
fields on non-test rows. The [finite binding plan](rotation240_pa/w6-route/table-binding.md)
turns this into a kernel-checkable obligation using cached subtree counts.
These are source plans and a data comparison; the concrete Lean table equality
and unbounded arithmetic simulation are still required. The
[frozen history](rotation240_pa/w6-route/history.json.gz) preserves the proposed
Lean proofs, inventories, parser corrections and source-only evidence.

**W4/W5 closed (Claude lane, 2026-10-19).** The register side of the PA chain
is now proved in Lean, in every model of IΣ₁, down to the W6 interface:
`ArithmeticL2.accepted_iff_rotation_halts` (module `ArithmeticL2Endpoint254`)
states that `∃ code, ArithmeticHistory254.value code = 2` iff
`controlRun ControlBisimRotation240.tableR` halts from
`liveValue 1 (enc ⟨3, 0, 0, 0, 3, 0, 0, 0, 0⟩)` (logical seed `np = 3`,
`p1 = 3`). The chain is: `ArithmeticEnumeratorSeed246.accepted_iff_seed_halts`;
`ArithmeticL2.halts_iff` (positive-clock transport of
`ArithmeticPositiveSimulation254` with the Σ₁ relation `ArithmeticL2.Related`;
one scheduler step is one run of the root, `ArithmeticL2.root_step`, built
from the internal port of the L2 contracts in `ArithmeticL2Lib254`,
`…Macros254`, `…Control254`, `…Axioms254`, `…AxiomsEval254`, `…Root254`,
`…Scheduler254`); the root occurrence `ArithmeticL2.root_occ` (one
`decide +kernel` on the packed dag254 table, fuel 220, controls 1–6460, normal
exit to control 1; Python model `rotation240_pa/check_root_occ.py`); and the W3
bisimulation `ControlBisimRotation240.halts_iff`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`. The concrete root occurrence, the
identification of the AX dispatch with the validator's AX operation
(`ArithmeticL2.ax_eval`), the scheduler/seed composition and both halting
directions, listed as open in the review above, are therefore discharged.
W6 (binary240 ⟺ the `tableR` interpreter) and W7 remain open.

The [independent source review through `3dbf5abe7f`](rotation240_pa/upstream-review-3dbf5abe7f/README.md)
finds no substantive blocker in this Root/Scheduler/Endpoint composition and
confirms the exact W6 interface. The upstream compilation and axiom claims
remain attributed: these commits added no raw build/audit records, and the
review ran no Lean. It records the nondefault proof limits and the diagnostic
Python helper's narrower role. On the W6 side, fresh local checks now cover
the [generic control prerequisites](rotation240_pa/control-prerequisites/README.md)
and the [canonical counted decoder tree](rotation240_pa/counted-tree/README.md).

**W7, register half (Claude lane, 2026-10-19).** As fixed sentences
(`ZFCinPA.RotationInterpreterConsistency240`, in the ZFCinPA facade; standard
axioms only): `rotationHaltsSentence` says that
`controlRun ControlBisimRotation240.tableR` reaches `0` from the seed state
(physical fields `[0,0,0,3,0,0,3,0,0]` as nested Cantor pairs);
`isigma1_proves_accepted_iff_rotation_halts : 𝗜𝚺₁ ⊢ acceptedFalsitySentence 🡘
rotationHaltsSentence`; and, with `ValidatorConsistencyEquivalence`,
`peano_proves_con_ZFC_iff_not_rotation_halts : 𝗣𝗔 ⊢ Con(𝗭𝗙𝗖) 🡘
∼rotationHaltsSentence` (also the `𝗭𝗙` and `𝗜𝚺₂` versions). The final W7
sentence `𝗣𝗔 ⊢ Con(𝗭𝗙𝗖) 🡘 blank240 never halts` then needs only the W6
semantic theorem (every IΣ₁ model: blank240 halts iff this interpreter halts)
and one more completeness step.

The [independent W7 source review](rotation240_pa/upstream-review-f5c47661df/README.md)
confirms the exact seed, represented formula, arbitrary-model completeness
and PA weakening. Upstream compile and axiom claims remain attributed; this
review does not provide a fresh local audit of that module.

**W6 finite table identification checked (Codex lane, 2026-10-19).**
[`TableRowsRotation240.table_eq`](../../Lean/BusyBeaver/ZFC/TableRowsRotation240.lean)
identifies all 6,455 packed rows with the exact decoder catalogue, including
both successor fields and exact length. The
[complete check](rotation240_pa/table-rows/README.md) passes 35 modules with
1,061 probes and typed callers, zero warnings and default proof limits.
Its pilot contributes one further probe and caller. The final equality uses
only `propext` and `Quot.sound`. This closes item (i) of the W6 interface above;
the represented binary frame/step simulation and its halting transport remain.

The internal runtime now also has checked
[carry/rollback traversal](arithmetic_carry_traversal_rotation240.md),
[end pulse](arithmetic_end_pulse_rotation240.md) and
[complete marked-target increment](arithmetic_increment_rotation240.md).
Together these pass 34 probes and 38 typed callers with zero warnings and
default proof limits. The spare count and register values are arbitrary
internal model elements. Increment preserves the other registers and appends
one spare with an exact positive clock; its blank right exterior is explicit.
The subsequent checked [decrement contracts](arithmetic_decrement_rotation240.md),
[symbolic executor and concrete runtime](arithmetic_symbolic_execution_rotation240.md),
[canonical rebasing](arithmetic_dispatch_rebase_rotation240.md) and
[instruction runtime](arithmetic_site_rotation240.md) now provide the six
instruction cases. Each has a positive internal clock, preserves the whole
configuration and reaches the exact packed-table successor or halt state.
The instruction unit passes 15 probes and 15 typed callers with zero warnings.

**W6 binary/control connection checked (Codex lane, 2026-10-19).** The
[global simulation](arithmetic_control_simulation_rotation240.md) now uses
positive-clock Σ₁ induction to prove both internal halting directions from
arbitrary represented entries. The
[exact startup identification](arithmetic_startup_frame_rotation240.md)
places the 409,691-step startup in that relation with control 1, physical
seed `[0,0,0,3,0,0,3,0,0]`, 167 spares and gap 117. The
[blank-control composition](arithmetic_blank_control_rotation240.md) combines
them with halt absorption to prove blank240 halts iff its packed control
interpreter halts from that seed, in every IΣ₁ model. These three new units
pass 28 probes and 34 typed callers with zero warnings and default proof
limits. The last unit includes the explicit nested-pair seed and the existing
fixed binary halting sentence; it imports no L2 scheduler or consistency
sentence. Final W7 composition and fresh local checks of the upstream
register/validator consistency chain remain separate work.
The [reviewed final-composition draft](rotation240_pa/final-composition-plan/README.md)
now fixes the literal sentence bridge and both ZF/ZFC endpoints. It has no
fresh compiler result. Its accompanying inventory and dependency plans track
the outstanding upstream checks. The subsequent R2Neg, R2Quant, R2Main, R2Gic,
NativePeel and
[internal renaming/substitution](../../../../SetTheory/BoundedConsistency/internal_soundness_check.md)
checks and seven [register-program prerequisites](arithmetic_register_prerequisites.md)
have passed. The first concrete control-bisimulation check hit the 4 GiB
memory limit; [all 3,862 entries and the assembled equivalence](control_bisim_rotation240_split.md)
now pass after splitting the certificate into 31 intervals, with the memory
cap unchanged. These results close fourteen of the inventory's 88 missing
module checks; the final PA endpoint remains pending.
