# Smaller machines for Con(ZFC)

The goal is a binary, single-tape machine with fewer than 254 nonhalting
states whose halting status is independent of ZF. The original target was
blank-tape nonhalting provably in **PA** equivalent to Con(ZFC). The search
now also permits equivalence to consistency of an effectively axiomatized
stronger theory, as clarified by the user on 17 October 2026. Each candidate
must state the assumptions used for its two unprovability directions;
consistency alone must not be confused with arithmetic soundness. The
external Lean equivalence with Con(ZFC) is now proved for a 252-state
machine; its internal PA proof remains open. All new formal work uses Lean.
An intended set-theoretic meaning is optional: any effectively presented
theory or proof calculus is eligible once its consistency calibration is proved.
The complete compiled search, including its data and initialization, is the
cost measure that decides whether a candidate improves the baseline.

Stronger targets must stay within well-understood assumptions widely believed
to be consistent (user clarification, 17 October 2026). Preferred benchmarks
are finite consistency iterations over ZF/ZFC and standard inaccessible-cardinal
assumptions. A shorter encoding alone does not justify an unfamiliar increase
in consistency strength. For an artificial calculus T, identify an accepted
benchmark S and prove both Con(S) → Con(T) and Con(T) → Con(ZF), with the
formalization base stated. This supplies a consistency upper bound as well as
the lower bound needed for the independence argument; no absolute consistency
proof is claimed. Require a concrete encoding benefit before increasing the
benchmark strength.

The active focus is verifying and formalizing the
[246-state contextual-fold candidate](candidate-prefix246/README.md).
The checked components of the earlier
[shared-carry 250 construction](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-160.md)
provide reusable proof infrastructure. Sources 58–59 contain the same
250-state table. All 8391 guarded
instruction cases, its 585,431-step complete blank startup and all nine stronger
audit jobs pass on fresh copies. Independent ordinary-proof review found no
fatal defect within its scope. The exact-table Lean endpoint and its internal
PA equivalence remain open. The different rejected250 scanner fold from the
predecessor report does not refute this construction.

The [247-state selector reduction](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-161.md)
removes three further states. Its seven executable checks and separate
741,241-step blank startup pass. Independent review found no mathematical
blocker in the ordinary argument; its exact-table Lean and internal PA
endpoints remain open. The same intake preserves broader semantic-seed
criteria and two 255-state research controls.

The [246-state contextual-fold candidate](candidate-prefix246/README.md)
removes one more pulse state and supplies a separate 410,735-step blank
startup. All nine main checks and two additional audits pass. The
[batch 162 review](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-162.md)
also preserves a further audit of the identical 247 table. Independent review
found no mathematical blocker within the ordinary-proof scope; exact-machine
Lean endpoints and the equivalence proved inside PA remain open.

The [exact 246-state table](table_prefix246.md) is now checked in Lean:
492 transitions, the state numbering, the unique halt action, and the
selector and folded-pulse rows. Its 47 theorem audits and 47 client examples
pass with no warnings. This is the finite table layer for the active target.

The [exact 246 arithmetic lookup](arithmetic_machine_graph_prefix246.md)
now represents those 492 actions by a fixed bounded arithmetic formula in
every IOpen model. Eight theorem audits and eight typed callers pass with no
warnings, including the terminal write and movement.

The [exact arithmetic step](arithmetic_machine_step_prefix246.md) and
[run graph](arithmetic_machine_run_prefix246.md) now cover all encoded
configurations and every internal IΣ1 time index. The standard natural-number
graph agrees with every actual blank runtime. The
[finite startup transfer](arithmetic_bootstrap_prefix246.md) proves in IΣ1
and PA the fixed arithmetic sentence for the complete 410,735-step bootstrap.
These three modules pass 28 axiom probes and 35 typed callers, with no final
warnings. The unbounded internal register/binary simulation and the PA
consistency equivalence remain open.

The [seeded arithmetic scheduler](arithmetic_enumerator_seed246.md) now
starts at candidate 3 with `TW=WS=H=0,D=3`, matching the required logical
seed. In every IΣ1 model, an accepted refutation code exists iff this
scheduler halts; its fixed sentence has IΣ1 and PA proofs. Ten axiom probes
and eleven typed callers pass with zero final warnings. Identifying this
internal scheduler with the binary run and with standard ZFC proof codes
remains separate work.

The [246 logical seed](logical_seed246.md) is now calibrated in Lean:
the unchanged register program started at `(3,0,0,0,3,0,0,0,0)` halts iff
ZFC has a refutation. Seven theorem audits and seven client examples pass.
The binary startup now reaches this exact logical seed. Complete decoder
coverage and runtime composition must still connect the program theorem to
the literal blank-tape machine; the PA comparison remains open.

The [246 pulse contracts](prefix246_pulse.md) and
[unbounded register operations](prefix246_boxes.md) now pass in Lean on the
exact folded table. The proofs retain the whole tape, arbitrary natural
register values, and the required spare suffix. Zero decrement restores the
file; positive decrement shifts its boundary; increment adds a value-one
spare. Complete decoder coverage and whole-program composition remain open.

The [246 fast lookup](fast_table_prefix246.md) is checked equal to the
canonical machine on every transition. It supports bounded kernel
calculations for the new bootstrap and symbolic decoder without changing
their machine semantics.

The [nine 246-state register selectors](prefix246_mark.md) have checked
unbounded marking and return contracts on the reduced selector table. Ten
theorem audits and six client examples pass with no warnings.

[First 1,024 steps of the 246-state machine](boot_prefix246_first.md) proves the exact blank-run state, head and entire tape, and supplies the checkpoint-composition lemma for the bootstrap chain. The guarded source/audit run passed seven axiom probes and nine callers with zero warnings.

[The exact 246-state bootstrap](boot_prefix246.md) is checked through all
410,735 transitions from the blank tape. The final theorem fixes state 88,
head −5 and every tape cell, and rules out earlier halting. Eight continuation
modules compose with the checked first 1,024 steps and final 16,384-step block;
the consolidated manifest preserves the exact records and independent review.

The [246 bootstrap frame](prefix246_bootstrap_frame.md) identifies that entire
tape with the calibrated logical seed, gap 181 and 167 spare registers of
value one. Five theorem audits and five callers pass with no warnings. The
history preserves the initial failed simplification and its one-line repair.

The [246 symbolic executor](prefix246_symbolic.md) and
[per-instruction interface](prefix246_site.md) now have checked whole-tape
soundness proofs. Their 15/15 and 12/13 theorem/client audits pass with zero
warnings. Complete coverage of the actual decoder and final runtime
composition remain separate obligations.

The [246 whole-tape frame adapters](prefix246_frame.md) connect symbolic
execution to the logical register file while preserving the spare suffix and
header distance. Fourteen theorem audits and fourteen callers pass; complete
decoder coverage and runtime composition remain separate.

The [246 instruction composition](prefix246_instruction.md) implements
every accepted logical instruction by a positive binary execution segment,
preserving the complete dispatch frame and nonempty spares. Its seven
theorem audits and seven callers pass with no warnings.

The [246 conditional runtime equivalence](prefix246_runtime.md) now proves
both directions of register/binary halting from a related whole-tape frame
and accepted decoder coverage. Eleven theorem audits and twelve callers pass
with no warnings. The checked blank startup and its frame identification are
available for composition; the complete coverage certificate remains open.

The [exact 250-state table](table_prefix250.md) is now checked in Lean: all 500
actions, the state numbering, the unique halt edge and the incoming edges of
the shared initializer. Its 40 named theorem audits and 40 callers pass.
Whole-run and consistency proofs for this table remain in progress.

Lean also checks the [initializer pulse invariant](prefix250_pulse.md) and
[unbounded register operations](prefix250_boxes.md), including positive
decrement’s boundary shift, zero decrement’s complete restoration and
increment’s extra spare block. The [nine register selectors](prefix250_mark.md)
also have checked unbounded marking and return contracts. These are local
execution theorems; the full
250-state bootstrap and global simulation remain open.

The [balanced prefix250 lookup](fast_table_prefix250.md) is now checked equal to the exact canonical table on all 500 actions. Its first source/audit run passed with two ordered probes, four client examples and zero warnings; the finite transition equality is axiom-free and complete machine equality uses only `Quot.sound`. This reusable calculation layer contains no bootstrap or consistency endpoint. [Exact evidence](results/fast-table-prefix250-verification.json) and [preserved history plus independent review](results/fast-table-prefix250-history.json) bind its source, generator and actual providers.

The [prefix250 symbolic executor](prefix250_symbolic.md) now has a checked
soundness theorem for the complete infinite tape. Its 14 theorem audits and
14 client examples pass with no warnings. Accepted symbolic traces justify
positive literal runs; complete instruction coverage and global composition
remain in progress.

The [per-instruction soundness interface](prefix250_site.md) now preserves
the independent gap changes from positive decrement and PC overflow. Its
12 theorem audits and 13 client examples pass. Checking every original
instruction against that interface remains the next coverage obligation.

The [whole-tape frame adapters](prefix250_frame.md) now connect those
symbolic endpoints to the logical register file and preserve the changed
spare suffix and header distance. Fourteen theorem audits and fourteen
client examples pass; complete runtime composition remains in progress.

The [first 1,024 blank-tape steps](boot_prefix250_first.md) are now checked
in Lean, with a complete tape description and a reusable checkpoint
composition theorem. This is a finite prefix; the full 585,431-step startup
still needs its remaining checked segments and final frame identification.

The [instruction composition](prefix250_instruction.md) now proves that
every accepted logical instruction has a positive binary execution and
preserves the complete dispatch frame with nonempty spares. Its seven theorem
audits and seven client examples pass. The all-sites premise remains open.

The [conditional runtime equivalence](prefix250_runtime.md) now connects
the 250-state instruction adapter to both directions of register/binary
halting, from a related whole frame and assuming site coverage. Its eleven
theorem audits and twelve client examples pass with no warnings. This proof
provides a template for the active 246-state target; complete coverage and
blank initialization for that exact table remain separate obligations.

The [previous intake](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-158-159.md)
preserves five complete reports and one explicitly partial salvage, including
cache-result MP, semantic seeds, countdowns and pairing-shift negation.

The [252-state register-permutation machine](candidate-permutation252/README.md)
now has a [closed ZFC endpoint](choice_calibration254.md): its literal blank-tape
nonhalting is equivalent to consistency of ZFC. The proof passes through the
checked ordinary ZF comparison, including Foundation and Power, then Choice in
the constructible subtype. It retains the complete original proof-search program. The proof
includes all 82,552 bootstrap steps, all 8,391 decoder guard cases, unbounded
register operations and both directions of global binary simulation. No
coverage or register-operation premise remains. The exact table, full startup
tape and independent regeneration are preserved. This is distinct from the
older reduced-calculus 252-state experiment below.

The [direct well-founded-model construction](wf_model.md) now proves in Lean
that the exact native/numerical calculus is equiconsistent with ordinary ZF,
including Foundation and Power. It uses the quotient's existing collection
resource. The [constructible-class lane](constructible_order.md) now supplies
Choice and the external ZFC refutation comparison.
[PA internalization](pa_internalization.md) still requires an explicit arithmetic
proof-code and finite-trace bridge. The active goal is the original PA equivalence.

The [167-unit integration](results/binary-zfc252-integration-verification.json)
freshly checks both Choice/binary compositions and every affected consumer:
seven modules, eighteen axiom reports and twelve callers, with 160 source- and
object-matched previously checked imports. It extends the earlier
[165-unit integration](results/choice-calibration254-integration-verification.json).
The final theorem retains no model, Choice, coverage or startup premise and
uses only standard Lean axioms. The earlier checkpoints below document the
steps leading to this result; their then-open Choice interfaces are now closed.

The latest [168-unit integration](results/arithmetic-machine-perm252-integration-verification.json)
adds the [exact numeric machine simulation](arithmetic_machine_perm252.md).
Two natural-number tape halves agree with every cell of the actual blank run
at every natural time, including the final halting write and move. The new
module and umbrella pass fresh checks, with 166 source/object-matched imports
reused; nineteen axiom probes and twenty-seven callers pass.

The separate [arithmetic machine extension](arithmetic_machine252.md) now
represents all504 actions, a complete encoded configuration step, and iteration
by fixed arithmetic formulas. Its run graph is total at every internal time in
every IΣ1 model and agrees with the actual Core run at every ordinary natural
time. A closed Σ1 sentence expresses actual blank halting; PA proves unique
totality of the evaluator. Eight fresh arithmetic modules/audits pass196 axiom
reports and237 callers. The internal PA proof connecting this sentence to ZFC
refutations remains open.

The [169-unit core integration](results/command-word254-integration-verification.json)
adds the [numeric command-word codec](command_word254.md): total encoding and
decoding, exact command-tail replacement, and concatenation on all natural
codes. It distinguishes empty word0 from the original nonempty candidate0.
Two units are freshly checked and167 source/object-matched imports reused;
21 axiom reports and25 callers pass. The separate
[bounded arithmetic tail/replacement graphs](arithmetic_command_word254.md)
also pass a narrow fresh check with Cantor:38 reports and42 callers, reusing14
matched core imports. The subsequent
[represented concatenation](arithmetic_command_append254.md) proves the exact
recurrence at every internal index and all-Nat command-list agreement. Its
24 axiom reports and 30 callers pass. The complete proof-to-command compiler and its internal execution contract
are now checked by the later word-history and correctness modules below.
The [validator recurrence](arithmetic_history_recurrence254.md) also holds at
all internal indices: accepted MP/GEN parents force acceptance of their actual
child codes. Eleven reports and twelve generic callers pass.
The [actual compiler-block circuits](arithmetic_command_blocks254.md) now have
fixed arithmetic graphs and symbolic agreement with the existing command
lists, including all leaf, MP and GEN blocks. Fifteen reports and twenty-five
callers pass; the later execution modules below establish their internal
command contracts.
The [internal word laws](arithmetic_command_word_laws254.md) prove tail
replacement identities and append associativity for arbitrary internal codes,
with six reports and seven callers.
The [arithmetic proof-word history](arithmetic_proof_word254.md) now builds
these words at every internal proof code, then applies the original validator
once at its public output. Twenty-eight reports and twenty-one callers pass.
Its PA theorem asserts unique totality. The later correctness module below
proves accepted-proof execution; consistency transport remains open.
The [quotation and nonemptiness adapters](arithmetic_proof_word_adapters254.md)
give exact structural-compiler agreement on ordinary quoted proof trees,
including invalid ones, and identify empty public outputs with validator
rejection at every internal code. Separate audits pass two/eighteen and
twelve/eighteen reports/callers.
The [actual command-step graph](arithmetic_command_step254.md) agrees with
`Enum254.cstep` on every natural command and represents its exact effects on
every internal IOpen input. Replacing the rest pointer preserves that effect.
The two audits pass seventeen/nineteen and three/four reports/callers.
The [internal word interpreter](arithmetic_command_run254.md) now represents
all internal time steps and proves termination on every coded word, with
halt and successful completion kept distinct. Its twenty-five reports and
thirty callers pass. PA proves unique totality of this evaluator.
The [execution adapters](arithmetic_command_execution254.md) now prove
agreement with the existing natural executor and all-internal successor and
append execution, passing twelve/fifteen and fifteen/twenty reports/callers.
The [Π1 contract interface](arithmetic_proof_word_contract254.md) proves that
compiler correctness for every initial top and saved stack admits IΣ1
induction. Six reports and eight callers pass. The
[fixed block execution contracts](arithmetic_command_block_execution254.md)
now cover discard, all leaves, GEN and MP, passing 19/20, 12/12 and 11/8
reports/callers. The [compiler correctness theorem](arithmetic_proof_word_correct254.md)
discharges the twelve-case successor premise and proves the exact contract
for every accepted internal code, with five reports and thirteen callers.
The [represented refutation word](arithmetic_refutation_word254.md) then halts
from every working state for each internal accepted falsity proof, passing
eleven reports and twelve callers. The scheduler comparison below is now
checked; binary-trace and internal proof-system transport remain open.
The [arithmetic scheduler step](arithmetic_enumerator_step254.md) now models
the actual six-register fetch/execute operation at every internal input and
agrees with `Enum254.enumStep` on every ordinary state, passing fourteen
reports and twelve callers. Its [internal iterator and fairness theorem](arithmetic_enumerator_run254.md)
prove that every candidate is reached unless the scheduler halts earlier.
A positive word halting from every working state therefore forces scheduler
halting. Sixteen reports and thirteen callers pass. The proof records the
first completed-word witness before the scheduler resumes enumeration.
The [validator-to-scheduler composition](arithmetic_enumerator_refutation254.md)
now proves a fixed arithmetic implication in IΣ1 and PA: every internal
accepted falsity proof forces scheduler halting from pointer/candidate zero
and arbitrary working registers. Five reports and nine callers pass. The
[two-way blank scheduler comparison](arithmetic_enumerator_equivalence254.md)
now proves the fixed validator/scheduler equivalence in IΣ1 and PA. Its
reverse direction uses certified initial working fields. Fourteen reports
and seventeen callers pass for soundness and composition. The internal
binary and ZFC proof-code comparisons remain open.
The [ordinary-Nat scheduler adapter](arithmetic_enumerator_run_nat254.md)
also proves exact agreement with actual `Enum254.run` for every time and
six-register state, and identifies arithmetic blank halting with the native
`Enum254.Halts` predicate. Eleven reports and fourteen callers pass.
The [original validator's constructor equations](arithmetic_proof_constructors254.md)
now produce accepted internal proof codes for every original rule, with
seventeen reports and eighteen callers. They support the checked
[bounded proof-witness stack invariant](arithmetic_enumerator_soundness_plan254.md)
for the reverse implication.
The [internal stack-tail drain](arithmetic_stack_tail254.md) now bounds every
stream by its numerical code, and the [bounded certificate module](arithmetic_stack_certificate254.md)
proves Δ1 stack certification, push/pop, bound weakening, zero certification
and cached-falsity extraction. Their audits pass fourteen/fifteen and
twenty-four/seventeen reports/callers. The
[local preservation theorem](arithmetic_command_preservation254.md) covers
every actual command, preserves one explicit bound, and extracts an accepted
falsity witness on halt. Twelve reports and fifteen callers pass.
The [internal positive-clock transport lemma](arithmetic_positive_simulation254.md)
then supplies a conditional halting-equivalence argument without a global
clock bound, passing four reports and four callers. Its concrete binary
simulation premises remain to be proved.
The [arbitrary-initial binary iterator](arithmetic_machine_run_from_perm252.md)
now supplies actual internal run composition, full halted-tape absorption
and equality with the blank evaluator, passing nineteen reports and twenty
callers. The [arithmetic bootstrap theorem](arithmetic_bootstrap_perm252.md)
transfers the checked 82,552-step prefix into every IΣ1 model and proves its
fixed sentence in PA, passing eleven reports and thirteen callers.
The [prefix-removal theorem](arithmetic_machine_prefix_perm252.md) now
equates blank halting with halting from that exact bootstrap target in every
IΣ1 model, passing four reports and six callers. The
[internal tape-prefix algebra](arithmetic_tape_prefix254.md) and
[actual binary scan](arithmetic_machine_scan_perm252.md) prove an unbounded
endpoint for a literal table row at arbitrary internal lengths and entire
tape halves. Their audits pass ten/ten and eight/eleven reports/callers.
The complete internal register and dispatcher simulation remains open.
The [uniform scan module](arithmetic_machine_uniform_scans_perm252.md)
now handles zeros and ones in both directions, passing 21 reports and 18
callers, including four concrete table rows. The theorems retain the full
numeric tape at arbitrary internal scan lengths.
The [zero-register block iterator](arithmetic_zero_register_blocks254.md)
represents an internally long spare suffix and proves exact concatenation,
two-bit read and ordinary-Nat tape-code laws, passing fourteen reports and
fifteen callers. Internal preservation of the spare shape remains open.

The [finite proof-template compiler](model_coded_core_compiler.md) now handles
arbitrary internal free parameters by compiling the existing logical proof
core and cutting supplied translated-axiom proofs at the root. Four local
modules and two audits pass, with six axiom reports and fourteen callers.
Its source proof remains standard finite syntax; translating arbitrary
internal source proofs remains part of the PA bridge.
The separate [internal axiom-proof transport](internal_axiom_proof_transport.md)
now handles arbitrary internally coded derivations when both theories use
the same language and the target proves every well-formed source axiom.
Three reports and seven callers pass. The actual C254/ZFC formula and axiom
translations remain to be supplied.
The [represented set-schema constructors](../../../../Logic/Interpretability/ZFCinPA/model_coded_schema_axioms.md)
now provide actual internal ZF/ZFC Separation and Replacement axiom proofs
for every shift-fixed internal matrix of arity one or two. Eleven reports
and ten callers pass. This earlier checkpoint retains shift-fixedness;
the later all-internal closing construction below removes that premise for
universally closed schema axiom proofs.
The subsequent lifted-PA client supplies the finite axiom witnesses itself.
Its fresh five-module check passes nine reports and twenty callers, including
specialization at matrices with internal free parameters.
The [fixed-template arithmetic graphs](model_coded_template_graph.md) now
represent this substitution and yield actual IΣ1/PA provability statements
quantifying over every internal matrix. Six fresh modules and four audits
pass twenty-two reports and thirty-seven callers.

The complete binary endpoint passed a
[153-unit source-verified integration](results/binary-perm252-integration-verification.json):
all151 reused source identities match successful scoped builds, with fresh
standard-theory bounds, umbrella and joint callers. This is not a full153-module
rebuild. At this checkpoint the ZFC direction was one-way; the later Choice
calibration above closes the reverse implication. The internal PA proof remains open.

**Choice transport (closed).** `ConstructibleChoice` proves Gödel's
theorem in Lean: the constructible class of any model of `ZFax_s` is a model
of `ZFCax_s`, hence `BProv ZFax_s [] ⊥ ↔ BProv ZFCax_s [] ⊥`
(`zf_refutation_iff_zfc_refutation`, standard axioms only). With the closed ZF
endpoints this gives `Endpoint254.literal_nonhalting_iff_zfc_consistent`
(the literal `Prog254` register program never halts iff Con(ZFC)) and
`BinaryZFC252.nonhalting_iff_zfc_consistency` (the 252-state blank machine
never halts iff Con(ZFC)). The original remote check of `BinaryZFC252` used a
typed stub. The merged version now passes the verified integration against
the actual `BinaryPerm252` object and its source-matched full dependency
closure, including the complete site certificates. The independent
[source review](results/binary-zfc252-review.json) records the exact interfaces. See
[tarski_logic_layer.md](tarski_logic_layer.md).

The later merged `SatSupport` module also passed a
[154-unit integration](results/sat-support-integration-verification.json).
It proves uniform internally finite support for satisfaction on every internal
formula code, including nonstandard codes. The independent
[Choice-route review](constructible_choice_review.md) records its scope; the
internal well-order and Choice arguments were still open at this checkpoint.

The [156-unit integration](results/history-abs-integration-verification.json)
checked the first part of `ConstructibleAbs`, `Code254History` and the umbrella,
with 153 source-matched reused units. The
[numeric history checker](code254_history.md) agrees with the original proof
validator on every natural input, including invalid codes. It is the next
concrete evaluator for the PA representation work, not an internal PA theorem.

The later [157-unit integration](results/barrier-constructible-integration-verification.json)
freshly checks the extended `ConstructibleAbs`, the actual enumerator's
[stack-barrier foundations](enum_stack_barrier254.md), and the umbrella;
154 source-matched units are reused. Formula codes, definable subsets and
hierarchy stages now compare between the ambient model and its constructible
submodel, proving **V=L inside that submodel**. The proof covers internal
nonstandard codes and uses internally finite environment restrictions.
Internal well-orders and Choice were still open here. The enumerator lemmas establish
the local stack invariant and the injection of NIP occurrences into earlier
DROP occurrences; the global trace/counting theorem remains separate.

The [160-unit integration](results/stack-count-order-integration-verification.json)
now closes that counting link in
[`EnumStackCount254`](enum_stack_count254.md). It proves the actual enumerator's
halting/refutation equivalence from `pl=np=d=0` with arbitrary current formula,
stack and cache, and supplies a general late-start credit interface. Four units
were freshly checked and 156 source-matched units reused. The merged
`InternalWO` and `OrderRec` modules also pass: they provide internal well-order
operations and an ordinal-recursive order-extension interface. A concrete
constructible well-order and Choice transport were implemented in the later
164- and 165-unit checkpoints.

Intake156/source49's [six dirty starts](dirty_reset254.md) are now proved for the
actual enumerator: next candidate `0,1,2,4,5,6`, empty command pointer, and
arbitrary current formula, stack, additive parameter and cache. Counter3 with
cache1 is checked to halt immediately. The
[161-unit integration](results/dirty-reset-integration-verification.json)
freshly checks `DirtyReset254` and the umbrella, with 159 source-matched reused
units. This enlarges the proved logical targets for initializer searches; it
does not supply a new binary initializer or reduce the 252-state table.

[Intake156](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md#batch156-sparse-certificates-reset-synchronization-and-the-zfc-comparison)
reconciles the three reports from `2447a98214`. Its useful new directions are a
canonical sparse proof certificate with square-root row bound, the six dirty
starts now ported above, and a classical HOD implementation plan for Choice.
All advertised finite compiler, fusion and rotation controls reproduce; none
improves 252 states. The ordinary ZFC reconstruction and HOD arguments remain
distinct from the later checked external Choice comparison and the still-open
internal PA/ZFC endpoints.

The later [163-unit integration](results/code-tuple-order-integration-verification.json)
checks the merged [internal code and tuple orders](internal_code_tuple_order.md):
every recognized internal formula code is in a represented well-order, and
tuples of every internal natural length admit a lexicographic well-order.
Four units are freshly checked and159 source-matched units reused. Nonstandard
codes and lengths are included. The subsequent
[constructible order](constructible_order.md) supplies bounded key sets and
Choice under V=L; [Choice calibration](choice_calibration254.md) applies it
inside the actual constructible subtype and closes the external ZFC endpoint.

The separate [arithmetic Cantor adapter](arithmetic_cantor.md) now proves the
exact pairing and bounded inverse graphs in arbitrary IOpen models, then
identifies them with the live numerical checker on every natural input.
Its27 axiom probes and20 callers pass using pinned Foundation/Mathlib caches.
This closes the pairing component of the PA representation plan. The history
extension below now supplies represented evaluation; the full coded proof/trace
comparison remains open.

The subsequent [constructor arithmetic graphs](arithmetic_code254.md) cover all
four exact base4 operations and the complete rho1 payload branch. Their fixed
parameter-free bounded formulas work in every IOpen model and agree with the
actual numerical definitions on all natural inputs. Fresh checks of this module,
Cantor and both audits pass56 axiom probes and47 callers. The following extension
adds the other positive templates. These arithmetic modules use separate
Foundation/Mathlib dependencies and are outside the Std-only core runner.

The [fixed-template extension](arithmetic_templates254.md) now covers rho2–8,
both theory components and the complete original bundle. A reusable finite
circuit compiler produces fixed bounded formulas and proves their correctness
in every IOpen model. The three-module arithmetic chain passes97 axiom probes
and83 callers. All positive template graphs are present; the gated twelve-case
row function is supplied by the next extension.

The [full arithmetic rule row](arithmetic_row254.md) now includes all twelve
cases, failed MP, both bundle gates and invalid tags. Its fixed bounded graph
works in every IOpen model and agrees with the actual history checker's row on
every natural input, with child results supplied explicitly. The four-module
chain passes 114 axiom probes and 120 callers. The next extension supplies the
history lookup, construction and outer proof-code decoding.

The [represented history checker](arithmetic_history254.md) now has fixed Σ1
and Δ1 graphs and unique Boolean outputs at every element of every IΣ1 model.
Its standard interpretation agrees with `Code254Proof.check` on every input,
including invalid codes. Lean also proves actual IΣ1 and PA derivability of the
fixed checker-totality sentence. Internal translations of proof codes and
binary traces remain necessary for the requested PA equivalence with Con(ZFC).
The five-module arithmetic verification passes 151 axiom probes and 164 callers.

The first [complete term-certificate register implementation](term-register/README.md)
now has an actual blank binary table and full cost: **4,704 working states**.
It retains all twelve rules, both gates and fixed falsity. Finite differential
tests pass, but it is far larger than the checked 252-state machine. Repeated
pattern-path traversal dominates its control; supplied constructor witnesses
and a shared checking loop are the next concrete comparison.

[Intake157/source50](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md#batch157-canonical-term-certificates-for-the-full-calculus)
adds exact quotation bounds and canonical constructor-only certificates for all
twelve C254 rules, with both freshness gates and a fixed contradiction target.
Its checker avoids computing the large formula integers; the binary codec,
enumerator and complete state cost remain open. The complete132,048-recipe
search repeats source48's family; the larger two-incoming search is partial.
Both the certificate proofs and continuation obstruction are ordinary
mathematics, separate from the existing Lean endpoint and the PA target.

The new [constructor-witness experiment](term-certificates/README.md) develops
that representation further: duplicate arena nodes are allowed, both freshness
conditions carry distinguishing paths, and explicit constructor IDs eliminate
template searches. It includes a total finite binary codec and fair search
specification for the same full calculus. All twelve rule controls, adversarial
duplicate/gate cases, 261 template comparisons and 262,143 short binary words
pass the finite checks. A deep bundle needs 62 supplied-record constructor
checks instead of 297,059 template-lookup visits in the first prototype.
These are verifier operation counts; tape access, fixed data, initialization
and the complete TM state cost still need implementation and measurement.

The subsequent [fixed-pattern matcher](term-certificates/pattern-matching.md)
eliminates the supplied constructor IDs too. It handles dynamically normalized
zero and retains the exact twelve rules, both gates and fixed falsity target.
The small bundle's unary certificate shrinks from 4,582 to 2,506 bits; matching
uses 98 constructor checks instead of the shared circuit's 62. All 261 template
controls and 262,143 short-word parses pass. This trades certificate size for
more reads; complete machine compilation is still needed to establish a saving.

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

A new [finite quotient checker](finite_quotient_frontend.md) replaces the
source44 kernels' explicit equality-clause enumeration with class labels,
three predicate tables, and retained-function congruence checks. Its exact
finite `stage_exists` decision uses one packed candidate counter and direct
literal endpoints. It removes 735 stored clause bits and reduces the largest
native substitution interface from six variables to four. Ordinary equivalence
and practical finite tests are recorded; the stage cutoff can be extremely
slow, and no complete RM/TM implementation or state saving is yet established.

A wider ordinary [initializer credit criterion](dirty_initializer_credit.md)
allows an arbitrary dirty stack bottom when the safe prefix covers the exact
DROP-minus-NIP balance skipped by the starting candidate. Its AX-first adapter
has 161 eligible counters below 100,000 in the finite syntax audit. A replay of
28,672 map/start cases found only the known clean initializer; the all-start
portion is redundant with the earlier blank-ray classification. Under the
retained universal runtime contracts all 504 rows are used, so another fold
needs a weaker phase or continuation invariant, or a different evaluator.

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

Batch155 adds sources42–46 from `fab89c5d26` (placement `799bcd094d`,
reconciliation `ed2953a68c`) to the
[same host](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md#batch155-dirty-stack-barrier-nine-function-kernels-and-transport-controls).
The useful new initialization idea is an ordinary enumeration-order barrier
that shields arbitrary old stacks at PL=NP=D=0. It calibrates the older
unpermuted runtime252 table by a separate huge accelerated bootstrap; its four
checked Lean components do not yet prove the actual-enumerator theorem.
Finite nine-function kernels, unary BU deduction/support obstructions and
22/24-control name transports are new compiler inputs. Complete measured
265/271/299/300 controls do not beat the current252. All executable suites and
bounded searches reproduce, with exact limits in the five dossiers and offline
`code/reproduce_155.py`. The current closed permutation252/Con(ZFC) endpoint
remains distinct; its internal PA proof remains open.

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
| `ArithmeticMachinePerm252.lean` | Exact two-natural tape representation and all-time simulation of the actual Core blank run, with halting write/move and invalid state behavior explicit. Includes the frozen252 table binding; fixed first-order arithmetic run graphs remain separate. |
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
| `Code254History.lean` | Numeric12-rule course-of-values evaluator; `accepts_iff_check` covers all codes/conclusions and `c254_iff_history` gives exact derivability. The separate `ArithmeticHistory254` extension now represents this evaluator and proves checker totality in PA. |
| `Enum254.lean` | The abstract six-register enumerator halts from zero iff code 1 is `C254`-derivable. Every candidate is reached unless an earlier one halts; proof blocks handle arbitrary retained registers. Model corollaries explicitly require a valuation. Its literal Prog254/RegisterPath simulation and the permutation252 complete binary composition are checked. |
| `RMDag.lean`, `Dag254.lean`, `L2Lib254.lean`, `L2Macros254.lean`, `L2Control254.lean`, `L2Axioms254.lean`, `L2AxiomsEval254.lean`, `L2Root254.lean` | L2 for the shared 219-node register program (attributed data port of the pinned `Dag254.v`, used by the 253- and 254-state tables): Wade's structured semantics with determinism; every loop, `pair`, the unpair walk, all stack/formula macros, the equality test, fetch, MP/NIP/DROP and the generated `axioms()` closed forms; `root_step` (one root run is one `enumStep`, halting included), `iter_halts_boot` and `program_halts_iff : IterHalts dag254 (nextproof = 2) ↔ C254 1`. |
| `RMEquiv.lean`, `RMEquiv254.lean` | L3: Wade's path semantics and the structured semantics agree for every well-formed DAG (`halts_iff_iterHalts`, forward and backward simulation up to trailing zero bits, Boolean well-formedness check); the 219-node program is well-formed (kernel-checked tables), giving `path_halts_iff : Halts pathDag254 (nextproof = 2) ↔ C254 1`. |
| `RMBisim.lean`, `Bisim254.lean` | L4: segment bisimulations transfer path halting for every register file (symmetric relation defined by certificate lookup, so one check gives both directions); 3010 related test-site pairs between the literal 6459-row `Prog254` and the 219-node DAG, kernel-checked in 16 chunks, giving `literal_halts_iff : Halts Prog254.program Prog254.initial ↔ C254 1` ([tarski_logic_layer.md](tarski_logic_layer.md)). |
| `NamedZF.lean`, `InternalOrd.lean`, `InternalRank.lean`, `ZFRank.lean`, `ZFNative.lean`, `Endpoint254.lean` | ZF proves the native axioms: named formulas over `Form` with named Separation/Replacement; inside any model of the ZFAxioms bundle with Power and set Regularity (no external well-foundedness), ordinals with trichotomy, the cumulative hierarchy by transfinite recursion, the rank theorem, Collection for every matrix and power containers; hence every `ZFax_s` model satisfies `NativeAx`, `zf_refutation_of_native` by `theory_transfer`, and `literal_nonhalting_of_zfc_consistent : Con(ZFC) → ¬ Halts Prog254.program Prog254.initial` ([tarski_logic_layer.md](tarski_logic_layer.md)). The reverse ZF comparison is checked in `WFTheory`; `ChoiceCalibration254` now closes the external ZFC comparison. |
| `TransRec.lean`, `ConstructibleDef.lean`, `Constructible.lean`, `ConstructibleReflect.lean`, `ConstructibleZF.lean` | Gödel's L inside any ZF model (no external well-foundedness): transfinite recursion for a definable stage operation; `Def(X)` through BoundedZFCConsistency's certificate satisfaction of coded formulas, with the truth bridge for standard formulas; `L_a ∩ Ord = a`; pairing, union and power in L; the reflection theorem for the L-hierarchy (closed limits by ω-iteration of a definable closing step); Separation and Replacement in L; `L_models_ZF`: the constructible substructure satisfies `ZFax_s`. The later `ConstructibleOrder` and `ChoiceCalibration254` supply AC in L and external refutation transport ([choice_calibration254.md](choice_calibration254.md)). |
| `OutgoingProfile.lean` | Four-node outgoing equality from exact full-profile singletons, actual raw-PSC model corollaries and reserved-zero named semantic translation at one false point. Source equality denotes full observational classes. |
| `ConstructibleAbs.lean` | Formula-code, satisfaction, definable-subset and hierarchy comparisons between the ambient ZF model and its constructible submodel. Internal-code induction, least internal rank and internally finite environment restrictions give `vEqL` in the submodel, used by `ChoiceCalibration254` to discharge Choice in L. |
| `Numeric254.lean`, `NamedNumeric254.lean` | Exact original four-tag numerical rules and gated C/G/vacuity bundle; named proof transport and refutation equivalence for the explicitly defined encoded-numerical-theorem theory Q. The later native/ZF and Choice modules close the external ZFC calibration; represented arithmetic transport remains open. |
| `BootstrapFrame253.lean` | The actual 312,975-step binary bootstrap realizes the actual 330-step register endpoint, with all nine permuted registers, 158 spare blocks and exterior blanks retained. |
| `Code254Containers.lean` | A literal gated bundle gives the existing transitive, powerset-bounding container resource in an irreflexive model with an explicit valuation. |
| `ZipperRuns.lean`, `RegisterBoxes253.lean` | Generic whole-tape sequential execution and preserving scans; actual public253 zero-decrement box for arbitrary preceding and following registers, in exactly twice the prefix width plus five steps. No PC-update or complete instruction simulation claim. |
| `Code254GIC.lean`, `Code254Models.lean` | Hygienic actual Form matrices and padded gated bundles give the CP/GIC model interface; semantic encoding/decoding gives the decoded-to-encodable model implication. The reverse implication is now supplied by `NativeDecoded254`; the later `ChoiceCalibration254` closes the external ZFC calibration. |
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
| `ProgramZF0.lean` | A ZF0 refutation forces the actual 219-node structured program to halt from nextproof = 2; structured non-halting implies Con(ZF0). The subsequent `BinaryPerm252` endpoint includes literal blank execution and Foundation; `ChoiceCalibration254` adds the external ZFC comparison. |
| `NativeDecoded254.lean` | Native CP + full actual-Form GIC + raw IR satisfy every decoded bundle, including coincident binders and truth code 0. With an explicit valuation, ModelsEncodable and ModelsDecoded are equivalent. |
| `NativeTheory254.lean` | Numerical falsity and actual 219-node structured-program halting are each equivalent to refutability of the explicit sentence theory CP + full native-Form GIC + IR. The later `BinaryPerm252` and `ChoiceCalibration254` close binary execution and the external ZFC comparison. |
| `EnumStackBarrier254.lean` | Actual candidate/command round trips, injective marked NIP-to-earlier-DROP replacement, witnessed safe stack prefix over arbitrary bottom, local preservation with positive credit, and candidate-zero reset. The global scheduler/counting theorem is not supplied. |
| `EnumStackCount254.lean` | Closes the actual global scheduler/counting link; safe credit at every candidate boundary, arbitrary dirty bottom, and `dirty_start_iff` for `pl=np=d=0`. No binary initializer or internal PA theorem is inferred. |
| `DirtyReset254.lean` | `six_dirty_starts_iff`: counters0,1,2,4,5,6 accept arbitrary four working fields, including d, through the actual AX eight-row shield and credit7=1; counter3/cache1 halts immediately. |
| `InternalWO.lean`, `OrderRec.lean` | Internal natural, lexicographic, pullback and appended well-orders, with explicit collection/separation premises; definable order recursion on internal ordinals. The concrete instance is now supplied by `ConstructibleOrder`. |
| `EnumSafeStart254.lean`, `DirtyRoot254.lean`, `DirtyProgram254.lean` | Attributed arbitrary-cutoff enumeration and dirty-root absorption, composed with the actual structured219/path program. Six numerical fields are unrestricted; top/cache/stack retain their exact theorem invariant and logical registers beyond8 remain zero. |
| `SeedInvariant254.lean` | Six constructors certify nonzero initial theorem codes, unshifted stacks, and the resulting dirty-start/native-refutation equivalence. This gives a larger sufficient initializer target; no binary startup is inferred. |
| `WellFoundedPart.lean`, `WFRelativization.lean`, `WFModel.lean`, `WFTheory.lean` | One actual GIC instance supplies closure of internal well-foundedness. Actual translated Separation/Replacement, Infinity and Power make its subtype a ZF model, yielding `C254 F ↔ BProv ZFax_s [] Bot` and native/ZF equiconsistency. `ChoiceCalibration254` supplies the external ZFC comparison; internal PA proof codes remain open ([direct route](wf_model.md)). |
| `RMBisim.lean` | Merged generic segment bisimulation with symmetric halting transport and a sound finite checker on explicit decoder trees. No concrete certificate instance is included in this module. |
| `SitesPerm252Checks0–7.lean`, `SitesPerm252.lean` | All233 decoder chunks and8,391 guarded instruction cases, composed against the complete literal tree. No external coverage premise remains. |
| `BinaryPerm252.lean`, `ZFCBoundPerm252.lean` | Actual blank252 halting iff numerical/native/ZF refutation, also iff an accepted finite proof code. Con(ZFC) implies blank nonhalting; the following Choice module closes the converse. Internal PA formalization remains open. |
| `CodeOrder.lean`, `TupleOrder.lean`, `ConstructibleOrder.lean` | Represented well-orders of all internal formula codes and finite tuples; bounded definition-key sets; definable ordinal recursion orders each constructible stage; `choice_of_VL` proves the exact selector-Choice axiom under V=L. |
| `ChoiceCalibration254.lean` | Choice in the actual constructible subtype, sealed ZFC model, refutation transfer through external completeness, and closed actual252 blank nonhalting iff Con(ZFC). No internal PA proof-code claim. |
| `ConstructibleChoice.lean`, `BinaryZFC252.lean` | Independently supplied Choice-in-L/refutation bridge and its composition with the exact literal 252-state binary endpoint. Both merged endpoints pass the 167-unit integration against actual binary objects and the complete source-matched certificate closure; the earlier remote stub check is superseded. |

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
transport remains open; the external ZFC comparison is now closed. `PositiveClosure`
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

This compiles 168 source units: first-order logic, set-theory dependencies,
`BusyBeaver.Core`, the research modules and the umbrella into a
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

1. Represent the proof-data translations and finite binary runs inside PA,
   building on the represented checker and exact numeric machine simulation.
   Prove the required arithmetic comparison; the external Lean nonhalting iff
   Con(ZFC) theorem does not settle this stronger requirement.
2. Continue minimizing complete machines. Alternative and artificial calculi
   remain eligible once their consistency comparison is justified; preserve
   the complete252 machine as the current implementation baseline.
3. Preserve the finite-sort countermodel when evaluating reduced logical
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


The [internal register-forward macro](arithmetic_register_forward_perm252.md)
crosses one actual unary register block in exactly `value+2` internal steps,
retaining both entire numeric tape halves. Three seek/probe pairs are tied to
the frozen table. Its ten-report/twelve-caller fresh check passes with zero
warnings; portable maintained preparation is recorded separately.

The [MP dummy-push experiment](mp_dummy_push_partial_cost.md) removes one successful-MP
helper occurrence while retaining the complete source calculus. Both tested
raw compilers keep their original 281/341 state counts. The direct optimized-decoder patch also retains 252 states, with its changed
blank entry unresolved within one million steps. No new bound or lower bound
follows from these controls.


The [internal zero-spare scan](arithmetic_zero_spare_scan_perm252.md) crosses any
internal count of zero register blocks in exactly twice that many steps,
preserving both complete numeric tape halves. Three frozen-table instances
pass eleven axiom reports and twelve callers with zero new warnings. This
endpoint supplies a scan component; the register-file invariant and full
internal binary/scheduler comparison remain separate.


The [internal register-return macro](arithmetic_register_return_perm252.md)
returns across one actual unary block in exactly `value+2` steps, retaining
both entire numeric halves through a recentered left-facing frame. Six
entry/probe wrappers cover the three return families. Eleven reports and
twelve callers pass with zero warnings.

The [internal free-parameter closing construction](../../../../Logic/Interpretability/ZFCinPA/model_coded_free_closure.md)
now handles every internal formula code, including nonstandard codes and
arbitrary internal free labels. A binder-aware traversal proves shift-fixedness
and exact reopening with the actual internal `bv` bound. The new closed-schema
constructors yield literal ZF/ZFC Separation and Replacement axiom proof codes
without a shift-fixedness premise on the matrix. Their separate fresh checks
pass 15/15 and 13/13 reports/callers, with zero warnings. The later
[internal specialization proof](../../../../Logic/Interpretability/ZFCinPA/model_coded_specialization.md)
opens an arbitrary internal number of closing binders using explicit proof
codes. Its 14 reports and 16 callers pass with zero warnings, including open
Separation in ZF and Replacement in ZFC. The full PA consistency comparison
remains open.


The [internal zero-spare suffix shift](arithmetic_zero_spare_shift_perm252.md)
retains the changing tape while increment shifts across an arbitrary internal
zero-spare count. Its exact value+2*count+2-step endpoint and blank-tail turn
pass three axiom reports and six callers with zero warnings. Complete
increment/file framing and the internal runtime comparison remain separate.


The [MP continuation mapping](mp_dummy_push_partial_cost.md#exact-mapping-into-the-optimized-decoder)
connects the source edit to one actual 252-table row. All 8,366 changed-program
guards pass conditional checks, and the 2,998-pair program certificate passes
independent validation. The state count remains 252 and its blank bootstrap
is unresolved; the complete frozen baseline is unchanged.

The [fixed register-file increment proof](arithmetic_register_file_perm252.md)
extends the internal spare-tail result to arbitrary internal values in every
preceding and following register of a fixed finite file. It includes the
complete seek, shift and return, with an exact positive running time. Its
first Lean run passes seven axiom reports and fourteen callers with zero
warnings. The list lengths are external; the values and growing spare count
are internal. This covers the fixed nine-register shape while leaving the
remaining instruction families and full arithmetic dispatcher refinement open.


The [internal marked-register increment](arithmetic_register_increment_perm252.md)
composes actual mark restoration, suffix shifting and return for a target
followed only by an arbitrary internal zero-spare tail. Its exact
2*value+4*count+7-step endpoint passes five axiom reports and eight callers
with zero warnings. A nonzero following register and the whole runtime
comparison require the separate register-file layer.


The [internal positive-decrement endpoint](arithmetic_register_decrement_perm252.md)
handles a fixed finite prefix/suffix of arbitrary internal register values and
an arbitrary internal zero-spare count. It decreases the marked positive
target and appends exactly one zero spare, in the stated whole-tape endpoint.
Ten axiom reports and twelve callers pass with zero warnings; first exit and
the complete dispatch/runtime invariant remain separate.

The [open-schema proof constructors](../../../../Logic/Interpretability/ZFCinPA/model_coded_open_schema_axioms.md)
now supply actual ZF and ZFC proofs of open Separation and Replacement bodies
for arbitrary internal matrices and free labels. Their fixed Σ1 operation
uses the checked closing and specialization constructions, with no shift-fixedness
premise. Eleven axiom reports and sixteen callers pass with zero warnings.
The numeric C254 formula translation and PA consistency comparison remain open.

The [internal zero-decrement endpoint](arithmetic_register_zero_perm252.md)
restores a marked zero and preserves every other register and spare in exactly
`2*fileTime pre+5` steps. Six axiom reports and ten callers pass with zero
warnings, including the fixed boot suffix with an arbitrary internal count
of appended zero spares. The subsequent marking proof completes the four box
operations; dispatcher composition remains.


The [internal primary-register marking endpoint](arithmetic_register_mark_perm252.md)
uses the nine literal selectors, arbitrary internal register values and both
complete tape halves. An externally fixed prefix of at most eight registers
is retained while the selected header is marked in the exact 2*fileTime+3-step
endpoint. Eight axiom reports and twelve callers pass with zero warnings;
PC/dispatch transport remains separate.

The [single-variable binding construction](../../../../Logic/Interpretability/ZFCinPA/model_coded_bind_one.md)
now binds an arbitrary internal free label at an arbitrary internal binder
depth and proves exact reopening. Fifteen axiom reports and nineteen callers
pass with zero warnings. This supplies the named-quantifier syntax for the
checked C254 decoder; transporting GEN proofs remains a separate obligation.

The [internal C254 decoder](../../../../Logic/Interpretability/ZFCinPA/model_coded_decoder254.md)
now has a fixed total Σ1 graph, exact code-indexed history and positive
recurrence, and formula well-formedness for every internal code. Sixteen axiom
reports and twenty-four callers pass with zero warnings. Source code 0 retains
the literal truth formula and its syntactic free label 0; the implication alias
at zero and all twelve proof-rule translations remain explicit obligations.

The [literal decoder constructor equations](../../../../Logic/Interpretability/ZFCinPA/model_coded_decoder_constructors254.md)
now identify all four arithmetic constructors with their decoded syntax for
arbitrary internal inputs, including the exact implication case split at zero
and code 1's membership(0,0) output. Nine axiom reports and twelve callers pass
with zero warnings; proof-rule and consistency transport remain separate.

The [decoded truth and MP proof constructors](../../../../Logic/Interpretability/ZFCinPA/model_coded_decoder_propositional254.md)
now supply explicit internal proof codes with fixed total Σ1 graphs. MP handles
the zero implication alias by returning the antecedent proof. Nine axiom
reports and fourteen callers pass with zero warnings, including actual ZF/ZFC
clients. The source axiom rows and the full PA endpoint remain open.

The [internal free-renaming and binder alignment](../../../../Logic/Interpretability/ZFCinPA/model_coded_free_renaming.md)
checkpoints supply fixed total syntax operations, their SHIFT/substitution
laws, actual ZF/ZFC axiom invariance and the exact named-binder opening law.
All labels and counters are internal. Together the three modules pass
twenty-three axiom reports and twenty-four callers with zero warnings.
These syntax laws support the internal derivation transport below.

The [internal proof-renaming and named-GEN theorem](../../../../Logic/Interpretability/ZFCinPA/model_coded_proof_renaming.md)
now transports arbitrary internal derivations of actual ZF and ZFC, including
nonstandard formula codes. A fixed-budget Σ1 induction bounds both changing
renaming counters and handles all ten derivation rules. Named generalization
has no remaining freshness or axiom-closure premise. Two modules pass seventeen
axiom reports and eighteen callers with zero warnings; the C254 axiom rows and
accepted-history translation remain separate.

The [decoded-falsity endpoint](../../../../Logic/Interpretability/ZFCinPA/model_coded_decoder_falsity254.md)
now proves internal ZF-provability of `decode 1` exactly when ZF proves
primitive Bottom. It quotes a fixed ordinary irreflexivity theorem, opens it
at free label zero, and uses explicit internal cut constructors. Eight axiom
reports and twelve callers pass with zero warnings. Accepted-history
translation and the full PA endpoint remain open.

The [decoded single propositional axiom](../../../../Logic/Interpretability/ZFCinPA/model_coded_decoder_lukasiewicz254.md)
now has an internal proof for arbitrary input codes in every IΣ1 model.
Provable implication equivalence handles the zero alias through the actual
arithmetic `rho8` constructor; a fixed Peirce proof supplies the target
tautology. Five axiom reports and eight callers pass with zero warnings.

The [decoded numerical GEN rule](../../../../Logic/Interpretability/ZFCinPA/model_coded_decoder_generalization254.md)
connects the actual `wal` constructor to internal named generalization in
ZF and ZFC. It includes free label zero and repeated binders. Three axiom
reports and six callers pass with zero warnings. The remaining axiom rows,
set-theoretic bundle and accepted-history translation remain open.


The [named-binder laws and universal-distribution template](../../../../Logic/Interpretability/ZFCinPA/model_coded_named_quantifiers254.md)
prove negation/implication compatibility at arbitrary internal binder depths
and supply a finite typed universal-distribution proof. Together they pass
three axiom reports and eight callers with zero warnings.

The [decoded numerical universal-distribution row](../../../../Logic/Interpretability/ZFCinPA/model_coded_decoder_rho2_254.md)
now has an internal proof in actual ZF and ZFC for arbitrary internal labels
and formula codes. Named-universal congruence transports the implication zero
alias under the binder; the final endpoints discharge the generalization
resource. Eight axiom reports and eight callers pass with zero warnings.
The other logical rows, gated set-theoretic bundle and full PA endpoint remain
separate obligations.


The [three decoded equality rows](../../../../Logic/Interpretability/ZFCinPA/model_coded_decoder_equality254.md)
now have internal proofs for arbitrary labels in actual ZF and ZFC. Fixed
ordinary equality/congruence theorems are internalized before their bound slots
are specialized at model elements; decoder implication equivalence identifies
the actual `rho7`, `rho5` and `rho3` codes. Eleven axiom reports and twelve
callers pass with zero warnings.

The [decoded exchange of named universals](../../../../Logic/Interpretability/ZFCinPA/model-coded-decoder-rho4-254.md)
proves the actual `rho4` row for arbitrary internal labels and matrices,
including coincident labels. Its syntax, finite logical template and numerical
client pass fourteen axiom reports and twenty callers, with four retained
style warnings. The [repeated-binding and vacuous-opening laws](../../../../Logic/Interpretability/ZFCinPA/model_coded_binder_absorption.md)
pass seven reports and nine callers with no warnings; they supply the vacuity
step for `rho6`.

The [decoded existential-universal row](../../../../Logic/Interpretability/ZFCinPA/model-coded-decoder-rho6-254.md)
now proves actual `rho6` in internal ZF and ZFC, including variable zero.
Proof equivalence and named generalization handle capture of its relative
falsity formula. Twelve axiom reports and sixteen callers pass with one
retained style warning.

The [decoded existence-of-equality row](../../../../Logic/Interpretability/ZFCinPA/model-coded-decoder-rho1-254.md)
proves actual `rho1` in internal ZF and ZFC, including coincident and zero
labels. Opening its named binder at the other label yields reflexive equality.
Ten axiom reports and sixteen callers pass without warnings. All eight
individual logical-row clients are now proved; the gated set-theoretic bundle,
accepted-proof translation and full PA equivalence remain open.

The [two decoded atomic vacuity clauses](../../../../Logic/Interpretability/ZFCinPA/model-coded-decoder-atomic-vacuity254.md)
now have internal proofs for every Δ1 set-language theory under the actual
gates `c ≠ a` and `c ≠ b`, allowing `a=b`. Syntactic binder invariance supplies
finite generalization without a target axiom or GEN premise. Ten axiom reports
and twelve callers pass without warnings. The outer conjunction and the
container and collection clauses remain open.

The [finite circuit decoder](../../../../Logic/Interpretability/ZFCinPA/model-coded-decoder-circuits254.md)
now handles every fixed constructor circuit at arbitrary internal inputs in
actual ZF and ZFC. It transports relative falsity through named binders while
keeping the original numeric variable labels. The [logical normalization
helpers](../../../../Logic/Interpretability/ZFCinPA/model-coded-named-logical-normalization254.md)
identify its conjunction and existential encodings with the native logical
operations. Together their focused checks pass fourteen axiom reports and
twenty callers with zero warnings. The C/G/bundle decoder results are
equivalences; proving C and G remains open.


The [arithmetic symbolic-tape interpretation](arithmetic_symbolic_tape_perm252.md)
reuses actual finite segment/configuration syntax and normalization with an
arbitrary internal gap and parameterized box prefixes. Accepted comparisons
preserve the complete numeric configuration; exterior deletion uses terminal 0.
Ten axiom reports and twelve callers pass with zero warnings. Concrete boxes,
symbolic execution and the full runtime refinement remain separate.


The [internal read/write scans](arithmetic_writing_scans_perm252.md) permit
replacing the consumed bit under explicit actual self-loop rows, for every
internal length and both whole tape halves. Six axiom reports and twelve
callers pass with standard axioms; four audit style warnings are preserved.
Concrete boxes and full symbolic/runtime transport remain separate.


The [concrete internal register-box interpretation](arithmetic_symbolic_boxes_perm252.md)
now uses the actual finite Box/Effect/Branch syntax, nine arbitrary internal
primary values and an internal zero-spare count. It retains the explicit final
padding cell, checks branches on the original values, and reuses all four
checked box endpoints. Positive decrement alone appends a zero spare. Seventeen
axiom reports and twenty callers pass with standard axioms; four source
unused-section-variable style warnings are preserved. Full internal runtime
transport remains separate.

The [arithmetic soundness of the actual symbolic checker](arithmetic_symbolic_execution_perm252.md)
now connects the existing `sstep`, `exec` and `verifies` decisions to complete
numeric machine runs in every IΣ1 model. A checked erasure equality retains
the exact native targets, guards and progress flags; initially false progress
yields a positive internal clock, including the real halt write and move.
Twenty-five axiom reports and twenty callers pass with zero warnings. Syntax
and fuel remain external finite data; the definable dispatcher relation and
full internal runtime/PA endpoint remain separate.

The [arithmetic site contracts](arithmetic_site_perm252.md) now turn actual
accepted `SitePerm252` checks into their numeric endpoints in every IΣ1 model,
including positive execution clocks, physical decrement guards and the
complete final halt step. Twelve axiom reports and fourteen callers pass with
zero warnings. The accepted-site premises remain explicit; internal dispatch
and global runtime remain separate.

The [arithmetic blank-to-Site entry](arithmetic_site_boot_perm252.md) connects
the existing 82,552-step bootstrap to `Site.start []` with nine zero primary
registers, zero gap and 56 variable zero spares in every IΣ1 model. Finite
bit/register/Box compatibility preserves the exact final padding cell. Fifteen
axiom reports and seventeen callers pass without warnings; this uses the
checked bootstrap without replaying it. Global runtime remains open.

The [composable arithmetic dispatch entries](arithmetic_dispatch_rebase_perm252.md)
now connect each accepted nonhalting instruction to the next accepted canonical
entry, with exact register updates, carry padding and one spare append on positive
decrement. Actual decoder coverage supplies the next leaf and its `follow`
equation. The bootstrap also reaches its first accepted leaf at the same
82,552-step clock. Sixteen axiom reports and eighteen callers pass with zero
warnings. Variable-PC representation and global internal runtime remain open.

The [compact finite-control representation](arithmetic_finite_control254.md)
proves binary constants and bounded table lookup in every IOpen model, together
with an exact common 40-bit dispatch frame under IΣ1. Eight axiom reports and
thirteen callers pass with zero warnings. Large constants use their binary
digits, keeping the recursive term only once at each step. Binding these
formulas to the actual 6,460 control rows, the represented interpreter and the
internal scheduler bridge remain open.

The [literal control catalogue](finite_control_table254.md) derives all 6,460
actual source leaves from the checked tree. It proves unique source indexing,
inherited site acceptance, and a deterministic walk/consume/index resolver,
including the empty pointer's first control. Fourteen axiom reports and
seventeen callers pass with zero warnings, reusing the existing coverage
proofs. Resolving a pointer alone does not justify whole-frame equality without
`Clean`; arithmetic lookup/iteration and the internal scheduler remain open.

`ArithmeticControlData254.lean` ([note](arithmetic_control_data254.md)) derives
coherent fixed arithmetic opcode/register/successor/overflow/spare/PC columns
from the actual 6,460-leaf literal catalogue. Its 16-probe/20-caller focused check
reuses 81 matched project objects and six boundaries. Compact constants and
bounded graphs cover arbitrary internal keys; absent zero differs from genuine
halt opcode four. Represented control step/run and the internal scheduler bridge
remain open. Exact proof and preparation/history records are stored separately.

[`NativeZFContainers254`](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeZFContainers254.lean) extracts the actual ordinary Foundation ZF axioms into the checked native rank interface, then proves two fixed power-container sentences, including the exact C-row binder/connective order. The 380-line source and 15-probe/15-caller audit passed with standard axioms only and zero warnings. The guarded closure reuses ten native project objects and one recorded direct Foundation boundary; both unsuccessful attempts and the successful run are retained. This is the ordinary fixed container theorem. The finite all-internal alpha/substitution client, coincident-label C case, arbitrary-internal Collection G, full bundle and PA proof-code comparison remain separate obligations. See [the note](../../../../Logic/Interpretability/ZFCinPA/native-zf-containers254.md) and [evidence](../../../../Logic/Interpretability/ZFCinPA/results/native-zf-containers254-verification.json).

`ArithmeticControlStep254.lean` ([note](arithmetic_control_step254.md)) represents
one step using the actual numbered literal-control columns and a bijective
fixed nine-register code. Its 27-probe/30-caller focused check passed with zero
warnings, reusing 82 matched project objects and six boundaries. Fixed Sigma1
graphs and a total Delta1 step cover every internal input; invalid0 and genuine
halt4 remain distinct opcode facts. Binary simulation, represented iteration
and the internal L2/scheduler connection remain open.

The [positive-code freshness theorem](../../../../Logic/Interpretability/ZFCinPA/model-coded-decoder-freshness254.md) proves that binding any positive label at least as large as an internal source code leaves its decoded formula unchanged, at every internal binder depth. Its eight-probe/twelve-caller Lean audit passed without warnings. The proof uses internal Π1 order induction and the actual strict child bounds, with the literal source0/label0 exception explicit. Positive codes therefore supply their own fresh label for the Collection row. The all-internal Collection proof and its zero-matrix case remain open.

[`ModelCodedDecoderContainer254`](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedDecoderContainer254.lean) now proves the actual numerical C clause in internal ZF for arbitrary internal `a,b,c` satisfying only `c≠a` and `c≠b`, including `a=b` and valid zero-label cases. The 330-line source and 16/20 audit passed with standard axioms only and zero warnings. The finite distinct-label quote/substitution calculation uses the fixed ordinary NativeZF container row; the coincident branch is proved separately by irreflexivity and existential monotonicity. All failed attempts are retained, with no resource increase or dependency build. [The note](../../../../Logic/Interpretability/ZFCinPA/model-coded-decoder-container254.md) and [evidence](../../../../Logic/Interpretability/ZFCinPA/results/model-coded-decoder-container254-verification.json) retain the remaining G, full-bundle, accepted-proof and PA comparison obligations.

[Finite shift cancellation](../../../../Logic/Interpretability/ZFCinPA/model-coded-shift-cancellation.md)
now constructs actual internal proofs of p from proofs of any externally finite
iteration of free-variable shift on p. Arbitrary internal formula codes and
free parameters are retained; six axiom probes and nine callers pass with
standard axioms and zero warnings. This is the cancellation step for a proposed
open-predicate template compiler. That compiler and Collection remain separate.

The [finite-buffer proof-template compiler](../../../../Logic/Interpretability/ZFCinPA/buffered-template-proof-compiler.md)
now passes seven axiom probes and nine callers with standard axioms and zero
warnings. It handles both universal introduction and explicit SHIFT with an
externally finite buffer, then cancels that buffer at a closed source conclusion.
The interface admits arbitrary internal free parameters and actual axiom-proof
callbacks. Concrete predicate-family laws and Collection callbacks remain to
be instantiated; no internal ZFC comparison is inferred from this interface.

`ArithmeticControlFrame254.lean` and
[arithmetic_control_frame254.md](arithmetic_control_frame254.md) give a fixed
Sigma1 whole-frame relation for every valid represented catalogue control and
six exact source-case binary runtimes in arbitrary `IΣ1` models. The relation
keeps invalid controls out, and rebasing retains the actual walk/resolver
witness; positive decrement adds one zero spare exactly once. The focused
check passed 27 probes and 30 callers with zero warnings, using 83 matched
project providers. Coded-step calibration, represented iteration and the
internal L2/scheduler connection remain separate obligations.

The [open set-template compiler](../../../../Logic/Interpretability/ZFCinPA/open-set-template-compiler.md)
now instantiates that buffer interface for arbitrary internal set predicates,
including free parameters, with no shift-fixedness condition. The two unchanged
precursor modules, new client, and eight-probe/eight-caller audit pass with
standard axioms. Two harmless style warnings are recorded. Actual target
axiom-proof callbacks remain explicit; Collection and numerical G are separate.

`ArithmeticControlSimulation254.lean` and
[arithmetic_control_simulation254.md](arithmetic_control_simulation254.md) close
the concrete local step/halt obligations for the represented numbered control
program. In every `IΣ1` model, a valid `Related` frame reaches the exact live
successor or actual binary halt after a positive internal clock. Invalid
control0 is excluded and all physical-selector/source cases are calibrated.
The focused check passed ten probes and ten callers with zero warnings, using
84 matched project providers. Represented iteration, blank-entry composition
and the internal L2/Enum connection remain separate obligations.

`ArithmeticControlRun254.lean` and
[arithmetic_control_run254.md](arithmetic_control_run254.md) iterate the actual
source-derived numbered control step at every internal `IΣ1` time and prove
`halts_iff_blank`: that interpreter reaches zero exactly when the actual blank
binary evaluator halts. The concrete positive-clock simulation and existing
bootstrap discharge all runtime assumptions; no bootstrap or guard replay is
needed. The focused first check passed 16 probes and 18 callers with zero
warnings, using 87 matched project providers. The further all-internal L2/Enum
scheduler connection remains explicit.

The checked [fixed Collection template](../../../../Logic/Interpretability/ZFCinPA/collection_template254.md) proves one ordinary enlarged-language sentence from lifted ZF, explicit enlarged equality, and three particular predicate-dependent schemas: witness-rank Separation, globally total least-rank Replacement with empty-ordinal fallback, and output Separation. The two new modules and audit pass 7 axiom reports/12 callers with standard Lean axioms and zero warnings; the record preserves all six attempts, including an interrupted second attempt. The source theorem is ready for a finite-template compiler, while translated schema/equality callbacks and the exact decoder-G conclusion bridge remain separate obligations. It does not establish the internal bundle or PA proof-code comparison.


The [actual internal clear-loop contract](arithmetic_control_clear254.md) now proves the literal catalogue occurrence 6431/6432/6433 in every IΣ1 model: physical register 7 is cleared in exactly `2*v+1` represented interpreter steps, stopping before the exit `brk1`. The generic loop proof keeps default limits; only three closed catalogue equations use a measured local recursion setting. The first complete source/audit check passed 9 probes/11 callers with standard axioms and zero warnings. All four attempts and the separate maintained-default UNBUILT preflight are retained. This is a local interpreter contract; the internal L2/Enum connection remains open.

The [actual initial fetch contract](arithmetic_control_fetch254.md) now covers both literal interpreter branches in every IΣ1 model. Positive PL takes 2 logical instructions; PL=0 with scratch1=0 takes exactly `7*NP+4`, preserving the whole file except the specified NP/PL updates. The actual copy and restore loops and catalogue controls 0–10 are checked. Run2 passed 12 probes/15 callers with standard axioms and zero warnings; run1 and the separate UNBUILT preparations remain archived. This advances the internal L2/runtime bridge; actual unpair/read and the complete scheduler connection remain open.

The [represented relativization checkpoint](internal_relativization.md) now checks all-internal formula laws and conditional derivation transport with explicit domain side formulas:11 probes/12 callers, only the standard three axioms and zero warnings. Domain-side discharge and actual L/ZFC axiom proofs remain separate.

The actual first read/unpair macro is now checked in [`ArithmeticControlRead254.lean`](../../Lean/BusyBeaver/ZFC/ArithmeticControlRead254.lean). For every IΣ1 model and whole nine-register file with both scratch registers zero, literal controls 10–24 reach the next read after a positive internal logical time, replace PL by its second Cantor projection, add the first projection to AC, and preserve the remaining fields. The proof includes the IOpen inverse-successor walk, all three actual transfer loops and a fixed-file Σ1 existential-clock invariant. The focused audit passed 16 ordered probes and 19 callers, standard axioms only, with zero warnings; one failed source attempt is preserved. See [the scoped note](arithmetic_control_read254.md), [verification](results/arithmetic-control-read254-verification.json), [history](results/arithmetic-control-read254-history.json), [independent review](results/arithmetic-control-read254-review.json) and [publication record](results/arithmetic-control-read254-publication.json). The complete internal interpreter/Enum and PA endpoint remain open.

- [Consolidated internal relative interpretation and set-language adapter](internal_relativization_refresh.md): fresh827+50 source check,16/18+3/6 audits,std3,zero warnings; conditional all-internal proof/refutation transport with actual domain/axiom obligations retained. Earlier701 checkpoint remains historical.

The actual second read and both reads together are checked in [`ArithmeticControlReadTemplate254.lean`](../../Lean/BusyBeaver/ZFC/ArithmeticControlReadTemplate254.lean). A finite `ReadShape` records only actual catalogue edges and continuations; its generic all-internal proof is closed by the literal controls24–37→38 binding. `read_p1` consumes PL into its Cantor components and adds the first to D. `reads_run` composes the checked controls10→24→38, giving AC=`oldAC+first(oldPL)`, D=`oldD+first(second(oldPL))`, PL=`second(second(oldPL))`, a positive internal logical clock, and preservation of the other six fields. The first focused source/audit attempt passed 12 ordered probes and 15 callers, standard axioms only, with zero warnings. See [the scoped note](arithmetic_control_read_template254.md), [verification](results/arithmetic-control-read-template254-verification.json), [history](results/arithmetic-control-read-template254-history.json), [independent review](results/arithmetic-control-read-template254-review.json) and [publication record](results/arithmetic-control-read-template254-publication.json). Dispatch/constructor calibration and the complete internal interpreter/Enum and PA endpoint remain open.

Actual dispatch classification and the cached-falsity NIP branch are checked in [`ArithmeticControlDispatch254.lean`](../../Lean/BusyBeaver/ZFC/ArithmeticControlDispatch254.lean). All internal AC values split into 0, 1, 2, c+3 and enter the actual MP/DROP/NIP/AX branches with exact 1/2/3/3 logical instruction clocks and whole-file effects. Cache=1/scratch1=0 NIP halts in seven instructions, or ten including AC=2 classification; the other unused fields remain arbitrary. Existing positive-clock transport gives existential halting from the corresponding prepared binary entry, not a ten-step binary or blank-start claim. The focused audit passed 14 ordered probes and 18 callers, standard axioms only, with zero warnings; the first failed source attempt is retained. See [the scoped note](arithmetic_control_dispatch254.md), [verification](results/arithmetic-control-dispatch254-verification.json), [history](results/arithmetic-control-dispatch254-history.json), [independent review](results/arithmetic-control-dispatch254-review.json) and [publication record](results/arithmetic-control-dispatch254-publication.json). Remaining branch effects, the complete internal interpreter/Enum connection and the PA endpoint remain open.

The actual NIP nonfalsity comparison/cache-clear phase is checked in
[`ArithmeticControlNip254`](arithmetic_control_nip254.md): cache0 takes eight
logical instructions and cache=c+2 takes `2*c+8`, for arbitrary internal c.
Both reach the actual stack-pop entry with cache0 and preserve the other fields;
classification from AC2 is also composed. The WS unpair/pop body remains a
separate obligation, so this is not yet the complete internal NIP or L2/Enum
connection. Source/audit, exact verification, all attempts, and the unbuilt
default-path preflight are recorded separately under `results/arithmetic-control-nip254-*`.

[`ArithmeticControlUnpair254`](arithmetic_control_unpair254.md) checks the actual
WS unpair and complete literal NIP control branch for all internal values in
IΣ1 models: cache1 halts; otherwise cache:=first(WS),WS:=second(WS), then the two
literal breaks return to fetch. Both scratches start at0 and all other file
fields are preserved; the AC2 dispatcher composition is included. The generic
shape has explicit source/target physical bindings and disjointness. First
source/audit check passed18/22 with zero warnings and standard axioms only.
Exact evidence/history, independent reviews, and the unbuilt default-path
preflight are separate; the complete L2/Enum and PA machine equivalence remain
open.

[Internal pairing and its actual DROP/MP occurrences](arithmetic_control_pair254.md)
now have terminating contracts for all internal files in IΣ1 models. Pairing
clears scratch1 and TW, adds their Cantor pair to scratch2, and preserves the
remaining fields. Both literal occurrences are bound to actual controls; the
complete DROP/MP instructions need further composition. The source and audit
passed 13 probes and 18 callers with standard axioms and zero warnings. Exact
evidence, all three attempts and the unbuilt default preparation are preserved
in the matching `results/arithmetic-control-pair254-*` records.

The [complete actual DROP contract](arithmetic_control_drop254.md) now composes
those helpers through the literal cache restore and return to fetch. For all
internal files in IΣ1 models with both scratches zero, TW becomes the old cache
and WS becomes the Cantor pair of old TW and WS; other fields are preserved.
Its AC=1 dispatcher composition also clears AC. The check passed 12 probes and
18 callers with standard axioms; eleven unused-simp source warnings remain.
Both attempts, exact evidence and independent review are recorded. Complete
MP/AX, interpreter-to-Enum and the final PA equivalence remain open.

The [actual MP destructive comparison](arithmetic_control_compare254.md) now has
an exact all-internal logical clock: `3*a+2*distance(a,b)+2`, where `a` and `b`
are the original scratch1 and cache. It clears both fields, preserves every
other register, and enters the actual success push exactly on equality;
otherwise it returns to fetch. The first source/audit check passed 14 axiom
probes and 18 callers with standard axioms and no warnings. The full MP
constructor and success-push composition remain open.

`ArithmeticControlParamPush254` now proves both actual MP parameter pushes and the complete comparison-to-fetch tail in every model of IΣ₁. Each push requires scratch1=scratch2=0, sets TW to param1 and WS to cantor(old TW, old WS), and preserves every other field. The copy/restore sub-block takes exactly 7*param1+2 logical steps. The tail requires only scratch2=0 and returns to fetch in both comparison cases. The first guarded source/audit check passed 12 axiom probes and 22 callers with no warnings; the short unpair and constructor sequence needed for full MP remain open. See [the proof note](arithmetic_control_param_push254.md).

`ArithmeticControlUnpairCore254` proves the actual short MP unpair and its composition with the initial parameter push in every IΣ₁ model. Entry6367→6404 restores the original WS, puts old TW in scratch1 and param1 in TW, and preserves all other fields under clean scratch registers. The source passed; one audit projection was repaired and the audit-only continuation passed 12 probes/18 callers with zero warnings, reusing the originally recorded source object without rebuilding it. Full MP's constructor middle remains open in this module. See [the proof note](arithmetic_control_unpair_core254.md).

`ArithmeticControlMP254` now proves the complete actual MP branch and its AC=0 dispatch composition in every IΣ₁ model under clean scratch registers. Success sets TW to param1 and pushes the required zero filler on WS; failure clears TW and preserves WS. Both cases clear cache and preserve the remaining fields. The repaired source and unchanged audit passed 12 probes/22 callers with zero warnings; the original failed source attempt and scoped independent reviews are retained. AX and the complete internal interpreter/Enum/PA endpoint remain open. See [the proof note](arithmetic_control_mp254.md).

The [actual AX prefix](arithmetic_control_ax_prefix254.md) now checks its first
parameter push and opcode classifier in arbitrary IΣ₁ models, preserving the
whole register file with the specified updates and positive clocks. Seven
theorem audits and eight typed callers pass with no warnings. The complete AX
bundle and interpreter-to-scheduler comparison remain open; its inherited
binary relation still concerns the earlier 252-state implementation.
