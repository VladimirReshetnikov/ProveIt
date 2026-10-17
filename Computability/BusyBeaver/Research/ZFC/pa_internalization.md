# Internalizing the machine comparison in arithmetic

Research inventory begun 16 October 2026 against
`7b1e56dbc59f746695a7fb375546422f91de3a96`, updated with the explicitly linked
Lean checks below. The full PA equivalence is still open. The represented
checker and actual machine-run evaluator now have PA totality theorems,
described near the end.

The original request requires an equivalence provable in **PA**. The stored
goal record instead says ZFC; the original PA requirement remains our target.
A Lean theorem comparing halting and `BProv` is an ordinary metatheorem until
the intended arithmetic sentence and an object-theory proof are connected to
it. Completing the PA version would also serve the ZFC requirement, after
checking the chosen arithmetic interpretation in ZFC.

The [Choice calibration](choice_calibration254.md) now closes the external
Lean theorem for the literal 252-state machine: blank nonhalting iff Con(ZFC).
It uses Choice in L and external first-order completeness. This discharges the
external consistency comparison; it does not implement the represented proof
translations or prove their correctness for every internal code in every PA
model. Those obligations below remain.

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
representing that computation and its correctness inside PA remains open.

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
numeric operands may be internal model elements. The compiler history
remains the next step.

The simpler compiler design keeps an unconditional history of raw compiled
words and uses the already checked `ArithmeticHistory254.value` once as the
public validity gate. Invalid public inputs return empty word 0. This avoids
duplicating the twelve-rule validator in a paired history. For an accepted
parent, the validator's internal recurrence must imply acceptance of the
actual MP/GEN children; only then may their raw words be used with the
validity-conditional execution induction. The
[internal history recurrence](arithmetic_history_recurrence254.md) now proves
this MP/GEN validity inversion, including the actual child bounds and
whole-tail GEN convention. The word history and execution contract remain
to be implemented.

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
