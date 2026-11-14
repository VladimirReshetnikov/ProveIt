# Proof audit and transferable ideas

Pinned repository: `VladimirReshetnikov/ProveIt`, commit
`1c9524d8bf2e0a27b9a16ff622359927f536e663`.

This audit inspected current status documents, selected proof sources, and the
delivered PA194 calibration manuscripts. It did not perform a fresh build of
the Lean dependency closure. Statements about successful Lean builds below
are the repository's recorded results; the new command checker was run here.

## 1. The requested premise is stronger than the current baseline

The current PA project README explicitly states that neither
machine-specific iPRA direction is established for the primary PA194 table,
the original PA195 table, or the imported PA196 table. This is a substantive
qualification, not merely a complaint that a particular proof-assistant file
is missing. The primary PA194 manuscript's displayed theorem is a PA
provability theorem. Its calibration section concludes a PA-verifiable
equivalence between the source halting sentence and the existence of a PA
refutation. The manuscript does not state an iPRA proof of that equivalence.

An ordinary mathematical proof in iPRA would meet the user's request without
a new Lean development. The issue is that the supplied argument is explicitly
carried out in PA, and some inherited compiler correctness proofs use full
PA induction. Lowering those inductions is an additional mathematical task.
Conversely, the audit does not prove that lowering them is impossible.

Primary sources:

- [Current PA status](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/PA/README.md).
- [Primary PA194 calibration](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/report/calibration.tex).
- [Inherited PA195 calibration](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/report/reference/original_pa195_calibration.tex).

## 2. The exact remaining arithmetic boundary

The generic endpoint is already available. For a literal transition table T
and halt label h, the repository defines `Calibrated T h` to mean that in
**every** model V of IΣ₁, internal PA provability of falsum is equivalent to
the internal execution of T reaching h at some V-valued time. Both proof
codes and times may be nonstandard.

`ConPAUnconditional.machine_endpoint` discharges the generic PA witness
certificate and concludes the native standard-iPRA consistency equivalence
from `Calibrated T h`. Despite the module name, the machine calibration is
still a premise. No transition table is shown to satisfy it in that package.

The transfer uses conservation of IΣ₁ over the appropriate PRA presentation
and the Gödel–Gentzen interpretation. It does not require an intuitionistic
principle turning double-negated existence into existence. The requested
conclusion concerns the negations of the two Σ₁ predicates.

| Layer | Current status at the pinned head | What it does not establish |
| --- | --- | --- |
| Exact PA194 table and finite-run source simulation | Extensive standard-natural Lean results and physical certificates | Uniform simulation at arbitrary nonstandard model times |
| Exact arithmetic machine clock | Fixed codes and model-uniform clock/run equations | Identification with the whole source scheduler |
| Numerical calculus to modeled scheduler and converse | `PA194ModelFairness.halts_iff_provable` is checked for models with IΣ₁ reducts | PA-refutation translation or physical-machine comparison |
| Modeled scheduler halt to PA refutation | The distinct and equal gate cases are discharged; a modeled halt internally refutes PA | The corresponding result for the literal table |
| Actual iPRA consequence for the modeled scheduler | `Con(PA) → ¬Halt(modeled scheduler)` is checked | Either literal-table iPRA direction |
| PA refutation to the numerical calculus | Internal syntax, LK transport and some axiom suppliers are available | The complete uniform PA axiom supplier and the model-level numerical compiler |
| Generic all-model calibration to iPRA | Transfer and the PA witness certificate are available | The machine-specific calibration premise |

Sources:

- [Generic machine endpoint](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/PA/isigma1-machine/README.md).
- [IΣ₁ transfer](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/PA/isigma1-transfer/README.md).
- [Modeled scheduler equivalence](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/PA/pa194-model-fairness/README.md).
- [Completed modeled-scheduler soundness direction](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/PA/pa194-distinct-gate-sound/README.md).

Some older local READMEs still describe the gate or the final fairness
instantiation as open; the newer aggregate and dedicated completion notes
record their discharge. The table above follows those completion notes.

## 3. Why the existing PA proof cannot simply be relabeled iPRA

The forward compiler audit identifies concrete uses of
`InductionScheme.succ_induction (C := Set.univ)` in the imported PA196
development. The budgeted derivation invariant quantifies over smaller
derivations and all environments. The fuel invariant quantifies a table
bound and a table-wide realization condition. Neither displayed invariant
has been proved Σ₁. Their full-PA proofs do not establish the corresponding
claim in every IΣ₁ model.

An earlier full-PA substitution-translation proof has since been replaced
by an IΣ₁-model proof. This is real progress, but it does not supply the
entire axiom supplier or numerical compiler. The current PAeq supplier
still takes both the finite arithmetic-axiom proofs and the arbitrary
internal induction-schema proofs as hypotheses.

It is also insufficient merely to observe that a program computing a
proof translation is primitive recursive. Its totality then belongs to
PRA, but its **correctness on every valid encoded proof** is an additional
universal arithmetic assertion. That assertion must be proved in the weak
base, for example by explicitly checkable local transformations and a
quantifier-free or Σ₁ coded-history invariant.

There is no intrinsic obstruction from the fact that the generated object
proofs contain full PA induction. A weak metatheory can construct and check
a PA proof containing an arbitrary PA induction instance. It need not
accept the truth of that instance. The difficulty is the uniform syntactic
correctness proof, not the strength of the object proof whose bytes are
being produced.

Sources:

- [Forward induction audit](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/PA/pa194-forward-audit/README.md).
- [Conditional PA axiom supplier](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/PA/pa194-paeq-pa-supplier/README.md).
- [Ordinary-number Foundation LK compiler](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/PA/pa194-foundation-lk/README.md).

## 4. New AX11QH5 command result

The combined machine uses precisely the existing QH5 coefficient-five
numerical calculus D5. Its new feature is an eleven-entry AX operation
that pushes the guarded gate and then runs the existing no-push MP body.
This requires a fourth AX operand z, with exact effect

    A(c,x,y,z)(t,w,d,h) = (0,[q0,...,q9,t;w],z,0).

SHIFT halts iff the cached formula h equals one. The command compiler must
therefore end a refutation word with POP, not with a plain SHIFT. The
counterexample is already the zero stack: SHIFT(1,0,0,0)=(0,0,0,0).

The new symbolic checker passes on the exact delivered grammar and nodes.
It checks the full emitter in a free constructor algebra, the changed
logical head, the multiplier, both guard branches, arbitrary fourth
operand, four-field decoding, all selectors, generalization, MP framing,
and zero Cantor-stack aliases. It independently binds source instructions
25–47 and proves the precise candidate convention:

    seed(N,L) = N if L=0, else L-1;
    N' = N+1 if L=0, else N.

Thus a fresh candidate is b(command,e(tail)) without an outer +1, while a
positive continuation is e(command::tail)=1+b(command,e(tail)). The actual
clean source frame has N=2 and L=0. The prefix regression check covers 1,681
pairs (N,L); its universal proof is the copy/restore and Cantor-unpair
invariant in the TeX article, not an extrapolation from that grid.

The proof fragment provides an explicit Σ₁ tracked-executor argument for
the high-level scheduler equivalence with D5 refutation. AX increases a
virtual stack height by eleven, SHIFT consumes one, and MP preserves it.
The witness to a successful proof word consists of one empty-base tracked
execution with no underflow. A separate frame lemma makes it valid over
every carried base stack. This removes an implicit ∃word ∀stack invariant
that would be too strong for direct Σ₁ induction.

The exact final theorem remains conditional on (i) internalizing the
literal-machine/source simulation and (ii) the IΣ₁ calibration of D5 to PA
refutations. The command-level result does not assume PA consistency and
does not manufacture the missing calibration.

Files prepared for integration:

- `analysis/proof_audit/ax11h/ax11qh5_preservation.tex`
- `analysis/proof_audit/ax11h/check_commands.py`
- `analysis/proof_audit/ax11h/commands_receipt.json`

## 5. Concrete lessons from the ZFC work

**Rotate without reducing the source DAG, then seek a new fold.** The
236-state ZFC construction keeps 224 distinct decoder subtrees while
reassociating three closed chunks of 245, 160 and 132 instruction leaves.
It changes four decoder rows and then obtains a previously unavailable
history-sensitive merge. Source size alone would have ranked this move as
neutral and missed the actual saving. The same search objective applies
to PA194: evaluate the *simultaneously folded literal table* after each
source-preserving rotation, not just the number of source nodes.

**Preserve whole configurations in local folds.** That ZFC fold merges
roles whose preceding writes leave distinct bits immediately to the left
of the head. Its four small blocks restore the whole tape and head,
with only the state mapped. The incoming-history property is established
for every tape, and the simulation blocks have positive length. This
is a clean basis for a weak-arithmetic relative equivalence. A merge
supported only by several observed blank runs would not provide it.

**Use explicit context-admission hypotheses for source rewrites.** The
checked `RMDagContextSubstitution`/`SourceRotation244` development proves
local loop equivalence for the complete register file and then substitutes
it into an admitted context, preserving restart behavior without assuming
global termination. This is the appropriate pattern for a new PA source
rewrite. Matching leaf words alone does not preserve a structured break's
resolved target. Our AX11 splice likewise requires the exact relocation
of every outside successor and the full extra-operand reader.

Sources:

- [236-state node-neutral rotation and fold](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/ZFC/candidate-rotated236/README.md).
- [237-state composition and exceptional paths](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/ZFC/candidate-composed237/README.md).
- [Checked source rotation/context substitution](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/BusyBeaver/Research/ZFC/source_rotation244.md).

The current 236/237 candidates' READMEs themselves distinguish their
ordinary ZFC-level mathematical calibration from a checked PA endpoint.
Those proof strengths must not be silently imported into this iPRA task.

## 6. Concrete lessons from DiophantineConsistency

**Use a uniform model bridge, then reuse the existing iPRA adapter.**
`Compact44/IPRAOrdinary12.lean` is a useful worked example: its
`PositiveModelBridge` quantifies every IΣ₁ model and states an equivalence
between an internal positive polynomial zero and an internal machine
halt. A simple, explicit x↦x+1 shift then feeds the already proved
native, standard, and equality-only iPRA transports. The PA machine work
now has the analogous generic endpoint, so the best reuse is this proof
architecture and its exact model-level quantifiers.

**Do not trade a machine-specific calibration for a standard-model
Diophantine statement.** A small polynomial for Con(ZFC) is about a
different target theory. For this problem one first needs the PA proof
predicate and its uniform internal reduction. Even a polynomial for the
right predicate needs an evaluator, candidate enumeration, and exact
blank initialization when compiled to a binary TM. An operation count
or variable count alone does not bound the final number of states.

**Account for fixed data.** The 12-variable free-J graph uses a symbolic
tuple including β=2^590069−1. Its iPRA endpoint is about the exact Lean
literal at that tuple; binding a displayed coefficient file is a
separate finite check. A machine design must similarly account for the
procedure that produces its constants from a blank tape. Compact
mathematical notation cannot be treated as a free preinitialized tape.
This is especially relevant to the rejected short-startup approaches in
the PA194 corpus.

Sources:

- [Exact positive-model bridge and three iPRA endpoints](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/DiophantineConsistency/Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean).
- [Exact target iPRA theory](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/DiophantineConsistency/IPRA_AXIOMATIZATION.md).
- [Equation status and coefficient scope](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Computability/DiophantineConsistency/README.md).

## 7. Concrete lessons from ConciseIPRA

**Derive a convenient interface instead of retaining it as primitive.**
The native scalar calculus recovers transport in compound formula
templates from a one-term transport rule, and it recovers a witnessed
progress rule from direct closure. Its one-sided-transport result even
removes literal-zero sources by fixed equation manipulations. The useful
analogue here is to change the emitter or command interface and provide
finite derived gadgets for the old proof operations. The new AX11QH5
proof does exactly this for Pop, Push, selectors, generalization, and MP.

**Keep the target theory separate from the metatheory.** Replacing the
searched PA calculus by the smaller iPRA proof checker changes the
consistency problem. The freedom to use a simpler calculus is available
only with a sufficiently weak, uniform refutation translation to and from
PA. The role of iPRA here is to prove that translation and the machine
simulation; it is not a license to enumerate iPRA refutations instead.

**Compare the relevant compilation cost.** ConciseIPRA measures a
standalone proof checker after code normalization. PA194 state count is
dominated by sharing and history-sensitive binary decoding. A shorter
source word can have a larger distinct-subtree grammar, and a neutral
grammar rotation can enable a state saving. Thus theorem-level
simplification is a source of candidate transformations, but the final
state count must be measured after compilation and simultaneous folds.

Source:

- [Native scalar calculus and derived-interface reductions](https://github.com/VladimirReshetnikov/ProveIt/blob/1c9524d8bf2e0a27b9a16ff622359927f536e663/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md).

## 8. Suggested wording of the research outcome

If no sub-194 construction is obtained and the absolute iPRA calibration
is still open, state that directly. The supportable result is a distinct
194-state AX11QH5 candidate, with exact source binding, complete symbolic
physical certificates, a corrected four-field proof-word compiler, and
an explicit description of the remaining iPRA premises. It must not be
presented as satisfying the full requested Con(PA) property unconditionally.

The new source semantics are materially different: AX consumes an extra
operand, leaves zero visible, pushes the guarded gate as an eleventh
entry, and continues through MP. This affects recurring command behavior;
it is more than state renaming or a different initialization trace.
