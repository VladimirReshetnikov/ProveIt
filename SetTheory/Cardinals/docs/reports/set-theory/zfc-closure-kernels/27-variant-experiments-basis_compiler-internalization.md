# From the finite-refutation endpoint to a theorem of ZFC

Audit date: 16 October 2026.  The source pin throughout this note is
`jeff87654/busy-beaver@c132d7eae8158cd3a9850ea3eb7251158c3dd821`, the merged
254-state development.  The public 253-state pull request changes the last
machine-simulation part of the chain and reuses the same program, logic, and
set-theory parts.  Its status should be described separately.

## 1. Exact claim and the distinction that matters

Let `M254` denote the literal binary transition table, started in its prescribed
initial state on the all-zero two-way infinite tape.  Fix a standard effective
presentation of ordinary ZFC, including Foundation, and an annotated finite
proof predicate `Prf_ZFC(p, bottom)`.  Put

\[
\operatorname{Con}(\mathrm{ZFC})\;\equiv\;
 \forall p\in\omega\;\neg\operatorname{Prf}_{\mathrm{ZFC}}(p,\bot),
\qquad
\operatorname{NH}(M)\;\equiv\;
 \forall t\in\omega\;\neg\operatorname{HaltTrace}_{M}(t).
\]

The desired ordinary mathematical theorem is

\[
\mathrm{ZFC}\vdash
 \operatorname{NH}(M254)\leftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\tag{1}
\]

The existing Coq endpoint, by itself, is a theorem of Coq about two finite
derivability predicates.  `Print Assumptions` reporting no axioms does not
turn that theorem into a serialized ZFC derivation.  However, no such general
Coq-to-ZFC translation is necessary for an ordinary mathematical proof of (1).
One specializes the definitions to the concrete finite/countable objects in
this development and repeats the finite-syntax and natural-number inductions
inside ZFC.  The audit below supplies that argument and identifies the actual
source lemmas it uses.  It does not claim that an encoded ZFC proof of (1) is
already checked by the distributed Coq project.

The decisive intermediate assertion is the **uniform** theorem

\[
\mathrm{ZFC}\vdash
 \bigl(\exists t\in\omega\;\operatorname{HaltTrace}_{M254}(t)\bigr)
 \leftrightarrow
 \bigl(\exists p\in\omega\;\operatorname{Prf}_{\mathrm{ZFC}}(p,\bot)\bigr).
\tag{2}
\]

Negating both sides gives (1), by classical propositional logic.  An external
assertion only about standard proofs and standard runs would not suffice;
the quantifiers and the inductions in (2) are those of ZFC.  In particular the
argument is uniform in a proof code or a computation length, rather than a
separate informal verification of each standard instance.

## 2. Coding the objects actually used

ZFC constructs `omega`, finite products and finite sequences of natural
numbers.  Use a tagged finite-tree coding for terms, formulas, derivations,
commands and traces.  The exact bijection is immaterial, provided the tags,
list operations and checking predicates are defined explicitly.  The Cantor
pairing already used in `Codes254.v` is one available choice.

* A formula is a finite tagged syntax tree with natural-number variable
  indices.  The concrete set-theory signature has no function symbols and two
  binary predicates, membership and equality.  A general library `term` is
  therefore just a variable after specialization; the more general finite
  vector constructor does not introduce an infinite object.
* An ND derivation is a finite tree whose nodes record the inference tag,
  conclusion, finite context and immediate subderivations.  The constructors
  `II`, `IE`, `AllI`, `AllE`, `ExI`, `ExE`, `Exp`, `Ctx`, conjunction/disjunction
  rules and `Pc` in `FullND.v` give an explicit recursive checker.  The
  de Bruijn shifts in `AllI` and `ExE` are syntactic list/formula operations.
* A use of a theory axiom carries a finite annotation identifying the base
  axiom, or the schema matrix and the number of universal closures.  For
  `SIR`, these are the constructors of `S0` plus `ax_ir`; for `ZFc`, they are
  `ZF0_base`, `ZF0_sep`, `ZF0_rep`, and infinity.  Checking the annotation and
  `closedf` is a finite syntactic computation.  Thus the use of an inductive
  predicate `T : form -> Prop` in the Coq statement causes no undecidable
  membership oracle in the arithmetized proof checker.
* The library's `tprv T phi` is explicitly
  `exists A, (forall psi, In psi A -> T psi) /\ prv A phi`.
  Because `A` is a finite list, the membership evidence can be attached to
  its entries.  This is exactly a finite annotated proof from `T`.
* A `thm254` derivation is a finite tree of `T_true`, `T_mp`, `T_gen`, the
  eight axiom constructors, and the guarded bundle constructor.  Its labels
  are natural-number formula codes; they need not be injective syntax codes.
* An enumerator state is the six-tuple of naturals `(pl,np,tw,ws,d,h)` in
  `Enum254.v`.  A command is one of `CMP x`, `CDROP`, `CNIP`, or `CAX c x y u`.
  Runs and command lists are finite sequences.
* `RM.v` presents registers as `nat -> nat`.  In the concrete program only
  nine registers are read or changed, and all others start at zero.  Replace
  this presentation by a nine-tuple, proving the agreement invariant by
  induction on the run.  Program nodes form a fixed finite table; the
  instruction pointer is a finite bit list.  Alternatively the full
  function space is a set in ZFC, so even retaining the generic presentation
  requires no universe assumption.
* BusyCoq's tape uses two coinductive streams and a scanned symbol.  In ZFC
  these are functions from `omega` to the finite symbol set.  For a blank-tape
  trace of length `n`, only a finite interval of radius at most `n` can have
  been visited.  A finite interval, state and head position therefore suffice
  for a recursive trace checker; induction on `n` proves its agreement with
  the stream presentation.

These constructions use sets of finite strings/trees and ordinary function
sets.  No inaccessible cardinal, Grothendieck universe, model of the whole
Coq type theory, or satisfaction predicate for the set-theoretic universe is
needed.  Generic `Type` parameters are specialized before this argument; we
do not interpret an arbitrary Coq universe in ZFC.

Sources: [Core.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/stdzf/vendor/undecidability/theories/FOL/Syntax/Core.v),
[FullND.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/stdzf/vendor/undecidability/theories/FOL/Deduction/FullND.v),
[S_def.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/settheory/S_def.v),
[Std_iface.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/stdzf/coq/Std_iface.v),
[RM.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/tm/RM.v),
[BusyCoq TM.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/stdzf/vendor/busycoq/TM.v).

## 3. Uniform proof-to-trace implication

Work inside ZFC and suppose `p` is an annotated ZFC refutation.  The following
are transformations of finite derivations and finite computations.

### 3.1 Ordinary ZFC refutation to an SIR refutation

First translate the chosen ordinary ZFC proof presentation to the library's
closed-schema ND presentation.  Equality as a logical symbol versus equality
axioms, named variables versus de Bruijn indices, universal closure, and the
two conventional infinity axioms are handled by finite syntactic proof
translations.  This is a conservative change of presentation, not an appeal
to the consistency or soundness of ZFC.

The endpoint named `ZFC` in `E2E254.v` is `ZFc + ax_ac`; `ZFc` itself omits
Foundation.  To cover ordinary ZFC with Foundation explicitly, use
`Z_main.ZFCReg_equicons`, whose left side is
`((ZFc + ax_reg') + ax_ac) ⊢TC bottom` and whose right side is
`ZFc ⊢TC bottom`.  Its proof uses `ac_relcon` and
`Link.regularity_relcon_std`.  The converse is direct weakening.

Now `S_main.ZF_to_S0` sends a `ZFc` refutation to an `S0` refutation, and
`ZF_to_S` weakens it to `SIR`.  The substantive step is `qt_tprv`, applied to
the fixed bisimulation formulas `Eqv` and `Mem`.  `qt_prv` is an induction on
the ND derivation, replacing each atomic formula by its fixed interpretation
and commuting that interpretation with substitution.  Each ZF axiom instance
has an S0 derivation supplied by `S_ZF0inf`.  A finite-list lemma collects the
finitely many assumption derivations and cuts them into the translated proof.
For bottom the translated conclusion is again bottom.

The quotient construction is performed in the object theory's formulas and
derivations.  It does not require that an actual universe of all S0 sets form
a set, nor that ZFC prove S0 consistent.  Its arithmetization is precisely an
induction transforming the input proof tree and its schema-instance labels.

Sources: [S_main.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/settheory/S_main.v),
[S_qt.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/settheory/S_qt.v),
[Z_main.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/stdzf_r3/zfc/Z_main.v),
[Link.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/stdzf/regcon/Link.v).

### 3.2 SIR refutation to a code-level derivation

`Comp_Bundle254.SIR_to_thm` converts a finite SIR refutation to `thm254 1`.
Its proof factors through `SIR_TB` and `TB_to_thm`; `SIR_TB` treats the finite
base cases, CP, each GIC schema instance, and IR.  `TB_gic` is uniform in the
input formula and closure length.  Fresh variables are chosen by explicit
arithmetic bounds on finite formulas.  `Comp_Prop254.lprov_thm` and the
associated translations supply the logical proof induction.

This part must be retained as written: the numeric code is intentionally
noninjective at special values.  In particular `1 = wel 0 0` and
`0 = wim 0 0`.  The source proves logical compatibility, rather than assuming
injectivity of a free syntax algebra.  `Wff254.D` is a fuelled decoder
`Df (S n) n`; stability and correctness follow from induction and the strict
decrease of positive subcodes.  `Sound254.D_fr_self` proves that variable `c`
is not free in `D c`; the separate guards `c != a` and `c != b` remain essential.

Sources: [Comp_Bundle254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/logic/Comp_Bundle254.v),
[Comp_Prop254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/logic/Comp_Prop254.v),
[Wff254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/logic/Wff254.v).

### 3.3 Code-level derivation to a halting enumerator run

`L1_Comp254.compile` is an explicit structural induction on a `thm254`
derivation.  It produces a finite command list `L` with block contract

\[
 \forall T,w\quad
 \operatorname{exec}(L,(T,w,0,0))=\mathrm{None}
 \ \lor\ 
 \operatorname{exec}(L,(T,w,0,0))=\mathrm{Some}(X,w,0,0).
\]

The induction has an explicit case for each constructor: `DISCARD` for
truth, `mpb` for modus ponens, `genb` for generalization, and `leaf`/`leafB`
for axioms and the guarded bundle.  For `X=1`, `program_halts` prefixes `START`
and appends `SUFFIX = [CDROP; CNIP; CNIP]`, obtaining a command list that
halts from **every** retained work-register state.  This matters because
the enumerator does not erase the entire work state between candidate numbers.

`enc_fields` and `enc_tail` encode that list as one natural number `N`.
`step_read` proves that one decoded command has the prescribed effect.
`run_tail` is a list induction, and `run_first` handles the first command.
The candidate-scheduling argument is explicit:

* `step_pl` bounds the next residual stream by its predecessor, while the
  candidate counter stays fixed until the residual is exhausted;
* `drain k` is induction on the natural bound `k` for that residual;
* `reach N` is induction on the candidate number and proves that the machine
  either already halted or reaches candidate `N` with `pl=0`;
* `enum_complete` composes those facts with the constructed command list.

Thus ZFC proves uniformly that every encoded `thm254 1` derivation has some
finite halting enumerator trace.  No claim about an asymptotic bound on that
trace is needed.  In particular this note makes no unproved claim that the
whole reduction has been audited down to primitive recursive arithmetic.

Source: [L1_Comp254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/logic/L1_Comp254.v).

### 3.4 Enumerator run to a literal TM run

`L2Root254.root_sem` proves the register-level implementation of one
`enum_step`; `root_step_gen`, `root_step_det`, and `iter_halts_dag` relate
iterations to finite enumerator runs.  `Main254.prog254` combines these with
the checked finite DAG bisimulation `p254_dag` and the equivalence of path
and structured register-machine semantics.  It also accounts for the initial
state exactly: the blank-tape boot lands at `nextproof=2`, and `s0_step1`,
`s0_step2`, `enum_s2` prove that the zero enumerator state reaches that state
after its first two harmless commands.

Finally `Sim.reach` is induction on the number of register steps.
`inv_step` supplies a positive finite TM run for each register step;
`inv_halt` supplies the final halting run.  `Main.tm254_rm` composes those
with the verified blank-tape boot.  Finite trace concatenation is a list
operation, so the result is a witness to `HaltTrace_M254(t)` in ZFC.

Sources: [L2Root254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/prog/L2Root254.v),
[Main254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/prog/Main254.v),
[Sim.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/tm/Sim.v),
[Main.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/tm/Main.v).

## 4. Uniform trace-to-proof implication

Now work inside ZFC with an arbitrary finite blank-tape halting trace.

`Main.tm254_rm` obtains a register-machine halt from this trace.  The
potentially subtle step is not an appeal to an infinite simulation: BusyCoq's
`progress_halts` uses **strong induction on the finite number of TM steps
remaining until halt**.  At each invariant boundary either the RM has halted,
or `Sim.inv_step` advances the TM by at least one step while restoring the
invariant.  The remaining length therefore strictly decreases.  Positivity
is explicit in `T -->+ T'`; a zero-step stuttering relation would not suffice.
`inv_next` and program well-formedness rule out treating an invalid decoder
walk as a successful logical halt.

The program-layer equivalence yields a finite enumerator halt.
`L1_Sound254.Inv` says that the current formula, cached formula and every
decoded stack entry have `thm254` derivations.  `good_0` accounts for the
infinite zero tail of the numeric stack encoding.  `good_push` and `good_pop`
maintain the stack assertion; `Inv_step` has four finite command cases;
`Inv_run` is induction on the run length.  At a halting `NIP`, `halt_step`
extracts the derivation of the cached code `1`.  In the numerical proof
presentation this induction attaches the actual finite derivation trees to
the current and cached entries and to the finite nonzero stack prefix.

`Sound254.thm_to_SIR` next produces an SIR refutation.  `thm_V` is induction
on the code-level derivation.  It treats the special codes via proved
equivalences `D_wim_E` and `D_F`.  The final step uses IR to turn the derived
self-membership `v0 in v0` into bottom.  This is why deleting IR merely
because `S0` is equiconsistent would break the existing alias-aware bridge.

`S_sound.S_to_ZF` sends that refutation to a `ZFc` refutation.  Its
intermediate `holdsL(a)` is **a finite-proof statement**, not a semantic
truth assertion about a proper class: it supplies a finite list of ZFR
axioms from which the relativization of `a` to the fixed formula `Lform`
has an ND derivation.  `L_cp` supplies the fixed CP proof and `L_gic` supplies
proofs uniformly in the GIC matrix and closure length.  In `L_gic` the
needed support is the explicit finite list
`oc_insts n (gicQ phi) ++ sepL_insts n (gicS phi)`.

`S_to_ZFR` traverses the finite input assumption list, uses `MinZF.collect`
to concatenate the finitely many supports, and applies the syntactic
relativization lemma `transfer` to the finite derivation.  It then eliminates
the auxiliary existence premise within ND.  `Link.regularity_relcon_std`
removes the temporary Foundation axiom.  Weakening, followed by the fixed
proof-presentation translation, gives an ordinary ZFC refutation.

The constructibility and reflection mathematics in these files proves
**object-level proof templates for each formula instance**.  It neither
requires an inaccessible cardinal nor asserts that ZFC can recognize all its
own axioms as true in a set model.  Confusing those two claims would turn an
ordinary relative-consistency proof into a much stronger and unnecessary
assumption.

Sources: [L1_Sound254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/logic/L1_Sound254.v),
[Sound254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/logic/Sound254.v),
[S_sound.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/settheory/S_sound.v),
and the TM, program, and regularity files linked above.

## 5. Why this is a ZFC proof and what it does not certify

Every induction just described is on a natural number, a finite list, a finite
syntax tree, or a finite derivation tree.  Structural induction on the last
two follows in ZFC by assigning a natural height and using induction on that
height.  All recursive definitions have a set-sized domain; finite proof
trees, finite traces and their encodings are sets.  Quantification over
contexts, formulas, registers or streams is over sets after specialization.
The source's syntactic proof transformations can therefore be expressed as
relations on these codes, and the same induction proves their totality on
valid inputs in ZFC.  We may also choose a canonical output by searching for
the least verified output code; the internal existence proofs prove that
this search terminates on valid inputs.  No complexity bound is implicit in
that observation.

Composing Sections 3 and 4 proves inside ZFC

\[
\begin{aligned}
&\forall p\in\omega\bigl(\operatorname{Prf}_{\mathrm{ZFC}}(p,\bot)
       \Rightarrow\exists t\in\omega\operatorname{HaltTrace}_{M254}(t)\bigr),\\
&\forall t\in\omega\bigl(\operatorname{HaltTrace}_{M254}(t)
       \Rightarrow\exists p\in\omega\operatorname{Prf}_{\mathrm{ZFC}}(p,\bot)\bigr).
\end{aligned}
\]

This proves (2) and hence (1).  Changing to another usual recursive proof
presentation of ZFC preserves the consistency sentence by the same explicit
finite proof translations.  This statement needs no assumption that ZFC is
consistent.  Assuming consistency is needed only for the additional external
conclusion that the machine really does not halt and, under the usual
derivability hypotheses, that ZFC cannot prove that particular non-halting.

The source's short endpoint is
`E2E254.zf254_halts_iff_ZFC`, obtained from `tm254_rm`, `prog254`, `L1_254`,
`bridge254`, and `S_ZFC_equicons`.  The paper-level argument above augments
its description by explicitly accounting for internalization and ordinary
Foundation-inclusive ZFC.  A serialized ZFC derivation or a formally checked
arithmetization of the whole development would be a useful further artifact;
it is a different deliverable from the existing Coq finite-refutation theorem.

Sources: [Bridge254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/logic/Bridge254.v),
[L1_254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/logic/L1_254.v),
[E2E254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/e2e/E2E254.v).

## 6. How to apply the argument to a changed compiler experiment

Replacing the Lukasiewicz schema by a complete K/S/Peirce or K/B/Peirce basis
is a logical change that can be justified by finite, substitution-uniform
propositional derivations in both directions.  Such derivations survive the
numeric aliases because substituting any chosen binary implication operation
in an exact propositional proof preserves each MP step; injectivity is never
used.  They prove equality of the two code-level theorem sets after the
remaining constructors are retained.

However, removing `u` from `CAX c x y u` changes the proof-stream grammar and
the stack gains two additional axiom rows.  A correct modified enumerator
needs `fields`, `step_read`, `ax_stack`, `DISCARD`, `leaf`, `genb`, and the
corresponding stack depths updated together.  The same list/derivation and
candidate-drain arguments then prove its soundness and completeness.

A finite RM bisimulation certificate between a directly emitted modified
source program and its rebracketing certifies only that pair of RM programs.
It cannot be described as a bisimulation to the original `p254`, whose
stream consumption is different.  Nor does the existing `tm254_rm` theorem
apply to a newly generated transition table merely because it came from the
same Python compiler.  The table still needs a verified simulation theorem
(or an independently established paper-level compiler theorem specialized
to that table).  The exact theorem required for a new candidate is therefore

\[
 \mathrm{ZFC}\vdash
 \operatorname{Halt}(M_{\rm new})
 \leftrightarrow\operatorname{EnumHalt}_{\rm new}
 \leftrightarrow\operatorname{Deriv}_{\rm new}(1)
 \leftrightarrow\operatorname{Deriv}_{254}(1)
 \leftrightarrow\neg\operatorname{Con}(\mathrm{ZFC}).
\]

This separates an established logical basis equivalence from the independent
program and binary-machine implementation obligations, while preserving the
ordinary internalization argument for every link that is actually proved.
