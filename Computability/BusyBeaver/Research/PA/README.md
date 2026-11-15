# PA consistency machines

This directory contains machine tables, imported research, and Lean proofs
concerning small Turing machines associated with the consistency of Peano
arithmetic, `Con(PA)`. The current goal is a Lean proof of
`iPRA ⊢ Con(PA) ↔ ¬Halt(M)` for the primary 194-state candidate, followed
by the other 194-, 195-, and 196-state consistency candidates. The machines start
on a blank two-way binary tape; state counts exclude the halt state.

The `pa194/` and `pa195/` directories contain the principal machine-specific
arithmetic developments. Supporting packages are grouped by candidate under
[`pa194-work/`](pa194-work/) and [`pa195-work/`](pa195-work/). The `docs/`
directory holds the delivered research packets.

**Status:** Neither machine-specific direction of this equivalence has yet
been established in iPRA for PA194, the original PA195, or the PA196 candidate. In
particular, a Lean theorem about ordinary finite runs, a Python certificate,
and a conditional iPRA theorem are not themselves an iPRA proof of the
consistency equivalence. See the individual READMEs for assumptions, exact
statements, and reproducibility instructions.

## Primary 194-state candidate

The target table is `pa194_conpa/construction/tables/pa194.tm` in
[the PA194 research packet](docs/pa194_conpa_2026-11-13/).
It has 194 working states, start state 0, halt label 194, and 388 transitions.
Its SHA-256 is
`4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`.
The packet reports a PA-provable consistency equivalence and proposes a
second 194-state table; it does not provide an end-to-end Lean proof or an
iPRA proof. The primary table is a seven-fold quotient of a 201-control
parent with a ten-entry source interface. The arithmetic and simulation
results below provide reusable methods but do not by themselves establish
the PA194 equivalence.

The [14 November incoming reports](INCOMING-2026-11-14.md) include another
194-state candidate and do not report a verified sub-194 blank-start machine.

[The PA194 arithmetic endpoint](pa194/ipra/README.md) binds the pinned table
to a standard-model halting sentence and constructs a conditional iPRA
equivalence. [The explicit machine codes](pa194/ipra/machine-code/README.md)
include a clock whose decoded execution is characterized in every candidate
PRA model. [The quotient proof](pa194-work/pa194-dense/README.md) connects the 201-control
parent and dense PA194 table for all standard finite runs; [the zipper bridge](pa194-work/pa194-zip-bridge/README.md)
connects blank-tape halting to the literal machine used by the arithmetic code.
[Source coverage](pa194-work/pa194-coverage/README.md) reduces the source-to-parent
simulation to a finite set of Lean checks; all 3,673 sites and the aggregate
have passed. [The clock/source composition](pa194-work/pa194-clock-source-complete/README.md)
connects the initialized source program to the exact machine clocks in
standard finite-run semantics. [The command scheduler](pa194-work/pa194-command-source/README.md)
is equivalent to that source program in standard finite-run semantics, and
[its clock composition](pa194-work/pa194-command-clock/README.md) connects the initial
scheduler state to the machine clocks. Parts of the literal register scanner
are also proved as native iPRA equalities; see the
[source-file engine](pa194/ipra/machine-code/SOURCE-FILE-ENGINE.md). The
[marking](pa194/ipra/machine-code/MARK-ALL.md) box has native iPRA sentences
for each physical position, and the
[marked increment](pa194/ipra/machine-code/INCREMENT-SOURCE.md) and
[marked decrement](pa194/ipra/machine-code/DECREMENT-SOURCE.md) boxes have
them for each logical register. The controller and physical-frame transitions have also been connected for selected
source sites, including a [matched loop through both site-32 branches](pa194/ipra/machine-code/LOOP-AFTER32.md),
the [site-38 zero branch](pa194/ipra/machine-code/SITE38-ZERO-PHYSICAL.md),
and both [zero](pa194/ipra/machine-code/SITE45-ZERO-PHYSICAL.md) and
[positive](pa194/ipra/machine-code/SITE45-POSITIVE-PHYSICAL.md) site-45 branches
in PRA models; a complete reachable-state simulation remains open. Native iPRA
clocked equalities cover the [physical positive loop](pa194/ipra/machine-code/ACTUAL-PHYSICAL-NATIVE.md),
[source fetch](pa194/ipra/machine-code/UNIFIED-FETCH-NATIVE.md),
[decoder](pa194/ipra/machine-code/DECODER-NATIVE.md),
[tag dispatch](pa194/ipra/machine-code/DISPATCH-TAG-NATIVE.md), and the
[site-31 physical increment](pa194/ipra/machine-code/SITE31-NATIVE.md). A
[native iPRA equality for the site-31 restore loop and zero exit](pa194/ipra/machine-code/SITE31-RESTORE-EXIT-NATIVE.md)
covers the model-length physical loop and its transition to site 34. The complete
[fetch/decode/dispatch prefix](pa194/ipra/machine-code/SCHEDULER-BRANCHES-OPEN.md)
is proved model-theoretically under the documented hypotheses. The general
[compiler](pa194-work/pa194-model-logic/FULL-SEPARATION-THEORY.md)
translates refutations of the finite equality-plus-weak-adjunction theory
combined with its classifier-defined parameter-closed separation theory into
modeled scheduler halting in PRA + IΣ₁ models. The classifier-defined standard
separation theory is [identified with the typed Foundation scheme](pa194-work/pa194-model-axioms/TYPED-THEORY.md).
The combined source theory [internally proves its open separation instances](pa194-work/pa194-model-axioms/FULL-SEP-OPEN.md)
for model-valued valid properties under the stated PRA and IΣ₁ assumptions.
[Internal closure and reopening](pa194-work/pa194-model-axioms/CLOSE.md)
also preserve proof existence for model-valued closure lengths. The source theory
[proves ordinal induction for all internally valid properties](pa194-work/pa194-model-axioms/INTERNAL-ORDINAL-FROM-BAD.md)
in each covered PRA model with IΣ₁ arithmetic reduct, including nonstandard
property codes. [Fixed Σ₁ graphs for deterministic ordinal proof codes](pa194-work/pa194-model-axioms/CANONICAL-ORDINAL.md)
now supply open and closed proofs uniformly in the property code, using an
internally least tuple of auxiliary proofs. These are model-level results under
the stated PRA and IΣ₁ assumptions, not native iPRA derivations. The source
theory also [proves successor cancellation for ordinal isomorphism](pa194-work/pa194-model-axioms/ISO-CANCEL-SOURCE.md);
the translated PA induction bridge remains open. A fixed
[universally closed least-point exclusion theorem](pa194-work/pa194-model-axioms/LEAST-EXCLUDES.md)
has an internal proof in the covered models, and a separate
[triple-specialization graph](pa194-work/pa194-model-axioms/CONTEXT-TRIPLE-SPECIALIZE.md)
handles nonstandard indices. The [addition](pa194-work/pa194-model-logic/PAEQ-ADDITION-CODE.md)
and [multiplication](pa194-work/pa194-model-logic/PAEQ-MULTIPLICATION-CODE.md)
code graphs establish syntax. Recursive PAeq [term](pa194-work/pa194-model-logic/PAEQ-TERM-DISPATCHER.md)
and [formula](pa194-work/pa194-model-logic/PAEQ-FORMULA-DISPATCHER.md)
dispatchers have scope preservation under an explicit environment bound. A
[conditional internal refutation compiler](pa194-work/pa194-model-logic/PAEQ-CONDITIONAL-REFUTATION.md)
assumes the quantifier, shift, and theory-axiom suppliers. Its original
root-packet invariant collapses distinct variables and does not supply the
needed domain guards, as explained in the guarded compiler notes. The [guarded identity-packet compiler](pa194-work/pa194-guarded-compiler/README.md)
retains those distinctions; it still requires the nonvariable existential
rule, axiom suppliers and domain inhabitation. Its identity translation is
independent of packet length for valid internal formulas. The
[ordinary PAeq theory now has a uniform classifier](pa194-work/pa194-model-logic/PAEQ-ORDINARY-CLASS.md),
and the [arithmetic induction-axiom supplier](pa194-work/pa194-model-logic/PAEQ-INDUCTION-SUPPLIER.md)
establishes modeled PAeq proof existence for every internal arithmetic induction
axiom, including nonstandard codes. The [finite arithmetic supplier and PA-refutation transport](pa194-work/pa194-model-logic/PAEQ-FINITE-SUPPLIER.md)
are also proved in every arithmetic IΣ₁ model, including for nonstandard proof
codes. There is a formal [classical IΣ₁ proof of `Con(ordinaryPAeq) → Con(PA)`](pa194-work/pa194-model-logic/PAEQ-CANONICAL-CONSISTENCY.md).
The [reflexivity](pa194-work/pa194-model-logic/FORWARD-REFL-ROOT.md),
[zero-not-successor](pa194-work/pa194-model-logic/FORWARD-ZERO-SUCC.md), and
[addition-by-zero](pa194-work/pa194-model-logic/FORWARD-ADD-ZERO.md), and
[multiplication-by-zero](pa194-work/pa194-model-logic/FORWARD-MUL-ZERO.md),
and [symmetry](pa194-work/pa194-model-logic/FORWARD-SYMMETRY.md) suppliers
prove the root-packet translations of those fixed axioms in the source theory
under the stated code bounds. A [normalized identity-packet bridge](pa194-work/pa194-model-logic/IDENTITY-FIXED.md)
now supplies these five fixed translations for the guarded route; the guarded
endpoint still needs to be specialized to those packets. The other fixed
axioms, induction and rule suppliers are still open; so is the unconditional
PAeq-to-source compiler. The [universal formula replacement theorem](pa194-work/pa194-model-logic/PAEQ-UNIVERSAL-FORMULA-CONGRUENCE.md)
supplies modeled PAeq proof existence for arbitrary internally valid arity-one
formulas, including nonstandard codes and nested quantifiers. These existence
results do not supply fixed proof-code transformers.
A proof-code interpretation of PA and the connection to the physical machine
remain open. In standard Lean semantics, [the calculus/clock composition](pa194-work/pa194-calculus-clock/README.md)
proves that either clock reaches 1 exactly when the displayed separate-diagonal
numerical calculus has a finite derivation of contradiction. Its calibration
to PA and its internalization in iPRA remain open, as do both machine-specific
consistency reductions.

## Original 195-state candidate

The target table is `pa195_conpa/pa195/pa195.tm` in
[the PA195 research packet](docs/pa195_conpa_2026-11-13/).
It has 195 working states, start state 0, halt label 195, and 390 transitions.
The table's SHA-256 is
`5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455`.
The packet claims a PA-provable consistency equivalence; it does not supply
an end-to-end Lean proof of that claim or an iPRA proof.

- [PA195 arithmetic endpoint](pa195/ipra/README.md) binds the table to a
  primitive-recursive halting test and an iPRA sentence in the standard
  model. Its equivalence theorem assumes two machine-specific classical PRA
  reductions; those assumptions remain open.
- [Quotient and dense-table proof](pa195-work/pa195-dense/README.md) proves in Lean that
  the 202-control parent and the delivered dense 195-state table halt under
  the same circumstances for every complete tape and head position.
  [The zipper bridge](pa195-work/pa195-zip-bridge/README.md) connects blank-tape
  halting to the arithmetic endpoint over the standard natural numbers.
- [Register engine](pa195-work/pa195-runtime/README.md),
  [source entry binding](pa195-work/pa195-source-entry/README.md), and
  [symbolic contract batches](pa195-work/pa195-symbolic/README.md) check parts of the
  parent machine's execution. The entry binding covers one source instruction
  and both branches; the complete source-graph and arithmetic correctness
  connections still need proof.
- [Explicit machine codes](pa195/ipra/machine-code/README.md) develop tape,
  transition-table, and configuration-step functions in the PRA language.
  Their model equations are ingredients for a weak-arithmetic proof, not the
  missing machine/refutation reductions.
- [Diagonal calibration](pa195-work/pa195-calibration/README.md) constructs an
  occurrence code and proves decoder self-freshness in classical PRA,
  including its behavior in nonstandard models. The component codes are
  supplied existentially; the proof-producing PA translation remains open.

## Other machines and related work

[James Chang's imported snapshots](jamesyc-upstream/README.md) contain the
upstream PA196 and PA209 developments. The imported PA196 result includes a
PA proof of the implication from literal nonhalting to PA consistency; this
alone does not establish the converse in PA or either direction in iPRA.
[PA196 versus U208](pa196-vs-u208/ipra/README.md) documents the PA196
arithmetic endpoint, conditional transfers, and the completed PA-refutation
witness certificate. The machine-specific reductions remain open.
[The archive audit](pa196-vs-u208/archive-audit/README.md) inventories related
196-state tables and distinguishes candidates from rejected machines.

[The later PA195 packet](docs/PA195_ConPA_research_2026-11-14/)
contains two further 195-state candidates, `machine_195S.tm` and
`machine_195C.tm`, along with source and physical execution certificates.
They are distinct from the original PA195 table. The packet gives mathematical
and executable evidence, not an end-to-end Lean proof of the desired iPRA
statement.

[The PA195 follow-up packet](docs/pa195_followup_research/)
contains another 195-state candidate, `M195S8`, and a claimed halting
equivalence with the original PA195. It also contains a rejected 194-state
construction. [A later PA194 packet](docs/pa194_new_designs_2026-11-13/)
proposes two other 194-state candidates and claims a PA-provable equivalence.
These packets do not supply an end-to-end Lean proof of the iPRA statement.

[Another PA194 packet](docs/pa194_conpa_2026-11-13_2/)
and [the PA195DC packet](docs/pa195_diagonal_combined_2026-11-13/)
propose additional 194- and 195-state machines respectively. Their reported
PA equivalences likewise do not constitute Lean proofs of the iPRA goal.

The later [radix-family](docs/pa194_radix_family_2026-11-13/),
[PA194J/PA194D](docs/pa194j_pa194d_conpa_2026-11-13/),
and [PA194Q/PA194CSZ](docs/pa194q_conpa_2026-11-13/)
packets propose further 194-state candidates with ordinary mathematical PA
calibrations. They do not report completed Lean proofs of the iPRA equivalence.

## Delivered research packets

[`docs`](docs/README.md) holds the contents of the research packets that were delivered
to `docs/incoming`, one directory per archive, filed as delivered. Its README lists the
packets, the wrapper directory of each archive, and the members that are not placed.
[`docs/MACHINES.md`](docs/MACHINES.md) lists the distinct machines among the tables of the
packets; a table that repeats a kept machine, also with its states renamed, is removed.
The archives themselves are no longer in `docs/incoming`. A script of this directory
that opens `docs/incoming/<archive>.zip` needs that archive restored from the history of
the repository, as `docs/README.md` describes, until it reads the placed files instead.

## Transfer from IΣ₁

[`isigma1-transfer`](isigma1-transfer/README.md) proves, for any bounded arithmetic formula
`δ`, that an `𝗜𝚺₁` proof of `paRefutation 🡘 ∃ t, δ t` gives the iPRA equivalence of PA
consistency and the negation of the mapped sentence `∃ t, δ t`, given the PA witness
certificate. It is independent of the machine and proves no machine equivalence. Its use is
that a machine reduction may be proved in models of `𝗜𝚺₁` instead of models of candidate PRA.
The same directory proves `halt_iff_refutation_of_models`: for an open halting matrix of the
PRA language, the two classical PRA reductions that the PA194 and PA196 assemblies take as
hypotheses follow if halting and the mapped PA refutation agree in every candidate PRA model
whose arithmetic reduct satisfies `𝗜𝚺₁`. Model arguments may therefore assume `𝗜𝚺₁`.

[The PA194 generic-machine bridge](pa194/ipra/machine-code/GENERIC-BRIDGE.md)
identifies its packed clock and the pinned table's arithmetic run at every model
time, including nonstandard times. [The one-way endpoints](pa194/ipra/machine-code/ONE-WAY-ENDPOINT.md)
separately reduce each iPRA implication to its corresponding all-model
machine/refutation implication. Neither of those machine-specific premises is
proved yet; the earlier standard-run source simulation does not supply them.

For the compiler's internal syntax operations, fixed candidate-PRA codes now
have all-model correctness proofs for [source formula shift](pa194-work/pa194-source-formula-shift-code-model/README.md)
and [arithmetic formula closing](pa195-work/pa195-calibration/PA194FormulaAgreement.md).
These cover nonstandard valid formulas in candidate PRA models with IΣ₁
reducts. They are components of the compiler, not a translation of arbitrary
PA proofs or a verification of source execution.

For the direction `Con(PA) → ¬Halt(M₁₉₄)`, a
[conditional source-line theorem](pa195-work/pa195-calibration/PA194SourceLineRefutation.md)
turns an internally valid numerical derivation of code 1 into an internal PA
refutation, provided its seed translations are PA-provable. Model-uniform
proofs cover the six numbered seeds, rho8 and diagonal, as well as modus
ponens and generalization. The guarded gate has since been discharged as
described below; the connection from the physical machine to such line histories
remains open. Separately, the
[machine-store invariant](pa194-work/pa194-machine-store-invariant/README.md) covers the
mathematical command effects using an independent target proof encoding; it
has not been identified with PA provability or the physical controller trace.
The finite codes for [AX](pa194-work/pa194-machine-ax-standard/README.md) and
[SHIFT/MP](pa194-work/pa194-machine-shift-mp-standard/README.md) have also been proved
to reproduce the corresponding standard-natural-number source commands;
those bindings do not establish the nonstandard controller simulation.
The [modeled scheduler iteration](pa194-work/pa194-scheduler-iteration/README.md)
preserves the store invariant for arbitrary model-length runs, and a modeled
halt yields a target proof of code 1. The [target-to-PA bridge](pa194-work/pa194-target-source/README.md)
turns that proof into an internal PA refutation assuming the guarded
gate seed. The [distinct-label endpoint](pa194-work/pa194-distinct-gate-endpoint/README.md)
discharges the equal-label gate case and narrows the premise to the remaining
distinct-label separation tails. The model-length
[universal-opening endpoint](pa195-work/pa195-calibration/PA194OpeningEndpoint.md) is
now identified even for nonstandard codes, and the resulting
[internal induction theorem](pa195-work/pa195-calibration/PA194FullInternalInduction.md)
constructs the required closed induction axiom bodies. General
[internal finite-set separation](pa195-work/pa195-calibration/PA194InternalSeparation.md)
is also checked for arbitrary internal formula codes, and its
[distinct-label numerical gate application](pa194-work/pa194-distinct-gate-sound/README.md)
now supplies the remaining gate premise in those models. A modeled scheduler
halt therefore yields an internal PA refutation with no remaining gate premise,
and iPRA proves `Con(PA) → ¬Halt(modeled scheduler)`. The scheduler is an
auxiliary encoded computation; the physical-machine connection remains open.

For the physical simulation needed in both directions, the
[blank startup](pa194/ipra/machine-code/DENSE-STARTUP.md) reaches state 24
with the encoded source seed tape after the fixed 58,154-step clock in every
candidate PRA model; the corresponding closed equality is also proved in
native iPRA. Its [source-frame decomposition](pa194/ipra/machine-code/STARTUP-SOURCE-FRAME.md)
identifies the permuted seed register file and all spare blocks. This is a
finite startup result, not a model-length simulation. The
[first seeded instruction](pa194/ipra/machine-code/FIRST-INSTRUCTION.md) is
also checked on the literal machine and as a closed native-iPRA equality: its
zero branch reaches the site-27 frame after another 462 steps. The
[restricted marker-to-increment trace](pa194/ipra/machine-code/MARKER-TO-INCREMENT.md)
checks a nonstandard-model path under explicit header, positivity and blank
suffix hypotheses. A [combined marker return](pa194/ipra/machine-code/ALL-SELECTED-MARKER-TO24.md)
now handles arbitrary selected values under its common intermediate-layout
assumptions. For the first non-first marker, a further
[combined return](pa194/ipra/machine-code/FIRST-ALL-TO24.md)
covers arbitrary first-register and selected-register values,
under the explicit eight-block blank-tail layout. These are model-uniform
conditional traces. A [seed-derived initial run](pa194/ipra/machine-code/SEED-FIRST-SITE38.md)
reaches the first site-38 physical frame from blank tape in every PRA model.
The [first decoder completion](pa194/ipra/machine-code/SEED-FIRST-DECODE-COMPLETE.md)
continues the concrete run to site 42 with existential model-valued clocks.
A complete source-frame correspondence and reachability invariant remain open.
The other direction, `¬Halt(M₁₉₄) → Con(PA)`, also needs an internal
translation of arbitrary PA refutations into the machine's numerical calculus.
The [model-level calculus logic](pa194-work/pa194-model-logic/README.md)
includes a finite source-formula translation code that agrees with an
independent structural reference on nonstandard valid formula codes.
Freshness, semantic correctness and the internal proof compiler remain open.
The [forward compiler audit](pa194-work/pa194-forward-audit/README.md) identifies where
the imported PA196 argument uses full PA induction. Current-Foundation ports
of the [PAeq formula translation](pa194-work/pa194-paeq-formula/README.md), its
[validity](pa194-work/pa194-paeq-translation-validity/README.md), [substitution graph
witness bounds](pa194-work/pa194-paeq-subst-witness/README.md), and [formula substitution
agreement](pa194-work/pa194-paeq-formula-subst/README.md) handle nonstandard model inputs.
The [LK proof transport](pa194-work/pa194-paeq-proof-transport/README.md) covers all
logical rules in IΣ₁ models, conditional on a uniform supplier of translated
source-axiom proofs. Its [represented version](pa194-work/pa194-paeq-transport-sentence/README.md)
is proved in IΣ₁ with that antecedent. The
[finite-axiom classifier](pa194-work/pa194-finite-axiom-classifier/README.md) reduces
the non-induction part of the supplier to its standard finite cases. The
[equality-reflexivity case](pa194-work/pa194-paeq-refl-source/README.md) and the
[symmetry and transitivity cases](pa194-work/pa194-paeq-equality-source/README.md) now
have explicit translated target proofs. The remaining finite axiom proofs,
arbitrary induction-schema supplier, numerical proof compiler and machine
connection remain open.

For the last step of that direction above the physical machine,
[`pa194-model-fairness`](pa194-work/pa194-model-fairness/README.md) proves in every model of `𝗜𝚺₁`,
for an abstract command semantics, that the scheduler meets a halting SHIFT as soon as some
command word computes the formula `1`, and that the formulas computed by command words are
closed under the rules of the numerical calculus. Words, candidates and times may be
nonstandard. Its module `PA194ModelFairness` instantiates this with the modeled scheduler and
`TargetProvable`: in every candidate-PRA model with an IΣ₁ reduct, the modeled scheduler halts
at some model time exactly when the numerical calculus has a target proof of the
contradiction code (`halts_iff_provable`). This concerns the modeled scheduler, not the
physical table. The translation of an internal PAeq or source-language proof into the
numerical calculus (the model-level counterpart of
[`pa194-foundation-lk`](pa194-work/pa194-foundation-lk/README.md)) has no model-level result.
[`pa194-model-sequent`](pa194-work/pa194-model-sequent/README.md) supplies its sequent layer for
an abstract calculus in a model of `𝗜𝚺₁`: hypothesis lists and hypothesis sets that are
elements of the model, with the deduction theorem, cut, the structural rules and
generalization. It is instantiated with the numerical calculus (`PA194ModelSequent`), and its
module `ConPADerivation` reduces the compilation of an internal derivation to one requirement
on the formula translation per inference rule. No translation is shown to meet them.
`PA194ModelEndpoint` is the step after that compiler: given a simulation for a theory `T` of
the relational source language, an internal refutation of `T` makes the modeled scheduler
halt, so a model in which it never halts has no internal proof of `⊥` from `T`. The
simulation is a hypothesis there, and `T` is not `𝗣𝗔`.
[`pa194-model-axioms`](pa194-work/pa194-model-axioms/README.md) starts the model-level target
proofs of the source axioms outside the equality theory: primitive equality entails
observational equality at every other label without a vacuity premise, and the translation of
the weak-adjunction, empty-set and irreflexivity sentences is target-provable, which gives
their axiom leaves for a simulation and the axiom rule of a theory with the equality axioms
and these three sentences. The separation
scheme is done instance by instance: the translation of the instance for an internal formula
of arity one, possibly nonstandard and with free variables, is target-provable. A source
theory containing the instances is open, because instances with parameters have to be
axioms in universally closed form.
[`pa194-guarded-compiler`](pa194-work/pa194-guarded-compiler/README.md) is about the
compiler from `ordinaryPAeq` derivations to the relational source theory. Its README argues
that the invariant of `conditional_compile` at `rootParameters` (the source theory derives
the translated sequent) fails for derivable sequents with free variables, so the four open
suppliers cannot all be proved in that form. The directory uses an invariant with the guards
`¬Dom(&i)` and a packet that keeps free variables distinct, proves the propositional rules,
cut, the shift rule, the universal rule and the existential rule for a variable witness for
it, and removes the guards at the root of a refutation. The existential rule for a function
term as witness, the translated theory axioms and the inhabitation of the domain in the
actual source theory are still hypotheses there, so `OrdinaryCompiler` is not proved.

[`isigma1-machine`](isigma1-machine/README.md) defines the run of an arbitrary transition
table inside a model of `𝗜𝚺₁` and its `Σ₁` halting sentence, and states the one obligation
`Calibrated T h` from which the iPRA equivalence follows. No table is shown to be calibrated.
