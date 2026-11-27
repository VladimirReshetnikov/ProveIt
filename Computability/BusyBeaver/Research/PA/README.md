# PA consistency machines

The [iPRA unification plan](../../../../Logic/PrimitiveRecursiveArithmetic/UNIFICATION-PLAN.md)
describes shared arithmetic reuse and replay checks at
the exact published PA machine endpoints.

This directory contains machine tables, imported research, and Lean proofs
concerning small Turing machines associated with the consistency of Peano
arithmetic, `Con(PA)`. The current goal is a Lean proof of
`iPRA ⊢ Con(PA) ↔ ¬Halt(M)` for the primary 194-state candidate, followed
by the other 194-, 195-, and 196-state consistency candidates. The machines start
on a blank two-way binary tape; state counts exclude the halt state.

The [verification directory](verification/) contains the
[primary PA194 proof](verification/pa194/), its
[supporting work](verification/pa194-work/),
[other machines and upstream snapshots](verification/other-machines/), and
[shared machine coding and IΣ₁ transfer](verification/shared/).
The [research packets](docs/) retain the layout references from their delivery.

Lean proves the unconditional iPRA equivalence for forty-one literal 194-state
tables. The theorems and staged replay instructions are under
[the primary endpoint](verification/pa194/ipra/native-endpoint/README.md),
[PA1944L](verification/pa194/ipra/variants/pa1944l/README.md),
[seven archived PA1944L variants](verification/pa194/ipra/variants/pa1944l/companions/README.md),
[PA194-AD](verification/pa194/ipra/variants/pa194ad/README.md),
[PA194AX11H](verification/pa194/ipra/variants/pa194ax11h/README-final.md),
[PA194B](verification/pa194/ipra/variants/pa194b/README.md),
[PA194C32](verification/pa194/ipra/variants/pa194c32/README.md),
[PA194HX](verification/pa194/ipra/variants/pa194hx/README.md),
[PA194LC](verification/pa194/ipra/variants/pa194lc/README.md),
[PA194LC_AX11H](verification/pa194/ipra/variants/pa194lcax11h/README.md),
[PA194LC_A](verification/pa194/ipra/variants/pa194lca/PA194LCAFinal.lean),
[PA194LC_B](verification/pa194/ipra/variants/pa194lcb/README.md),
[PA194LC_C](verification/pa194/ipra/variants/pa194lcc/README.md),
[the companion selector overlays](verification/pa194/ipra/variants/pa194sel/companions/README.md),
[M4R](verification/pa194/ipra/variants/pa194m4r/PA194M4RFinal.lean),
[PA194OR](verification/pa194/ipra/variants/pa194or/README.md),
[PA194P5](verification/pa194/ipra/variants/pa194p5/README.md),
[PA194SEL](verification/pa194/ipra/variants/pa194sel/README.md),
[PA194TDY](verification/pa194/ipra/variants/pa194tdy/README.md), and
the [seven timing variants](verification/pa194/ipra/variants/pa194fast/README.md).
The remaining 194-state candidates, the original PA195, and the PA196
candidate still need equivalence proofs.

The [LC_AX11H endpoint](verification/pa194/ipra/variants/pa194lcax11h/PA194LCAX11HFinal.lean) uses the checked blank startup and coverage of all 3,671 sites to transfer the AX11H equivalence to the literal LC_AX11H table.
The [radix-five](verification/pa194/ipra/variants/pa194m5/README-radix.md)
and [radix-six](verification/pa194/ipra/variants/pa194m6/README.md) proofs
use revised source programs with different numerical constructors.

The [AX11H source development](verification/pa194/ipra/variants/pa194ax11h/README-candidate.md)
checks the exact revised push and field-reader outputs at model-valued clocks.

## Primary 194-state candidate

The target table is `pa194_conpa/construction/tables/pa194.tm` in
[the PA194 research packet](docs/pa194_conpa_2026-11-13/).
It has 194 working states, start state 0, halt label 194, and 388 transitions.
Its SHA-256 is
`4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`.
The primary table is a seven-fold quotient of a 201-control parent with
a ten-entry source interface. Lean has checked the exact packed seed reached
from blank by [PA194-AD](verification/pa194/ipra/variants/pa194ad/README.md) after 58,122
steps and by [PA194HX](verification/pa194/ipra/variants/pa194hx/README.md) after 56,134
steps. For each table, Lean has checked the literal register engine
and all 3,673 source-site certificates. The
[PA194LC replay](verification/pa194/ipra/variants/pa194lc/README.md) checked the reassociated
trie, exact startup, full source coverage, and final iPRA transfer.

The [14 November incoming reports](INCOMING-2026-11-14.md) include another
194-state candidate and do not report a verified sub-194 blank-start machine.

[The PA194 arithmetic endpoint](verification/pa194/ipra/README.md) binds the pinned table
to a standard-model halting sentence and constructs a conditional iPRA
equivalence. [The explicit machine codes](verification/pa194/ipra/machine-code/README.md)
include a clock whose decoded execution is characterized in every candidate
PRA model. [The quotient proof](verification/pa194-work/pa194-dense/README.md) connects the 201-control
parent and dense PA194 table for all standard finite runs; [the zipper bridge](verification/pa194-work/pa194-zip-bridge/README.md)
connects blank-tape halting to the literal machine used by the arithmetic code.
[Source coverage](verification/pa194-work/pa194-coverage/README.md) reduces the source-to-parent
simulation to a finite set of Lean checks; all 3,673 sites and the aggregate
have passed. [The clock/source composition](verification/pa194-work/pa194-clock-source-complete/README.md)
connects the initialized source program to the exact machine clocks in
standard finite-run semantics. [The command scheduler](verification/pa194-work/pa194-command-source/README.md)
is equivalent to that source program in standard finite-run semantics, and
[its clock composition](verification/pa194-work/pa194-command-clock/README.md) connects the initial
scheduler state to the machine clocks. Parts of the literal register scanner
are also proved as native iPRA equalities; see the
[source-file engine](verification/pa194/ipra/machine-code/SOURCE-FILE-ENGINE.md). The
[marking](verification/pa194/ipra/machine-code/MARK-ALL.md) box has native iPRA sentences
for each physical position, and the
[marked increment](verification/pa194/ipra/machine-code/INCREMENT-SOURCE.md) and
[marked decrement](verification/pa194/ipra/machine-code/DECREMENT-SOURCE.md) boxes have
them for each logical register. The controller and physical-frame transitions have also been connected for selected
source sites, including a [matched loop through both site-32 branches](verification/pa194/ipra/machine-code/LOOP-AFTER32.md),
the [site-38 zero branch](verification/pa194/ipra/machine-code/SITE38-ZERO-PHYSICAL.md),
and both [zero](verification/pa194/ipra/machine-code/SITE45-ZERO-PHYSICAL.md) and
[positive](verification/pa194/ipra/machine-code/SITE45-POSITIVE-PHYSICAL.md) site-45 branches
and [one positive 45→46→47→45 transfer iteration](verification/pa194/ipra/machine-code/SITE45-TRANSFER-STEP.md)
in PRA models; the [site-45](verification/pa194/ipra/machine-code/SITE45-POSITIVE-CLOCK-CODE.md) and
[site-46](verification/pa194/ipra/machine-code/SITE46-CLOCK-CODE.md) segment clocks have
primitive-recursive codes. The [site-45 transfer and zero exit](verification/pa194/ipra/machine-code/SITE45-NATIVE-EXIT.md)
and [site-42 transfer and zero exit](verification/pa194/ipra/machine-code/SITE42-NATIVE-EXIT.md)
now have native iPRA sentences for their complete transfer loops. A
[matched five-instruction macro](verification/pa194/ipra/machine-code/TRANSFER-TO-SITE0-INVARIANT.md)
preserves a repeated-spare frame and its gap under explicit branch and padding
conditions; it is a model-uniform finite segment, not an all-site simulation. Its
[physical run and intermediate width equalities](verification/pa194/ipra/machine-code/TRANSFER-MACRO-WIDTHS-PHYSICAL.md)
have also been combined. A [native iPRA padding theorem](verification/pa194/ipra/machine-code/HEADER-WIDTH-GLOBAL.md)
rules out a gap below 21 under the explicit width-57 condition for every
path-length lookup input. Outside the source table the lookup defaults to zero.
A [blank-reachable matched loop](verification/pa194/ipra/machine-code/SEED-WIDTH-GROWTH.md)
returns to the same path with its header width increased by one, so constant
width does not describe the entire reachable run. A [conditional minimum-width
lemma](verification/pa194/ipra/machine-code/MINIMUM-WIDTH-SAFETY.md) shows that width at least
48 gives a gap of at least 12 in every covered PRA model. Establishing that
minimum for the run, and a complete simulation, remains open. A [checked
symbolic prefix interpreter](verification/pa194/ipra/machine-code/SOURCE-SYMBOLIC-ENTRY.md)
starts at any standard source site and executes a bounded literal prefix over
arbitrary model-valued tape data. It stops at unknown tape boundaries and does
not yet prove completion of a source instruction. Other native iPRA
clocked equalities cover the [physical positive loop](verification/pa194/ipra/machine-code/ACTUAL-PHYSICAL-NATIVE.md),
[source fetch](verification/pa194/ipra/machine-code/UNIFIED-FETCH-NATIVE.md),
[decoder](verification/pa194/ipra/machine-code/DECODER-NATIVE.md),
[tag dispatch](verification/pa194/ipra/machine-code/DISPATCH-TAG-NATIVE.md), and the
[site-31 physical increment](verification/pa194/ipra/machine-code/SITE31-NATIVE.md). A
[native iPRA equality for the site-31 restore loop and zero exit](verification/pa194/ipra/machine-code/SITE31-RESTORE-EXIT-NATIVE.md)
covers the model-length physical loop and its transition to site 34. The complete
[fetch/decode/dispatch prefix](verification/pa194/ipra/machine-code/SCHEDULER-BRANCHES-OPEN.md)
is proved model-theoretically under the documented hypotheses. The general
[compiler](verification/pa194-work/pa194-model-logic/FULL-SEPARATION-THEORY.md)
translates refutations of the finite equality-plus-weak-adjunction theory
combined with its classifier-defined parameter-closed separation theory into
modeled scheduler halting in PRA + IΣ₁ models. The classifier-defined standard
separation theory is [identified with the typed Foundation scheme](verification/pa194-work/pa194-model-axioms/TYPED-THEORY.md).
The combined source theory [internally proves its open separation instances](verification/pa194-work/pa194-model-axioms/FULL-SEP-OPEN.md)
for model-valued valid properties under the stated PRA and IΣ₁ assumptions.
[Internal closure and reopening](verification/pa194-work/pa194-model-axioms/CLOSE.md)
also preserve proof existence for model-valued closure lengths. The source theory
[proves ordinal induction for all internally valid properties](verification/pa194-work/pa194-model-axioms/INTERNAL-ORDINAL-FROM-BAD.md)
in each covered PRA model with IΣ₁ arithmetic reduct, including nonstandard
property codes. [Fixed Σ₁ graphs for deterministic ordinal proof codes](verification/pa194-work/pa194-model-axioms/CANONICAL-ORDINAL.md)
now supply open and closed proofs uniformly in the property code, using an
internally least tuple of auxiliary proofs. These are model-level results under
the stated PRA and IΣ₁ assumptions, not native iPRA derivations. The source
theory also [proves successor cancellation for ordinal isomorphism](verification/pa194-work/pa194-model-axioms/ISO-CANCEL-SOURCE.md);
the [translated PA induction bridge](verification/pa194-work/pa194-guarded-compiler/PA194OrdinalInductionLink.lean)
now supplies induction axioms at the root under the source naming and arithmetic
premises. A fixed
[universally closed least-point exclusion theorem](verification/pa194-work/pa194-model-axioms/LEAST-EXCLUDES.md)
has an internal proof in the covered models, and a separate
[triple-specialization graph](verification/pa194-work/pa194-model-axioms/CONTEXT-TRIPLE-SPECIALIZE.md)
handles nonstandard indices. The [addition](verification/pa194-work/pa194-model-logic/PAEQ-ADDITION-CODE.md)
and [multiplication](verification/pa194-work/pa194-model-logic/PAEQ-MULTIPLICATION-CODE.md)
code graphs establish syntax. Recursive PAeq [term](verification/pa194-work/pa194-model-logic/PAEQ-TERM-DISPATCHER.md)
and [formula](verification/pa194-work/pa194-model-logic/PAEQ-FORMULA-DISPATCHER.md)
dispatchers have scope preservation under an explicit environment bound. A
[conditional internal refutation compiler](verification/pa194-work/pa194-model-logic/PAEQ-CONDITIONAL-REFUTATION.md)
assumes the quantifier, shift, and theory-axiom suppliers. Its original
root-packet invariant collapses distinct variables and does not supply the
needed domain guards, as explained in the guarded compiler notes. The [guarded calculus and compiler](verification/pa194-work/pa194-guarded-compiler/README.md)
retain those distinctions and use existential guard bounds. Their interpretation
interface has no packet-length condition; the [domain-inhabitation supplier](verification/pa194-work/pa194-model-logic/SOURCE-INHABITED.md)
is proved. The term facts reduce to seventeen one-layer naming obligations;
[variable](verification/pa194-work/pa194-model-axioms/NAME-VARIABLE.md) and
[zero](verification/pa194-work/pa194-model-logic/NAME-ZERO.md) name existence and their
[variable](verification/pa194-work/pa194-model-axioms/NAME-VARIABLE-UNIQUE.md) and
[zero](verification/pa194-work/pa194-model-logic/UZERO-FIELD.md) uniqueness are proved in
the full source theory. The generic [reflexive naming](verification/pa194-work/pa194-model-logic/NAME-REFL.md)
and [transfer from uniqueness](verification/pa194-work/pa194-model-logic/NAME-OF-UNIQ.md)
fields are also proved. A separately replayed generic reduction derives all naming
fields from twelve fixed source facts and variable-name existence; the latter is
proved for the full source theory. Of the twelve fixed facts,
[equality reflexivity and successor existence](verification/pa194-work/pa194-model-axioms/SOURCE-FIXED-FACTS.md),
[equality-to-isomorphism](verification/pa194-work/pa194-model-axioms/SOURCE-EI.md),
[domain-zero existence](verification/pa194-work/pa194-model-axioms/SOURCE-Z1.md),
[isomorphism of zero representatives](verification/pa194-work/pa194-model-axioms/SOURCE-Z2.md),
[guarded isomorphism symmetry](verification/pa194-work/pa194-model-axioms/SOURCE-IS.md),
[guarded isomorphism transitivity](verification/pa194-work/pa194-model-axioms/SOURCE-IT.md),
and [successor compatibility](verification/pa194-work/pa194-model-axioms/SOURCE-S2.md)
are proved in the covered models. A separate [addition-existence supplier](verification/pa194-work/pa194-model-axioms/SOURCE-A1.md)
and a [multiplication-existence supplier](verification/pa194-work/pa194-model-axioms/SOURCE-M1.md)
have passed incremental replays. The [ten-fact assembly](verification/pa194-work/pa194-model-axioms/SOURCE-FACTS-TEN.md)
leaves addition and multiplication coherence as explicit premises. The
[full-source inclusive Separation supplier](verification/pa194-work/pa194-model-axioms/INCLUSIVE-SEPARATION-SOURCE.md)
provides one graph-restriction instance needed for the coherence proofs. The
[multiplication source chain](verification/pa194-work/pa194-model-axioms/SOURCE-M1-CHAIN.md)
has independently replayed. Older addition and
induction dependencies remain prebuilt in these replays; a
separate standalone source check of the corresponding addition-output
development passed with a Foundation overlay, without establishing byte identity
with those earlier staged objects.
A [successor-value transport](verification/pa194-work/pa194-model-axioms/SUCC-VALUE-FULL-SOURCE.md)
is proved in the covered models, including for nonstandard term codes. The
remaining source axiom suppliers are open. Identity translation is independent
of packet length for valid internal formulas. The
[ordinary PAeq theory now has a uniform classifier](verification/pa194-work/pa194-model-logic/PAEQ-ORDINARY-CLASS.md),
and the [arithmetic induction-axiom supplier](verification/pa194-work/pa194-model-logic/PAEQ-INDUCTION-SUPPLIER.md)
establishes modeled PAeq proof existence for every internal arithmetic induction
axiom, including nonstandard codes. The [finite arithmetic supplier and PA-refutation transport](verification/pa194-work/pa194-model-logic/PAEQ-FINITE-SUPPLIER.md)
are also proved in every arithmetic IΣ₁ model, including for nonstandard proof
codes. There is a formal [classical IΣ₁ proof of `Con(ordinaryPAeq) → Con(PA)`](verification/pa194-work/pa194-model-logic/PAEQ-CANONICAL-CONSISTENCY.md).
The [reflexivity](verification/pa194-work/pa194-model-logic/FORWARD-REFL-ROOT.md),
[zero-not-successor](verification/pa194-work/pa194-model-logic/FORWARD-ZERO-SUCC.md), and
[addition-by-zero](verification/pa194-work/pa194-model-logic/FORWARD-ADD-ZERO.md), and
[multiplication-by-zero](verification/pa194-work/pa194-model-logic/FORWARD-MUL-ZERO.md),
and [symmetry](verification/pa194-work/pa194-model-logic/FORWARD-SYMMETRY.md) suppliers
prove the root-packet translations of those fixed axioms in the source theory
under the stated code bounds. A [normalized identity-packet bridge](verification/pa194-work/pa194-model-logic/IDENTITY-FIXED.md)
supplies these five fixed translations for the guarded route; the interpretation
axiom supplier now reduces to four fixed axioms and arbitrary induction
instances. [Transitivity](verification/pa194-work/pa194-model-logic/TRANSITIVITY-PACKET.md)
is also supplied for every valid arity-zero packet. The [remaining source
axiom reduction](verification/pa194-work/pa194-model-logic/FORWARD-FIXED-FOUR.md) assumes four
fixed axioms and arbitrary induction instances. Other rule suppliers and the
unconditional PAeq-to-source compiler are still open. The [universal formula replacement theorem](verification/pa194-work/pa194-model-logic/PAEQ-UNIVERSAL-FORMULA-CONGRUENCE.md)
supplies modeled PAeq proof existence for arbitrary internally valid arity-one
formulas, including nonstandard codes and nested quantifiers. These existence
results do not supply fixed proof-code transformers.
A proof-code interpretation of PA and the connection to the physical machine
remain open. In standard Lean semantics, [the calculus/clock composition](verification/pa194-work/pa194-calculus-clock/README.md)
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

- [PA195 arithmetic endpoint](verification/other-machines/pa195/ipra/README.md) binds the table to a
  primitive-recursive halting test and an iPRA sentence in the standard
  model. Its equivalence theorem assumes two machine-specific classical PRA
  reductions; those assumptions remain open.
- [Quotient and dense-table proof](verification/other-machines/pa195-work/pa195-dense/README.md) proves in Lean that
  the 202-control parent and the delivered dense 195-state table halt under
  the same circumstances for every complete tape and head position.
  [The zipper bridge](verification/other-machines/pa195-work/pa195-zip-bridge/README.md) connects blank-tape
  halting to the arithmetic endpoint over the standard natural numbers.
- [Register engine](verification/other-machines/pa195-work/pa195-runtime/README.md),
  [source entry binding](verification/other-machines/pa195-work/pa195-source-entry/README.md), and
  [symbolic contract batches](verification/other-machines/pa195-work/pa195-symbolic/README.md) check parts of the
  parent machine's execution. The entry binding covers one source instruction
  and both branches; the complete source-graph and arithmetic correctness
  connections still need proof.
- [Explicit machine codes](verification/other-machines/pa195/ipra/machine-code/README.md) develop tape,
  transition-table, and configuration-step functions in the PRA language.
  Their model equations are ingredients for a weak-arithmetic proof, not the
  missing machine/refutation reductions.
- [Diagonal calibration](verification/other-machines/pa195-work/pa195-calibration/README.md) constructs an
  occurrence code and proves decoder self-freshness in classical PRA,
  including its behavior in nonstandard models. The component codes are
  supplied existentially; the proof-producing PA translation remains open.

## Other machines and related work

[James Chang's imported snapshots](verification/other-machines/jamesyc-upstream/README.md) contain the
upstream PA196 and PA209 developments. The imported PA196 result includes a
PA proof of the implication from literal nonhalting to PA consistency; this
alone does not establish the converse in PA or either direction in iPRA.
[PA196 versus U208](verification/other-machines/pa196-vs-u208/ipra/README.md) documents the PA196
arithmetic endpoint, conditional transfers, and the completed PA-refutation
witness certificate. The machine-specific reductions remain open.
[The archive audit](verification/other-machines/pa196-vs-u208/archive-audit/README.md) inventories related
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

[`isigma1-transfer`](verification/shared/isigma1-transfer/README.md) proves, for any bounded arithmetic formula
`δ`, that an `𝗜𝚺₁` proof of `paRefutation 🡘 ∃ t, δ t` gives the iPRA equivalence of PA
consistency and the negation of the mapped sentence `∃ t, δ t`, given the PA witness
certificate. It is independent of the machine and proves no machine equivalence. Its use is
that a machine reduction may be proved in models of `𝗜𝚺₁` instead of models of candidate PRA.
The same directory proves `halt_iff_refutation_of_models`: for an open halting matrix of the
PRA language, the two classical PRA reductions that the PA194 and PA196 assemblies take as
hypotheses follow if halting and the mapped PA refutation agree in every candidate PRA model
whose arithmetic reduct satisfies `𝗜𝚺₁`. Model arguments may therefore assume `𝗜𝚺₁`.

[The PA194 generic-machine bridge](verification/pa194/ipra/machine-code/GENERIC-BRIDGE.md)
identifies its packed clock and the pinned table's arithmetic run at every model
time, including nonstandard times. [The one-way endpoints](verification/pa194/ipra/machine-code/ONE-WAY-ENDPOINT.md)
separately reduce each iPRA implication to its corresponding all-model
machine/refutation implication. Neither of those machine-specific premises is
proved yet; the earlier standard-run source simulation does not supply them.

For the compiler's internal syntax operations, fixed candidate-PRA codes now
have all-model correctness proofs for [source formula shift](verification/pa194-work/pa194-source-formula-shift-code-model/README.md)
and [arithmetic formula closing](verification/other-machines/pa195-work/pa195-calibration/PA194FormulaAgreement.md).
These cover nonstandard valid formulas in candidate PRA models with IΣ₁
reducts. They are components of the compiler, not a translation of arbitrary
PA proofs or a verification of source execution.

For the direction `Con(PA) → ¬Halt(M₁₉₄)`, a
[conditional source-line theorem](verification/other-machines/pa195-work/pa195-calibration/PA194SourceLineRefutation.md)
turns an internally valid numerical derivation of code 1 into an internal PA
refutation, provided its seed translations are PA-provable. Model-uniform
proofs cover the six numbered seeds, rho8 and diagonal, as well as modus
ponens and generalization. The guarded gate has since been discharged as
described below; the connection from the physical machine to such line histories
remains open. Separately, the
[machine-store invariant](verification/pa194-work/pa194-machine-store-invariant/README.md) covers the
mathematical command effects using an independent target proof encoding; it
has not been identified with PA provability or the physical controller trace.
The finite codes for [AX](verification/pa194-work/pa194-machine-ax-standard/README.md) and
[SHIFT/MP](verification/pa194-work/pa194-machine-shift-mp-standard/README.md) have also been proved
to reproduce the corresponding standard-natural-number source commands;
those bindings do not establish the nonstandard controller simulation.
The [modeled scheduler iteration](verification/pa194-work/pa194-scheduler-iteration/README.md)
preserves the store invariant for arbitrary model-length runs, and a modeled
halt yields a target proof of code 1. The [target-to-PA bridge](verification/pa194-work/pa194-target-source/README.md)
turns that proof into an internal PA refutation assuming the guarded
gate seed. The [distinct-label endpoint](verification/pa194-work/pa194-distinct-gate-endpoint/README.md)
discharges the equal-label gate case and narrows the premise to the remaining
distinct-label separation tails. The model-length
[universal-opening endpoint](verification/other-machines/pa195-work/pa195-calibration/PA194OpeningEndpoint.md) is
now identified even for nonstandard codes, and the resulting
[internal induction theorem](verification/other-machines/pa195-work/pa195-calibration/PA194FullInternalInduction.md)
constructs the required closed induction axiom bodies. General
[internal finite-set separation](verification/other-machines/pa195-work/pa195-calibration/PA194InternalSeparation.md)
is also checked for arbitrary internal formula codes, and its
[distinct-label numerical gate application](verification/pa194-work/pa194-distinct-gate-sound/README.md)
now supplies the remaining gate premise in those models. A modeled scheduler
halt therefore yields an internal PA refutation with no remaining gate premise,
and iPRA proves `Con(PA) → ¬Halt(modeled scheduler)`. The scheduler is an
auxiliary encoded computation; the physical-machine connection remains open.

For the physical simulation needed in both directions, the
[blank startup](verification/pa194/ipra/machine-code/DENSE-STARTUP.md) reaches state 24
with the encoded source seed tape after the fixed 58,154-step clock in every
candidate PRA model; the corresponding closed equality is also proved in
native iPRA. Its [source-frame decomposition](verification/pa194/ipra/machine-code/STARTUP-SOURCE-FRAME.md)
identifies the permuted seed register file and all spare blocks. This is a
finite startup result, not a model-length simulation. The
[first seeded instruction](verification/pa194/ipra/machine-code/FIRST-INSTRUCTION.md) is
also checked on the literal machine and as a closed native-iPRA equality: its
zero branch reaches the site-27 frame after another 462 steps. The
[restricted marker-to-increment trace](verification/pa194/ipra/machine-code/MARKER-TO-INCREMENT.md)
checks a nonstandard-model path under explicit header, positivity and blank
suffix hypotheses. A [combined marker return](verification/pa194/ipra/machine-code/ALL-SELECTED-MARKER-TO24.md)
now handles arbitrary selected values under its common intermediate-layout
assumptions. For the first non-first marker, a further
[combined return](verification/pa194/ipra/machine-code/FIRST-ALL-TO24.md)
covers arbitrary first-register and selected-register values,
under the explicit eight-block blank-tail layout. These are model-uniform
conditional traces. A [seed-derived initial run](verification/pa194/ipra/machine-code/SEED-FIRST-SITE38.md)
reaches the first site-38 physical frame from blank tape in every PRA model.
The [first decoder completion](verification/pa194/ipra/machine-code/SEED-FIRST-DECODE-COMPLETE.md)
continues the concrete run to site 42 with existential model-valued clocks. From
that first frame, a [physical continuation](verification/pa194/ipra/machine-code/SEED-FIRST-SITE3671.md)
reaches site 3671 with gap 54, following the matched zero steps at sites 3664
and 3668. A complete source-frame correspondence and
reachability invariant remain open.
The other direction, `¬Halt(M₁₉₄) → Con(PA)`, also needs an internal
translation of arbitrary PA refutations into the machine's numerical calculus.
The [model-level calculus logic](verification/pa194-work/pa194-model-logic/README.md)
includes a finite source-formula translation code that agrees with an
independent structural reference on nonstandard valid formula codes.
Freshness, semantic correctness and the internal proof compiler remain open.
The [forward compiler audit](verification/pa194-work/pa194-forward-audit/README.md) identifies where
the imported PA196 argument uses full PA induction. Current-Foundation ports
of the [PAeq formula translation](verification/pa194-work/pa194-paeq-formula/README.md), its
[validity](verification/pa194-work/pa194-paeq-translation-validity/README.md), [substitution graph
witness bounds](verification/pa194-work/pa194-paeq-subst-witness/README.md), and [formula substitution
agreement](verification/pa194-work/pa194-paeq-formula-subst/README.md) handle nonstandard model inputs.
The [LK proof transport](verification/pa194-work/pa194-paeq-proof-transport/README.md) covers all
logical rules in IΣ₁ models, conditional on a uniform supplier of translated
source-axiom proofs. Its [represented version](verification/pa194-work/pa194-paeq-transport-sentence/README.md)
is proved in IΣ₁ with that antecedent. The
[finite-axiom classifier](verification/pa194-work/pa194-finite-axiom-classifier/README.md) reduces
the non-induction part of the supplier to its standard finite cases. The
[equality-reflexivity case](verification/pa194-work/pa194-paeq-refl-source/README.md) and the
[symmetry and transitivity cases](verification/pa194-work/pa194-paeq-equality-source/README.md) now
have explicit translated target proofs. The remaining finite axiom proofs,
arbitrary induction-schema supplier, numerical proof compiler and machine
connection remain open.

For the last step of that direction above the physical machine,
[`pa194-model-fairness`](verification/pa194-work/pa194-model-fairness/README.md) proves in every model of `𝗜𝚺₁`,
for an abstract command semantics, that the scheduler meets a halting SHIFT as soon as some
command word computes the formula `1`, and that the formulas computed by command words are
closed under the rules of the numerical calculus. Words, candidates and times may be
nonstandard. Its module `PA194ModelFairness` instantiates this with the modeled scheduler and
`TargetProvable`: in every candidate-PRA model with an IΣ₁ reduct, the modeled scheduler halts
at some model time exactly when the numerical calculus has a target proof of the
contradiction code (`halts_iff_provable`). This concerns the modeled scheduler, not the
physical table. The translation of an internal PAeq or source-language proof into the
numerical calculus (the model-level counterpart of
[`pa194-foundation-lk`](verification/pa194-work/pa194-foundation-lk/README.md)) has no model-level result.
[`pa194-model-sequent`](verification/pa194-work/pa194-model-sequent/README.md) supplies its sequent layer for
an abstract calculus in a model of `𝗜𝚺₁`: hypothesis lists and hypothesis sets that are
elements of the model, with the deduction theorem, cut, the structural rules and
generalization. It is instantiated with the numerical calculus (`PA194ModelSequent`), and its
module `ConPADerivation` reduces the compilation of an internal derivation to one requirement
on the formula translation per inference rule. No translation is shown to meet them.
`PA194ModelEndpoint` is the step after that compiler: given a simulation for a theory `T` of
the relational source language, an internal refutation of `T` makes the modeled scheduler
halt, so a model in which it never halts has no internal proof of `⊥` from `T`. The
simulation is a hypothesis there, and `T` is not `𝗣𝗔`.
[`pa194-model-axioms`](verification/pa194-work/pa194-model-axioms/README.md) starts the model-level target
proofs of the source axioms outside the equality theory: primitive equality entails
observational equality at every other label without a vacuity premise, and the translation of
the weak-adjunction, empty-set and irreflexivity sentences is target-provable, which gives
their axiom leaves for a simulation and the axiom rule of a theory with the equality axioms
and these three sentences. The separation
scheme is done instance by instance: the translation of the instance for an internal formula
of arity one, possibly nonstandard and with free variables, is target-provable. A source
theory containing the instances is open, because instances with parameters have to be
axioms in universally closed form.
[`pa194-guarded-compiler`](verification/pa194-work/pa194-guarded-compiler/README.md) is about the
compiler from `ordinaryPAeq` derivations to the relational source theory. Its README argues
that the invariant of `conditional_compile` at `rootParameters` (the source theory derives
the translated sequent) fails for derivable sequents with free variables, so the four open
suppliers cannot all be proved in that form. The directory uses an invariant with the guards
`¬Dom(&i)` and a packet that keeps free variables distinct, proves the propositional rules,
cut, the shift rule, the universal rule and the existential rule for a variable witness for
it, and removes the guards at the root of a refutation. Domain inhabitation is
proved for the actual source theory. A separate reduction derives term-witness
support from naming facts, and derives those facts from twelve fixed source
facts plus variable-name existence. A further reduction (`induction_body`) derives
the translated induction axiom of every internal formula, before the closure of its
parameters, from the term facts, the twelve facts and ordinal induction of the source
theory for every internal property. The closure of the parameters and the link
to the source induction proof have replayed. The
[conditional PA refutation transport](verification/pa194-work/pa194-guarded-compiler/REFUTATION-TO-SCHEDULER.md)
supplies all four remaining translated fixed axioms from the source facts and
the two recursion clauses, then reaches modeled scheduler halting. The [native
endpoint assembly](verification/pa194-work/pa194-guarded-compiler/CONDITIONAL-NATIVE-ENDPOINT.md)
uses the same literal halting sentence in both directions.

Lean identifies literal blank-tape halting with the source controller reaching
its absorbing halt, in every PRA model with a classical IΣ₁ arithmetic reduct.
The proof [checks all 3,673 source ordinals](verification/pa194/ipra/machine-code/COMPRESSED-CONTROLLER.md).
At the next layer, the [controller and scheduler synchronization](verification/pa194/ipra/machine-code/SCHEDULER-HALT-SOURCE.md)
reduces their halting equivalence to the commands that return to a scheduler
boundary. The [MP and SHIFT return proofs](verification/pa194/ipra/machine-code/MODEL-MP.md)
establish those cases for arbitrary model-valued stores. The [AX command proof](verification/pa194/ipra/machine-code/ax-controller/README.md)
checks all 251 body blocks and interprets their result in the same model as the
controller. It supplies the last return case, giving equivalence between literal
halting and scheduler halting in the covered models. The
[native iPRA theorem](verification/pa194/ipra/native-endpoint/README.md) combines the two
machine and arithmetic directions.

[`pa194-source-semantics`](verification/pa194-work/pa194-source-semantics/README.md) proves facts about
the source theory in its models instead of by derivations: a fixed hypothesis of the guarded
compiler is the typed quote of a standard sentence, and `source_supply` (completeness and
the first derivability condition) makes it internally provable in every model of `IΣ₁` once
the sentence is true in every structure with equality that satisfies weak adjunction and
all separation instances. The directory reduces the two recursion clauses to predecessor
laws of the addition and multiplication traces and commutativity of addition, and proves in
such structures those three, addition and multiplication coherence, and the other ten source
facts (isomorphism is an equivalence compatible with successor; zero, successors, sums and
products exist). Its `calibration` and `sourceFacts_semantic` state, with no hypothesis and
for every model of `IΣ₁`, internal proofs in the source theory of the four facts of the
arithmetic calibration and of all twelve source facts; no internal proof from
`pa194-model-axioms` is used. Each module has been compiled separately.
`ArithmeticCalibration` itself, for the models of the candidate PRA presentation, is stated
from `calibration` in `PA194ArithmeticCalibrationSemantic` of the
[native endpoint](verification/pa194/ipra/native-endpoint/README.md), which also uses
`sourceFacts_semantic` for the equivalence between a halt of the modeled scheduler and an
internal refutation of arithmetic. The literal machine and modeled scheduler agree by the
model-level proof above.

Most of the other delivered candidates change the source program, so the arithmetic half
above does not apply to them unchanged. The first change treated is the command controller.
The packets describe four: the primary one; PA194N, whose successful modus ponens does not
push a zero; PA194C and PA194CS, which return the result of modus ponens in the cache and
halt a SHIFT on `h = 1`; and PA194H and PA194HS, which combine the no-push modus ponens with
that halting test. The AX command has two layouts: ten stack entries with the gate on top,
and the eleven entries of PA194AX11, where the gate is pushed and the command takes a fourth
field.
[`pa194-command-controllers`](verification/pa194-work/pa194-command-controllers/README.md) restates the
command-word theory of `pa194-model-fairness` with the controller as a parameter, and
[`pa194-controller-schedulers`](verification/pa194-work/pa194-controller-schedulers/README.md) defines a
scheduler for each controller and each layout by PRA codes and proves that, in every
candidate-PRA model
whose arithmetic reduct satisfies `𝗜𝚺₁`, it halts exactly when the numerical calculus proves
the contradiction code, hence exactly when the modeled scheduler of the primary table halts
and exactly when arithmetic has an internal refutation; the corresponding equivalence with
the consistency sentence is derived in iPRA. These are statements about schedulers defined
at the level of commands; a connection with a literal table and its source program is a
separate proof, which the [PA194AX11H endpoint](verification/pa194/ipra/variants/pa194ax11h/README-final.md)
supplies for one of them.

The same directory treats six changes of the axiom emitter, independent of each other and
of the controller: the separate diagonal `Γ(D)` in place of `Γ(A)` (PA194D, PA194DHS, the GD
family), the sixth head with exchanged premises (the Q families, PA194G, PA194GH), the
fifth head with an arbitrary consequent (PA194H5X), the generalization `U(c, h)` in
place of `U(d, h)` (the G, GH and GD families), the gate `¬(Γ(c) → (V → Q))` with no
separately pushed diagonal, which is the nine-entry AX of the original PA195, and the gate
`¬(Δ → (V → Q))` with the equality vacuity `Δ = E(a,b) → U(c, E(a,b))`, which is the
nine-entry AX of PA196. For each emitter and each controller, the scheduler halts at some
time of a model exactly when arithmetic has an internal refutation, and iPRA derives the
equivalence of its non-halting with the consistency sentence. For the emitters other than
the last the scheduler is compared with the calculus of the primary table, which they do
not change. The PA196 gate changes the calculus:
[`pa194-generic-calculus`](verification/pa194-work/pa194-generic-calculus/README.md) restates the
propositional and vacuity laws for an arbitrary set of codes closed under the rules, and
proves by `Σ₁` order induction on codes that such a set contains every diagonal `Γ(B)` once
it contains the vacuity of the two kinds of atoms at fresh labels, so the diagonals are
among the formulas that a scheduler with that gate computes; in the other direction the
invariant is that arithmetic proves the translations of the store entries, and arithmetic
proves the translation of the equality vacuity for all codes of the model.

The README of the directory lists the emitter and controller that the packets state for
sixteen candidates, among them the original PA195, PA195DC and PA196. For these machines
this is the arithmetic half at the level of commands only: no literal table is connected
with a scheduler here, and it has not been checked that the programs of PA195 and PA196
enumerate commands as the modeled scheduler of the primary table does. Not covered:
PA194JH5X, the fused head of the FW candidates, MP196 (its modus ponens halts), and the
candidates with another coefficient of the formula constructors.

[`isigma1-machine`](verification/shared/isigma1-machine/README.md) defines the run of an arbitrary transition
table inside a model of `𝗜𝚺₁` and its `Σ₁` halting sentence, and states the one obligation
`Calibrated T h` from which the iPRA equivalence follows. No table is shown to be calibrated.
