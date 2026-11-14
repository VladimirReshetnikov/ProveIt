# PA consistency machines

This directory contains machine tables, imported research, and Lean proofs
concerning small Turing machines associated with the consistency of Peano
arithmetic, `Con(PA)`. The current goal is a Lean proof of
`iPRA ⊢ Con(PA) ↔ ¬Halt(M)` for the primary 194-state candidate, followed
by the other 194-, 195-, and 196-state consistency candidates. The machines start
on a blank two-way binary tape; state counts exclude the halt state.

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

[The PA194 arithmetic endpoint](pa194/ipra/README.md) binds the pinned table
to a standard-model halting sentence and constructs a conditional iPRA
equivalence. [The explicit machine codes](pa194/ipra/machine-code/README.md)
include a clock whose decoded execution is characterized in every candidate
PRA model. [The quotient proof](pa194-dense/README.md) connects the 201-control
parent and dense PA194 table for all standard finite runs; [the zipper bridge](pa194-zip-bridge/README.md)
connects blank-tape halting to the literal machine used by the arithmetic code.
[Source coverage](pa194-coverage/README.md) reduces the source-to-parent
simulation to a finite set of Lean checks; all 3,673 sites and the aggregate
have passed. [The clock/source composition](pa194-clock-source-complete/README.md)
connects the initialized source program to the exact machine clocks in
standard finite-run semantics. [The command scheduler](pa194-command-source/README.md)
is equivalent to that source program in standard finite-run semantics, and
[its clock composition](pa194-command-clock/README.md) connects the initial
scheduler state to the machine clocks. Parts of the literal register scanner
are also proved as native iPRA equalities; see the
[source-file engine](pa194/ipra/machine-code/SOURCE-FILE-ENGINE.md). The
[marking](pa194/ipra/machine-code/MARK-ALL.md) box has native iPRA sentences
for each physical position, and the
[marked increment](pa194/ipra/machine-code/INCREMENT-SOURCE.md) and
[marked decrement](pa194/ipra/machine-code/DECREMENT-SOURCE.md) boxes have
them for each logical register. The controller
transitions into these boxes and the layout invariants between them remain
open. In standard
Lean semantics, [the calculus/clock composition](pa194-calculus-clock/README.md)
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
- [Quotient and dense-table proof](pa195-dense/README.md) proves in Lean that
  the 202-control parent and the delivered dense 195-state table halt under
  the same circumstances for every complete tape and head position.
  [The zipper bridge](pa195-zip-bridge/README.md) connects blank-tape
  halting to the arithmetic endpoint over the standard natural numbers.
- [Register engine](pa195-runtime/README.md),
  [source entry binding](pa195-source-entry/README.md), and
  [symbolic contract batches](pa195-symbolic/README.md) check parts of the
  parent machine's execution. The entry binding covers one source instruction
  and both branches; the complete source-graph and arithmetic correctness
  connections still need proof.
- [Explicit machine codes](pa195/ipra/machine-code/README.md) develop tape,
  transition-table, and configuration-step functions in the PRA language.
  Their model equations are ingredients for a weak-arithmetic proof, not the
  missing machine/refutation reductions.
- [Diagonal calibration](pa195-calibration/README.md) constructs an
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
have all-model correctness proofs for [source formula shift](pa194-source-formula-shift-code-model/README.md)
and [arithmetic formula closing](pa195-calibration/PA194FormulaAgreement.md).
These cover nonstandard valid formulas in candidate PRA models with IΣ₁
reducts. They are components of the compiler, not a translation of arbitrary
PA proofs or a verification of source execution.

For the direction `Con(PA) → ¬Halt(M₁₉₄)`, a
[conditional source-line theorem](pa195-calibration/PA194SourceLineRefutation.md)
turns an internally valid numerical derivation of code 1 into an internal PA
refutation, provided its seed translations are PA-provable. Model-uniform
proofs cover the six numbered seeds, rho8 and diagonal, as well as modus
ponens and generalization. The guarded gate and the connection from the
physical machine to such line histories are open. Separately, the
[machine-store invariant](pa194-machine-store-invariant/README.md) covers the
mathematical command effects using an independent target proof encoding; it
has not been identified with PA provability or the physical controller trace.
The finite codes for [AX](pa194-machine-ax-standard/README.md) and
[SHIFT/MP](pa194-machine-shift-mp-standard/README.md) have also been proved
to reproduce the corresponding standard-natural-number source commands;
those bindings do not establish the nonstandard controller simulation.
The [modeled scheduler iteration](pa194-scheduler-iteration/README.md)
preserves the store invariant for arbitrary model-length runs, and a modeled
halt yields a target proof of code 1. The [target-to-PA bridge](pa194-target-source/README.md)
turns that proof into an internal PA refutation assuming the still-open guarded
gate seed. The [distinct-label endpoint](pa194-distinct-gate-endpoint/README.md)
discharges the equal-label gate case and narrows the premise to the remaining
distinct-label separation tails. The model-length
[universal-opening endpoint](pa195-calibration/PA194OpeningEndpoint.md) is
now identified even for nonstandard codes; the required closed induction
axiom bodies and distinct-label comprehension remain open. Neither result
supplies the physical-machine connection.

For the physical simulation needed in both directions, the
[restricted marker-to-increment trace](pa194/ipra/machine-code/MARKER-TO-INCREMENT.md)
checks a nonstandard-model path under explicit header, positivity and blank
suffix hypotheses. A [combined marker return](pa194/ipra/machine-code/ALL-SELECTED-MARKER-TO24.md)
now handles arbitrary selected values under its common intermediate-layout
assumptions. A complete source-frame correspondence and blank-tape
reachability are open.
The other direction, `¬Halt(M₁₉₄) → Con(PA)`, also needs an internal
translation of arbitrary PA refutations into the machine's numerical calculus.
The [forward compiler audit](pa194-forward-audit/README.md) identifies where
the imported PA196 argument uses full PA induction. Current-Foundation ports
of the [PAeq formula translation](pa194-paeq-formula/README.md), its
[validity](pa194-paeq-translation-validity/README.md), [substitution graph
witness bounds](pa194-paeq-subst-witness/README.md), and [formula substitution
agreement](pa194-paeq-formula-subst/README.md) handle nonstandard model inputs.
The [LK proof transport](pa194-paeq-proof-transport/README.md) covers all
logical rules in IΣ₁ models, conditional on a uniform supplier of translated
source-axiom proofs. Its [represented version](pa194-paeq-transport-sentence/README.md)
is proved in IΣ₁ with that antecedent. The
[finite-axiom classifier](pa194-finite-axiom-classifier/README.md) reduces
the non-induction part of the supplier to its standard finite cases. The
[equality-reflexivity case](pa194-paeq-refl-source/README.md) now has an
explicit translated target proof. The remaining finite axiom proofs, arbitrary
induction-schema supplier, numerical proof compiler and machine connection
remain open.

[`isigma1-machine`](isigma1-machine/README.md) defines the run of an arbitrary transition
table inside a model of `𝗜𝚺₁` and its `Σ₁` halting sentence, and states the one obligation
`Calibrated T h` from which the iPRA equivalence follows. No table is shown to be calibrated.
