# Novelty decisions after assumed application

These decisions are about incremental proof-engineering content, not kernel acceptance. Every proposed Lean change remains uncompiled in this study. Six precise mechanisms pass. Prior vocabulary such as induction, records, injectivity or library reuse does not exclude every future use; the target and eliminated obligation matter.

## M1 — WangMachineAction.act_next_none_iff

**PASS: mechanism remains additional under the full assumed-applied outcome baseline**

New mechanism: Reflect equality through the existing injective stateNumber encoding.

Closest prior outcomes: NF004; EX008; EX073. NF004 requires finite dynamics and a forward-invariant predicate to recover predecessors. EX008 is scanner semiconjugacy, EX073 controller invariants. None eliminates pointwise equality transport for this new machine adapter.

Already available: stateNumber_injective.eq_iff; act_stateNumber; stateNumber_none.

Additional residual burden removed: No finite-surjectivity, periodicity or new invariant proof is needed. The two-direction equality transport remains after all prior APIs are applied.

Integration constraints: Keep target <216; invalid target216 also decodes to none. This composes with the new sentinel-equivalence proof without duplicating its benefit.

## M2 — WangMachineStep.color_action

**PASS: mechanism remains additional under the full assumed-applied outcome baseline**

New mechanism: Split only at the old head/write location; keep the new-head conditional symbolic.

Closest prior outcomes: EX012; NF028; NF010. Previous constructor/tag views concern annotated formula syntax or internal codes, not spatial tape-write support.

Already available: Tape.read_write_of_ne; Tape.read_write_same; moved_head_ne.

Additional residual burden removed: Prior APIs do not remove the redundant moved-head branch here. Normalizing the changed tape component before the color conditional removes one local branch.

Integration constraints: Preserve three-way result, write-before-move and halted target behavior; this changes proof case order, not operational semantics.

## M3 — WangMachineTraceBounds.run_read_of_abs_ge

**PASS: mechanism remains additional under the full assumed-applied outcome baseline**

New mechanism: Use le_abs' to convert the sharp absolute-value exterior condition directly.

Closest prior outcomes: EX001; EX067; NF018. General encouragement to reuse library lemmas is not an advertised simplification of every later theorem. None of the eleven packets targets this new trace-support conversion.

Already available: run_read_outside; le_abs'.

Additional residual burden removed: The underlying support theorem remains available and its final sign split remains redundant in the counterfactual checkout.

Integration constraints: Keep inclusive threshold |x|>=t, including t=0; no positive-time or stronger exterior assumption.

## E1 — WangMachineEncoding.stateNumber_injective

**PASS: mechanism remains additional under the full assumed-applied outcome baseline**

New mechanism: Identify unchanged terminal-slot encoding with Fin.val after finSuccEquivLast.symm.

Closest prior outcomes: NF014; NF004. NF014 removes existential missing-coordinate arguments for product pairing equivalences. NF004 assumes injectivity and uses finite invariant dynamics. Neither constructs Option(Fin215) terminal-slot injectivity.

Already available: Pinned Mathlib finSuccEquivLast and its some/none simplification laws; Fin.val_injective.

Additional residual burden removed: No baseline proposal identifies this new state encoding with the exact last-slot equivalence. The four Option cases can still be replaced by composition of existing injections.

Integration constraints: none must map to215 and some q to q, not the alternative zero-slot convention. Preserve executable stateNumber definition and all public statements.

## R2 — WangTiles942StepConstruction.stepTile_west/east/horizontal

**PASS: mechanism remains additional under the full assumed-applied outcome baseline**

New mechanism: Represent both horizontal edge fields by one spatial bond signal E.

Closest prior outcomes: EX059; EX073; R2-07; V12. Direction descriptors share field offsets/width/bounds; NorthView classifies high north colors; controller certificates concern local state dynamics. None establishes the translated spatial bond equation.

Already available: Existing sourceIndex/action, nextHead_eq/ne, stepTile, transitionRow, receiveTile.

Additional residual burden removed: Simultaneous west(x)=E(x-1) and east(x)=E(x) removes separate geometry in horizontal matching after all north/direction APIs are assumed present.

Integration constraints: Derived from actual constructors, not assumed matching; left/right moved-head bond orientation must be exact. Count signal/helper/wrapper cost. Treat as structural clarity, not guaranteed line saving.

## R1 — WangTiles942ResetRows.interval_propagate

**PASS: mechanism remains additional under the full assumed-applied outcome baseline**

New mechanism: Use guarded Int induction on translated displacement x-x0.

Closest prior outcomes: EX007; R2-06; NF004. Prior Nat scanner/cycle propagation and finite invariant predecessor APIs do not cover two-sided integer intervals.

Already available: Int.induction_on; existing hnext/hprev; strict seed bounds.

Additional residual burden removed: The two Nat recursions, two toNat bridges and final sign split are absent only after this additional refactor. All promised prior iteration APIs still leave this two-sided interval proof.

Integration constraints: Guard the motive by both strict interval bounds. Do not assume propagation outside the interval; preserve both local step premises and all theorem binders.

## Rejected as new work

- Re-proposing any old decoder fusion, NorthView, direct South prefix, binaryWord congruence move, zero-base propagation specialization, CRT congruence or Fin2 helper.
- Completing formerly unimplemented depth-certificate adapters, constructor views, internal recursive-graph adapters or scanner migrations: these are already assumed completed.
- Mining the current long coefficient/scanner/Pell proofs merely because the old proposal has not been committed.
- Counting the optional `step_head_ne` direct derivation as source saving; it is a minor clarity variant and is excluded from the six headline mechanisms.
