# PA194OR source simulation

The [delivered PA194OR table](../../../../docs/PA194ORH_research_2026-11-15/machines/PA194OR/machine.tm)
has 194 working states and SHA-256
`379e12957eafc5ecb1ec04868067fe931af913e7bc46e69a36b6067d83c4c79f`.
PA194OR rearranges the operand reader and changes 134 source addresses
while preserving the resolved 3,673-instruction program.

- [`PA194ORRows.rowAgreement`](PA194ORRows.lean) ties the native transition
  lookup used by the compressed checker to the first matching dense row.
- [`PA194ORMovedFirst`](PA194ORMovedFirst.lean) and
  [`PA194ORMovedSecond`](PA194ORMovedSecond.lean) check each moved address,
  its resolved instruction, and its symbolic branch outcomes.
- [`PA194ORPhysical.contract_sound`](PA194ORPhysical.lean) converts checked
  contracts to positive arithmetic execution segments when given the
  literal realizations of the register operations.
- [`PA194ORMark.mark`](PA194ORMark.lean) proves that the literal OR table
  marks any of the first nine unary register blocks at arbitrary
  model-valued lengths.
- [`PA194ORModelStartup.modeledStartup`](PA194ORModelStartup.lean) proves that
  58,170 steps from blank reach the common source seed in every `IΣ₁` model.
- [`PA194ORRoot.sourceRoot_eval`](PA194ORRoot.lean) relates the arithmetic
  root code to the checked OR trie, including model-valued header padding
  and register data.
  [`PA194ORInitializer.startup_root`](PA194ORInitializer.lean) identifies the
  startup configuration with that root at source site 25.
- [`PA194ORBoxAgreement.concreteBoxAgreement`](PA194ORBoxAgreement.lean)
  verifies the mark, zero and positive decrement, and increment operations
  used by the checker. Increment traverses and extends a spare list whose
  length may be nonstandard.
- [`PA194ORController.halt_iff_controller`](PA194ORController.lean) proves
  the modeled halting equivalence from the complete finite source
  certificates and the literal register engine. Its `literalBoxes` theorem
  supplies the register-engine premise.

Run from the repository root with fresh output directories.

```sh
pa=Computability/BusyBeaver/Research/PA
literal=/dev/shm/pa194-primary-for-or
shared=/dev/shm/pa194b-for-or
execution=/dev/shm/pa194-execution-for-or
bash "$pa/pa194/ipra/native-endpoint/check-literal.sh" "$PWD" "$literal"
bash "$pa/pa194/ipra/variants/pa194b/check.sh" "$literal" "$shared"
bash "$pa/shared/isigma1-machine/check-execution.sh" "$literal" "$shared" "$execution"
bash "$pa/pa194/ipra/variants/pa194or/check.sh" "$literal" "$shared" "$execution" /dev/shm/pa194or-replay
```

The replay regenerates the data from the pinned delivered table, labels,
source sites and instruction list. Lean checks the finite startup in 15
chunks, the exact row correspondence, and the moved-site certificates.
It also rebuilds the arithmetic root and register-engine proofs. The
checker uses the retained lower dependencies of the primary stages.
