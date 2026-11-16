# PA194-AD table and register allocation

The [delivered PA194-AD table](../../../../docs/pa194_conpa_2026-11-13/construction/tables/pa194_AD.tm)
has 194 working states and swaps the physical A and D registers. The table
SHA-256 is `27613aa92da79ba2ec6e2e88e0ac909fda218e06495ecc0af27201eac0e26c8f`.

- [`PA194ADTable.exact_table`](PA194ADTable.lean) checks the 388 rows against
  the primary table. Only dense row indices 219, 221 and 249 change, affecting
  the targets of the read-1 transitions at native controls 161, 17 and 144.
- [`PA194ADTable.run_eq_until`](PA194ADStep.lean) proves equality of the
  finite runs from any shared configuration as long as the primary run has
  read none of those three rows. It uses the existing primary semantics via
  [`primary_next` and `primary_run`](PA194ADBounded.lean).
- [`PA194ADStore`](PA194ADStore.lean) transports register access, single-register
  updates and tests under the A/D swap for any register value type.
- [`PA194ADFile`](PA194ADFile.lean) and [`PA194ADFrame`](PA194ADFrame.lean)
  transport the packed register file and the encoded source frame for
  arbitrary values in PRA models. They preserve the spare register and suffix.
- [`PA194ADDispatch`](PA194ADDispatch.lean) and [`PA194ADClock`](PA194ADClock.lean)
  define the companion's table lookup and packed clock. The model step
  agrees with the primary step at working rows outside the three changes.
- [`PA194ADStartupModel.startup_seed`](PA194ADStartupModel.lean) proves that
  the packed AD clock reaches the exact existing source seed after 58,122
  steps in every PRA model. The [standard clock bridge](PA194ADPackedStandard.lean)
  identifies its numerical run at every standard time, and Lean verifies
  the fifteen numerical startup checkpoints.
- [`PA194ADGenericRun.clock_run`](PA194ADGenericRun.lean) proves that the packed
  clock agrees with the generic arithmetic run at every clock in the `IΣ₁`
  reducts of the covered PRA models. Its `startup_seed` places the same
  finite initialization theorem directly on that arithmetic run.
- [`PA194ADCompressedRows.rowAgreement`](PA194ADCompressedRows.lean) relates
  the symbolic native transition table to the literal dense AD table.
  [`PA194ADBoxAgreement.concreteBoxAgreement`](PA194ADBoxAgreement.lean)
  supplies the literal mark, increment, and both decrement paths for the
  packed file, including arbitrary model-valued register and spare counts.
  [`PA194ADCompressedPhysical`](PA194ADCompressedPhysical.lean) converts
  checked source contracts into positive literal AD execution segments.

- [`PA194ADInitializer.startup_root`](PA194ADInitializer.lean) identifies
  the 58,122-step configuration with the exact coded AD source root.
  [`PA194ADControllerEndpoint.halt_iff_controller_literal`](PA194ADControllerEndpoint.lean)
  proves the halting comparison at arbitrary model-valued clocks, given
  the finite source certificates.
- [`PA194ADNative.consistency_iff_literal_nonhalt`](PA194ADNative.lean)
  derives the equivalence in standard iPRA given those same certificates.
  The kernel-checked coverage now supplies all 3,673 certificates, and
  [`PA194ADFinal.consistency_iff_literal_nonhalt`](PA194ADFinal.lean) gives the
  unconditional derivation. Its axiom audit reports `propext`,
  `Classical.choice`, and `Quot.sound`.

Run from the repository root with a fresh output directory.

```sh
dir=Computability/BusyBeaver/Research/PA/pa194/ipra/variants/pa194ad
bash "$dir/check.sh" /dev/shm/pa194ad-replay
```

The checker pins both delivered tables and label lists, regenerates the
primary row data and startup checkpoints, verifies all companion row
literals, and builds the proofs in one output directory. It uses the
retained primary scheduler dependency path, which can be passed as the
second argument.

The model-run replay also takes the checked primary and PA194B stages.

```sh
bash "$dir/check-model-run.sh" "$literal" "$shared" /dev/shm/pa194ad-replay /dev/shm/pa194ad-model-run
```

With the [shared register stage](../../../../shared/isigma1-machine/README.md)
and the AD startup output, replay the compressed table and literal register
proofs.

```sh
ad_registers=/dev/shm/pa194ad-registers
ad_controller=/dev/shm/pa194ad-controller
ad_coverage=/dev/shm/pa194ad-coverage
bash "$dir/check-registers.sh" "$register" /dev/shm/pa194ad-replay "$ad_registers"
bash "$dir/check-controller.sh" "$ad_registers" /dev/shm/pa194ad-model-run "$ad_controller"
bash "$dir/check-coverage.sh" "$ad_registers" "$ad_coverage"
bash "$dir/../check-controller-final.sh" PA194AD "$ad_controller" "$ad_coverage" /dev/shm/pa194ad-final
```
