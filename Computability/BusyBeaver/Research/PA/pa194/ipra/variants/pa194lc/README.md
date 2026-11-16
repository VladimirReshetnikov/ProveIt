# PA194LC source simulation

The [delivered PA194LC table](../../../../docs/pa194_loop_continuation_research_2026-11-14/machines/PA194LC/machine.tm)
has 194 working states and SHA-256
`9cb620ba1b869fb793fd9ba0a99e90dcc85d9a6d62a42f48109743a7fbeda3c8`.
The three native transition edits change 305 source addresses. The
delivered resolved instruction list is byte-identical to the primary
list of 3,673 instructions.

- [`PA194LCRows.rowAgreement`](PA194LCRows.lean) binds every native
  transition used by the symbolic checker to the literal dense table.
- [`PA194LCBoxAgreement.concreteBoxAgreement`](PA194LCBoxAgreement.lean)
  supplies literal marking, increment, spare extension, and both decrement
  outcomes at arbitrary model-valued register lengths.
- [`PA194LCPhysical`](PA194LCPhysical.lean) turns checked source contracts
  into positive literal execution segments. [`PA194LCSamples`](PA194LCSamples.lean)
  checks two of the altered five-instruction loops.
- [`PA194LCModelStartup.modeledStartup`](PA194LCModelStartup.lean)
  proves that 58,154 steps from blank reach the common packed seed
  in every `IΣ₁` model.
- [`PA194LCInitializer.startup_root`](PA194LCInitializer.lean) identifies
  that seed with the exact LC source root.
  [`PA194LCController.halt_iff_controller`](PA194LCController.lean) compares
  halting at arbitrary model-valued clocks using the source certificates
  and the checked LC boxes.
- [`PA194LCNative.consistency_iff_literal_nonhalt`](PA194LCNative.lean)
  derives both directions in standard iPRA conditional on the finite
  source certificates.

From the repository root, use the verified
[shared register stage](../../../../shared/isigma1-machine/README.md).

```sh
pa=Computability/BusyBeaver/Research/PA
lc="$pa/pa194/ipra/variants/pa194lc"
lc_base=/dev/shm/pa194lc-base
lc_startup=/dev/shm/pa194lc-startup
bash "$lc/check.sh" "$register" "$lc_base"
bash "$lc/check-startup.sh" "$lc_base" "$lc_startup"
bash "$lc/check-controller.sh" "$lc_startup" /dev/shm/pa194lc-controller
bash "$lc/check-coverage.sh" "$lc_base" /dev/shm/pa194lc-coverage
```

The startup replay uses 15 numerical chunks and lifts their composition
to model-valued arithmetic. Checking every source-site certificate is the
remaining premise. The finite replay is in progress.
