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

From the repository root, use the verified
[shared register stage](../../../../shared/isigma1-machine/README.md).

```sh
pa=Computability/BusyBeaver/Research/PA
lc="$pa/pa194/ipra/variants/pa194lc"
lc_base=/dev/shm/pa194lc-base
bash "$lc/check.sh" "$register" "$lc_base"
bash "$lc/check-startup.sh" "$lc_base" /dev/shm/pa194lc-startup
bash "$lc/check-coverage.sh" "$lc_base" /dev/shm/pa194lc-coverage
```

The startup replay uses 15 numerical chunks and lifts their composition
to model-valued arithmetic. The finite source coverage replay is in
progress.
