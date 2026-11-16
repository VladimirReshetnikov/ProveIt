# PA194P5 source simulation

The [delivered PA194P5 table](../../../../docs/pa194p5_research_2026-11-14/machine/pa194p5.tm)
has 194 working states and SHA-256
`cf3a2c2d3ba8e95d5c0ea825c3f279ae529b6591cc1280264b0ba3793e77d026`.
The generator verifies the seven selector edits against the pinned
primary table and checks the reconstructed native bytes against their
SHA-256 `a9d3a13786b6a0018713d8803865860b5e9e26692fde34975545c3bb0f09501c`.
P5 preserves all 3,673 resolved instructions and their addresses.

- [`PA194P5Rows.rowAgreement`](PA194P5Rows.lean) relates the native cache
  to the literal dense transitions.
- [`PA194P5BoxAgreement.concreteBoxAgreement`](PA194P5BoxAgreement.lean)
  verifies marking, increment, spare extension, and both decrement
  outcomes at arbitrary model-valued lengths.
- [`PA194P5ModelStartup.modeledStartup`](PA194P5ModelStartup.lean)
  identifies the packed configuration reached from blank at step 56,158
  in every `IΣ₁` model. [`PA194P5Seed.startup_root`](PA194P5Seed.lean)
  identifies that configuration with the exact source root.
- [`PA194P5SourceEndpoint.endpoint`](PA194P5SourceEndpoint.lean) compares
  blank-run halting with source-controller halting at model-valued clocks.
  It takes the finite source certificates as its remaining premise.
- [`PA194P5Native.consistency_iff_literal_nonhalt`](PA194P5Native.lean)
  derives both iPRA directions from that same premise.
- [`PA194P5Final.consistency_iff_literal_nonhalt`](PA194P5Final.lean) uses
  the checked certificate for all 3,673 sites to prove the unconditional
  iPRA equivalence for the literal table.

From the repository root, use the checked
[PA194HX controller](../pa194hx/README.md) and
[PA194LC table](../pa194lc/README.md) stages.

```sh
pa=Computability/BusyBeaver/Research/PA
p5="$pa/pa194/ipra/variants/pa194p5"
p5_model=/dev/shm/pa194p5-model
p5_native=/dev/shm/pa194p5-native
p5_coverage=/dev/shm/pa194p5-coverage
bash "$p5/check.sh" "$hx_controller" "$lc_base" "$p5_model"
bash "$p5/../check-selector-native.sh" PA194P5 "$p5_model" "$p5_native"
bash "$p5/../check-selector-coverage.sh" PA194P5 "$p5_model" "$p5_coverage"
bash "$p5/../check-controller-final.sh" PA194P5 "$p5_native" "$p5_coverage" /dev/shm/pa194p5-final
```

The model replay regenerates the dense and native tables and checks the
fourteen startup chunks. The coverage replay checks all 58 batches and
their aggregate certificate.
