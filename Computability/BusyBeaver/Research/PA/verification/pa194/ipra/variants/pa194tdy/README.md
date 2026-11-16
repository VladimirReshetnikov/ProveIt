# PA194TDY source simulation

The [delivered PA194TDY table](../../../../../docs/pa194_tdy_2026-11-14/artifacts/pa194_tdy.tm)
has 194 working states and SHA-256
`84bfe1368312c7c71c9e4706de7cb65923310e25f8d472997c9c57c5aedd7934`.
The generator pins its dense-to-native map and checks the four selector
changes against the primary native rows. The resolved instructions and
source addresses match the primary 3,673-site program.

- [`PA194TDYRows.rowAgreement`](PA194TDYRows.lean) matches the exact
  dense transitions to the native cache.
- [`PA194TDYBoxAgreement.concreteBoxAgreement`](PA194TDYBoxAgreement.lean)
  covers the marked register operations and spare extension at arbitrary
  model-valued lengths.
- [`PA194TDYSeed.startup_root`](PA194TDYSeed.lean) connects the blank run
  at step 57,594 to the exact source seed for the TDY register order.
- [`PA194TDYSourceEndpoint.endpoint`](PA194TDYSourceEndpoint.lean) gives
  both directions of the modeled comparison with the shared source
  controller, conditional on the 3,673 finite site checks.
- [`PA194TDYNative.consistency_iff_literal_nonhalt`](PA194TDYNative.lean)
  derives both iPRA directions from those finite checks.
- [`PA194TDYFinal.consistency_iff_literal_nonhalt`](PA194TDYFinal.lean)
  applies the checked certificate for all 3,673 sites to prove the
  unconditional iPRA equivalence for the literal table.

From the repository root, use the checked
[PA194P5 model stage](../pa194p5/README.md).

```sh
pa=Computability/BusyBeaver/Research/PA/verification
tdy="$pa/pa194/ipra/variants/pa194tdy"
tdy_model=/dev/shm/pa194tdy-model
tdy_native=/dev/shm/pa194tdy-native
tdy_coverage=/dev/shm/pa194tdy-coverage
bash "$tdy/check.sh" "$p5_model" "$tdy_model"
bash "$tdy/../check-selector-native.sh" PA194TDY "$tdy_model" "$tdy_native"
bash "$tdy/../check-selector-coverage.sh" PA194TDY "$tdy_model" "$tdy_coverage"
bash "$tdy/../check-controller-final.sh" PA194TDY "$tdy_native" "$tdy_coverage" /dev/shm/pa194tdy-final
```
