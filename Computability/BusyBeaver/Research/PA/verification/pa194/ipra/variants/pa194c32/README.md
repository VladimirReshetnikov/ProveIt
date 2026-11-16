# PA194C32 source simulation

The [delivered C32 table](../../../../../docs/pa194_ax11hc4_c32_research_2026-11-15/construction/cycle32/pa194_cycle32.tm)
has 194 working states and SHA-256
`3af42ea9d430e5df22b69e6fc540e3530f87263372580c7c554bae37ba524ac8`.
The generator pins its dense-to-native map and checks the seven changed
native selector rows. It expands the pinned compact grammar and compares
all 3,673 address, operator, and operand triples with the primary source.
The logical registers use physical positions `[6,4,0,3,2,8,7,5,1]`.

- [`PA194C32Rows.rowAgreement`](PA194C32Rows.lean) matches the native cache
  to the literal dense transitions.
- [`PA194C32BoxAgreement.concreteBoxAgreement`](PA194C32BoxAgreement.lean)
  verifies the register operations and spare extension at model-valued lengths.
- [`PA194C32Seed.startup_root`](PA194C32Seed.lean) connects the literal
  56,250-step blank run to the exact source root for this register allocation.
- [`PA194C32Native.consistency_iff_literal_nonhalt`](PA194C32Native.lean)
  gives both iPRA directions from the 3,673 finite site checks.
- [`PA194C32Final.consistency_iff_literal_nonhalt`](PA194C32Final.lean)
  applies the complete checked certificate and proves the unconditional
  iPRA equivalence for the literal table.

From the repository root, use the checked
[PA194P5 model stage](../pa194p5/README.md).

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
c32_model=/dev/shm/pa194c32-model
c32_native=/dev/shm/pa194c32-native
c32_coverage=/dev/shm/pa194c32-coverage
bash "$variants/check-selector-model.sh" PA194C32 "$p5_model" "$c32_model"
bash "$variants/check-selector-native.sh" PA194C32 "$c32_model" "$c32_native"
bash "$variants/check-selector-coverage.sh" PA194C32 "$c32_model" "$c32_coverage"
bash "$variants/check-controller-final.sh" PA194C32 "$c32_native" "$c32_coverage" /dev/shm/pa194c32-final
```
