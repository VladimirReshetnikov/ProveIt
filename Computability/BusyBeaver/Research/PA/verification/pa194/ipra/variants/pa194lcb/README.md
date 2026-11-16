# PA194LC_B literal source controller

The [delivered LC_B table](../../../../../docs/pa194_loop_continuation_research_2026-11-14/machines/PA194LC_B/machine.tm)
has 194 working states and SHA-256
`4b2b45e97fdd5f8a6e22c4f552dc3f26252c170e85cdb5ddb27ad5d5c580982a`.
The generator pins the table, labels, and site list and checks the resolved
source instruction list byte for byte against primary PA194.

Lean checks the [literal row agreement](PA194LCBRows.lean), [model-valued
register operations](PA194LCBBoxAgreement.lean), and [58,320-step blank
startup to the source root](PA194LCBInitializer.lean). The
[controller](PA194LCBController.lean) gives halting equivalence with the
primary source in all covered models under the finite site-check premise.
[The final theorem](PA194LCBFinal.lean) applies the checked certificate
for all 3,673 sites and proves the unconditional consistency equivalence
in iPRA.

From the repository root, use the checked [trie controller
stage](../pa194lcc/README.md).

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
lcb=/dev/shm/pa194lcb-model
bash "$variants/pa194lcb/check.sh" /dev/shm/pa194lcc-controller "$lcb"
bash "$variants/check-linear-coverage.sh" PA194LCB "$lcb" /dev/shm/pa194lcb-coverage
bash "$variants/pa194lcb/check-native.sh" "$lcb" /dev/shm/pa194lcb-native
bash "$variants/check-controller-final.sh" PA194LCB /dev/shm/pa194lcb-native /dev/shm/pa194lcb-coverage /dev/shm/pa194lcb-final
```
