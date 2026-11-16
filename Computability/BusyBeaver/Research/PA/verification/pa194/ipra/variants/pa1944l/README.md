# PA1944L source simulation

The [delivered PA1944L table](../../../../../docs/pa1944l_research_2026-11-14/machine/machine.tm)
has 194 working states and SHA-256
`c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253`.
Its decoder reassociates four increments, changing the trie addresses
while preserving the 3,673 resolved primary source instructions.
The generator pins its table, label map, and sites and compares the
delivered instruction list byte-for-byte with the primary list.

Lean checks [the exact dense rows](PA1944LRows.lean), the model-valued
[register operations](PA1944LBoxAgreement.lean), and the
[58,320-step blank run to the source root](PA1944LInitializer.lean).
The [native iPRA theorem](PA1944LNative.lean) derives both directions of
the consistency equivalence conditional on the finite site checks.

From the repository root, use the checked
[arbitrary-trie controller stage](../pa194lcc/README.md).

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
four_l=/dev/shm/pa1944l-model
bash "$variants/pa1944l/check.sh" /dev/shm/pa194lcc-controller "$four_l"
bash "$variants/check-linear-coverage.sh" PA1944L "$four_l" /dev/shm/pa1944l-coverage
```
