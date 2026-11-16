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
[`PA1944LFinal.consistency_iff_literal_nonhalt`](PA1944LFinal.lean)
applies the checked certificate for all 3,673 sites and proves the
unconditional iPRA equivalence.

From the repository root, use the checked
[arbitrary-trie controller stage](../pa194lcc/README.md).

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
four_l=/dev/shm/pa1944l-model
four_l_coverage=/dev/shm/pa1944l-coverage
bash "$variants/pa1944l/check.sh" /dev/shm/pa194lcc-controller "$four_l"
bash "$variants/check-linear-coverage.sh" PA1944L "$four_l" "$four_l_coverage"
bash "$variants/check-controller-final.sh" PA1944L "$four_l" "$four_l_coverage" /dev/shm/pa1944l-final
```

## Shared startup for LC_A and M4R

Lean checks that the 58,320-step PA1944L startup avoids dense controls
107 and 123. The [row comparisons](../PA194CommonStartupRows.lean) show
that LC_A and M4R agree with PA1944L on every other working control.
The [model startup theorems](../PA194CommonModelStartup.lean) transfer the
same trace to the two pinned tables in every arithmetic `IΣ₁` model.

The [LC_A](../pa194lca/PA194LCANative.lean) and
[M4R](../pa194m4r/PA194M4RNative.lean) native derivations use their exact
trie, register operations, and source root. Each takes the full finite
site certificate as its premise.

```sh
common=/dev/shm/pa194-common-startup
bash "$variants/check-common-startup.sh" "$four_l" "$common"
bash "$variants/check-shared-trie-model.sh" PA194LCA "$common" /dev/shm/pa194lca-model
bash "$variants/check-shared-trie-model.sh" PA194M4R "$common" /dev/shm/pa194m4r-model
bash "$variants/check-linear-coverage.sh" PA194LCA /dev/shm/pa194lca-model /dev/shm/pa194lca-coverage
bash "$variants/check-linear-coverage.sh" PA194M4R /dev/shm/pa194m4r-model /dev/shm/pa194m4r-coverage
```
