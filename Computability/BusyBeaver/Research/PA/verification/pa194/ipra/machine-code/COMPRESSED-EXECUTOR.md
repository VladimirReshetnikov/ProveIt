# Compressed execution of the literal PA194 machine

`PA194CompressedExecutor.checkedRun` interprets every successful
`M6.Runtime.exec` certificate as a literal PA194 run with a model-valued clock.
It reuses the staged bidirectional scan theorem for runs of length
`a * gap + c`. All tape halves and gap parameters may be nonstandard
elements of a PRA model. It also proves the clock positive when the executor
started with its movement flag false.

`PA194FoldedRuntimeRows.agreement` instantiates the exact dense row premise
by decoding native control names through the packet's checked control list.
Consequently the selector can retain the register oracle's original control
names while reading the literal dense table directly.

The register file remains an explicit model-local `BoxAgreement` premise.
It states that each file starts with a separator and that the marking,
increment and decrement oracles carry out their specified physical segments.
A complete source-instruction theorem still needs these contracts, normalized
endpoint equalities and verified certificate coverage.

Run from the repository root with a fresh output directory.

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-compressed-executor.py \
  "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-compressed-executor-repo \
  /dev/shm/pa194-bidirectional-run-scan-repo \
  /dev/shm/pa194-bidirectional-generic-repo \
  /dev/shm/pa194-symbolic-zipper-repo \
  /dev/shm/pa194-site28-work/build-carry-roundtrip \
  /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2/foundation-view \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

All three modules rebuild in one output. The checker records and verifies
hashes of the selected direct imports and local sources. The older physical,
M6 and Foundation stages remain prebuilt, with no authentication of their full
transitive source closure.
