# Register-file leading bits in arbitrary PRA models

`PA194RegisterFileHead.lean` extends `REGISTER-FILE.md` by connecting the
numeric file code to the actual parity and half codes used by the PA194
physical step. For any fixed positive number of register blocks, every
candidate classical PRA model reads the first bit as zero. After dividing
by two, it reads the mandatory first one; dividing again gives precisely the
remaining `v` one bits followed by the encoded suffix. The register value
`v`, the other register values, and the suffix may all be nonstandard model
elements.

This is an all-model numeric tape/frame building block. It does not by itself
establish a nonstandard source-step simulation, a full register permutation,
or a consistency equivalence.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-register-head.sh
```

The checker regenerates the pinned PA194 table, rebuilds the register-file
modules and their machine-code dependencies, checks selected source and
overlay object hashes, and rejects `sorryAx`. Other transitive prebuilt
overlay objects are assumed to correspond to their recorded sources; the
entire foundation and iPRA chain is not rebuilt by this replay.
