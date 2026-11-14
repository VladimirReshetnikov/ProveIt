# Logical-to-physical register-file code

`PA194RegisterPermutation.lean` constructs one explicit primitive-recursive
code for a ten-block physical register file. Its arguments are the nine
logical source registers, a tenth physical spare register, and a numeric tape
suffix. The code applies the inverse physical-slot order
`[2,8,1,4,3,7,0,5,6,9,10]` before invoking `fileCode 10` from
`REGISTER-FILE.md`.

The finite inverse calculation is checked against the actual imported
`M6.Source.physicalRegister`; the spare and suffix remain at arguments 9 and
10. In every candidate classical PRA model, interpreting the constructed
code equals interpreting the ten-block file code on the permuted arguments,
and the physical slot selected by each source register contains exactly that
source argument. Register values, spare, and suffix may be nonstandard model
elements.

This establishes the static encoding and permutation. It does not yet prove
a nonstandard source-step simulation or either machine-consistency direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-register-permutation.sh
```

The checker regenerates the pinned PA194 table, rebuilds the register-file,
source-permutation, and machine-code dependencies, checks selected source and
overlay object hashes, and rejects `sorryAx`. Other transitive prebuilt
overlay objects are assumed to correspond to their recorded sources; the
entire foundation and iPRA chain is not rebuilt by this replay.
