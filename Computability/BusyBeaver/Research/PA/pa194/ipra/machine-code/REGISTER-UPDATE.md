# Source-register updates and the physical file

`PA194RegisterUpdate.lean` proves that updating any logical register in the
input to the physical file constructor from `REGISTER-PERMUTATION.md`
commutes with the exact imported `M6.Source.physicalRegister` permutation.
The result is the physical argument vector with only the corresponding
physical register slot updated. The tenth spare and the tape suffix are
separate slots and are preserved.

The update and permutation theorem is parametric in the value type. Its
specialization to natural-number source registers agrees exactly with the
actual `M6.Source.write`. `modelSourceWrite` then binds the updated vectors
to the primitive-recursive physical file code in every candidate classical
PRA model, including for nonstandard values.

This is a static source-store/frame correspondence. It does not yet show
that the physical machine implements a source update, a full instruction,
or either machine-consistency direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-register-update.sh
```

The checker regenerates the pinned PA194 table, rebuilds the register-file
and source-permutation dependencies, checks selected source and overlay
object hashes, and rejects `sorryAx`. Other transitive prebuilt overlay
objects are assumed to correspond to their recorded sources; the entire
foundation and iPRA chain is not rebuilt by this replay.
