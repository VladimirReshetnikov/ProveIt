# PA194 finite controls in arbitrary PRA models

`PA194FiniteControls.lean` proves, in every model of the candidate classical
PRA, that parity of every model tape value is 0 or 1 and every control below
numeral 194 is one of the 194 standard control numerals. Combining these facts
with the explicit table lookup and the kernel-checked `PA194Bounded` table
binding, `modelWorkingLiteralRow` selects a literal `PA194.Literal.transition`
row and proves all three explicit lookup outputs equal its model numerals.
The model tape values may be nonstandard. This is an all-model Lean theorem,
not yet an iPRA derivation, source-runtime simulation, or consistency result.

Replay with the same overlays as the main machine-code README:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-controls.sh
```

The checker regenerates the pinned table, rebuilds the complete dependency
chain in a private directory, and rejects `sorryAx` in printed dependencies.
The transitive prebuilt overlay objects are assumed to match their recorded
sources; this script does not independently rebuild all of them.
