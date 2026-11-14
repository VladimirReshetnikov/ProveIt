# PA194 first-register physical segment

`PA194RegisterEngine.modelFirstRegister` connects the numeric register-file
encoding in `REGISTER-FILE.md` directly to the actual PA194 machine run. In
any candidate classical PRA model, start in dense state 12 with left half
`l` and the right half containing a fixed positive number of encoded
register blocks followed by an arbitrary suffix. If the first register has
value `v`, after exactly `2+v` physical steps the machine is in state 13.
The right half is the encoded remaining register blocks and suffix; the left
half is `zeros(v,4*l)`, because the crossed separator and one bits have been
written as zeros.

The number of remaining register blocks is a fixed standard syntax parameter;
all register values, the left half, and suffix may be arbitrary model
elements, including nonstandard ones. The proof composes the all-model
register-file code equations with the connected literal state-12/13 machine
segment. `PA194RegisterEngineSentence.lean` proves the corresponding
universally closed primitive-recursive-code equality in candidate classical
PRA and transfers it to native iPRA for every fixed arity. Thus the physical
segment itself is established in the object theory.

The companion standard-natural theorem `PA194RegisterFileStandard.sourceFile`
binds the code to the actual imported `M6.Runtime.sepsR` list encoding. This
is a local source-frame building block: it does not yet prove the full
source-to-physical instruction simulation, the source register permutation,
or either direction of the machine-consistency equivalence.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-register-engine.sh
```

The checker regenerates the pinned PA194 table, rebuilds the source-file and
machine-segment dependencies, checks selected source and overlay object
hashes, and rejects `sorryAx`. Other transitive prebuilt overlay objects are
assumed to correspond to their recorded sources; the entire foundation and
iPRA chain is not rebuilt by this replay.
