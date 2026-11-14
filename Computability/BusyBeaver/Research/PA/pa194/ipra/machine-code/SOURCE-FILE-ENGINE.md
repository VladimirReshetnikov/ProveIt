# PA194 physical segment on a permuted source file

`PA194SourceFileEngine.lean` combines the actual imported source-register
permutation in `REGISTER-PERMUTATION.md` with the physical first-register
segment in `REGISTER-ENGINE.md`. The numeric file has ten physical register
blocks: the nine permuted logical source registers and one spare, followed by
an arbitrary tape suffix. Physical slot 0 corresponds to logical source
register 2.

For any candidate classical PRA model, start the literal PA194 machine in
dense state 12 with an arbitrary left tape half `l` and this encoded file as
the right half. If logical register 2 has value `v`, after exactly `2+v`
physical steps the machine is in state 13. Its right half contains precisely
the remaining nine physical register blocks and suffix; its left half is
`zeros(v,4*l)`. The source register values, spare, tape halves, and suffix
may be arbitrary model elements, including nonstandard ones.

`PA194SourceFileEngineSentence.lean` proves the corresponding universally
closed, twelve-variable primitive-recursive-code equality in candidate
classical PRA and transfers it to native iPRA. The fixed physical permutation
is checked against the actual imported `M6.Source.physicalRegister`; the
standard-list connection to `M6.Runtime.sepsR` is checked separately in
`REGISTER-FILE.md`.

This is a local physical segment on a correctly permuted source file. It does
not yet prove a complete source instruction, a nonstandard full-program
simulation, or either machine-consistency direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-source-file-engine.sh
```

The checker regenerates the pinned PA194 table, rebuilds the source-file,
permutation, and physical-run dependencies, checks selected source and
overlay object hashes, and rejects `sorryAx`. Other transitive prebuilt
overlay objects are assumed to correspond to their recorded sources; the
entire foundation and iPRA chain is not rebuilt by this replay.
