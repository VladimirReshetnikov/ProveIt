# Ordinary certificates and shared semantic lemmas

The [combined Lean check](lean/README.md) validates the 184-module K215 endpoint
closure: 37 affected modules were freshly compiled and 147 predecessor
objects reused with exact source, dependency, object and log bindings. Both
typed endpoint clients pass with ten standard axiom reports and zero audit
warnings. The literal machine and both endpoint statements are unchanged.

The [source simulation](source-checker/README.md) now uses ordinary bisimulation.
All 2,240 certificate offsets were zero, so the generated data omits that field
and the endpoint no longer imports the integer-offset proof. The checker shares
one soundness argument for an arbitrary path decoder. K215 keeps its original
512-step decoding; substituting the legacy 128-step decoder changes
622 certificate entries.
All sixteen converted chunks are freshly kernel-checked, and regeneration
reproduces all eighteen Lean outputs. Source data decreases from 456,548 to
432,131 bytes. The retained offset checker and original ordinary API pass
separate compatibility checks.

The same packet records the register simulation's shared car/cdr cases and run
composition, shortening its main induction from 83 to 61 lines. The
[semantic lemmas](semantic-lemmas/README.md) remove 56 repeated impossible-tag
cases from `InternalSat` and share bounded-quantifier transport in
`ConstructibleAbs`. Those files decrease by 112 and five lines respectively;
their existing statements and executable definitions remain exact.

The zero-offset proposal comes from [Source 167](../../../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-204.md), delivered in
[05d063acef](https://github.com/VladimirReshetnikov/ProveIt/commit/05d063acef).
Its symmetry proposal was already checked in [phase two](../phase2/README.md).
The alternate GC–ZC215 construction remains separate from the accepted K215.
The [decoder-trace investigation](../../../../decoder-sharing-research/notes.md)
is preliminary; no checker speedup is established by its local counts.

This is an incremental check against the immutable
[185-module phase-four basis](../phase4/README.md). The
[compatibility refresh](legacy/README.md) checks fifteen additional modules and
five retained interfaces. Earlier receipts and failed attempts remain intact.
The external proof-assistant endpoint still supplies no internal PA derivation
or minimum-size theorem.
