# Independent review: natural-80 recorded ancestry expansion

The [natural-80 ancestry inspection](../../research/ordinary14-natural80-recorded-ancestry-audit/README.md)
reproduces and its bounded recorded-closure comparison is supported. The
independent checker below runs no Lean process.

This checker pins the natural-80 receipt, qualified-cut receipt, earlier
root74 survey and retained build state. It separately reconstructs the
recorded project edge graph using FIFO traversal from both the 31 earlier
seeds and the 40 natural-80 seeds. The reached sets and external names agree;
the nine additional seed names were already in the old recorded closure. It
reproduces the 627 P72 and 919 base producers, 4,414 recorded edges and 80
external leaf names, and compares the sorted-set digests with the natural-80
receipt. It also checks that the 29,860 guard-slot counts agree with the
previous independent receipt.

For current source, object, link, external-edge and guard-slot bytes, this
review deliberately **replays** the pinned, independently reviewed
[root74 recorded-ancestry checker](../ordinary14-root74-recorded-ancestry-independent/README.md)
and compares its exact output. It is not a second independent implementation
of those file/guard checks. The closure-equality traversal is separately
implemented, but both reviews consume the same pinned retained records and
filesystem. They therefore do not independently establish the historical
authenticity of the earlier P72 row records. The inspector's final row is
anchored by progress metadata; the other observed row files are not each
independently anchored by that fact.

Neither this review nor the underlying records establish the 80 external
leaves' transitive package, toolchain, runtime or implicit-import closure,
required companion loading, actual Lean resolution, provider compatibility,
or an iPRA theorem. Reads are non-atomic and depend on temporary retained
paths. No immutable snapshot or resource slot is reserved.

Run from the repository root while the retained paths remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-recorded-ancestry-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-recorded-ancestry-independent/result.json
```
