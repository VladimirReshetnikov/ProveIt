# Independent review: proposed root-74 iPRA adapter

**PASS at source-interface scope.** The native, standard and equality-only
statements use the corresponding `native_of_positive`, `standard_of_positive`
and `reference_of_positive` interfaces with the same 74 expression,
`positiveShift`, and proposed `PositiveModelBridge`. The first two use the
mapped native-refutation right-hand side; the third erases both the no-zero
formula and mapped refutation in the same positions as the existing reference
interface. The three declaration bodies and statements agree byte-for-byte
with the root-78 adapter after the bridge namespace substitution.

The checker pins the 74 adapter, its positive-bridge source, the existing
interface and root-78 adapter; compares the exact theorem blocks; checks all
three applications; and replays the author receipt. The 74 positive bridge is
separately under review: pinning its source is not review or elaboration of
that bridge. Neither its transitive dependencies nor the adapter have been
Lean-checked. No provider closure, axiom replay, checked iPRA theorem, physical
byte/PDF binding, or Lean run is asserted.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary14-root74-ipra-endpoint-independent/check.py | cmp - reviews/ordinary14-root74-ipra-endpoint-independent/observation.json
```
