# Source-only Lean transcription of the natural 81 graph

`P81NaturalForcedJ.lean` is an **uncompiled draft** of a literal expression
graph for the [natural 81 candidate](../ordinary14-natural-forcedj81/). The
14 `Fin 14` variable slots and four symbolic integer ports have the same
order as its JSON. Ten structure fields expose its five unit factors, output,
and four intermediate nodes. The `output_shape` proof is source text and
has not been elaborated.

The standalone checker parses the Lean source and compares all 81 rows,
operations and ordered operands to the SHA-256-pinned JSON; it also checks
aliases, topology, liveness, exposed fields, and the stated product shape.
It does not run Lean. This is source transcription evidence only: it does
not prove Lean semantics, bind symbolic ports to physical bytes or a PDF,
establish an iPRA proof, or prove the candidate's zero-existence argument.

An [independent source review](../../reviews/ordinary14-natural-forcedj81-lean-independent/README.md)
reconstructs the literal text from the pinned graph without running Lean.

```
python3 -I -S -B research/ordinary14-natural-forcedj81-lean-draft/check.py > /tmp/natural81-lean.json
cmp /tmp/natural81-lean.json research/ordinary14-natural-forcedj81-lean-draft/result.json
```
