# Source-only Lean transcription of the natural 80 graph

`P80NaturalForcedGamma.lean` is an **uncompiled draft** of a literal
expression graph for the [natural 80/107 candidate](../ordinary14-natural-forced-gamma80/).
The 14 `Fin 14` variable slots and four symbolic integer ports use the same
order as its JSON. Ten structure fields expose the five unit factors, final
output and four intermediate nodes. The `output_shape` proof is source text
and has not been elaborated.

The deterministic checker parses the Lean source and compares all 80 rows,
operations and ordered operands to the SHA-256-pinned JSON; it also checks
aliases, topology, liveness, exposed fields, and the stated product shape.
It does not run Lean. This is source transcription evidence only: it does
not prove Lean semantics, bind symbolic ports to physical bytes or a PDF,
establish an iPRA proof, or prove the candidate's zero-existence argument.

An [independent source review](../../reviews/ordinary14-natural-forced-gamma80-lean-independent/README.md)
reconstructs the source from the pinned graph without running Lean.

```
python3 -I -S -B research/ordinary14-natural-forced-gamma80-lean-draft/check.py > /tmp/natural80-lean.json
cmp /tmp/natural80-lean.json research/ordinary14-natural-forced-gamma80-lean-draft/result.json
```
