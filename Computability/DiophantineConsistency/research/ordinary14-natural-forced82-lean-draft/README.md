# Source-only Lean transcription of the natural 82 graph

`P82NaturalForced.lean` is an **uncompiled draft** of a literal expression
graph for the [natural 82 candidate](../ordinary14-root74-natural-forced82/).
The 14 `Fin 14` variable slots and four symbolic integer ports are in the
same order as the candidate JSON. The ten structure fields expose its five
unit factors, final output and four intermediate nodes. The stated
`output_shape` proof is source text and has not been elaborated.

The standalone checker parses the Lean source independently and compares
all 82 rows, operations and ordered operands to the SHA-256-pinned JSON;
it also checks aliases, topology, liveness, exposed fields, and the stated
product shape. It does not run Lean. This check is evidence of source
transcription only: it does not prove Lean syntax or semantics, bind the
symbolic ports to physical coefficient bytes or a PDF, establish an iPRA
proof, or verify the candidate's external zero-existence argument.

The transcription has an [independent source review](../../reviews/ordinary14-natural-forced82-lean-draft-independent/README.md);
that review also does not establish elaboration or semantics.

```
python3 -I -S -B research/ordinary14-natural-forced82-lean-draft/check.py > /tmp/natural-forced82-lean.json
cmp /tmp/natural-forced82-lean.json research/ordinary14-natural-forced82-lean-draft/result.json
```
