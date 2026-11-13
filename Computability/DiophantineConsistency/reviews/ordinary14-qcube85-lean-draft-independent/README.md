# Independent source review: literal 85-row graph

The generated graph's 85 literal rows, ordered dependencies, input and port
bindings, and six exposed fields match the pinned candidate on source review.
The output-shape expression follows the candidate's final sum of squares.
The checker independently parses the literal Lean rows and compares them to
the JSON rows, checks every named dependency, pins the source and syntax
interface, and replays the author's generator and receipt.

This is source review only: the generator has not elaborated the Lean code,
and the output-shape theorem, source/object providers, model theorem, iPRA
endpoint, operation-count proof and external equation binding remain unproved.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-qcube85-lean-draft-independent/check.py > /tmp/qcube85-independent.json
cmp /tmp/qcube85-independent.json reviews/ordinary14-qcube85-lean-draft-independent/result.json
```
