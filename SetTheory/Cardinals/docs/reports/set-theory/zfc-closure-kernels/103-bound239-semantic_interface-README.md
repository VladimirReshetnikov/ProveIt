# Register-path semantic interface

`RegisterPath.lean` is the exact upstream file fetched read-only from
[`VladimirReshetnikov/ProveIt` at commit `13ec39ed43148b1807f51ed6e6528e1c84659562`](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RegisterPath.lean).
Its Git blob SHA-1 is `ee8b60a3c3971472004755fb08e6e264550b5bc8`.
That identifier was independently recomputed from the saved bytes using the
Git object prefix `blob <byte-length>\0`. The result and SHA-256 digest are in
`semantic_interface.json`.

A direct reading of these definitions confirmed their exact correspondence
with `formalism/source_result.tex` and its independent source control-flow
checker. Paths are read most-significant bit first, with implicit trailing
zeros; `0` selects the first child and `1` the second. After finding a leaf at
depth `d`, the executor zero-extends and truncates its input to exactly `d`
bits. Increment preserves word length and rolls all ones over to all zeros.
Break strips through the requested zero from the right and then increments;
continue strips through the requested one. Explicit break and continue each
take one source step and preserve all registers.

The accompanying record lists every instruction branch, including both cases
of decrement, and distinguishes literal halting from decoder fuel exhaustion.
The identified baseline DAG has maximum depth 51 and supplies fuel 204, so
fuel exhaustion cannot occur there. The checker also imposes the stronger
canonicality condition on unused successor suffixes disclosed in the TeX.

This is a documented comparison of concrete definitions, not a new Lean
kernel proof or a replacement for the source-equivalence and binary-runtime
certificates. No Lean dependencies were built. The upstream source retains
its original attribution and notices. Previously frozen artifacts were left
unchanged.
