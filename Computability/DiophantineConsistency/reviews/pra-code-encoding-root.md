# PRA function-code encoding: independent replay

29 October 2026. The new module gives finite arity-indexed function codes a
numeric encoding via tagged binary trees and Cantor pairing. Its decoder
checks constructor and arity constraints, and Lean proves the exact
`decodeCode n (encodeCode c) = some c` roundtrip. Focused checks exercise
invalid composition, a wrong requested arity, and an out-of-range projection.

I read the source and independently rebuilt the main and checks in a fresh
private provider with Lean 4.32, `-M6000 -j1 -DElab.async=false`. Both object
hashes and complete logs match the author's clean pair. The main log is empty;
four axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The checked parent code objects and existing Mathlib package objects were
reused; no complete Mathlib source rebuild is claimed. The replay driver,
state, logs and author's initial import-overlay failure are retained in
[pra-code-encoding-root-replay](pra-code-encoding-root-replay/). The author
notes that earlier scratch versions were not all separately snapshotted.

This establishes Lean encodability and the roundtrip. It does not prove the
codec or axiom recognition primitive recursive, define PRA derivability, or
prove conservation.
