# Compact local cell digits

`CompactCellDigit.lean` defines a local digit function from a row and a
dummy bit. On the author-side word and payload-slot providers, Lean proves
that its selector positions, dummy position and all 41 copy positions have
the intended values, and that every digit is at most one when the dummy bit
is at most one. Tool session `18074` exited 0 without warnings or `sorryAx`;
the four printed reports contain only `propext`, `Classical.choice` and
`Quot.sound`. The sampled direct dependency and companion records remained
unchanged; the command, logs and hashes are retained in `observations/`.

This incremental single-author result inherits the word and lookup providers'
transitive and package ancestry. It does not yet prove uniform definability,
pack the digits into a cell, establish no-carry or graph-zero conditions, or
prove an iPRA endpoint.
