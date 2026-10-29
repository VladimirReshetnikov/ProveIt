# Finite primitive-recursive function-code encoding

The `PRACodeEncoding` module defines an explicit numerical representation of
`PRAFiniteFunctionCodes.Code n`. Constructors and arities are encoded as a
tagged binary tree; the tree is encoded using `Nat.pair`. A total decoder of
numbers to trees decreases the unpair components. The subsequent structural
parser checks projection bounds and all composition, recursion and list arities
before constructing indexed syntax. Lean proves both tree and code roundtrips,
including `decodeCode n (encodeCode c) = some c`, and supplies the resulting
`Encodable (Code n)` instance.

The focused checks include malformed composition, an incorrect requested arity,
and an out-of-range projection. Four axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

The main and checks compiled cleanly with Lean 4.32 under
`-M6000 -j1 -DElab.async=false`, with a private output directory at
`/tmp/pra-code-encoding-20261029/lib`. The compiler used the existing Mathlib
package cache and the previously checked private `PRAFiniteFunctionCodes`
provider; this is not a fresh transitive Mathlib build or independent replay.
Source snapshots and logs are in the sibling `logs` directory. The first main
command failed because the first search root contained the namespace directory
but not its prerequisite object; `main.log` preserves that diagnostic. After
linking the two actual prerequisite objects into that private root, the second
main command and checks passed; `main-2.log` is empty. Scratch development
attempts preceded this frozen pair and were not all snapshotted separately;
the current scratch sources remain in `/tmp/pra-tree-encoding*.lean`.

This establishes an effective Lean codec, not that its numerical encoding,
decoding, arity validator, or future PRA axiom recognition is primitive
recursive. It does not define the PRA theory or prove conservation.
