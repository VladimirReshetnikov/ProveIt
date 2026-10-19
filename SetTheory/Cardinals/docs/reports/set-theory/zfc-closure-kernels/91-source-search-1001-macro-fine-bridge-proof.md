# Universal bridge from Wade macros to optimized fine words

The nineteen macro substitutions in `macro_to_fine.json` preserve the exact
nine-register partial function, for arbitrary natural values in all nine
registers. A block returns in one representation exactly when it returns in the
other, and the complete register vectors then agree. This supplies the source
contract needed to compose the changed AX words in the DNE construction.

The original macros are parsed from the attributed pinned `Dag254.v`. Their
fine expansions are independently reconstructed from the optimized baseline
AST in `closed-sequence-grammar-next22.json`. The actual macro spellings are
read from the theory experiment's `macro_to_fine.json`. No aggregate AX hash is
used as a substitute for a per-macro semantic proof.

## Why a literal tree comparison is insufficient

For example, original macro 192 repeatedly decrements register 3, increments
register 6, and increments register 7. Its optimized fine token `Y` executes
the two increments in the opposite order. Each iteration has the same exact
effect on the complete register vector. A comparison requiring equal ordered
instruction lists would reject this valid substitution.

The certificate instead compares increment multiplicities between matching
decrement tests. A finite sequence containing only increments has the exact
transformer

\[
 (r_0,\ldots,r_8)\longmapsto(r_0+k_0,\ldots,r_8+k_8),
\]

where \(k_j\) counts its increments of register \(j\). Structural break and
continue operations change the source address but no registers. Equal vectors
\((k_0,\ldots,k_8)\) therefore prove equal effects without restricting the
initial values or their relative sizes.

## Closed blocks and the return boundary

Both each original macro and its expansion have structural bounds `(0,0)`.
For a decrement leaf the bounds are `(1,0)`; for `break k` they are `(k,0)`;
for `continue k` they are `(0,k)`; other leaves have zero bounds. A binary node
with child bounds \((b_L,c_L)\) and \((b_R,c_R)\) has bounds

\[
 (\max(b_L-1,b_R,0),\ \max(c_L,c_R-1,0)).
\]

These are the inherited lexical break/continue bounds. Zero bounds state that
the block has no outstanding transfer to an enclosing control construct.
Each fine terminal is independently checked to be closed, so any sequence of
them is also closed.

The checker appends a distinguished halt as the right child of a new binary
root, placing the block on the left. It verifies that the block itself contains
no halt. Thus the only halt of the wrapped program is the return boundary at
address `1`. This is a specification device: the final machine has no new halt
or states for these checks. Equivalence at this boundary transports to any
enclosing continuation because the blocks are closed.

## Finite product certificate

The new checker constructs a control-flow graph from complete binary source
addresses using integer binary increment and index-based break/continue cuts.
It follows each unconditional segment to the next decrement test or return,
recording every visited address and the exact increment vector. Repeated
addresses in such a segment are rejected, so every accepted segment has a
finite literal execution.

The product relation starts after the initial unconditional segments. Every
related pair must contain either matching decrements of the same register or
the two distinguished return boundaries. At a decrement pair the certificate
contains **both** branches. The positive branch subtracts one from the same
positive register in both programs; the zero branch leaves that register zero
in both. Each subsequent unconditional segment has an equal increment vector,
and its endpoints belong to the finite product relation.

Induction on the number of visited tests preserves equality of all nine
registers and the relation between control locations. Any finite return is
therefore matched by a return with the same registers. Conversely, an infinite
execution passes through infinitely many tests, because all intervening
segments are finite. Each test requires a positive number of literal steps in
both programs, so the related execution is also infinite. This proves both
directions of the partial-function equivalence, including divergence.

## Independent semantic replay and result

After generating the graph, the checker replays every edge with the separately
attributed upstream `rmpath.py`. This second implementation uses the inherited
Boolean-list source path semantics. It independently resolves each site,
computes both decrement successors, executes the unconditional segment, and
checks its exact increment vector and target pair. All product vertices must
be reachable from the initial pair.

All **19 macros** pass. The certificates contain **192 product pairs** and
**346 guarded decrement edges**, with one distinguished return pair for each
macro. The thirty fine terminals, original Dag254 source, optimized AST, macro
map, checker, upstream path interpreter, and complete certificate file are
identified by SHA-256 in `macro-fine-bridge.json`.

The checked macro IDs are 119, 121, 131, 158, 166, 168, 171, 176, 177, 178,
180, 181, 182, 183, 192, 197, 208, 211, and 218. They cover every scalar push,
constructor, input read, gate, and cleanup macro used by all 64 DNE AX variants.
Consequently the original per-macro contracts can be composed along each
changed RPN word. The logical transfer from the new bundle to the original
calculus and the complete binary-machine simulation remain separate, explicit
parts of the overall theorem.

This is an ordinary mathematical proof accompanied by an executable finite
certificate. It is not a claim that a new Lean or Coq endpoint was built.

## Reproduction

From the workspace root used during this experiment:

```sh
python3 work/machine_reduction/audit_macro_fine_bridge.py \
  --dag work/theory_encoding/snapshot/ZF/m254/coq/prog/Dag254.v \
  --grammar work/machine_reduction/base/zfc245-proof-20261018/inputs/closed-sequence-grammar-next22.json \
  --macro-map work/theory_encoding/macro_to_fine.json \
  --rmpath work/machine_reduction/base/zfc245-proof-20261018/reference/jeff/ZF/m254/tools/prog/rmpath.py \
  --output work/machine_reduction/macro-fine-bridge.json \
  --certificates work/machine_reduction/macro-fine-bridge-certificates.json
```

All path arguments are explicit and can be changed to match an incorporated
package layout. Run ordinary Python with assertions enabled.
