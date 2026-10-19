# Independent source certificate for K227

The checker `verify_source_reassociation.py` establishes that the accepted K229
and K227 sources have the same ordered guarded instruction graph. Its proof is
independent of the source compiler, the search procedure, and the symbolic
Turing-machine runtime engine. It imports only the Python standard library.
The result is recorded in `source227_independent_audit.json`.

## Source semantics and the relation being checked

Let a source be a finite full binary tree, with its instruction leaves numbered
from left to right by $0,\ldots,N-1$. A source state consists of the selected
leaf index and nine natural-valued logical registers. The register operations
are increment and decrement with a zero branch; the other leaves are break,
continue, and halt.

The checker constructs the full trie from the path records. It rejects
duplicate paths, any leaf that is a proper prefix of another leaf, incomplete
internal nodes, invalid instructions and arguments, and a JSON record order
different from the tree's left-to-right order. Thus the index used in the
certificate is a mathematically fixed source position, rather than a pairing
chosen after looking at the control graph.

The successor computation uses parent pointers and subtree boundaries:

| Instruction and guard | Structural successor |
|---|---|
| Increment, or decrement with a positive value | The next leaf, cyclically at the root boundary. |
| Decrement with value zero | Ascend through the first left edge encountered; continue after the entire resulting ancestor subtree. |
| Break $k$ | Ascend while counting left edges; after the $k$-th such edge, continue after the resulting ancestor subtree. |
| Continue $k$ | Ascend while counting right edges; after the $k$-th such edge, enter the resulting ancestor subtree at its first leaf. |
| Halt | A distinguished terminal outcome. |

If an ascent exhausts the path before reaching its specified count, the
remaining path is empty, with the corresponding root boundary behavior. These
rules agree with the path semantics: a left edge is the bit zero and a right
edge is the bit one; ascending deletes the rightmost path bits through the
specified counted bit. Break then increments the retained prefix, whereas
continue leaves that prefix as the new program counter. Sequential execution
increments the complete current leaf word.

The final comparison checks equality of the opcode and operand at every leaf
index, followed by equality of every guarded successor index. The zero and
positive decrement cases are checked separately. For any valuation of the nine
registers, exactly the same branch is selected in both trees; the same register
is updated by the same operation, and the successor leaf indices agree. The
relation

\[
 (i,R)_{229}\ \mathcal R\ (i,R)_{227}
\]

is therefore a one-step bisimulation, including the terminal outcome. Induction
on the number of source steps gives equality of every finite instruction trace
after replacing paths by leaf indices. Consequently either source halts from
leaf zero and a register valuation if and only if the other does. This holds
for every natural register valuation; no register bounds or finite source
execution samples are used.

## The initial counter and the no-stray condition

The checker separately implements right-to-left binary carry on finite words.
For each nonhalting guarded operation it computes its output program-counter
word $w$. Let $p_j$ be the path of the structural successor leaf. It checks

\[
 w\,0^{m-|w|}=p_j\,0^{m-|p_j|},
 \qquad m=\max(|w|,|p_j|).
\]

Thus following the stored word, with implicit trailing zeros, reaches precisely
the structurally predicted leaf. If the stored word extends beyond that leaf,
the discarded suffix consists entirely of zeros. This is the no-stray condition
needed to compose the per-leaf Turing-machine frame theorems: normalizing the
program counter only transfers zero cells between the literal leaf word and
the padding, and leaves the complete physical tape unchanged. The same check
is applied to the initial empty word. Both sources normalize it to leaf zero,
whose path is `000`.

The output carry is recorded for audit, but equality of carry bits across the
two different encodings is not assumed. The binary runtime theorem for each
encoding already accounts for its own head displacement and gap increase on
overflow. The source bisimulation relates logical leaf indices and registers;
the frame theorem supplies the implementation relation for each encoding.

## Exact audit outcome

| Property | K229 source | K227 source |
|---|---:|---:|
| Ordered instruction leaves | 5,121 | 5,121 |
| Internal nodes in the unfolded full tree | 5,120 | 5,120 |
| Guarded instruction cases, including halt | 6,656 | 6,656 |
| No-stray checks, including the initial word | 6,656 | 6,656 |
| Maximum leaf depth | 40 | 37 |
| Maximum consecutive zero bits in a leaf word | 6 | 6 |
| Initial leaf index | 0 | 0 |

There are 4,916 changed leaf paths. All 5,121 opcode/operand pairs and all
6,656 guarded outcomes agree. There is one halt leaf, so the 6,655 nonhalting
guarded successors plus the initial word give 6,656 normalization checks.

The K229 source SHA-256 is
`61450579877bc79cc4bc323ff0b8ae506064c79644107f4d818401dcfbce941b`.
The K227 source SHA-256 is
`339511182a98cec549d4c2b5ee98192fd92fd137e8e925ff11c620a9b1865e3f`.
The common serialized guarded graph has SHA-256
`ef721756093cd51f4107c12305c4684374d91a3a95a85885e3138c4bc1b8a145`.

To reproduce, run:

```sh
python3 -B verify_source_reassociation.py \
  --old-source sites229.json \
  --new-source sites227.json \
  --output source227_independent_audit.json
```

## Composition with the machine proof

This certificate establishes the source reassociation independently of how the
new tree was found. The dynamic-programming search and its optimality need not
be trusted to justify this particular source transformation. It composes with
the separate four closed-chunk rewrites connecting the pinned K230 source to
K229, and with exact blank startup plus the final K227 universal runtime
certificate. The latter must still be replayed on the exact delivered transition
table. This source checker does not certify a transition table, a global minimum
state count, or a newly compiled Rocq proof object.
