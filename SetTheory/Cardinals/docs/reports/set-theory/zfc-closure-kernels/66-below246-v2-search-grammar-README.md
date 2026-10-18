# Decoder grammar research: context, association, and commutation

This package records an unsuccessful search for a machine below 246 working
states. It contains useful abstract grammar reductions, including a particularly
small one-state proposal, but **none of the included 245-state transition tables
has been validated as a replacement for the baseline machine**. Their failed
verification attempts are retained so that a subsequent search does not
rediscover and incorrectly accept them. No assertion about their eventual
blank-tape halting behavior follows merely from these failed checks.

The reference is the `zfc-context246` archive from the ProveIt incoming material.
Its old-label transition table has SHA-256
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.
The exact extracted grammar and its source/table pins are in
`inputs/closed-sequence-grammar.json`. This input snapshot contains **18 partial
projection constraints**, not a complete characterization of valid compilation.
`inputs/closed-sequence-grammar-next22.json` contains the expanded 22-constraint
snapshot used by the final wider-depth search.

## Search representation

The baseline contains 127 pure decoder states whose two successors represent
closed sequential subprograms. Each becomes a binary concatenation rule.
Twenty-four entry roots must remain available because they are used by code
outside this subgrammar. Their expanded words contain 921 atom occurrences in
total; the longest root contains 702. There are 35 physical atomic state IDs but
44 semantic atom variants. The distinction is necessary because some physical
states perform different operations in different left contexts.

Every nonterminal is identified by its fully expanded atom word. The optimizer
changes binary parses by associativity, reuses an existing rule when its word
already exists, and deletes rules unreachable from the required roots. It starts
from the exact original 127-rule grammar. Simulated annealing permits temporary
cost increases and revisits equal-cost parses. The saved candidate files are
independently checkable; stochastic search itself provides no lower bound or
exhaustive coverage claim.

For semantic searches, the original observed incoming-bit orientations of every
atom are enforced. Later runs also enforce the 18 exported folded-entry
projections and calculate weighted properties of the reconstructed source AST:

```
lead(Seq(a,b))  = 1 + lead(a)
zeros(Seq(a,b)) = max(1 + lead(a), zeros(a), zeros(b))
depth(Seq(a,b)) = 1 + max(depth(a), depth(b))
```

A leaf has all three properties zero. Atomic subprograms are expanded through
their AST DAG, including references to rewritten sequence roots. If a deleted
nonroot word occurs inside an atomic AST, the search uses its original split as
a reconstruction fallback. This is a source-expression heuristic; an actual
decoder proof must resolve physical contexts separately. The initial whole
source has leading-zero length 3, maximum zero run 7, and leaf depth 34.

The first constrained searches require maximum zero run at most 7 and depth at
most 40. This depth bound is conservative: the blank bootstrap supplies a gap
of 181, so a new proof can use a larger minimum gap without adding a state.
The final search keeps the zero-run bound, allows depth up to 64, and enforces
all 22 known projection constraints. One search minimizes
`K + max(0, zeros - 6)`, where `K` is the number of
sequence rules, so it also searches for a 127-rule grammar with maximum zero run
6. Such a grammar could permit a separate one-state marker-scanner reduction,
subject to checking all machine phases.

## The exact one-state proposal and its obstruction

The best physical-word grammar differs from the original by one association:

```
178 = (23,208)       208 = (24,206)       16 = (23,24)
178 = (16,206)       delete 208
```

The corresponding proposed table edit is `178/0 = 0 R 16` and
`178/1 = 1 R 206`, followed by deletion of state 208. Its source-program
association has a 2,985-entry RM bisimulation certificate. Its maximum zero run
remains 7 and its maximum leaf depth remains 34. Nevertheless, whole-frame
binary instruction verification fails at
`11101001001010100111000000`, a zero decrement of logical register 1
(physical register 2). The machine marks physical register 0 instead.

The cause is a partial entry through a left-moving shortcut. State 218 on zero
moves left to 154. With a preceding zero, the old detour reads:

```
218 --0 L--> 154 --0 R--> 178 --0 R--> 23
```

The rewrite inserts state 16 at the end of that path. It changes the folded
subprogram from 23 to `(23,24)`, even though the association is valid when
entered at the root of the complete sequence.

Changing `218/0` to `0 L 178` repairs this preceding-zero context, but 218 also
occurs with a preceding one. That old path selects 105 through
`154/1 -> 179/0`; the proposed repair selects 23 through `178/1 -> 206/0`.
A literal sweep rejects the repaired proposal at
`11101001001010100010110000`, zero decrement of logical register 2.
The root dispatcher and the full source program are not interchangeable entry
contracts for a folded decoder state.

For the repaired proposal, a reproducible bounded literal rejection uses head
0, header 40, physical registers `[0,3,6,2,5,1,4,0,3]`, and one zero spare.
At step 2,292, after 16 dispatcher visits, its tape still differs from the
specified macro target. `code/replay_rejected_rotation.py` independently
records this result and the exact blank replay. This bounded rejection is
not an impossibility proof for a different eventual-return contract.

An independent blank-tape replay of that repaired proposal still reached the
baseline frame at exactly 410,735 steps: state 96, head -5, marker -6,
header 176, physical registers `[0,0,0,3,0,0,3,0,0]`, and 167 spare registers
all equal to 1. This emphasizes why a successful bootstrap cannot replace
universal instruction verification. It does not validate the proposal.

The original and rotated grammars, rejected table, changed instruction sites,
and proof auditor's rejection result are included. The auditor's source scripts
and complete RM verification machinery belong to the companion proof-audit
package; this directory alone does not rerun that proof.

## Why 126 abstract rules were still insufficient

The first semantic 126-rule grammar preserved all fixed semantic words and
immediate atom orientations. Its reconstructed source passed RM bisimulation
with 2,992 certificate entries. Its maximum zero run increased to 12 and leaf
depth to 46, violating the original scanner bound and the existing checker's
40-cell frame assumption. The latter is a conservative proof parameter, not
a necessary machine-state cost. Full binary verification rejected it.
A subsequent 126-rule parse
has maximum zero run 13 and depth 44, and was not accepted as a machine.

The one-state example additionally proves that bounding depth and zero runs is
insufficient. Folded-entry projections must also be respected. The supplied
18 constraints cover direct left-moving transitions into the sequence grammar.
Further restrictions are needed through the nonsequence state 177: preserve
`175/0 -> word113`, `175/1 -> word105`, `207/0 -> word213`, and
`207/1 -> word231`. These four were identified after the first three constrained
runs. Those searches already found no improvement under the weaker constraints.
The final depth-64 run included these four as well and also found no improvement.

## Commutation as a separate search direction

Two closed subprograms with no halt instruction and disjoint syntactic register
footprints commute as partial register-store transformations. Each subprogram's
termination and output on its own registers depend only on those registers.
If both terminate, either order produces the same combined store. If one
diverges, executing the other first cannot change that divergence. Closedness
is needed to keep break and continue effects inside the subprogram.

The input has 82 adjacent independent atom occurrences across its 24 required
root words, comprising 10 distinct pairs. The most frequent are `68:0` with
`36:0` (24 occurrences), with `151:0` (23), and with `250:0` (23).
Canonicalization under these commutations does not directly identify any two
of the existing 127 sequence words. It nevertheless permits new parses and
new sharing after reassociation.

`anneal_commute.cpp` uses a canonical word for each commutation class. To compute
it, it preserves the relative order of all atoms touching each register and
chooses the lexicographically first topological ordering of those nine
dependence chains. A halt-containing atom is made dependent on every other
atom. The optimizer also swaps children when their register footprints are
disjoint. It retains the partial projection constraints modulo those same
commutations and the weighted source bounds. This run remained at 127 rules.
No validated machine or proof-assistant commutation certificate is claimed.

## Recorded searches

Iteration counts include proposed moves rejected as inapplicable. They are not
counts of distinct grammars and do not measure exhaustive coverage.

| Search | Seed | Iterations | Best rules | Result |
|---|---:|---:|---:|---|
| Physical words | 7351 | 5,532,133 | 126 | Exact 178 rotation; physical failure |
| Semantic words, orientations | 1943 | 6,032,012 | 126 | RM equivalence; zero-run/depth failure |
| Semantic continuation | 127654 | 5,881,361 | 126 | Zero-run 13, depth 44 |
| Semantic, projections and bounds | 73623 | 3,522,732 | 127 | No improvement |
| Joint sequence/scanner objective | 113219 | 2,516,448 | 127 | Zero-run remained 7 |
| Commutation classes, projections and bounds | 551023 | 3,189,935 | 127 | No improvement |
| Semantic, all 22 projections, depth at most 64 | 635311 | 3,447,017 | 127 | No improvement |

All archived abstract candidate objects pass `code/validate_grammars.py`. That
validator checks their source encodings, rule counts, reachability, word or
commutation-class identities, guarded atom orientations, claimed partial
projections, and reconstructed source bounds. Its output explicitly states
that machine correctness has not been established.

## Reproduction

From this directory, run the independent artifact checks:

```sh
python3 code/validate_grammars.py
python3 code/replay_rejected_rotation.py
```

To repeat the constrained sequence search with a 50-second budget:

```sh
g++ -O3 -std=c++17 code/anneal3.cpp -o /tmp/zfc-grammar-anneal
/tmp/zfc-grammar-anneal inputs/semantic.txt /tmp/zfc-grammar-best.json 50 73623 1 inputs/semantic-constraints.txt
```

To repeat the commutation-aware search:

```sh
g++ -O3 -std=c++17 code/anneal_commute.cpp -o /tmp/zfc-commutation-anneal
/tmp/zfc-commutation-anneal inputs/semantic.txt /tmp/zfc-commutation-best.json 50 551023 1 inputs/semantic-constraints.txt inputs/semantic-footprints.txt
```

The wall-clock budget means the final iteration count can vary across machines.
The saved candidates, their exact source representation, and their independent
validation are the reproducible artifacts. The archived runs do not establish
a lower bound on this compiler, much less on arbitrary Turing machines.
