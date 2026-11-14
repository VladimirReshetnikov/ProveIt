# PA196 head-order search packet

This is a portable research packet for changing the order and presentation of
the six arithmetic axiom heads emitted by the PA196 AX command. It contains
**no verified Turing machine with fewer than 196 working states**.

Run the retained evidence with Python 3.10 or later:

```sh
python3 verify.py
```

The verifier uses only the standard library and bundled data. It checks the
SHA-256 identities of the pinned upstream files, reconstructs the source tree
and macro word, extracts all six independent head emitters, checks every
generated macro expression contract, and recomputes the sizes and words of
the retained grammar witnesses. It does not run Lean or certify a binary
machine's runtime.

## Exact new facts

The original AX representation has 200 atomic macro tokens, 201 composite
source blocks, and 264 symbolic arithmetic operations. The head emitters have
these zero-based, half-open atomic intervals:

| Head | Atomic interval | Original primitive interval |
|---|---:|---:|
| 1 | [18,35) | [503,786) |
| 2 | [35,54) | [786,1085) |
| 3 | [54,70) | [1085,1381) |
| 4 | [70,86) | [1381,1677) |
| 5 | [86,102) | [1677,1908) |
| 6 | [102,121) | [1908,2258) |

The fixed prefix has 18 atoms and the fixed suffix 79. None of the six entire
emitter intervals is one existing subtree of the original AX source tree.
Consequently a literal exchange of six existing subtrees is unavailable.

All 720 emitter permutations preserve the scalar registers, field tail,
gate expression, and older stack entries. They place the six head formulas
on the stack in the reverse of the selected emission order. The checker also
generates the eight choices obtained by exchanging the two antecedents in
heads 3, 4, and 6. All 5,760 resulting words are distinct and pass their exact
symbolic arithmetic-expression contracts. The two presentations of a swapped
head are related by the separate propositional exchange theorem
`(A → (B → C)) → (B → (A → C))`; this packet's finite computation does not
itself prove native-calculus completeness or its PA arithmetization.

## Search results and limits

The greedy grammar screen credits existing source macros, including the
existing pair of `inc1` operations and its already available composite.
It tests all 5,760 words with one deterministic randomized heuristic run per
word. The best complete-program source grammar has 161 distinct internal
nodes. This is an upper bound from one heuristic, not an optimality result.

Eight shortlisted words were then optimized for 30 seconds each with a
mixed-integer flow formulation. The retained complete-program internal-node
counts are **160, 160, 159, 158, 162, 160, 160, 159**. All solver gaps remain
nonzero. The best three are:

| Witness | Emission order | Swapped heads | Internal nodes |
|---|---|---|---:|
| `reorder_milp_3.json` | 1,6,5,2,3,4 | 6 | 158 |
| `reorder_milp_2.json` | 1,4,5,6,2,3 | 4 and 6 | 159 |
| `reorder_milp_7.json` | 4,1,6,5,2,3 | 4 and 6 | 159 |

These are source grammar proposals. An internal DAG node is not a physical
TM state: shared helper contexts, tape geometry, allocation, startup, and
arbitrary-register runtime still need separate checks. No proposed grammar
here is claimed to improve the 196-state record.

The `results/` directory contains the exact head intervals, symbolic receipts,
greedy histogram and shortlist, all eight grammar trees and metadata, and the
solver log. `verify.py` recomputes each retained tree's expanded atomic word
and complete-program internal-node count independently of the solver log.

## Optional search replay

The greedy screen is standard-library Python:

```sh
python3 code/reorder_grammar.py
```

The optional MILP replay also needs NumPy and SciPy. The recorded environment
used Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0, and the bundled HiGHS interface
reporting version 1.8.0. It uses SciPy's private `_highspy` interface, so later
versions may need an API adjustment. Replaying a time-limited solve can give
a different feasible grammar; the retained witnesses remain independently
checkable without these dependencies.

```sh
python3 code/run_reorder_milp.py --start 0 --stop 8 --limit 30
```

Search replay overwrites the corresponding files in `results/`; copy this
packet first if the original receipts should be retained.

## Provenance and license

All files in `vendor/` are copied unchanged from
[`jamesyc/BusyBeaver` revision `407cdc356f6b586635e71ac92be394255f4bfea4`](https://github.com/jamesyc/BusyBeaver/tree/407cdc356f6b586635e71ac92be394255f4bfea4).
`provenance.json` records each source URL and SHA-256. The upstream MIT license
and James Chang's copyright notice are retained in `vendor/LICENSE`.
The Python scripts were prepared for this investigation and include the
exact numeric constructor and symbolic operation conventions of those
sources. None of the vendored Lean files has been modified.
