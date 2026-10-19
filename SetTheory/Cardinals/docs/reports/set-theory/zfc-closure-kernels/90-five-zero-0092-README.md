# Canonical grammar and scanner research

This directory contains a new search representation, an exact obstruction to one inherited search regime, and finite research results. **It does not contain a machine below 245 states.** The separate machine compiler and runtime certificates at the package root determine which abstract candidates are complete constructions.

## Main results

The inherited 54 bootstrap projections force a six-zero source address. A grammar with maximum zero run at most five cannot preserve those projections and the required state 172 source root, regardless of its grammar size. `verify_zero5_bootstrap_obstruction.py` checks the obstruction directly against the immutable source AST and original lock file.

Four of those sufficient bootstrap constraints can be relaxed together. The state-neutral change

```
((eijkKCqkjG,e),U)  ->  (eijkKCqkjG,(e,U))
```

replaces the obsolete helper `eijkKCqkjGe` by `eU`. These strings use the inherited 44 physical-symbol notation, rather than the canonical alphabet used in candidate JSON. The resulting `canonical-relax50-seed.json` has 128 grammar rules and retains 50 locks. Its complete 245-state compilation passes the independent source, actual-table, affine-runtime, and blank-bootstrap checks in the parent package. The blank-start root takes 407995 steps with the six-zero scanner. Its 244-state five-zero-scanner compilation reaches a safe root in 405175 steps but fails ordinary instruction dispatch, so it is a negative control rather than a solution.

A further coordinated repair produces a grammar whose entire source has maximum zero run five. `canonical-zero5-relax50-targeted.json` has 138 rules and source depth 61. The parent's independent compiler verifies its 254-state compilation using address padding 96; all 8391 affine cases and the 405175-step safe blank bootstrap pass. Padding 64 is too short for its deep paths and fails a runtime check. A final 300-second compression run made 6,112,052 proposals and reduced the witness to **136 grammar rules**. The frozen `canonical-zero5-final.json` compiles to **252 working states**. At padding 96, the parent package independently verifies 3042 source-bisimulation pairs and 6082 edges, all 8391 affine cases, actual-table macro inductions, all 22 folded projections, the 50 retained locks, and the same 405175-step safe blank bootstrap with gap 181. Its source depth remains 61. This establishes a complete implementation of the 116-state framework with the five-zero scanner. Reaching 128 grammar rules with that framework remains an open optimization problem.

## Why a new representation helps

The original grammar uses 44 physical atoms as indivisible letters. Their source meanings are not all irreducible closed programs. We compute free-exit bounds on the immutable source AST. Whenever both children of a source sequence are closed, we split it recursively. The 44 physical atoms become words over 30 finest closed atoms.

Canonical words identify programs that differ only by the grouping of closed sequential components. This permits a parser to move a cut through a formerly opaque physical atom, then use another physical atom to cover the resulting substring. It also permits routes with different original spellings to share a canonical word. The current 128-rule baseline has no immediate collisions between its distinct rules, and no rule collides with a physical dictionary terminal. A useful improvement therefore requires a genuine change of segmentation or parse; merely quotienting the baseline does not save a state.

The 30 finest atoms are **not** assumed to have 30 separately callable machine entries. The zero-cost terminal dictionary is exactly the 44 inherited physical atoms, with their actual allowed left/right entry masks. Some canonical words have length greater than one yet are physical terminals. Some individual canonical letters have no direct entry. Treating string length as terminalhood would make the search unsound.

The current search also forbids a newly allocated grammar rule from shadowing a word that already denotes a physical terminal. This simplifies routing and evaluation but restricts the search family. A future implementation could distinguish a physical entry from a separately allocated rule with the same semantic word, provided its compiler and proof track those implementations separately.

## The exact obstruction

Let `lead(x)` be the number of initial zero edges on the leftmost source path of a binary expression. For a leaf, `lead=0`; for a node `(a,b)`, `lead=1+lead(a)`.

Five rows of the original 54-lock file prescribe these left projections:

| Parent word | Locked left child |
|---|---|
| `eijkKCqkjGeU` | `eijkKCqkjGe` |
| `eijkKCqkjGe` | `eijkKCqkjG` |
| `eijkKCqkjG` | `eijkKC` |
| `eijkKC` | `eijk` |
| `eijk` | `e` |

Physical atom `e`, identified in the inherited dictionary as `34:0`, has one more fixed left edge to the `dec1` leaf. The parent at the top is required source root 172, corresponding to immutable AST 221, which occurs at original source path 1111. Its leading zero depth is consequently 6. This proof does not depend on the remaining grammar, the optimizer, or a state-count objective.

The result rules out the stated *syntactic family*. It is not a lower bound on all Turing machines, all compilers, or even all reachable-address arguments for this scanner. A different source occurrence, relaxed bootstrap constraints, a different encoding, or a proof restricting the scanner's reachable inputs can avoid its premises. The verified variants retaining 50 locks demonstrate why that distinction matters.

## Search methods and limits

`anneal_canonical.cpp` adapts the inherited routing-aware annealer to canonical dictionary words and a configurable hard maximum zero run. `anneal_canonical_dynamic.cpp` additionally makes a route change and its enabling child reparses in one proposal, and includes local dynamic programming that can shift boundaries through physical atoms. `anneal_canonical_zero5_strong.cpp` assigns a penalty to source nodes with a sixth zero while retaining a hard six-zero ceiling; it is used to approach the feasible zero-five region before exact repairs.

`canonical_milp.py` builds a finite binary-grammar model over the baseline words and repeated substrings up to a length cutoff. Each selected nonterminal chooses exactly one legal split. Dependencies, terminal orientation masks, bootstrap constraints, and folded projections are enforced. At cutoff 24 the solver returned optimum 128 in a model with 1756 candidate words, 14535 binary variables, and 25728 constraints. This is a solver result for that explicit finite dictionary, not a lower bound for unrestricted grammars. The model does not enforce source-depth or scanner constraints; its returned candidate is checked independently after solving.

`canonical_milp_warm.py` extends the dictionary with all prefixes and suffixes of the longest source word and provides the 128-rule seed to HiGHS. The bounded run retained 128; it did not prove optimality. It uses SciPy's internal HiGHS interface and may need adaptation when SciPy changes.

`target_zero5.py` performs a coordinated repair of the remaining M/P atom and AX leading chains in a gradient candidate retaining 50 locks. The P repair needs a simultaneous alternate route for 183/1. `repair_zero_strong.py` greedily combines reassociation and exact route closure. `parse_zero5.py` is a local minimum-new-tree-cost parser with leading-depth budgets and real terminal masks. Its objective counts new tree joins, not the globally optimal number of distinct shared grammar rules. These are research tools, not complete compilers.

Annealing is heuristic, depends on the C++ implementation's unordered-container iteration and wall-clock timing, and is not expected to reproduce an identical trajectory on every environment. Frozen candidates, their hashes, and finite independent checks are the reproducible evidence. Failed searches do not establish a grammar or machine lower bound. The only exact impossibility result in this directory is the five-projection forced-chain theorem above.

Some frozen JSON files retain inherited fields such as `framework_states:118`, `erase177`, and `retarget`. These are legacy search metadata. **They do not describe a newly compiled machine and must not be used to infer its state count.** Actual compiled state counts and acceptance status come from the parent package's independent machine certificates.

## Replay the finite evidence

Python 3's standard library suffices for the finite checks:

```sh
python3 -B research/grammar/verify.py --output /tmp/zfc-grammar-replay
```

The output directory must be new or empty. This regenerates the canonical dictionary and inputs, checks their frozen bytes, replays the exact forced-chain obstruction, verifies each frozen canonical candidate's 44 physical entry orientations and 22 route projections, verifies the specified locks, and confirms the exact ordering of 6460 source instruction leaves. It recomputes the source's leading-zero depth, maximum zero run, and binary depth.

A source/grammar PASS does not by itself certify a Turing machine. The package root's `verify.py` separately reconstructs literal tables, checks source bisimulation and actual-table macro inductions, validates the unbounded affine runtime cases, and recognizes the safe blank-start root for the principal candidates.

## Reproduce optional optimization

From the package root:

```sh
g++ -O3 -std=c++17 research/grammar/anneal_canonical_dynamic.cpp -o /tmp/zfc-anneal
/tmp/zfc-anneal research/grammar/inputs/canonical-grammar.txt research/grammar/inputs/canonical-constraints.txt /tmp/canonical-search.json 300 700001 127 research/grammar/inputs/canonical-lock54.txt research/grammar/inputs/canonical-resume.txt 6
```

Arguments after the seed are target grammar count, lock file, resume file, and maximum zero run. The target count is a stopping objective; reaching it still requires independent source/runtime/bootstrap validation. A zero-five run with all 54 locks is ruled out by the exact obstruction, so use the 50-lock input and a feasible zero-five resume instead.

For the finite MILP experiment, install NumPy and SciPy, then run:

```sh
python3 research/grammar/canonical_milp.py 24 300 /tmp/zfc-milp24
```

The final output prefix should point to a writable scratch directory. The canonical input generator also accepts `--reference` and `--output`, so regeneration never needs to alter the frozen inputs.

## Provenance

`reference_data/` contains byte-identical copies of the seven required files from the vendored `zfc245-proof-20261018` package; it preserves their original relative paths. The source, grammar, physical entry dictionary, and original routing-aware annealer retain the upstream authorship described in `NOTICE.txt` and the retained licenses. `provenance.json` identifies every copied reference input by SHA256. New work here is canonical semantic atom factoring, boundary-crossing and coordinated-route search, the forced-chain obstruction, lock relaxation, targeted zero-five repair, finite checkers, and the accompanying bounded evidence.
