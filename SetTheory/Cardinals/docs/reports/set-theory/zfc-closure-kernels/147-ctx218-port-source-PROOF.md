# All-natural source correspondence for the 218-state candidate

## Reproduction

Run `python reconstruct_source.py` in this directory, or invoke the script by its absolute path from any working directory. Python 3.9 or later and its standard library suffice. No repository imports, network, search process, machine simulator, or external package is used.

The four required inputs are `reconstruct_source.py`, `baseline_sites219.json`, `dag_recipe.json`, and `candidate_sites218.json`. The script writes `reconstructed_sites218.json`, `ordinal_correspondence.json`, and `verification.json`. It pins the two source inputs by SHA-256 and requires the reconstructed candidate to equal the supplied candidate byte for byte.

## Exact lineage

1. The upstream K219 source is the exact `machine/sites219.json` from `K219_Construction_2026-10-20`, SHA-256 `0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789`. It has 206 distinct DAG nodes, of which 183 are interiors.
2. `dag_recipe.json` specifies 44 topologically ordered new DAG definitions over that pinned source. Root249 reconstructs the startup-preserving source with SHA-256 `1b7c4685c3a594cd52f30872ec4cb2e70360e86cd5eb5411d71dcf454174a3c6`, containing 205 distinct DAG nodes and 182 interiors. This declarative reconstruction does not depend on the historical search trace.
3. Replace all five occurrences of native logical node98, `((83,56),67)`, by `(83,(56,67))`. Native node68 is already `(56,67)`. The occurrence starts are ordinals568,1260,1935,2892,3208, with their exact intermediate prefixes recorded in the verification receipt. The result is candidate SHA-256 `1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe`.

The final source retains 205 DAG nodes, 182 interiors, 4,744 primitive occurrences, maximum address depth38, and maximum zero run6. The first37 primitive addresses are identical at every stage. That last address check is a useful startup constraint, not by itself a proof of binary-machine startup.

## The source theorem

Let P and Q be any two of the three reconstructed sources. Number their primitive occurrences from0 through4743 in left-to-right order. For every ordinal i and every register store v in the nine-fold Cartesian product of the natural numbers, relate `(P,i,v)` to `(Q,i,v)`.

The verifier establishes two finite syntactic facts exhaustively:

- At every ordinal, P and Q have the same primitive operation and the same argument.
- For every possible guard of that operation, P and Q have the same successor ordinal, or both halt.

The second fact is calculated independently by two algorithms: binary successor plus address cutting, with explicit no-stray-one checks, and subtree intervals plus outward ancestor walking. Both algorithms agree with each other and between all three source stages. There are6,166 nonhalting guarded successor edges; adding the halting case gives6,167 primitive cases. The arithmetic resolver additionally checks the initial ordinal, giving6,167 no-stray-successor checks.

For an increment, identical arguments give identical register updates. For a decrement, equality of stores gives the same zero/positive guard, and the same update (no change at zero, decrement by one when positive). Break and continue leave the store unchanged; halt is identical. The checked successor equality therefore preserves the relation after every nonhalting source step. This proves a strong step-for-step bisimulation for all natural stores, not merely for the initialized store and not merely for sampled executions.

In particular the sources have identical halting behavior from corresponding initialized states. The same ordinal identity also transports any already proved register-store invariant: its initialization and closure conditions are unchanged at every guarded transition. `ordinal_correspondence.json` records the old, intermediate, and new addresses, operations, arguments, and successors for every ordinal.

## Scope and calibration

This proof is unconditional as a statement about the three explicitly given register programs and their specified primitive semantics. It does not independently establish the upstream program's foundational interpretation or its equiconsistency with ZFC. That remains the separately pinned upstream K219 calibration theorem.

It also does not prove that a binary Turing-machine table implements the final source, reaches its initialized frame from blank tape, has218 states, or satisfies an unbounded runtime certificate. Those are separate fresh machine-binding, startup, table-census, and runtime obligations. Conditional on those obligations and the upstream calibration, the source bisimulation transfers the upstream halting characterization to the new machine.
