# Exact labeled minimization: little additional compression

**Result: 1,426 canonical test/halt sites minimize to 1,423 classes.** There are only three two-member classes and 1,420 singletons, a reduction of three nodes (0.2104%). Both independently reconstructed latest Lean graphs yield the same partition, quotient and initial edge. All 1,426 original nodes are reachable in the symbolic branch graph; this is not a claim that every branch is concretely feasible for one initial register file.

This is a useful bounded negative. Removing the 814 raw path aliases remains worthwhile; adding a second class-membership layer to remove only three further rows is not a priority. It does not eliminate the obligation to bind every canonical path to its checked segment behavior, and the class map may increase certificate size.

## Exact scope

The graph is the literal pinned Lean source/target count-block graph from `../verify_lean_canonical_cfg.py`, at `e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad`. Its source SHA256 is `43093f181bfdd86408a7c88bbf8c0d99ada494b5e3780ae9d93cff05502dbe67`.

Each node label is either halt or the **exact tested register**. Each ordered positive/zero branch label is the **exact register increment-count vector**. Successor classes must match. Branch order is never exchanged. The initial increment vector and target class are preserved separately. Break/continue have already been contracted by the earlier checked-in-Python extraction; this is not a new semantics proof.

Partition refinement starts from the ten node-label classes and repeatedly refines by the two ordered labeled successors until stable. There are 99 refinement rounds including the final stability check. The stable quotient is itself refined to confirm that no further such labeled-bisimilar classes remain. This is the coarsest exact labeled bisimulation of this finite graph, **not** the coarsest program equivalence, a proof of minimal TM states, or a search for 214-state machines.

## The only merges

All numbers below are zero-based canonical **block ordinals**, not Turing-machine states or structured-DAG node IDs.

- Original rows 1369 and 1397 form class 1369: test register 5; positive branch has no increments and returns to class 1369; zero branch has no increments and goes to class 1370.
- Rows 1370 and 1398 form class 1370: test register 6; positive branch has no increments and goes to class 1369; zero branch has no increments and goes to class 0.
- Rows 1414 and 1425 form class 1412: test register 6; positive branch increments register 5 once and returns to class 1412; zero branch has no increments and goes to class 0.

The initial branch has no increments and targets class 0.

## Possible Lean adaptation, not recommended as the first implementation

The existing canonical-row proposal defines a related pair by matching both consumed sites to one paired row. For a quotient, instead use separate left and right location tables and class maps:

`Related P Q := ∃ i j, tsite t1 P = some(edge_i,left_i) ∧ tsite t2 Q = some(edge_j,right_j) ∧ leftClass i = rightClass j`.

Required checker/soundness obligations are:

1. Every site/row is bound to its exact consumed path and boundary label.
2. Every class has one boundary label, shared by every member on both sides.
3. Every member's positive/zero segments have the representative's exact increment-count vector and reach the specified successor class. Keep the branch order fixed.
4. Initial segments have equal increment counts and terminate in the same initial class.
5. Halt classes contain literal halt sites and have no outgoing branches. A missing transition, exhausted fuel or control-only cycle must not count as halt.

These obligations again instantiate existing `RMBisim.BranchGood`, `EntryGood`, and `Bisim.halts_iff`; no new TM semantics theorem is needed. However, the benefit is only three classes, while checking all 1,426 path locations remains necessary unless an additional reusable context theorem is proved. Keep the simpler paired canonical-row relation for the first proof refactor.

## Reproduction and verification boundary

Run `python minimize_canonical_cfg.py` from any directory. It reads only the packaged local pinned Lean source via the sibling strict parser and reconstructs both graphs independently. It writes `minimization_result.json` and `quotient_certificate.json`. The certificate contains the complete ordinal-to-class map, class members, quotient rows and initial edge.

The checker verifies every original row against its claimed quotient row. Negative controls alter the initial target, a class assignment, an increment-count vector, and branch order; each is rejected. Optimized Python is rejected explicitly because assertions are required.

**No Lean/Rocq compiler was run. No kernel proof, elapsed-time improvement or TM state reduction is claimed.**
