# Exact local-window abstraction: four 215-state machines

## Result

All 40 requested finite domains were computed to a least fixed point and independently checked: four pinned machines, radii 1 through 5, and blank versus arbitrary initial windows. Every domain retains all 215 working states and all 430 read rows. No direct safe pair merger exists. The exact step-for-step bisimulation partition has 215 singleton classes for each machine. No 214-state candidate is produced by this bounded abstraction family.

The domain sizes per machine and initial mode are 1,720; 6,880; 27,520; 110,080; and 440,320 state/window pairs. Full counts are in counts.csv and verification.json. These are finite abstract reachability computations, not bounded simulations of the blank run.

## Sound abstraction

For radius r, a window is the 2r+1 bits from head-r through head+r, with the leftmost bit stored least-significant. The abstract state is a working control state and a window. A transition reads the central bit, writes that bit exactly, and shifts the window in the actual head direction. The newly exposed cell is chosen nondeterministically as either 0 or 1. This choice is made on every transition, including when the cell might have been visited before; no unproved virgin-cell or zero-exterior assumption is used.

In blank-initial mode the only seed is state0 with an all-zero window. In arbitrary-initial mode every window at state0 is a seed. Halt is terminal and has no successor obligations.

For any concrete configuration, its window projection follows one of these abstract edges: the exterior choice is simply the actual bit at the newly exposed cell. Therefore initial inclusion plus inductive closure proves that every concrete reachable configuration projects into the certificate. A missing abstract control state or read row would justify its exclusion from concrete runs. There are no such exclusions here.

## Independent checking

reach.cpp generates explicit least fixed points using integer bit operations. verify.py parses the pinned native tables independently, constructs successor windows as lists of bits, checks every initial seed and closure edge, and recomputes an independent BFS to establish exact leastness. Its additional pair checks normalize a proposed target-state identification; partition refinement checks general exact step-for-step state bisimulation.

The bitset certificate for each domain is stored in MACHINE/rR_aA.bits, accompanied by a human-readable census. Bits are ordered by dense state index then window value. inputs.json binds dense indices to native labels and pins the four authoritative table hashes. All source packets and sealed machines remain unchanged.

The checker is ordinary Python, not a Lean or Rocq kernel theorem. The soundness argument above can be formalized once, with certificate closure discharged by a verified Boolean checker. This replaces repeated ad hoc reachability lemmas, but this experiment itself makes no new kernel-verification claim.

## Reproduction

From the repository root, run prepare.py to copy and pin the four inputs, compile reach.cpp with a standard C++17 compiler, and run it for each machine, radius 1..5 and mode 0/1. Its arguments are INPUT.rows OUTPUT_STEM RADIUS ARBITRARY_FLAG. Then run:

    python research_proof_simplification/window_reduction/verify.py
    python research_proof_simplification/window_reduction/test_rejection.py

Negative controls confirm rejection of optimized Python, a missing initial window, an inductive-closure hole, a truncated certificate, and a changed pinned table. No external dependencies are needed.
