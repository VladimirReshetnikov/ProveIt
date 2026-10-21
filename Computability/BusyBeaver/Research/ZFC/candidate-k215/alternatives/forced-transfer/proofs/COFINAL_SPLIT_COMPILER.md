# Full vacuity plus cofinal K: fixed-eleven-head compiler

This is an abstract, source-priced alternative, not a calibrated target machine.
Keep every old gated vacuity instance V(A,B,c). Replace the other conjunct by K(A,B,R(A,B)+c). For each fixed A,B its third arguments range over a cofinal tail, and R(A,B)>max(A,B), so this K instance is always enabled. The cofinal-K calibration requires ALL old gated V instances to remain available; it does not justify restricting the whole old bundle to a cofinal tail. The appropriate separate calibration argument is recorded in research216_cofinal/PAIRING_GATE_RESTRICTION_REVISIT.md.

The changed AX has top V if c differs from A and B, otherwise zero; its first saved head is the always-enabled K, followed by exactly the original ten saved heads. It resets the same parameter and scratch registers as the original AX. It therefore has a fixed eleven-head output, not an input-dependent count.

One literal realization preserves the original C and replaces the twelve C loads inside K's matrix by C+R(A,B). A second computes R(A,B), adds it to C, constructs K, recomputes R(A,B), subtracts it from C, and constructs V before applying the original destructive gate. The subtraction precondition holds because C was increased by exactly this nonnegative quantity. The second R construction saves K on the stack. Removing the initial PUSH from the subsequent first-field copy avoids an extra zero head. All original matrix operations and the original gate are retained. No gated V is silently exposed when disabled.

## Compiler with cache-return MP

Let S and MP retain the calibrated cache-return216 command semantics. Let D denote AX(0;0,0). The old forced-failure calculations apply with one extra crossed head:

* H = D; S^12 removes one original stack head while preserving top, resets D, and leaves that head in cache, or halts on incoming top 1.
* PUSH = D; S^10; MP(0) gives (0,[t;w],0,0). The last comparison fails because its cache is the unchanged quantifier row, whose constructor tag differs from implication.
* DISCARD = MP(1); AX(1;0,0); S^11; MP(0) gives (0,w,0,0) from every (t,w,0,0). The two comparisons are the same forced failures as in the original compiler.
* J(u) is MP(u) for positive u and the empty word for u=0, from top, D and cache all zero.

For inherited row j=1,...,7, use DISCARD; AX(c;a,b); S^(j+2); H^(9-j). The extra K head and top V are crossed before the inherited rows; the remaining number of discarded heads is unchanged.
For L(a,b,c,u), use DISCARD; J(u); AX(c;a-u,b); S^10; H. Its old domination condition a>=u still applies.
For a gated V instance use DISCARD; AX(c;a,b); H^11.
For K(A,B,R(A,B)+c) use DISCARD; AX(c;a,b); S^2; H^9.
For generalization use B_X; PUSH; J(i); S; AX(i;0,0); S^11, crossing the extra K head before the old quantified row.

The cache-return inference block remains DISCARD; PUSH; B_major; PUSH; B_minor; PUSH; S; S; MP(Y); S. It reserves a zero and ends at (Y,w,0,0), or halts if Y=1. Each induction hypothesis has the arbitrary-store contract, not merely the safe-stack contract. Thus the changed row counts do not undermine completeness. Soundness uses theoremhood of both new components, the retained gate, and the ordinary protected-stack invariant. Conservative AX credit increases from ten to eleven; old prefix credit bounds remain sufficient. Binary decoder runtime and blank startup are separate, unresolved obligations.

## Concrete source pricing

COFINAL_SPLIT_PRICE.json: twelve shared C-prime loads, 212 DAG nodes; allocator rejects a dirty prefix.
COFINAL_SHIFT_PRICES.json: all 1,430 associations of the nine closed shift/build/restore factors have 210 DAG nodes. Twelve representative physical allocations reject dirty prefix 0011001000000. There is no 215-state claim and no implication that these finite searches prove a lower bound.
