# Independent review: bounded one-gate identity search

The reviewed `research/ordinary13-eta-zeta85-single-gate-exact-search/` concerns the pinned **eta/zeta-natural 85-row probe**, not the original parent with a shifted zeta. Its negative result is valid for the stated finite rewrite space; it is not a minimality proof or a zero-set analysis.

At row index i, the available wires consist of 17 input variables, five constants 0 through 4, and the i earlier operation rows. For each direct predecessor operation used only by the target row, the search removes that predecessor from the available wires, leaving `21+i` choices for each operand. It tests all ordered operand pairs and all three binary operations `+`, `−`, and `*`. An independent pass over the actual graph finds 60 eligible target/predecessor pairs, and the sum `Σ 3*(21+i)²` over those pairs is **1,099,002** expressions. Using sets for consumer rows correctly counts a predecessor used twice by one target as one eligible pair.

The review independently re-evaluates every expression using eight deterministic assignments generated from a distinct SHA-256 domain, modulo 1,000,003. Every expression differs from its target on at least one assignment. An integer polynomial identity would remain an identity after substitution of those integer representatives and reduction modulo this positive integer; therefore each observed mismatch is a rigorous counterexample to that proposed global identity. The conclusion does not depend on those assignments being random or on the modulus being prime.

The test excludes only replacing one existing gate by one binary operation on earlier wires or constants 0 through 4 while deleting an exclusive direct predecessor. It does not cover a multi-gate rewrite, extra or reordered operations, other constants, a changed witness, zero-set equivalence, or an identity that holds only after fixing the compact coefficients. The input assignments do not instantiate the actual compact tuple. Thus the result does not rule out a smaller equivalent equation or establish anything about an internal proof.

The independent checker pins the probe and author's packet, reproduces the author's receipt, recomputes the eligible pairs and count, and exhausts the same replacement space using the independent modular assignments. No Lean, build, staging, provider selection or iPRA conclusion was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-eta-zeta85-single-gate-search-second-independent/check.py | cmp - reviews/ordinary13-eta-zeta85-single-gate-search-second-independent/receipt.json
```
