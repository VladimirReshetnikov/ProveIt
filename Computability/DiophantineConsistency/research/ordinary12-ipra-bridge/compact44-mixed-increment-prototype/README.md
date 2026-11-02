# Mixed-digit decoder for an incremented low mask

For every IΣ₁ model, the theorem considers a positive block length m and
repetition count N, a block `MC < 2^(67m)`, a positive carrier C, and the
explicit premise `NoCarry (C−1) (MC * rep(67m,N) + 1)`. It assumes every
block digit is one of `2^67−1`, `2^67−2`, or `2^67−4`, and that the block's
origin digit is `2^67−2`. It concludes that digit zero of C is 1 and every
one of its first mN digits is at most 3.

The proof adapts the origin and increment handling in
`ArithmeticWindowBits.low_mask_decode`; at positive positions it applies the
independently audited 0/1/3 local bounds. The three-way hypothesis permits the
compact44 exceptional dummy, but is still a premise, not a derivation of the
concrete MC digits. This theorem does not identify the actual graph ports or
NoCarry premise, provide coefficient-mass bounds, prove cyclic temporal
support, simulate the machine, or construct a PRA proof.

The two matched sides use independently audited mixed-mask parents over the
same audited 24-module window provider, with copied parent hashes and direct
imports checked. The provider audit does not constitute a complete axiom
inventory or complete package-transitive/dynamic ancestry check. The resource
monitor samples processes and does not enforce a hard whole-tree quota.

Exploratory session 80710 exited 1 on an unnecessary rewrite after a `set`
operation already substituted the mask digit; its source and full log are
retained. The corrected exploratory session 27180 exited 0 without warnings or
sorryAx; its log is retained. The matched replay is recorded separately.
