# A small parameter extension of the scheduler credit proof

The diagonal argument in TRANSFER_PROTECTED_CREDIT.md works unchanged for conservative AX credit a>=5, rather than just10, while S costs-1 and MP costs0 and all three wire arities remain1/2/3.

Using q=g+1, the first k AX candidates give at least(a-1)k. During AX candidate y, the prefix is at least(a-2)y+a. The MP candidate leaves at least(a-2)(s-1); the final S candidate is bounded by

    (a-2)(s-1)-1-s = (a-3)s-(a-1).

For s>=2 this is at least a-5>=0. The exceptional candidates0,1,2 remain S,MP,SS. The same shifted-prefix induction and finite-horizon credit computation follow, including d(1)=2.

This is only a scheduler theorem. It neither supplies a proof compiler for a smaller axiom-output bundle nor changes the201-node source or215-state machine. The threshold5 is sufficient for this proof, not asserted minimal.
