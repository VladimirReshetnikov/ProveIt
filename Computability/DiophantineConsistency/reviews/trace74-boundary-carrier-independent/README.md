# Independent review of boundary-seed carrier obstruction

The independent check pins the candidate JSON, verifies the full dependency rows for h, X, Y, c, D, H, K, Z and M, derives the numerical values from the prior seed's inputs, and recomputes `D=112`, `H=479`, `K=2459256`, `M=53648` and `h*D*K mod H=176`. The exact row identity is `Z=h*D*(H*(n−V²*B)+K)−H*(D*B+h*e)`. For every integer B,e,n,V, it gives `Z ≡ 176 (mod H)`; because `H | M`, M cannot divide Z.

This is a valid conditional obstruction for integral Z/M at the specific seed. It does not prove the 74 graph has no zero there: this packet does not show that a trace74 zero implies `M | Z` when old alpha is zero. It is not an unrestricted or fixed-port counterexample. The check is on the external candidate JSON; no Lean replay, formal JSON binding or broader search claim is made.
