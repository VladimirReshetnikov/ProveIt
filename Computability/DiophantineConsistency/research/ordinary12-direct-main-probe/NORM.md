# Conditional direct-main norm and orientation

`DirectMainNorm.lean` proves two further lemmas for every IΣ₁ model with the same Lean model interface as the projection packet. It imports the accepted `DirectMainProjection` object.

* `oriented_scaled_norm`: if `U > 0`, `N < P`, and the magnitude of the signed pair `(P,N)` has square `U*U*(1+C)`, there is an `m > 0` with `P = N+U*m` and `m*m = 1+C`.
* `direct_main_orientation`: for `a = X*Y+Y`, `c = eta+Y*k`, `H = 3+4*a`, `P = U*(X+a*c)+H*(U*G+R+1)`, and `N = H*k`, assuming `U > 0`, `Y ≥ 8`, `k > 0`, and the exact norm equation `magnitude(P,N)² = U²*(1+(H+a²)*c²)`, there is an `m > 0` with `P = N+U*m` and `m² = 1+(H+a²)*c²`. The orientation inequality follows from the checked projection packet.

These are conditional results: deriving the norm equation from a modified graph's zero, obtaining the first factor and the Pell-index hypotheses, and proving the graph's soundness and completeness all remain open. In particular, this is not a 90-operation equivalence or an iPRA derivation.

`run-norm.py` produced `observations/norm-attempt01/terminal.json` and its source and stdout/stderr snapshots. Lean exited 0 without warnings; the only printed axioms for each theorem were `propext`, `Classical.choice`, and `Quot.sound`. The source SHA-256 is `738c9a708950bca11bccb1904fe9d79192f85939f76c9bab6a0a549f3af74400`, the imported projection object is pinned to `e2510b3deeebc7d4067710ad1f3210191e6189050a9b3bfa8641f9a9a2bf3182`, and the new object is `e5f6eae350719a9b1586c21e64b974ffe70048580e2a37adc872d0a76e7965a5`. The selected 1,291-object 92 halt union was checked before and after and remained unchanged. Package, dynamic, and source-to-object ancestry are inherited rather than freshly rebuilt; temporary paths may not persist. Resource samples are in the receipt.
