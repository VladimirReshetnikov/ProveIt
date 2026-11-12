# Independent source review: AQ17/105 residual extraction

This is a static source and external free-ring algebra audit, not a Lean build. Run `python3 -I -S -B check.py` from any directory and compare with `result.json`; the author's source receipt also reproduces. All tactic scripts, definitional equalities, imports, provider objects and axiom reports remain unelaborated.

All eight proposed mixed-evaluation residual identities have matching parent and child indices. The separate [mixed graph review](../adaptive-aq17-natural-forced105-independent/README.md) checks the complete external polynomial equality. The source proposes to combine the eight square identities and derive zero equivalence; this review does not establish those Lean steps.

The checker independently expands residuals 0, 1, 2, 3 and 7 and verifies the two quotient norms, strong equality, auxiliary equality and time equation. Writing `S=I²−Q` for the strong residual and `A=y²−Q*(y²−z²)−1` for the auxiliary residual, the required additive cut is exactly `A−(y²−z²)*S=0`. This confirms the sign and coefficient of the source's `linear_combination`. The time equation uses the shifted rank `v 13+1`, matching the graph. The q-bound argument is mathematically valid: the shifted eta and `Y*k` terms give `c≥2`; with shifted `i≥1`, `I=c²*i≥2` and `q=I²≥4`.

The endpoint source proposes to supply the prior `ZeroEquivalence` and `SixForced` premises using these unelaborated proofs, but still explicitly takes the AQ22, AQ20 and AQ17 graph obligations. The optional seventh J-forcing step and AQ17/104 endpoint are outside this packet. This review proves no new internal iPRA theorem or PDF semantics and does not upgrade the historical parent provenance.
