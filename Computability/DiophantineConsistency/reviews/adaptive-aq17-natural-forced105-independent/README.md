# Independent review: six forced inputs in the AQ17 natural graph

This is an external, all-model mathematical review of the 17-variable, 105-operation natural candidate. Run `python3 -I -S -B check.py` from any directory and compare with `result.json`. The author's 105 and 108 receipts also reproduce. No Lean, staging, provider audit or internal iPRA proof was performed.

The checker independently expands the parent under exactly the mixed substitution and the complete 105-row child: all 34,492 integer polynomial terms and all eight named residuals match for arbitrary integer inputs and ports. All rows, inputs and ports are live and the output is exactly eight residual squares. Its port-independent monomial `n_Y⁸*n_eta⁸*n_i⁴` has coefficient 1, proving exact degree 20 for every fixed integer port tuple. The fully shifted graph is generally a different polynomial at the same tuple; only the mixed-substitution identity is pointwise. The intermediate 108 graph's three unshifted inputs and every shift/parent row were separately checked against the same parent, and its author receipt reproduces.

For the model zero maps, all 11 shifted values are positive model naturals. Put `k=eta+zeta`, `E=X*Y`, `ell=E*Y*k`, `c=eta+Y*k`, `Delta=3+4*(E+Y)+(E+Y)²`, `I=c²*i`, and `Q=Delta*(f²-1)`. Then `ell,c>0`, `Delta>0`, and `I≥2`, independent of every unshifted input and every port. The exact graph wiring of the relevant eight-square residuals is checked.

- The two quotient norm equations have right sides at least one, so each quotient is positive.
- If `vValueVariable=0`, strong residual zero gives `Q=I²≥1`; the auxiliary residual gives `y²=1+Q*y²`, impossible for nonnegative `y²`.
- If `f=0`, then `Q=-Delta<0`, contradicting `Q=I²>0`.
- If `y=0`, the auxiliary and strong residuals give `Q*z²=1` and `Q=I²≥4`. For natural z, `z=0` gives product zero, while `z>0` gives `z²≥1` and product at least four.
- If `T=0`, the v-binding residual gives `z=-f²*rank-c<0`, contradicting that z is a model natural.

Each contradiction stands alone and uses none of the other five unshifted variables' positivity. The resulting positive parent zero and the reverse map using predecessors for the 11 shifted coordinates yield equal zero-existence statements in the stated ordered IΣ₁ models for arbitrary integer ports. This uses model discreteness, nonnegative cone/order and sum-of-squares zero properties; it does not constitute elaborated Lean or a literal internal proof. The inherited AQ20 bridge still needs fixed positive represented beta, and all earlier provenance and endpoint limitations remain.
