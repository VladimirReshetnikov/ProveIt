# First and doubled strong Pell facts for the 80-row graph

`Direct80Pell.first_and_doubled` is a Lean theorem for arbitrary natural ports with `beta>0` and every strictly positive valuation of the exact 80-row Lean graph in any IΣ₁ model with the repository's ordered-ring interface. Given internal zero of that graph, it constructs positive `tau`, `f`, a positive first Pell index `n`, and a positive doubled ordinate `I` with:

* `E=tau²` and `1+a=f²`, where `a=delta*U²*E`;
* `n≤k`, `xcoord n (2*(P-1)+1)=tau`, and `2*ycoord n (2*(P-1)+1)=k`, where `P=X*(mu*Y)²` and `k=eta+zeta`;
* `I=2*U*tau*f`, `(1+2*a)²=1+delta*I²`, and `delta*(4*a*(1+a))=(delta*I)²`;
* `c² ∣ I`.

Definitions of `delta,U,E,c,X,mu,Y` and the exact graph are in the separately checked [80-row factor-root packet](../ten-positive-80-model-binding-prototype/README.md). That packet uses an external JSON/source comparison; no Lean file/PDF interpretation is claimed. This theorem applies the existing `ArithmeticPellFirstNorm.positive_parameter_solution` to the derived first norm, then derives the doubled identities by ring algebra. The existential `n` is an index; it must not be confused with the separate graph witness also named `n` in the source chart.

This establishes necessary model-level arithmetic consequences of an actual graph zero. It does **not** establish the adjacent rational-Pell descent or integrality of the second root quotient, decode the graph's remaining factors, prove either graph-to-machine direction, prove internal iPRA derivability, or establish the external file binding inside Lean.

The clean author `observations/pell-attempt02/` run exited 0 without warnings or `sorryAx`, and the printed axiom report was `[propext, Classical.choice, Quot.sound]` (Lean metatheory). Source SHA-256 is `2cba59b067dccb9f7710d9dc54d67628ecee8ad29e3268b294f357b295dd93c3`; object SHA-256 is `764c9ce5f5f8e55323128ef195307ca030eee2596bd6eda283a6e0fc2be97807`. Attempt 01 failed to rewrite under local abbreviations and is retained; attempt 02 uses a factored intermediate identity.

The guarded runner pins the six earlier prototype objects, selected `ArithmeticGcdNormalization` object, source, runner and Lean executable before and after. Its selected provider also supplies the direct `ArithmeticPellFirstNorm` object; that object and the full union are inherited and were **not** separately hashed by this runner. Package-transitive and dynamic dependencies and full historical source-to-object ancestry likewise remain inherited. Resource observations are sampled, and `/tmp` objects may disappear. This is not a paired replay or independent review.

From the repository root, with the recorded provider present and a free guarded Lean slot, use `ATTEMPT=attempt03 python3 -I -S -B Computability/DiophantineConsistency/research/ten-positive-80-pell-prototype/run.py` for a fresh run.
