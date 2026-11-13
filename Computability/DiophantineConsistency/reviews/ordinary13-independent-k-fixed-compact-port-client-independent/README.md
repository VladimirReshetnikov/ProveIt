# Independent review: fixed compact port client

The [source-only client](../../research/ordinary13-independent-k-fixed-compact-port-client-draft/README.md) uses the expected symbolic compact tuple and passes the correct port and witness arguments to its conditional first-rank theorem. I found no source-level tuple, cast-direction, index or argument-order mismatch. Lean has not checked the proposed `rfl`, casts, tactics, source providers, or transitive dependencies.

The pinned `C44Short15Facts.c44` and `CompactSymbolicModelIff.p` sources both name the natural tuple `ports betaNat (paramKernel rho) lowNat highNat`, the latter cast pointwise to integers. The `ports` definition makes its components betaNat, paramKernel rho, lowNat, and betaNat+highNat, with beta included exactly once in the fourth port. The proposed `port_cast` applies `P72Root.cast_port` in the direction from each integer port embedded in the difference ring to the embedded model-natural port. Its definitional equality and cast proof remain unelaborated; these are symbolic source identities, not byte or PDF authentication.

The source calls `port_bounds` with betaNat, the fixed kernel, lowNat and highNat; `beta_identity` matches its beta premise, and both mask equalities are reflexive. `K_pos` is applied with exactly the fixed kernel equality. The conjunction projections supply positive beta and K0 and the low/high mask inequalities in the order expected by the helper. The independent child J declaration is applied to the same natural tuple and its pointwise integer cast.

The candidate's slots 0,1,2,7,8,9,12 are J, F−1, alpha−1, s−1, r, eta and gamma; ports 0–3 are beta, K0, MC and MF. The call to `IndependentKFirstRankDiscreteDraft.zero_k_impossible` maps all 15 values and its assumptions in that same order. The client correctly supplies positivity of the shifted F, alpha and s, d=X+K0, and q. Its first norm, represented rank, Y=q³s, main root and main norm are explicitly hypotheses, as are q's defining equation and J positivity. `child_J_positive` is a separate proposed declaration; it does not silently turn those graph bindings into established theorems.

The receipt reproduces the author's checker and independently verifies the exact tuple, cast interface, source declaration signatures, complete helper call order and graph slot names. The result is a bounded source inspection, with no proof replay, axiom report or physical equation binding. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-independent-k-fixed-compact-port-client-independent/check.py | cmp - reviews/ordinary13-independent-k-fixed-compact-port-client-independent/receipt.json
```
