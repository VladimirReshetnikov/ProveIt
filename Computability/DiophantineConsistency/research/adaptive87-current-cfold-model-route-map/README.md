# Shortest proposed all-model route: current 88/28 ↔ 88/30

The shortest identified route is to formalize one **shared, parameterized model-natural calibration** and use it in both witness directions. It reuses existing fact-level Pell, rank, orientation and power lemmas, rather than routing through the compact44 fixed tuple or proving a second large-k theorem. This is a dependency and obligation map, not an elaborated source, a provider plan, or an iPRA proof. The independently reviewed standard-integer argument is pinned separately.

Work with a model `V` of IΣ₁. Let `ι : V →+* DiffRing V`, and let `p : Fin 4 → ℕ` be the current2011 tuple, with each natural port cast to an integer for the syntax. Let `v : Fin 13 → V` have all coordinates positive. Use the same `q`, `Y=v 7`, `k=v 9+v 10`, `ell=X*Y²*k`, `C`, `Bt`, `R`, `Dstar`, `Vaux` and `y=Vaux+v 11` as in the graph. The 88/28 and 88/30 circuits differ only at `root_skew`, `k*C` versus `k*Bt`.

The intended final interface is two **existential** witness maps, not a same-valuation equivalence:

```
child_to_parent : PosZero child p → PosZero parent p
parent_to_child : PosZero parent p → PosZero child p
```

Here `PosZero e p` quantifies `v : Fin 13 → V`, all coordinates positive, and `InternalZero (e p) v`. Their contraposition supplies `HAExpressionNoZeroEquiv.SameNoZero` after the exact positive-shift conversion and model-natural predecessor witnesses; then `HAExpressionNoZeroEquiv.bridge` transports the **existing 88/30 parent bridge**. The parent bridge itself is a separate unelaborated proposal that instantiates the historical 87 parent; it must be checked in the same coherent environment. Do not apply `SameZero` to these witness-changing maps.

## 1. Literal and port foundation

Generate an 88/28 `Expr` literal and residual fields from the pinned graph, compare all rows to the 88/30 literal, and prove the output/evaluator identity when only coordinate 8 changes. Extract four residual zeros from a sum of squares in `DiffRing V`, then bind the first and main signed roots and the strong and auxiliary fields. These are new graph-specific Lean obligations; a JSON comparison is not a theorem about the Lean literal.

`ArithmeticAdaptiveScaledNorms2011.currentPorts` and `currentPorts_cast`, or `ModelThirteenCarrier.port0`–`port3`, supply the source-level current tuple interface. The fourth component is `(highPort+beta : ℕ)` cast once, not a second beta shift. `ArithmeticAdaptiveRankWindow2011.current_bounds_nat` gives the mask inequalities but only states `15≤beta`; the convenient `beta_lower_nat : 46≤beta` in `ArithmeticAdaptivePowerLowerBound2011` is **private**. Reprove or export a small 46-bound from its exact natural proof, then cast it into V; do not cite that private name from another module. Current-port-to-physical-byte/PDF semantics are separate.

## 2. Shared model calibration, with witnesses retained

Propose a parameterized theorem taking a positive valuation, represented natural ports and their bounds, `F+alpha<q`, positive `s,tau` with `Y=q³s`, and the four exact natural/signed norm facts. It should return, for the **same** valuation and witnesses,

```
X = Exp.exp R ∧ q*q ≤ X ∧
∃ n w : V, 13≤n ∧ 2*n=R+1 ∧
  2*ycoord n (2*(X*Y*Y−1)+1)=k ∧
  k=2*n+4*(X*Y*Y)*w.
```

It must also retain the oriented natural main root d and its x/y Pell coordinates through the internal proof. The proof may follow the reviewed fact replay, but its following adapters are not yet checked for the new graph:

* Reflect `C>0` in `DiffRing V` to `F+alpha<q` in V. Only then use bounded `tsub` and `P72Root.ι_tsub` to represent `C`, `q−F` and the graph's signed rank by their natural counterparts. Apply the **scalar** `ArithmeticAdaptiveRankWindow2011.scalar_rank_window`, not its old-literal-zero wrapper. A short scalar lower bound `q²≤R` follows from the gap and `q≥2`; `R<Exp.exp R` then gives `q²≤X` once the power equality is known. This avoids a new universal induction for `2^q≥q²`.
* Extract the first natural tau from the signed ring square with `AuxRingNormExtractionDraft.root_of_scaled_ring_square` or the existing `ReducedNormSigned.natural_magnitude_square` plus `ArithmeticAdaptiveQuotients2011.scaled_quotient`. The former is a research draft; neither its graph binding nor its provider is checked. Reflect a signed divisibility result to V with an appropriate model lemma such as `Trace75IntegralTransport.natural_dvd_of_signed`; do not use standard `Int.natAbs` or silently cast truncated subtraction.
* For the actual extra-term main root, adapt the exact `Positive84MainDraft` field binding and use `DirectMainNorm.direct_main_orientation` with its final rank parameter instantiated as `R+X*Y*q`. It requires `U>0`, `Y≥8` and `k>0`, all obtainable from positive s and `q≥2`. Prove the actual magnitude-square equation first; the 84 graph wrapper itself is not this graph. Build the arithmetic 12-slot tuple `![J,F,alpha,f,i,X,Y,T,eta,zeta,u,gamma]` and the required `FreeJMainCongruence` equality from this same oriented root. Then `FreeJMainOrientation.rank_congruence_from_main` yields `q⁴ ∣ magnitude (R+1,k)`; the theorem accepts that explicit fact and does not require an old 12-variable graph zero. Keep the `X*Y*q` term and its factor-three cancellation.
* `ResidueFirstIndexModelDraft.early_index_of_natural_norm` is an unelaborated fact-level wrapper around the existing first-Pell classification and congruence. Given this tau, the q³ quotient, scalar window and signed rank congruence, it produces n and w together. Classify the **same positive d and c** with `ArithmeticPellClassification.solution_index`. Use `P72Exact.indices_ordinary` at `mu=q⁴`, with `i'=i`, the same n/w and main index, and the actual offset `u=v 11`. The graph's auxiliary ordinate is `ι(f²Tc)−ι(f²R+c)`; `P72Root.ι_magnitude_sq` converts its square and the square after adding ιu to the two exact `absdiff`s. Unlike the separate direct-y 84 draft, this graph already has positive u; its geometry-dependent reconstruction of a fresh offset is unnecessary. Strong reflection must establish `(i*c²)²+Delta=Delta*f²` without assuming f²−1 embeds as truncated subtraction before proving `1≤f²`.
* Adapt the **fact-level**, not graph-specific, `ResidueQBalanceDraft.q_balance`, `Positive84PowerDraft.sixteen_of_three` and `growth`, and `Positive84OrientedPowerDraft.power_of_oriented_balance`. Their source drafts are unelaborated. They use the same d, n and w, the actual extra-term balance and `Y=q³s`; `q | 3X` gives `X≥16` using the new 46 bound. They must not assume `q | X`, cancel 3 modulo H, or import the graph-specific 84 definition `Y=q³*(v 7)` as though it were this graph's input.

## 3. Child → parent

At a child zero, its first ring norm and positive scales imply `C>0`: if C≤0 then Bt<0 and the signed first root exceeds `M(ell+k)`, contradicting the norm. Generalize the positive-root bound and quotient pattern from `ArithmeticAdaptiveTransport2011.first_root_bound` and `FreeJRootBinding`: represent the signed root by its magnitude, extract a natural tau with `ArithmeticAdaptiveQuotients2011.scaled_quotient`, reduce its signed quotient modulo q³ and use the explicit unit identity `q³−(q−1)(q²+q+1)=1` to get `Y=q³s` with `s>0`. The old `first_factor_forces_Y_divisible` is tied to a different literal root; it is a proof pattern, not a direct call.

After the shared calibration, `X≥q²` and `F+alpha<q` imply the signed Bt has a natural representative B with `B>Cnat`, where `Cnat=q−(F+alpha)` is justified by the proven gap. Explicitly prove the rank/Bt cast and `B−Cnat+Cnat=B` in V. Set

```
r_old = rho + k*(B−Cnat) > 0.
```

The free-ring identity checked here gives `Zold(r_old)=Znew(rho)`, so the other coordinates and three remaining residuals stay fixed. The source-level ring identity alone does not establish positivity, the cast equalities, or either graph-zero map.

## 4. Parent → child, reusing the same calibration

At an 88/30 parent zero, the proposed `AdaptiveFourSquare88ModelDraft.unshifted_same_zero` reaches the 87 product literal. `AdaptiveFirstRootFactor87Literal.split_expression_eq` relates that literal to the old adaptive product at the same unshifted valuation. This permits the existing `ArithmeticAdaptiveTransport2011.expressionAt_transport_positive` and `ArithmeticAdaptiveFirstDivisibility2011.current_Y_quotient` to supply the gap/Bt positivity and positive `Y=q³s`, after the current-port cast and positive-valuation hypotheses are matched. Those theorems concern the old literal; they must not be called on the new child zero. Alternatively reprove the same factor facts directly from the four squares.

Let `P=Bt` in the difference ring and normalize the **old** first root by q³ using `Y=q³s`:

```
z = b*(ell+k+(r_old+s)−k*P)−P,
Zold=q³*z,  z²=b²*(1+ell*(ell+k)).
```

The unelaborated `PositiveCarrierDataDraft.root_data` applies to `r_old+s`: it yields a positive model-natural `B=b*t`, positive t, a natural tau satisfying the same first norm, and the signed-root alternatives. Feed this **tau** into the shared calibration, so no equality between separately chosen Pell witnesses is needed. Its retained n≥13 and `k=2*ycoord n Bfirst` imply `k≥8*X*Y²+4`: `ycoord` is monotone, and its value at 2 is `4*X*Y²+2` after justified `m−1` subtraction. This derives large-k from the already needed index and avoids the separate unelaborated `FirstMainLargeKDraft` dependency.

`UnscaleFirstMarginDraft.qcube_margin` then proposes `ell+s<tau`. Adapt its positive-root construction: its existing `shifted_positive_root` assumes the same P in both positions, whereas the C-fold needs C inside `k*C` and B outside. With `Cnat≥1`, B=b*t and the proven margin, use the positive model-natural witness

```
rho = k*(Cnat−1) + t + (tau−(ell+s)) > 0.
```

The checker verifies the corresponding free-ring identity `Znew(rho)=M*tau`; the model proof must separately justify both predecessor subtractions, B's embedding, nonzero scale cancellation and all field evaluations. The other three residuals are independent of coordinate 8.

## Ordering and limits

A practical order is: (1) graph/port and sum-of-squares bindings; (2) signed-to-natural first quotient, gap, rank and main orientation; (3) one parameterized exact-index/power calibration returning n; (4) the two positive witness constructors and final `SameNoZero` client. The parent branch can use the existing old-literal transport while the child branch needs a new root binding. The compact 84/85 clients are valuable sources of fact-level proof patterns but have different coordinate shifts, tuple and Y representation; none may be imported as an unexplained graph-zero implication.

Every proposed source, local materialization name, cast, tactic, nonstandard-model theorem application, `#print axioms`, compiled object and transitive package provider remains unverified for this composition. Run `python3 -I -S -B research/adaptive87-current-cfold-model-route-map/check.py` to reproduce only the pinned source-interface observations and the two exact free-ring coordinate identities. It does not run Lean, stage artifacts, authenticate providers, or prove the stated model equivalence.
