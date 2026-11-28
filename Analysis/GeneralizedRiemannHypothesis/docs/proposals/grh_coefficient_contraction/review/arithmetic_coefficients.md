# Independent replacement: universal integrality, one height bound, one terminal finite sum

Source snapshot: `d417d0b5b08edd4f5f67224fd310add7f1618ca0`; the targeted files below are unchanged at the newer proposal-audit snapshot `1a59f50680e470fb5269bbe70c06f974c95ad930`.
All paths below are relative to `Analysis/GeneralizedRiemannHypothesis/Lean/grh/src/`.

## 1. What is new after the newly added sweep proposals

The canonical diagonal sweep, exact Fourier cost, and proposed active-frontier representation must no longer be presented as new. The added `grh_diagonal_sweep_proposal` and `grh_exchange_sweeps` cover those directions. The new integral-field proposal concerns the auxiliary CM field's integer ring, different and Frobenius orbits. The new Ribet-lattice proposal concerns Fitting ideals, Smith duality and block assembly. Neither is this proposal.

This proposal instead changes the **arithmetic specification of a coefficient family** and the **terminal argument that consumes it**:

* Replace an exact representation as a bounded multiset of roots of unity by the arithmetic facts actually consumed: integrality at every required nonarchimedean place, and an absolute-value bound under every complex automorphism.
* Carry the quantitative absolute-value bound **only for the trivial twist**. All nontrivial twists need coefficient integrality, covariance and support, but no coefficient-height budget.
* Establish one exact joint finite-class expansion of the terminal period. Obtain integrality by closure of a subring under sums and products, and the archimedean estimate by the ordinary finite triangle inequality.

The new sweep proposals can be assumed implemented. Their chosen transformations supply the same local integral linear operators; this proposal uses those operators without changing their schedule or numerical cost.

The inventory agent checked both newly added sweep reports and plans. The diagonal-sweep report explicitly retains the existing `nsmul` summation/integrality argument. The exchange-sweep proposal's future frontier question does not supply the coefficient-specification replacement or the terminal theorem here. Its future questions about Fourier norms and integrality-preserving normalization should be acknowledged, but the present proposal does not normalize Fourier transforms or claim a better Fourier norm.

## 2. The decisive source-level asymmetry

The current `IsPathDatum N` field (iii) requires every value to be a sum of at most `N` roots of unity (`AuxiliaryForms/PathData.lean:418–467,533–543`). For a twist family, `TransfersPeriods` carries a function `N : MFoldTwist → ℕ` and a function-valued growth factor (`Turns.lean:803–810`).

There is exactly one substantive consumer of the root expression: `LastPath.lean:935`, inside `exists_lastPathPeriod_mem_smul_norm_le`. That theorem has two consumers:

1. `SpanningForms.lean:223–271`, `exists_mul_lastPathPeriod_mem_embValRing`. It applies to every twist, but discards both the coefficient count and the final number of summands. It uses only closure of the integral-valued additive subgroup.
2. `SpanningForms.lean:325–384`, `norm_lastPathPeriod_le`. It uses the coefficient/summand count, but its twist is explicitly `1`.

The final API preserves this same distinction. `exists_lowerChain_integral_and_weylNormSq_le` (`SpanningForms.lean:667–741`) and `exists_span_short_lifts_eq_top` (line 773) require integrality for all twists, at primes not dividing the twist modulus, but an archimedean conjugate bound only for the untwisted lift.

Therefore neither the exact multiset witness nor quantitative coefficient bounds at nontrivial twists are used by the final result. This is an audited weakening of the intermediate contract, not an assumption that only one twist is needed in the mathematical proof.

## 3. The replacement arithmetic specification

Let

\[
 \mathcal I=
 \{z\in\mathbb C:\ z\in\mathrm{embValRing}_{p,\iota}
       \text{ for every rational prime }p
       \text{ and every }\mathrm{PadicPlace}\ \iota\}.
\]

This is a subring of `ℂ`, as an intersection of valuation subrings. It contains every root of unity: a root of unity remains of finite order under a field homomorphism, and its norm is one. The source defines `embValRing` in `Lib/Adelic/AutomorphicForms/PAdicGauge.lean:172`.

For a nonnegative real `B`, define

\[
 \operatorname{HouseBound}(B,z)
 \quad\Longleftrightarrow\quad
 \forall\sigma\in\operatorname{Aut}(\mathbb C),\quad
 |\sigma(z)|\le B.
\]

For a family `Ψ_ϑ : X_ϑ → ℂ` of finite coefficient functions, the new arithmetic contract is

\[
 \tag{I}\forall\vartheta,S,\quad\Psi_\vartheta(S)\in\mathcal I,
 \qquad
 \tag{H}\forall S,\quad\operatorname{HouseBound}(B,\Psi_1(S)).
\]

The geometric parts of `IsPathDatum`—dependence on the actual edge variables, character covariance, and the split-injective support condition—are retained. If an active-frontier implementation has already eliminated dependence bookkeeping, use its geometric datum type unchanged.

### Algebraic-integer formulation

One may replace (I) by `IsIntegral ℤ (Ψ_ϑ(S))`, which is more familiar mathematically and is satisfied by all coefficients constructed here. It implies (I): if `α` satisfies a monic polynomial with integer coefficients and `|ι_p(α)|>1`, the leading term has strictly greater nonarchimedean norm than every lower term, contradicting the polynomial equation. The direct intersection-of-valuation-rings formulation is an economical initial Lean port: it uses exactly the existing local API, and sum/product closure is immediate.

It is unnecessary to prove that all the coefficients lie in one chosen number field, compute their degrees, choose a common cyclotomic conductor, or extend finite-field embeddings to `Aut(ℂ)`. The source already quantifies over `Aut(ℂ)` for its height estimates, and the new (H) uses the same quantifier. A bound only for the identity or ordinary complex conjugation would be insufficient.

The new predicate is deliberately weaker than “a sum of at most `N` roots of unity.” An algebraic-integer/house specification should not be converted back to such a multiset. That reverse implication is not needed and is generally false.

## 4. Finite integral-operator theorem

**Theorem.** Let `I_ϑ,J_ϑ` be finite sets and `T_ϑ : ℂ^{I_ϑ} → ℂ^{J_ϑ}` linear operators. Suppose every matrix coefficient of every `T_ϑ` belongs to `𝓘`. Suppose also that for one nonnegative number `K`,

\[
 \forall\sigma\in\operatorname{Aut}(\mathbb C),\ \forall j\in J_1,
 \qquad
 \sum_{i\in I_1}|\sigma(T_1(j,i))|\le K.
\]

If a family `f_ϑ` satisfies (I) and (H) with bound `B`, then `T_ϑ f_ϑ` satisfies (I) and (H) with bound `KB`.

**Proof.** Every output is a finite sum of products of elements of `𝓘`. For the trivial twist, apply `σ` to the finite sum, use the triangle inequality and multiplicativity of the complex norm, and bound every input by `B`:

\[
 |\sigma((T_1f_1)(j))|
 \le\sum_i|\sigma(T_1(j,i))|\,|\sigma(f_1(i))|
 \le KB.
\]

There is no sum-count penalty in the nonarchimedean assertion. There is no quantitative hypothesis at a nontrivial twist. Composition multiplies the scalar budgets, so repeated operators need only one natural or real budget, not a function of the twist.

### Application to the existing operators

* The first point data take values `0` or `1` (`GridFirstColumns.lean:422–430`). Their integrality and bound one are immediate.
* The initial level averaging is an **unnormalized** finite sum with root-of-unity character factors (`GridFirstColumns.lean:633`). It preserves integrality at every twist and costs `|LevelCosets(1)|` in (H). The existing larger bound may be retained.
* The local Fourier transform is an unnormalized sum with root-of-unity coefficients (`Turns.lean:172`). Integrality is preserved for every twist, and only its matrix at twist one needs a row-sum estimate.
* `matchOf` evaluates a function at a selected representative and multiplies by one root of unity, or returns zero (`Chain/SquareLaw.lean:230`). It preserves integrality and costs one in (H). The support, completion and covariance proofs remain unchanged.

No new finite-field matching theorem is being proposed. The operator theorem is the elementary arithmetic abstraction needed to consume those already existing or proposed transformations. The root-valued entries are used locally to prove two simple operator properties; there is no need to retain a root decomposition of each resulting coefficient.

**Normalization safeguard.** The line scalar `c_line(ϑ)` stays in the period factor `c_square/c_line`. It must not be absorbed into the coefficient operator. Its square-root norm factor need not be integral. Nothing here legitimizes normalized Fourier transforms or division by a group order.

## 5. A smaller family-transfer contract

Write `Geom(Γ,Ψ)` for the retained geometric datum conditions, `Int(Ψ)` for (I), and `Ht₁(B,Ψ)` for (H). The replacement of `TransfersPeriods Γ' Γ k c` has the form

\[
\begin{split}
\forall B,\Psi',\quad &
 \operatorname{Geom}(\Gamma',\Psi')\land\operatorname{Int}(\Psi')
 \land\operatorname{Ht}_1(B,\Psi')\\
 &\Longrightarrow\exists\Psi,\quad
 \operatorname{Geom}(\Gamma,\Psi)\land\operatorname{Int}(\Psi)
 \land\operatorname{Ht}_1(kB,\Psi)\\
 &\hspace{5em}\land\bigl[\forall\Xi,\quad
 (\Psi\propto_\Gamma\Xi)\Longrightarrow
 (\Psi'\propto_{\Gamma'}\Xi/c)\bigr].
\end{split}
\]

Here `B,k : ℕ` can be scalars, whereas `c : MFoldTwist → ℂˣ` remains a function of the twist. This keeps every uniformity requirement for the seesaws and final normalization. In particular, the same constructed family works for all initial forms, and proportionality scalars remain independent of the twist and the forms. Only the superfluous family of quantitative budgets has been removed.

The diagonal transfer remains a backward proportionality implication. The polynomial line-flip map remains twist-independent. Neither a pointwise identity of old/new path periods nor a new archimedean test-space map is required.

For a low-risk migration, first replace the arithmetic field of `IsPathDatum N` with integrality plus a house bound while keeping its parameter shape. Once the terminal consumers compile, specialize the family size to the twist-one component. The first stage already eliminates the multiset API; the second removes unnecessary twist-dependent quantitative conditions.

## 6. The exact terminal theorem

Let `X_ϑ` denote the finite set of actual terminal edge assignments, using either the current supported-tuple encoding or a future intrinsic encoding. Set

\[
 \mathcal C_\vartheta=
 \left(\prod_{j=0}^{m}\mathrm{Cl}(K^-_{\vartheta,j})\right)
 \times
 \left(\prod_{j=0}^{m-1}\mathrm{Cl}(K^+_{\vartheta,j})\right).
\]

For `c∈𝒞_ϑ`, choose the standard class representatives. There are `2m+1` independent points. The final point of the true half is `lastPathBlockPoint(ϑ,h)` for the last point `h` of the false half, so it is not a separate class variable.

For each pair `(c,S)`, apply the successive pointwise `jetMap`s along each chain to the initial vectors, and denote the resulting vectors by `V⁻_ϑ(c,S)` and `V⁺_ϑ(c,S)`. Define

\[
 A_\vartheta(c,S)=
 \operatorname{lastPathPairing}
       (V^-_\vartheta(c,S),V^+_\vartheta(c,S)).
\]

**Terminal expansion theorem.** Under the retained covariance conditions and fixed outer levels,

\[
 \tag{E}
 \operatorname{lastPathPeriod}(\Psi_\vartheta,y)
 =\sum_{c\in\mathcal C_\vartheta}\sum_{S\in X_\vartheta}
     \Psi_\vartheta(S) A_\vartheta(c,S).
\]

No coefficient-integrality, coefficient-height, or normed-field hypothesis is needed to prove this identity.

### Proof route with existing source lemmas

The source already has an exact single-chain identity, `IsJointlyInvariant.sum_chain_eq_sum_kernelProduct` (`UpperBound/Objects/LiftChains.lean:225–279`). Apply it to one half while the other half supplies the linear functional, then to the second half. The covariance lemma `IsPathDatum.sum_lastPathPairing_omega_invariant` (`LastPath.lean:737`) supplies the required joint invariance. Convert the shared-endpoint integral to its class sum with `classIntegral_eq_classSum`.

All the levels are free, by the argument at `LastPath.lean:921–924`; thus there are no stabilizer denominators. Finite-sum distributivity and the product-type bijection combine the indices into `𝒞_ϑ×X_ϑ`. This establishes (E).

Only the **sum over edge assignments** is right invariant under the levels. Individual summands need not be invariant. Keep the weighted sum inside each use of the joint-invariance theorem. A termwise conversion of each individual lift into a class sum would be invalid.

The proof does not require a product adelic group, a new quotient measure, or analytic Fubini. `classIntegral` is already a finite-sum construction (`Lib/Adelic/Hecke/ClassSums.lean:74`). It also does not permit removal of the generic tensor-chain infrastructure, which has independent users.

## 7. The two replacement corollaries

### Arithmetic corollary: no counting at all

Fix any required rational prime `p`, any `PadicPlace p`, and a twist `ϑ` with `p∤ϑ.normQ`. Suppose the existing kernel and pairing bounds give

\[
 M A_\vartheta(c,S)\in\mathrm{embValRing}_{p,\iota}
 \quad\text{for every }c,S.
\]

Then, by (I) and (E),

\[
 M\Xi_\vartheta
 =\sum_{c,S}\Psi_\vartheta(S)
       \bigl(M A_\vartheta(c,S)\bigr)
 \in\mathrm{embValRing}_{p,\iota}.
\]

This is just `sum_mem` and `mul_mem` for the valuation subring. There is no `N`, no `L`, no cardinality estimate and no multiset witness in this argument. The existing clearing factor `M_pair * liftDenominator^(2m)` and its size estimate are unchanged. The old start/step `IsCleared` induction applies to the explicit kernel products.

### Archimedean corollary: one triangle inequality

For the trivial twist, fix `σ∈Aut(ℂ)` and suppose the existing jet and branching estimates give `|σ(A₁(c,S))|≤R`. Then

\[
 \tag{B}
 |\sigma(\Xi_1)|
 \le |\mathcal C_1|\,|X_1|\,B\,R.
\]

Apply `σ` to (E), distribute across finite sums/products, and use (H). The existing class-count, boundary-count, kernel-growth and branching-pairing estimates give exactly the old final bound. The old `IsSmall` induction is replaced or reused as the existing `kernelProduct_induction` on explicit point tuples (`LiftChains.lean:288`).

The estimates for the initial coefficients and local transforms can be the improved ones from the sweep proposals or the original coarse ones. This proposal claims no additional numerical improvement; it removes the stronger intermediate witness and unused quantitative family.

## 8. Exact consumer audit and removable mechanisms

`rg` over the full source found the following uses of `IsSumOfRootsOfUnity` or its structure field:

| Source | Role | Replacement |
|---|---|---|
| `PathData.lean:418–467` | Multiset predicate, root multiplication, finite multiset sum, set-`nsmul` lemma | Integral coefficient and house properties; finite integral-operator theorem |
| `PathData.lean:533–547` | Datum field and budget monotonicity | Geometric datum plus arithmetic family contract |
| `GridFirstColumns.lean:422–430,713–716` | Point-value and initial averaging certificate | `0/1` integrality; finite sum of integral root phases; height only at `1` |
| `Turns.lean:501–513,540` | Certificate through Fourier/matching | Integral linear-operator preservation; row-sum bound only at `1` |
| `LastPath.lean:935` | Turns each coefficient into a set-`nsmul` witness | Direct multiplication by the coefficient in (E) |

The terminal `exists_lastPathPeriod_mem_smul_norm_le` has exactly two callers in `SpanningForms`, at lines 265 and 359. Both are replaced by the preceding two corollaries. `IsJointlyInvariant.sum_chain_mem_nsmul` in `LiftChains.lean:323–350` has only the two calls inside the old terminal proof (`LastPath.lean:954,976`); if those disappear, this wrapper has no remaining source caller. Its underlying exact expansion theorem is retained and remains used in `UpperBound/Divisibility/ChainValuation.lean`.

The exact ranges above include statements/comments/retained hypotheses. They are not deletion counts. The directly affected arithmetic packaging is a few hundred source lines, plus family-transfer signatures and their callers. The expected reduction is substantially narrower than the 2,862-line swept-path cluster. Net Lean savings must be measured after implementation; the mathematical gain is removal of three unnecessary layers: exact cyclotomic multisets, quantitative budgets for all twists, and nested set-of-sums induction.

## 9. Integration gates

1. Reproduce the source search showing that the root witness has no other consumer and that the archimedean estimate is invoked only at twist one.
2. Define the integral coefficient ring or algebraic-integer bridge; quantify over every required prime and every `PadicPlace`, not one selected embedding.
3. Keep the unnormalized averaging/Fourier operators and separate period scalar unchanged.
4. Prove the exact terminal identity before replacing either arithmetic consumer. Check `2m+1` nodes and free-level normalizations explicitly.
5. Preserve the final `exists_lowerChain_integral_and_weylNormSq_le` and `exists_span_short_lifts_eq_top` signatures.
6. Compile those consumers and the public theorem targets. Only then remove the old root/nsmul wrappers if a reverse-reference scan remains empty.

This is a paper-level replacement with a precise port plan. It is neither a compiled Lean patch nor an independent verification of the claimed RH/Dirichlet-GRH proof.
