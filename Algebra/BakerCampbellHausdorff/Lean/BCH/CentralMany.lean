/-
# Several factors with central pairwise commutators (Corollary 9.3)

Corollary 9.3 of the accompanying article (`docs/combined`): if all the
commutators `⁅Xᵢ, Xⱼ⁆` commute with every `X_k`, then the ordered product of
the exponentials is a single exponential,

`e^{X₀} e^{X₁} ⋯ e^{X_{m-1}} = exp(∑ⱼ Xⱼ + ½ ∑_{i < j} ⁅Xᵢ, Xⱼ⁆)`

(`exp_prod_range_of_central`). This is the all-factors form behind the Weyl and
displacement multiplication laws; it follows from the two-factor identity
`BCH.exp_mul_exp_of_central` by induction on the number of factors, peeling off
the last one.
-/
import BCH.Central

open NormedSpace Finset

namespace BCH

section Lie

variable {R : Type*} [Ring R]

/-- The bracket is additive in the left argument, for a `Finset` sum. -/
lemma sum_lie' {ι : Type*} (s : Finset ι) (f : ι → R) (b : R) :
    ⁅∑ i ∈ s, f i, b⁆ = ∑ i ∈ s, ⁅f i, b⁆ := by
  simp only [Ring.lie_def, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

/-- An element commuting with `a` and `b` commutes with `⁅a, b⁆`. -/
lemma commute_lie_right {c a b : R} (ha : Commute c a) (hb : Commute c b) :
    Commute c ⁅a, b⁆ := by
  rw [Ring.lie_def]
  exact (ha.mul_right hb).sub_right (hb.mul_right ha)

end Lie

section Many

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- The exponent of the ordered product of `m` exponentials in the central-commutator case:
`∑_{j < m} Xⱼ + ½ ∑_{j < m} ∑_{i < j} ⁅Xᵢ, Xⱼ⁆`. -/
noncomputable def centralExponent (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] (X : ℕ → 𝔸) (m : ℕ) : 𝔸 :=
  ∑ j ∈ range m, X j + (1 / 2 : 𝕂) • ∑ j ∈ range m, ∑ i ∈ range j, ⁅X i, X j⁆

omit [CompleteSpace 𝔸] in
/-- An element commuting with `X₀, …, X_{m-1}` commutes with the exponent. -/
lemma commute_centralExponent {X : ℕ → 𝔸} {c : 𝔸} {m : ℕ} (hc : ∀ k < m, Commute c (X k)) :
    Commute c (centralExponent 𝕂 X m) := by
  refine Commute.add_right
    (Commute.sum_right _ _ _ fun j hj => hc j (Finset.mem_range.mp hj)) ?_
  refine Commute.smul_right (Commute.sum_right _ _ _ fun j hj => ?_) _
  rw [Finset.mem_range] at hj
  exact Commute.sum_right _ _ _ fun i hi =>
    commute_lie_right (hc i ((Finset.mem_range.mp hi).trans hj)) (hc j hj)

/-- **Corollary 9.3**: if every commutator `⁅Xᵢ, Xⱼ⁆` commutes with every `X_k`, then the
ordered product `e^{X₀} ⋯ e^{X_{m-1}}` equals
`exp(∑_{j<m} Xⱼ + ½ ∑_{j<m} ∑_{i<j} ⁅Xᵢ, Xⱼ⁆)`. -/
theorem exp_prod_range_of_central (X : ℕ → 𝔸) :
    ∀ m : ℕ, (∀ i < m, ∀ j < m, ∀ k < m, Commute (X k) ⁅X i, X j⁆) →
      ((List.range m).map fun j => exp (X j)).prod = exp (centralExponent 𝕂 X m)
  | 0, _ => by simp [centralExponent, exp_zero]
  | m + 1, h => by
    have hlt : ∀ i, i < m → i < m + 1 := fun i hi => hi.trans (Nat.lt_succ_self m)
    have ih := exp_prod_range_of_central X m fun i hi j hj k hk =>
      h i (hlt i hi) j (hlt j hj) k (hlt k hk)
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    -- the new commutator is the central element `C = ∑_{i < m} ⁅Xᵢ, X_m⁆`
    set E := centralExponent 𝕂 X m with hE
    set C := ∑ i ∈ range m, ⁅X i, X m⁆ with hC
    have hCcen : ∀ k < m, Commute C (X k) := fun k hk =>
      Commute.sum_left _ _ _ fun i hi =>
        (h i (hlt i (Finset.mem_range.mp hi)) m (Nat.lt_succ_self m) k (hlt k hk)).symm
    have hEC : ⁅E, X m⁆ = C := by
      rw [hE, centralExponent, lie_add_left', sum_lie', lie_smul_left', ← hC]
      have hz : ⁅∑ j ∈ range m, ∑ i ∈ range j, ⁅X i, X j⁆, X m⁆ = 0 := by
        rw [sum_lie']
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [sum_lie']
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [Ring.lie_def,
          (h i (hlt i (hi.trans hj)) j (hlt j hj) m (Nat.lt_succ_self m)).symm.eq, sub_self]
      rw [hz, smul_zero, add_zero]
    have hXcen : Commute (X m) ⁅E, X m⁆ := by
      rw [hEC, hC]
      exact Commute.sum_right _ _ _ fun i hi =>
        h i (hlt i (Finset.mem_range.mp hi)) m (Nat.lt_succ_self m) m (Nat.lt_succ_self m)
    have hEcen : Commute E ⁅E, X m⁆ := by
      rw [hEC]
      exact (commute_centralExponent (𝕂 := 𝕂) hCcen).symm
    rw [List.map_singleton, List.prod_singleton,
      exp_mul_exp_of_central (𝕂 := 𝕂) hEcen hXcen, hEC]
    congr 1
    rw [hE, centralExponent, centralExponent, Finset.sum_range_succ, Finset.sum_range_succ,
      hC, smul_add]
    abel

end Many

end BCH
