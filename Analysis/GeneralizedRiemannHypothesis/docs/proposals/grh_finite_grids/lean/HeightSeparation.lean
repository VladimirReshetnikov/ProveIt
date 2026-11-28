import Mathlib.NumberTheory.Height.Basic

/-! A quantitative local separation lemma for the relative height used in the
frequency count. The field and its product formula are the pinned mathlib ones. -/
open Function Height Height.AdmissibleAbsValues

namespace FrequencyHeights

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- A single nonarchimedean absolute value is bounded by the relative height. -/
theorem local_le_height (w : nonarchAbsVal (K := K)) (u : K) :
    w.val u ≤ mulHeight₁ u := by
  classical
  let g (v : nonarchAbsVal (K := K)) := max (v.val u) 1
  have hf : g.HasFiniteMulSupport := by
    unfold g
    fun_prop
  have hfinite : w.val u ≤ ∏ᶠ v : nonarchAbsVal (K := K), g v := by
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.subset_insert w _)]
    exact Finset.le_prod_max_one (Finset.mem_insert_self w _) (fun v ↦ v.val u)
  unfold mulHeight₁
  exact hfinite.trans (le_mul_of_one_le_left ((w.val.nonneg u).trans hfinite)
    (Multiset.one_le_prod_map fun _ _ ↦ le_max_right ..))

/-- A residue collision forces a large local reciprocal difference; high
enough precision makes such a collision impossible on a bounded-height pair.
This applies to either chart, since inversion preserves relative height. -/
theorem separate (w : nonarchAbsVal (K := K)) {u v : K} {B L : ℝ}
    (hu : mulHeight₁ u ≤ B) (hv : mulHeight₁ v ≤ B)
    (large : 2 ^ totalWeight K * B ^ 2 < L)
    (close : u ≠ v → L ≤ w.val ((u-v)⁻¹)) : u = v := by
  by_contra hne
  have h : L ≤ 2 ^ totalWeight K * B ^ 2 := calc
    L ≤ w.val ((u-v)⁻¹) := close hne
    _ ≤ mulHeight₁ ((u-v)⁻¹) := local_le_height w _
    _ = mulHeight₁ (u-v) := mulHeight₁_inv _
    _ ≤ 2 ^ totalWeight K * mulHeight₁ u * mulHeight₁ v := mulHeight₁_sub_le _ _
    _ ≤ 2 ^ totalWeight K * B * B := by
      have hB := (mulHeight₁_nonneg u).trans hu
      gcongr
    _ = 2 ^ totalWeight K * B ^ 2 := by rw [sq, mul_assoc]
  exact (not_le_of_gt large) h

/-- Count the two disjoint charts on an arbitrary bounded finite set.
The affine code and the reciprocal code may have different finite target sizes. -/
theorem two_chart_card {A I : Type*} [Fintype A] [Fintype I]
    (w : nonarchAbsVal (K := K)) (X : Finset K) {B L : ℝ}
    (bounded : ∀ x ∈ X, mulHeight₁ x ≤ B)
    (large : 2 ^ totalWeight K * B ^ 2 < L)
    (aff : K → A) (inf : K → I)
    (ha : ∀ u v, w.val u ≤ 1 → w.val v ≤ 1 → aff u = aff v →
      u ≠ v → L ≤ w.val ((u-v)⁻¹))
    (hi : ∀ u v, w.val u < 1 → w.val v < 1 → inf u = inf v →
      u ≠ v → L ≤ w.val ((u-v)⁻¹)) :
    X.card ≤ Fintype.card A + Fintype.card I := by
  classical
  let code (x : K) : A ⊕ I := if w.val x ≤ 1 then .inl (aff x) else .inr (inf x⁻¹)
  have hinj : Set.InjOn code (X : Set K) := by
    intro u hu v hv heq
    have bu := bounded u hu
    have bv := bounded v hv
    by_cases h₁ : w.val u ≤ 1 <;> by_cases h₂ : w.val v ≤ 1
    · exact separate w bu bv large <| ha _ _ h₁ h₂ (by simpa [code, h₁, h₂] using heq)
    · simp [code, h₁, h₂] at heq
    · simp [code, h₁, h₂] at heq
    · have inv_small (t : K) (ht : ¬w.val t ≤ 1) : w.val t⁻¹ < 1 := by
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ (lt_of_not_ge ht)
      apply inv_injective
      apply separate w (by simpa only [mulHeight₁_inv] using bu) (by simpa only [mulHeight₁_inv] using bv) large
      exact hi _ _ (inv_small u h₁) (inv_small v h₂) (by simpa [code, h₁, h₂] using heq)
  rw [← Finset.card_image_of_injOn hinj]
  simpa using Finset.card_le_univ (X.image code)

#print axioms two_chart_card
#print axioms local_le_height
#print axioms separate
end FrequencyHeights
