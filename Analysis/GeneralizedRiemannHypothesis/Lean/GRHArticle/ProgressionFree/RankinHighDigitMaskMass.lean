import GRHArticle.ProgressionFree.RankinHighDigitChargeMass

/-!
# Geometric upper bound for the high-digit masks

The low part of a mask remains greedy. Its high part is nonzero. Dropping
the greedy restriction on the high part leaves a product of geometric
series with the zero term removed.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- Greedy exponents that fit below a specified ternary digit cut. -/
noncomputable def rankinLowExponents (k : ℕ) : Finset ℕ := by
  classical
  exact (range (3^k)).filter (· ∈ greedyExponents)

theorem mem_rankinLowExponents {k n : ℕ} :
    n ∈ rankinLowExponents k ↔ n < 3^k ∧ n ∈ greedyExponents := by
  simp only [rankinLowExponents,mem_filter,mem_range]

/-- Bound the mask mass by the finite greedy low mass times the unrestricted
nonzero high mass. -/
theorem reciprocalExponentMass_rankinHighDigitMasks_le {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (h₁ : ∀ i, u i < 1) (k : ι → ℕ) :
    reciprocalExponentMass u (rankinHighDigitMasks k) ≤
      (∏ i, ∑ a ∈ rankinLowExponents (k i), (u i)^a) *
        ((∏ i, (1-(u i)^(3^(k i)))⁻¹)-1) := by
  classical
  let L := Fintype.piFinset (fun i ↦ rankinLowExponents (k i))
  let Y : Set (ι → ℕ) := ({0} : Set (ι → ℕ))ᶜ
  let D := ↥(rankinHighDigitMasks k)
  let U (i : ι) := u i^(3^(k i))
  let g (a : ↥L) := reciprocalExponentWeight u a.val
  let h (b : Y) := reciprocalExponentWeight U b.val
  let lo (v : D) (i : ι) := v.val i % 3^(k i)
  let hi (v : D) (i : ι) := v.val i / 3^(k i)
  have hlo (v : D) : lo v ∈ L :=
    Fintype.mem_piFinset.mpr fun i ↦ mem_rankinLowExponents.mpr
      ⟨Nat.mod_lt _ (by positivity),
        ((mem_greedyExponents_iff_mod_pow_and_div _ _).mp (v.property.1 i)).1⟩
  have hhi (v : D) : hi v ∈ Y := by
    change hi v ≠ 0
    intro he
    obtain ⟨i,hi⟩ := v.property.2
    have hz : v.val i / 3^(k i) = 0 := congrFun he i
    exact hi.ne' hz
  let f (v : D) : ↥L × ↥Y := (⟨lo v,hlo v⟩,⟨hi v,hhi v⟩)
  have hCut (v : D) (i : ι) : lo v i + 3^(k i)*hi v i = v.val i :=
    Nat.mod_add_div _ _
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    rw [←hCut v i,←hCut w i]
    exact congrArg (fun p : ↥L × ↥Y ↦ p.1.val i + 3^(k i)*p.2.val i) he
  have hW (v : D) : reciprocalExponentWeight u v.val = g (f v).1 * h (f v).2 := by
    change (∏ i, u i^v.val i) = (∏ i, u i^lo v i)*(∏ i, (u i^(3^(k i)))^hi v i)
    rw [←prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    rw [←hCut v i,pow_add,pow_mul]
  have hU₀ (i : ι) : 0 ≤ U i := pow_nonneg (hu i) _
  have hU₁ (i : ι) : U i < 1 := pow_lt_one₀ (hu i) (h₁ i) (by positivity)
  have hG : Summable g := (hasSum_fintype _).summable
  have hH₀ := summable_reciprocalExponentWeight hU₀ hU₁
  have hH : Summable h := hH₀.subtype _
  have hg₀ (a : ↥L) : 0 ≤ g a := reciprocalExponentWeight_nonneg hu _
  have hh₀ (b : Y) : 0 ≤ h b := reciprocalExponentWeight_nonneg hU₀ _
  have hProd := hG.mul_of_nonneg hH hg₀ hh₀
  have hYsum : (∑' b : Y, h b) ≤ (∏ i, (1-U i)⁻¹)-1 := by
    have hAll : (∑' b, reciprocalExponentWeight U b) ≤ ∏ i, (1-U i)⁻¹ :=
      Real.tsum_le_of_sum_le (reciprocalExponentWeight_nonneg hU₀)
        (sum_reciprocalExponentWeight_le hU₀ hU₁)
    have hSplit := hH₀.tsum_subtype_add_tsum_subtype_compl ({0} : Set (ι → ℕ))
    have hZero : (∑' b : ({0} : Set (ι → ℕ)), reciprocalExponentWeight U b.val) = 1 := by
      rw [_root_.tsum_subtype]
      simp [reciprocalExponentWeight,Set.indicator]
    rw [hZero] at hSplit
    have he : 1 + (∑' b : Y, h b) = ∑' b, reciprocalExponentWeight U b := hSplit
    linarith
  have hLsum : (∑' a : ↥L, g a) = ∏ i, ∑ a ∈ rankinLowExponents (k i), (u i)^a := by
    rw [tsum_fintype,univ_eq_attach]
    change (∑ a ∈ L.attach, ∏ i, u i^a.val i) = _
    rw [sum_attach L (fun a ↦ ∏ i, u i ^ a i)]
    exact (Finset.prod_univ_sum (fun i ↦ rankinLowExponents (k i)) (fun i a ↦ u i^a)).symm
  rw [reciprocalExponentMass_eq_tsum_subtype]
  calc
    _ ≤ ∑' p : ↥L × ↥Y, g p.1 * h p.2 :=
      Summable.tsum_le_tsum_of_inj f hf (fun p _ ↦ mul_nonneg (hg₀ p.1) (hh₀ p.2))
        (fun v ↦ (hW v).le) ((summable_reciprocalExponentWeight hu h₁).subtype _) hProd
    _ = (∑' a : ↥L, g a) * ∑' b : Y, h b := (hG.tsum_mul_tsum hH hProd).symm
    _ ≤ _ := by
      rw [←hLsum]
      exact mul_le_mul_of_nonneg_left hYsum (tsum_nonneg hg₀)

end GRHArticle.ProgressionFree
