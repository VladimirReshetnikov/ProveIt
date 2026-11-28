import GRHArticle.ProgressionFree.RectangularPrefixWeights
import GRHArticle.ProgressionFree.LightPrimeBlocks

/-!
# Reciprocal mass by ternary digit slices

Euclidean division gives a bijection between an exponent vector and its
high part paired with a bounded low vector. Reciprocal weights factor under
this bijection, allowing a finite inequality on every low slice to be summed.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- Join a low exponent vector and a high exponent vector at ternary cuts. -/
def joinExponentDigits {ι : Type*} (k : ι → ℕ) (a h : ι → ℕ) : ι → ℕ :=
  fun i ↦ a i + 3^(k i)*h i

/-- High exponents paired with a vector in the low box parameterize all
exponent vectors by Euclidean division. -/
def exponentDigitSliceEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℕ) :
    ((ι → ℕ) × ↥(exponentBox (fun i ↦ 3^(k i)-1))) ≃ (ι → ℕ) where
  toFun p := joinExponentDigits k p.2.val p.1
  invFun v := (fun i ↦ v i/3^(k i),⟨fun i ↦ v i%3^(k i),mem_exponentBox.mpr fun i ↦ by
    have h := Nat.mod_lt (v i) (show 0 < (3:ℕ)^(k i) by positivity)
    omega⟩)
  left_inv p := by
    have hd (i : ι) : p.2.val i < 3^(k i) := by
      have h := mem_exponentBox.mp p.2.property i
      have hp : 0 < (3:ℕ)^(k i) := by positivity
      omega
    apply Prod.ext
    · funext i
      change (p.2.val i + 3^(k i)*p.1 i)/3^(k i) = p.1 i
      rw [Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt (hd i),zero_add]
    · apply Subtype.ext
      funext i
      change (p.2.val i + 3^(k i)*p.1 i)%3^(k i) = p.2.val i
      exact (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hd i))
  right_inv v := funext fun i ↦ Nat.mod_add_div (v i) (3^(k i))

/-- Factor the weight of a joined exponent vector. -/
theorem reciprocalExponentWeight_joinExponentDigits {ι : Type*} [Fintype ι]
    (k a h : ι → ℕ) (u : ι → ℝ) :
    reciprocalExponentWeight u (joinExponentDigits k a h) =
      reciprocalExponentWeight (fun i ↦ u i^(3^(k i))) h * reciprocalExponentWeight u a := by
  unfold reciprocalExponentWeight
  rw [←prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  simp only [joinExponentDigits,pow_add,pow_mul]
  exact mul_comm _ _

/-- The reciprocal mass is the sum of the finite low masses weighted by
the corresponding high parts. -/
theorem reciprocalExponentMass_eq_tsum_digitSlices {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (h₁ : ∀ i, u i < 1) (k : ι → ℕ)
    (F : Set (ι → ℕ)) :
    letI : DecidablePred (· ∈ F) := fun _ ↦ Classical.propDecidable _
    reciprocalExponentMass u F =
      ∑' h : ι → ℕ, reciprocalExponentWeight (fun i ↦ u i^(3^(k i))) h *
        ∑ a ∈ exponentBox (fun i ↦ 3^(k i)-1), if joinExponentDigits k a h ∈ F then
          reciprocalExponentWeight u a else 0 := by
  classical
  let L := exponentBox (fun i ↦ 3^(k i)-1)
  let e := exponentDigitSliceEquiv k
  have hs : Summable (F.indicator (reciprocalExponentWeight u)) :=
    summable_subtype_iff_indicator.mp ((summable_reciprocalExponentWeight hu h₁).subtype _)
  have hs' : Summable (fun p : (ι → ℕ) × ↥L ↦ F.indicator (reciprocalExponentWeight u) (e p)) :=
    e.summable_iff.mpr hs
  unfold reciprocalExponentMass
  rw [←e.tsum_eq (F.indicator (reciprocalExponentWeight u))]
  rw [hs'.tsum_prod' (fun p ↦ (hasSum_fintype _).summable)]
  apply tsum_congr
  intro h
  rw [tsum_fintype,univ_eq_attach,mul_sum]
  have he (a : ↥L) : F.indicator (reciprocalExponentWeight u) (e (h,a)) =
      reciprocalExponentWeight (fun i ↦ u i^(3^(k i))) h *
      (if joinExponentDigits k a.val h ∈ F then reciprocalExponentWeight u a.val else 0) := by
    change F.indicator (reciprocalExponentWeight u) (joinExponentDigits k a.val h) = _
    by_cases hF : joinExponentDigits k a.val h ∈ F
    · rw [Set.indicator_of_mem hF,if_pos hF,reciprocalExponentWeight_joinExponentDigits]
    · rw [Set.indicator_of_notMem hF,if_neg hF,mul_zero]
  calc
    _ = ∑ a ∈ L.attach, reciprocalExponentWeight (fun i ↦ u i^(3^(k i))) h *
        (if joinExponentDigits k a.val h ∈ F then reciprocalExponentWeight u a.val else 0) :=
      sum_congr rfl fun a _ ↦ he a
    _ = _ := sum_attach L (fun a ↦ reciprocalExponentWeight (fun i ↦ u i^(3^(k i))) h *
      (if joinExponentDigits k a h ∈ F then reciprocalExponentWeight u a else 0))

/-- The finite low mass at a fixed high vector. -/
noncomputable def exponentDigitSliceMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (k : ι → ℕ) (F : Set (ι → ℕ)) (h : ι → ℕ) : ℝ := by
  classical
  exact ∑ a ∈ exponentBox (fun i ↦ 3^(k i)-1), if joinExponentDigits k a h ∈ F then
    reciprocalExponentWeight u a else 0

private theorem summable_weighted_exponentDigitSliceMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (h₁ : ∀ i, u i < 1) (k : ι → ℕ) (F : Set (ι → ℕ)) :
    Summable (fun h : ι → ℕ ↦ reciprocalExponentWeight (fun i ↦ u i^(3^(k i))) h *
      exponentDigitSliceMass u k F h) := by
  classical
  let U (i : ι) := u i^(3^(k i))
  let L := exponentBox (fun i ↦ 3^(k i)-1)
  have hU₀ (i : ι) : 0 ≤ U i := pow_nonneg (hu i) _
  have hU₁ (i : ι) : U i < 1 := pow_lt_one₀ (hu i) (h₁ i) (by positivity)
  have hw (h : ι → ℕ) := reciprocalExponentWeight_nonneg hU₀ h
  apply Summable.of_nonneg_of_le _ _
    ((summable_reciprocalExponentWeight hU₀ hU₁).mul_right (∑ a ∈ L, reciprocalExponentWeight u a))
  · intro h
    apply mul_nonneg (hw h)
    exact sum_nonneg (fun a _ ↦ by split_ifs <;> first | exact reciprocalExponentWeight_nonneg hu a | exact le_rfl)
  · intro h
    apply mul_le_mul_of_nonneg_left _ (hw h)
    apply sum_le_sum
    intro a _
    split_ifs
    · exact le_rfl
    · exact reciprocalExponentWeight_nonneg hu a

/-- A comparison on every low slice gives the same comparison of total
reciprocal masses. -/
theorem mul_reciprocalExponentMass_le_of_digitSlices {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (h₁ : ∀ i, u i < 1) (k : ι → ℕ)
    {E F : Set (ι → ℕ)} (c : ℝ)
    (h : ∀ b, c * exponentDigitSliceMass u k E b ≤ exponentDigitSliceMass u k F b) :
    c * reciprocalExponentMass u E ≤ reciprocalExponentMass u F := by
  let w := reciprocalExponentWeight (fun i ↦ u i^(3^(k i)))
  have hS₁ := summable_weighted_exponentDigitSliceMass u hu h₁ k E
  have hS₂ := summable_weighted_exponentDigitSliceMass u hu h₁ k F
  rw [reciprocalExponentMass_eq_tsum_digitSlices u hu h₁ k E,
    reciprocalExponentMass_eq_tsum_digitSlices u hu h₁ k F]
  change c * (∑' b, w b * exponentDigitSliceMass u k E b) ≤
    ∑' b, w b * exponentDigitSliceMass u k F b
  rw [←hS₁.tsum_mul_left c]
  apply (hS₁.mul_left c).tsum_le_tsum _ hS₂
  intro b
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (h b)
    (reciprocalExponentWeight_nonneg (fun i ↦ pow_nonneg (hu i) _) b)

end GRHArticle.ProgressionFree
