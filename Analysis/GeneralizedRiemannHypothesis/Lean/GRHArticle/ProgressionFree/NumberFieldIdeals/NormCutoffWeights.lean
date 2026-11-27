import GRHArticle.ProgressionFree.IntegerPrefixTransfer
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealPurePowerExchange

/-!
# Reciprocal weights from ideal norm cutoffs

The weight of an ideal is its contribution to every norm interval beginning
at its absolute norm. Changing the order of summation retains the
multiplicity of ideals with the same norm.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open Filter Topology NumberField Ideal Finset
open scoped BigOperators nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

private noncomputable def normCutoffKernel (n k : ℕ) : ℝ :=
  if n ≤ k then integerPrefixStepWeight k else 0

/-- Reuse the singleton case of the integer prefix-weight identity for each
ideal's norm. -/
private theorem hasSum_normCutoffKernel {n : ℕ} (hn : 0 < n) :
    HasSum (normCutoffKernel n) (n : ℝ)⁻¹ := by
  classical
  let A : Set ℕ := {n}
  letI := (Set.finite_singleton n).fintype
  have hpos' : ∀ a ∈ A, 0 < a := by
    intro a ha
    have h : a = n := ha
    simpa [h] using hn
  have hsum := integerPrefix_hasSum_stepWeight A hpos' (hasSum_fintype _).summable
  have hweight : (∑' a : A, (a.val : ℝ)⁻¹) = (n : ℝ)⁻¹ := by
    rw [_root_.tsum_subtype A (fun a : ℕ ↦ (a : ℝ)⁻¹)]
    rw [tsum_eq_single n]
    · simp [A]
    · intro b hb
      simp [A,hb]
  rw [hweight] at hsum
  refine hsum.congr_fun ?_
  intro k
  by_cases hk : n ≤ k
  · have hslice : integerPrefixSlice A k = {n} := by
      ext m
      simp only [integerPrefixSlice, integerPrefix, mem_filter, mem_Icc, mem_singleton]
      change (1 ≤ m ∧ m ≤ k) ∧ m = n ↔ m = n
      constructor
      · exact And.right
      · rintro rfl
        exact ⟨⟨hn,hk⟩,rfl⟩
    simp [normCutoffKernel, hk, hslice]
  · have hslice : integerPrefixSlice A k = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro m hm
      have hm' : (1 ≤ m ∧ m ≤ k) ∧ m = n := by
        simpa only [integerPrefixSlice, integerPrefix, mem_filter, mem_Icc, A, Set.mem_singleton_iff] using hm
      exact hk (hm'.2 ▸ hm'.1.2)
    simp [normCutoffKernel, hk, hslice]

private theorem normCutoffKernel_column (A : Set (Ideal (𝓞 K))⁰) (k : ℕ) :
    (∑' I : A, normCutoffKernel (absNorm I.val.val) k) =
      (countUpTo A (k : ℝ) : ℝ) * integerPrefixStepWeight k := by
  classical
  let T : Set A := {I | absNorm I.val.val ≤ k}
  let e : T ≃ idealNormCutoff A k :=
    { toFun := fun I ↦ ⟨I.val.val,I.val.property,I.property⟩
      invFun := fun I ↦ ⟨⟨I.val,I.property.1⟩,I.property.2⟩
      left_inv := by intro I; exact Subtype.ext (Subtype.ext rfl)
      right_inv := by intro I; exact Subtype.ext rfl }
  letI := (idealNormCutoff_finite A k).fintype
  letI := Fintype.ofEquiv (idealNormCutoff A k) e.symm
  have hc : Fintype.card T = countUpTo A (k : ℝ) := by
    rw [Fintype.card_congr e, countUpTo_nat_eq_ncard, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  calc
    _ = ∑' I : A, T.indicator (fun _ ↦ integerPrefixStepWeight k) I := by
      apply tsum_congr
      intro I
      by_cases h : absNorm I.val.val ≤ k <;> simp [normCutoffKernel, T, h]
    _ = ∑' _ : T, integerPrefixStepWeight k := (_root_.tsum_subtype T _).symm
    _ = _ := by rw [tsum_fintype, sum_const, card_univ, nsmul_eq_mul, hc]

/-- The step-weighted ideal counting series equals the reciprocal-norm series.
The formula applies to arbitrary subsets with summable reciprocal norm. -/
theorem hasSum_countUpTo_stepWeight (A : Set (Ideal (𝓞 K))⁰)
    (hs : Summable (fun I : A ↦ (absNorm I.val.val : ℝ)⁻¹)) :
    HasSum (fun k : ℕ ↦ (countUpTo A (k : ℝ) : ℝ) * integerPrefixStepWeight k)
      (∑' I : A, (absNorm I.val.val : ℝ)⁻¹) := by
  let f (I : A) (k : ℕ) := normCutoffKernel (absNorm I.val.val) k
  have hnonneg : 0 ≤ Function.uncurry f := by
    intro x
    unfold Function.uncurry f normCutoffKernel
    split
    · unfold integerPrefixStepWeight
      positivity
    · exact le_rfl
  have hrow (I : A) := hasSum_normCutoffKernel (absNorm_pos_of_nonZeroDivisors I.val)
  have hprod : Summable (Function.uncurry f) := by
    apply (summable_prod_of_nonneg hnonneg).mpr
    refine ⟨fun I ↦ (hrow I).summable, ?_⟩
    exact hs.congr fun I ↦ (hrow I).tsum_eq.symm
  have hswap := hprod.prod_symm
  have houter : Summable (fun k ↦ ∑' I : A, f I k) :=
    ((summable_prod_of_nonneg (f := fun q : ℕ × A ↦ f q.2 q.1) (fun q ↦ hnonneg q.swap)).mp hswap).2
  have he := hprod.tsum_comm' (fun I ↦ (hrow I).summable) hswap.prod_factor
  rw [tsum_congr fun I ↦ (hrow I).tsum_eq] at he
  exact (he ▸ houter.hasSum).congr_fun fun k ↦ (normCutoffKernel_column A k).symm

end GRHArticle.ProgressionFree.NumberFieldIdeals
