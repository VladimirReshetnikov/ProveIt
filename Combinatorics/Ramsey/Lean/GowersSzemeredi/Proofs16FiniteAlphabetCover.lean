import GowersSzemeredi.ProofInfrastructure

/-! Finite-alphabet obstructions to covering a function by affine graphs.
Each nonconstant affine graph hits a given alphabet at most once per
symbol; constant graphs are charged to their actual fibre masses. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem finiteAlphabet_nonconstant_affine_agreement {F : Type*} [Field F] [DecidableEq F]
    (T S : Finset F) (f : F → F) (hf : ∀ x ∈ T, f x ∈ S) (a b : F) (ha : a ≠ 0) :
    (T.filter (fun x => f x = a * x + b)).card ≤ S.card := by
  let U := T.filter (fun x => f x = a * x + b)
  have hi : Function.Injective (fun x : F => a * x + b) := by
    intro x y h
    exact mul_left_cancel₀ ha (add_right_cancel h)
  have hs : U.image (fun x => a * x + b) ⊆ S := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hx' := Finset.mem_filter.mp hx
    rw [← hx'.2]
    exact hf x hx'.1
  calc
    _ = (U.image (fun x => a * x + b)).card := (Finset.card_image_of_injective _ hi).symm
    _ ≤ _ := Finset.card_le_card hs

theorem finiteAlphabet_affine_union_card {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (T S : Finset F) (f : F → F) (hf : ∀ x ∈ T, f x ∈ S)
    (J : Finset I) (a b : I → F) :
    (T.filter (fun x => ∃ i ∈ J, f x = a i * x + b i)).card ≤
      ∑ i ∈ J, if a i = 0 then (T.filter (fun x => f x = b i)).card else S.card := by
  classical
  have he : T.filter (fun x => ∃ i ∈ J, f x = a i * x + b i) =
      J.biUnion (fun i => T.filter (fun x => f x = a i * x + b i)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    aesop
  rw [he]
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i hi => ?_)
  by_cases ha : a i = 0
  · simp [ha]
  · rw [if_neg ha]
    exact finiteAlphabet_nonconstant_affine_agreement T S f hf (a i) (b i) ha

theorem finiteAlphabet_affine_union_balanced {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (T S : Finset F) (f : F → F) (hf : ∀ x ∈ T, f x ∈ S)
    (J : Finset I) (a b : I → F) (beta : Real) (hbeta : 0 ≤ beta)
    (hbalanced : ∀ c : F, ((T.filter (fun x => f x = c)).card : Real) ≤ beta * T.card) :
    ((T.filter (fun x => ∃ i ∈ J, f x = a i * x + b i)).card : Real) ≤
      J.card * (beta * T.card + S.card) := by
  have hc := finiteAlphabet_affine_union_card T S f hf J a b
  have hc' : ((T.filter (fun x => ∃ i ∈ J, f x = a i * x + b i)).card : Real) ≤
      ∑ i ∈ J, if a i = 0 then ((T.filter (fun x => f x = b i)).card : Real) else S.card := by
    exact_mod_cast hc
  calc
    _ ≤ ∑ i ∈ J, if a i = 0 then ((T.filter (fun x => f x = b i)).card : Real) else S.card := hc'
    _ ≤ ∑ _i ∈ J, (beta * T.card + S.card) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases ha : a i = 0
      · rw [if_pos ha]
        have h := hbalanced (b i)
        have hs : (0 : Real) ≤ S.card := Nat.cast_nonneg _
        linarith only [h, hs]
      · rw [if_neg ha]
        have ht := mul_nonneg hbeta (Nat.cast_nonneg T.card)
        linarith only [ht]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem finiteAlphabet_affine_cover_bound {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (T S H : Finset F) (f : F → F) (hf : ∀ x ∈ T, f x ∈ S)
    (J : Finset I) (a b : I → F) (beta : Real) (hbeta : 0 ≤ beta)
    (hbalanced : ∀ c : F, ((T.filter (fun x => f x = c)).card : Real) ≤ beta * T.card)
    (hHT : H ⊆ T) (hcover : ∀ x ∈ H, ∃ i ∈ J, f x = a i * x + b i) :
    (H.card : Real) ≤ J.card * (beta * T.card + S.card) := by
  have hsub : H ⊆ T.filter (fun x => ∃ i ∈ J, f x = a i * x + b i) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hHT hx, hcover x hx⟩
  have hcard : (H.card : Real) ≤ (T.filter (fun x => ∃ i ∈ J, f x = a i * x + b i)).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (finiteAlphabet_affine_union_balanced T S f hf J a b beta hbeta hbalanced)

end LeanProofs.GowersSzemeredi
