/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Logic.Equiv.Prod
import OAI.Combinatorics.Progressions.Estimates.RelativeFiberSlicePatch
import OAI.Combinatorics.Progressions.Estimates.SmoothWindowChange

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerIntervalCenter {I : Type*} (lo hi : I → ℤ) : I → ℝ :=
  fun i => ((lo i : ℝ) + hi i) / 2

noncomputable def integerIntervalWidth {I : Type*} (lo hi : I → ℤ) : I → ℝ :=
  fun i => ((hi i - lo i : ℤ) : ℝ)

theorem integerIntervalWidth_pos {I : Type*} (lo hi : I → ℤ)
    (hlen : ∀ i, lo i < hi i) (i : I) : 0 < integerIntervalWidth lo hi i := by
  unfold integerIntervalWidth
  exact_mod_cast sub_pos.mpr (hlen i)

theorem integer_interval_box_inner {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (z : I → ℤ)
    (hz : z ∈ Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))) (i : I) :
    |(z i : ℝ) - integerIntervalCenter lo hi i| ≤ integerIntervalWidth lo hi i / 2 := by
  have h := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hz i)
  have hlo : (lo i : ℝ) ≤ z i := by exact_mod_cast h.1
  have hhi : (z i : ℝ) < hi i := by exact_mod_cast h.2
  simp only [integerIntervalCenter, integerIntervalWidth, Int.cast_sub]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem integer_interval_box_card {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) :
    ((Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))).card : ℝ) =
      ∏ i, integerIntervalWidth lo hi i := by
  rw [Fintype.card_piFinset, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Int.card_Ico]
  simp only [integerIntervalWidth]
  exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hlen i).le)

theorem smooth_interval_box_change {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ integerIntervalWidth lo hi i)
    (hZ : 0 < shiftedSmoothProductMass (integerIntervalCenter lo hi) (integerIntervalWidth lo hi)) :
    ∃ w : rectangularWeightIndices (integerIntervalCenter lo hi) (integerIntervalWidth lo hi) 1 → ℝ,
      (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      ∀ f : (I → ℤ) → ℝ,
        (𝔼 z ∈ Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)), f z) =
          (3 : ℝ) ^ Fintype.card I *
            (smoothSourceFiniteWeights (integerIntervalCenter lo hi) (integerIntervalWidth lo hi)
              (integerIntervalWidth_pos lo hi hlen) hZ).mean (fun z => w z * f z.val) := by
  have hp : (∏ i, integerIntervalWidth lo hi i) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => integerIntervalWidth_pos lo hi hlen i))
  obtain ⟨w, hw, he⟩ := smooth_window_change_of_measure (integerIntervalCenter lo hi)
    (integerIntervalWidth lo hi) (integerIntervalWidth_pos lo hi hlen) hZ hscale
    (Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)))
    (fun z hz i => integer_interval_box_inner lo hi z hz i)
  refine ⟨w, hw, fun f => ?_⟩
  have h := he f
  rw [integer_interval_box_card lo hi hlen, mul_div_cancel_right₀ _ hp] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteBoxPointsEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (S : I → Finset ℤ) : (∀ i, S i) ≃ Fintype.piFinset S where
  toFun x := ⟨fun i => (x i).val, Fintype.mem_piFinset.mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, Fintype.mem_piFinset.mp x.property i⟩
  left_inv x := by funext i; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem finiteBoxPoints_expect {I : Type*} [Fintype I] [DecidableEq I]
    (S : I → Finset ℤ) (f : (I → ℤ) → ℝ) :
    (𝔼 x : Fintype.piFinset S, f x.val) = 𝔼 x : (∀ i, S i), f (fun i => (x i).val) :=
  (Fintype.expect_equiv (finiteBoxPointsEquiv S)
    (fun x => f (fun i => (x i).val)) (fun x => f x.val) (fun _ => rfl)).symm

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def coordinateFiberParameters (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ)
    (i : I) : MvPolynomial {i // keep i} ℝ :=
  if hi : keep i then X ⟨i, hi⟩ else C (fixed ⟨i, hi⟩ : ℝ)

omit [Fintype I] [DecidableEq I] in
theorem coordinateFiberParameters_degree (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ)
    (i : I) : coordinateFiberParameters keep fixed i ∈ weightedSupportLE (fun _ => 1) 1 := by
  by_cases hi : keep i
  · simp only [coordinateFiberParameters, dite_eq_left hi]
    exact weightedSupportLE_X _ _
  · simp only [coordinateFiberParameters, dite_eq_right hi]
    exact weightedSupportLE_C _ _ _

noncomputable def PolynomialPatch.coordinateFiber {s d : ℕ} (A : PolynomialPatch I s d)
    (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ) : PolynomialPatch {i // keep i} s d :=
  A.reparam (coordinateFiberParameters keep fixed) (coordinateFiberParameters_degree keep fixed)

theorem PolynomialPatch.coordinateFiber_value {s d : ℕ} (A : PolynomialPatch I s d)
    (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ) (x : {i // keep i} → ℤ) :
    (A.coordinateFiber keep fixed).value (fun i => (x i : ℝ)) =
      A.value (fun i => ((finiteSplitPoint keep x fixed i : ℤ) : ℝ)) := by
  let _ : Fintype I := inferInstance
  let _ : DecidableEq I := inferInstance
  rw [coordinateFiber, reparam_value]
  congr 1
  funext i
  by_cases hi : keep i <;> simp [coordinateFiberParameters, finiteSplitPoint, hi]

theorem finiteBoxPoints_expect_finset (S : I → Finset ℤ) (f : (I → ℤ) → ℝ) :
    (𝔼 x ∈ Fintype.piFinset S, f x) = 𝔼 x : (∀ i, S i), f (fun i => (x i).val) := by
  simpa only [Finset.expect_eq_sum_div_card, Finset.card_univ, Finset.sum_coe_sort,
    Fintype.card_coe] using finiteBoxPoints_expect S f

theorem exists_integerBox_coordinate_fiber (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (keep : I → Prop) (f : (I → ℤ) → ℝ) {a : ℝ}
    (hmean : a ≤ 𝔼 x ∈ integerBox N, f x) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i, 0 ≤ fixed i ∧ fixed i < N i) ∧
      a ≤ 𝔼 x ∈ integerBox (fun i : {i // keep i} => N i), f (finiteSplitPoint keep x fixed) := by
  let X := fun i => Finset.Ico (0 : ℤ) (N i)
  let e := Equiv.piEquivPiSubtypeProd keep (fun i => X i)
  have hn (i : I) : Nonempty (X i) :=
    ⟨⟨0, Finset.mem_Ico.mpr ⟨le_rfl, by exact_mod_cast hN i⟩⟩⟩
  let : ∀ i, Nonempty (X i) := hn
  have hsplit : (𝔼 x : (∀ i, X i), f (fun i => (x i).val)) =
      𝔼 v : (∀ i : {i // ¬keep i}, X i),
        𝔼 u : (∀ i : {i // keep i}, X i),
          f (finiteSplitPoint keep (fun i => (u i).val) (fun i => (v i).val)) := by
    calc
      _ = 𝔼 uv : (∀ i : {i // keep i}, X i) × (∀ i : {i // ¬keep i}, X i),
          f (finiteSplitPoint keep (fun i => (uv.1 i).val) (fun i => (uv.2 i).val)) := by
        apply Fintype.expect_equiv e
        intro x
        change f (fun i => (x i).val) =
          f (finiteSplitPoint keep (fun i => (x i.val).val) (fun i => (x i.val).val))
        exact congrArg f (finiteSplitPoint_restrict keep (fun i => (x i).val)).symm
      _ = _ := by
        rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  have hfull : a ≤ 𝔼 x : (∀ i, X i), f (fun i => (x i).val) := by
    rw [← finiteBoxPoints_expect_finset X f]
    exact hmean
  rw [hsplit] at hfull
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hfull
  refine ⟨fun i => (v i).val, fun i => Finset.mem_Ico.mp (v i).property, ?_⟩
  rw [← finiteBoxPoints_expect_finset (fun i : {i // keep i} => X i)
    (fun x => f (finiteSplitPoint keep x (fun i => (v i).val)))] at hv
  exact hv

theorem PolynomialPatch.exists_coordinate_fiber_score {s d : ℕ} (A : PolynomialPatch I s d)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (keep : I → Prop)
    (score : (I → ℤ) → ℝ) {a : ℝ}
    (hmean : a ≤ 𝔼 x ∈ integerBox N, score x * A.value (fun i => (x i : ℝ))) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i, 0 ≤ fixed i ∧ fixed i < N i) ∧
      a ≤ 𝔼 x ∈ integerBox (fun i : {i // keep i} => N i),
        score (finiteSplitPoint keep x fixed) *
          (A.coordinateFiber keep fixed).value (fun i => (x i : ℝ)) := by
  obtain ⟨fixed, hfixed, hscore⟩ := exists_integerBox_coordinate_fiber N hN keep
    (fun x => score x * A.value (fun i => (x i : ℝ))) hmean
  exact ⟨fixed, hfixed, by simpa only [coordinateFiber_value] using hscore⟩

end Erdos3

end

end OAI
