/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.WeightedPatchReparam

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def localTentKernel (d q : ℕ) (hq : 8 ≤ q) : PatchKernel d where
  value x := max 0 (1 - (q : ℝ) / 2 * dist x 0)
  nonneg x := le_max_left _ _
  le_one x := max_le zero_le_one (by
    have h : 0 ≤ (q : ℝ) / 2 * dist x 0 := by positivity
    linarith)
  support x hx i := by
    have hqR : (8 : ℝ) ≤ q := by exact_mod_cast hq
    have hsmall : (q : ℝ) / 2 * dist x 0 < 1 := by
      by_contra h
      exact hx (max_eq_left (by linarith))
    have hcoord : |x i| ≤ dist x 0 := by
      simpa only [Real.dist_eq, Pi.zero_apply, sub_zero] using dist_le_pi_dist x 0 i
    have hdist : 0 ≤ dist x 0 := dist_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hqR hdist]
  lip := (q : ℝ≥0) / 2
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |max 0 (1 - (q : ℝ) / 2 * dist x 0) - max 0 (1 - (q : ℝ) / 2 * dist y 0)| ≤
      (q : ℝ) / 2 * dist x y
    calc
      _ ≤ |(1 - (q : ℝ) / 2 * dist x 0) - (1 - (q : ℝ) / 2 * dist y 0)| := by
        rw [max_comm 0 _, max_comm 0 _]
        exact abs_max_sub_max_le_abs _ _ _
      _ = (q : ℝ) / 2 * |dist x 0 - dist y 0| := by
        rw [show (1 - (q : ℝ) / 2 * dist x 0) - (1 - (q : ℝ) / 2 * dist y 0) =
          -((q : ℝ) / 2) * (dist x 0 - dist y 0) by ring,
          abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (q : ℝ) / 2)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_dist_sub_le x y 0) (by positivity)

theorem localTentKernel_ge_half {d q : ℕ} (hq : 8 ≤ q) (x : Fin d → ℝ)
    (hx : dist x 0 ≤ 1 / (q : ℝ)) : 1 / 2 ≤ (localTentKernel d q hq).value x := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmul : (q : ℝ) * dist x 0 ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ hqR).mp hx
  exact (by linarith : (1 : ℝ) / 2 ≤ 1 - (q : ℝ) / 2 * dist x 0).trans (le_max_right _ _)

theorem localTentKernel_support {d q : ℕ} (hq : 8 ≤ q) (x : Fin d → ℝ)
    (hx : (localTentKernel d q hq).value x ≠ 0) : dist x 0 ≤ 2 / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply (le_div_iff₀ hqR).mpr
  have hsmall : (q : ℝ) / 2 * dist x 0 < 1 := by
    by_contra h
    exact hx (max_eq_left (by linarith))
  nlinarith

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators NNReal

namespace WeightedParameterSlots

variable {σ : Type*} {p : σ → ℕ} {d n D E : ℕ}

theorem placementSubstitution_degree {w : Fin d → ℕ} {v : Fin n → ℕ}
    (f : Fin d → Fin n) (hweight : ∀ i, v (f i) = w i) (k : Fin n) (i : Fin d)
    (a : σ ⊕ Fin i.val) :
    PolynomialSlots.placementSubstitution f k i a ∈
      weightedSupportLE (weightedPatchVariableWeight p v k) (weightedPatchVariableWeight p w i a) := by
  cases a with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
    simp only [PolynomialSlots.placementSubstitution, Sum.elim_inr]
    split_ifs with h
    · have hX := weightedSupportLE_X (R := ℝ) (weightedPatchVariableWeight (σ := σ) p v k)
        (Sum.inr (⟨(f (earlierSlot i j)).val, h⟩ : Fin k.val))
      change _ ∈ weightedSupportLE _ (v (f (earlierSlot i j))) at hX
      rw [hweight] at hX
      exact hX
    · exact (weightedSupportLE _ _).zero_mem

noncomputable def placeCenter {w : Fin d → ℕ} (A : WeightedParameterSlots σ p d w)
    (f : Fin d → Fin n) (k : Fin n) (i : Fin d) :
    MvPolynomial (σ ⊕ Fin k.val) ℝ := aeval (PolynomialSlots.placementSubstitution f k i) (A.center i)

theorem placeCenter_degree {w : Fin d → ℕ} {v : Fin n → ℕ}
    (A : WeightedParameterSlots σ p d w) (f : Fin d → Fin n)
    (hweight : ∀ i, v (f i) = w i) (k : Fin n) (i : Fin d) :
    A.placeCenter f k i ∈ weightedSupportLE (weightedPatchVariableWeight p v k) (w i) :=
  weightedSupportLE_aeval _ _ _ (placementSubstitution_degree f hweight k i) (A.degree i)

theorem placeCenter_eval {w : Fin d → ℕ} (A : WeightedParameterSlots σ p d w)
    (f : Fin d → Fin n) (hf : StrictMono f) (i : Fin d) (t : σ → ℝ) (x : Fin n → ℝ) :
    aeval (Sum.elim t (fun j => x (earlierSlot (f i) j))) (A.placeCenter f (f i) i) =
      (A.slots t).center (fun j => x (f j)) i := by
  simp only [placeCenter, MvPolynomial.comp_aeval_apply, slots]
  apply congrArg (fun g : σ ⊕ Fin i.val → ℝ => aeval g (A.center i))
  funext a
  cases a with
  | inl a => simp [PolynomialSlots.placementSubstitution]
  | inr j =>
    have h : (f (earlierSlot i j)).val < (f i).val :=
      hf (show earlierSlot i j < i from j.isLt)
    simp only [PolynomialSlots.placementSubstitution, Sum.elim_inr, dite_eq_left h, aeval_X]
    rfl

noncomputable def interleave {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : WeightedParameterSlots σ p D w) (B : WeightedParameterSlots σ p E v) (I : SlotInterleaving D E) :
    WeightedParameterSlots σ p (D + E) (I.fill w v) where
  center k := Fin.addCases (A.placeCenter I.left k) (B.placeCenter I.right k) (I.perm k)
  degree k := by
    change Fin.addCases (A.placeCenter I.left k) (B.placeCenter I.right k) (I.perm k) ∈
      weightedSupportLE (weightedPatchVariableWeight p (I.fill w v) k) (Fin.append w v (I.perm k))
    generalize I.perm k = z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) z
    · simpa only [Fin.addCases_left, Fin.append_left] using
        A.placeCenter_degree I.left (fun j => I.fill_left w v j) k i
    · simpa only [Fin.addCases_right, Fin.append_right] using
        B.placeCenter_degree I.right (fun j => I.fill_right w v j) k i

@[simp] theorem interleave_center_left {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : WeightedParameterSlots σ p D w) (B : WeightedParameterSlots σ p E v) (I : SlotInterleaving D E)
    (i : Fin D) : (A.interleave B I).center (I.left i) = A.placeCenter I.left (I.left i) i := by
  simp [interleave, SlotInterleaving.left]

@[simp] theorem interleave_center_right {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : WeightedParameterSlots σ p D w) (B : WeightedParameterSlots σ p E v) (I : SlotInterleaving D E)
    (i : Fin E) : (A.interleave B I).center (I.right i) = B.placeCenter I.right (I.right i) i := by
  simp [interleave, SlotInterleaving.right]

theorem interleave_slots {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : WeightedParameterSlots σ p D w) (B : WeightedParameterSlots σ p E v) (I : SlotInterleaving D E)
    (t : σ → ℝ) : (A.interleave B I).slots t = (A.slots t).interleave (B.slots t) I := by
  apply TriangularSlots.ext
  intro x k
  apply I.cases (p := fun k => ((A.interleave B I).slots t).center x k =
    ((A.slots t).interleave (B.slots t) I).center x k) _ _ k
  · intro i
    change aeval _ ((A.interleave B I).center (I.left i)) = _
    rw [interleave_center_left]
    simpa only [TriangularSlots.interleave, SlotInterleaving.fill_left] using
      A.placeCenter_eval I.left I.left_strictMono i t x
  · intro i
    change aeval _ ((A.interleave B I).center (I.right i)) = _
    rw [interleave_center_right]
    simpa only [TriangularSlots.interleave, SlotInterleaving.fill_right] using
      B.placeCenter_eval I.right I.right_strictMono i t x

end WeightedParameterSlots

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s D E : ℕ}

noncomputable def product (A : WeightedParameterPatch σ p s D) (B : WeightedParameterPatch σ p s E) :
    WeightedParameterPatch σ p s (D + E) :=
  let I := SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono
  { weight := I.fill A.weight B.weight
    weight_pos := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_pos i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_pos i)
    weight_le := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_le i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_le i)
    weight_mono := SlotInterleaving.sorted_weight_mono _ _ _ _
    form := A.form.interleave B.form I
    kernel := A.kernel.product B.kernel I }

@[simp] theorem product_lip (A : WeightedParameterPatch σ p s D) (B : WeightedParameterPatch σ p s E) :
    (A.product B).kernel.lip = A.kernel.lip + B.kernel.lip := rfl

@[simp] theorem product_value (A : WeightedParameterPatch σ p s D) (B : WeightedParameterPatch σ p s E)
    (t : σ → ℝ) : (A.product B).value t = A.value t * B.value t := by
  let I := SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono
  change ((A.form.interleave B.form I).slots t).patchValue (A.kernel.product B.kernel I) = _
  rw [WeightedParameterSlots.interleave_slots, TriangularSlots.interleave_patchValue]
  rfl

def castRank {d e : ℕ} (P : WeightedParameterPatch σ p s d) (h : d = e) :
    WeightedParameterPatch σ p s e := h ▸ P

@[simp] theorem castRank_value {d e : ℕ} (P : WeightedParameterPatch σ p s d)
    (h : d = e) (t : σ → ℝ) : (P.castRank h).value t = P.value t := by
  subst e
  rfl

@[simp] theorem castRank_kernel_lip {d e : ℕ} (P : WeightedParameterPatch σ p s d)
    (h : d = e) : (P.castRank h).kernel.lip = P.kernel.lip := by
  subst e
  rfl

noncomputable def unitRank (σ : Type*) (p : σ → ℕ) (s d : ℕ) (hs : 1 ≤ s) :
    WeightedParameterPatch σ p s d where
  weight := fun _ => 1
  weight_pos := fun _ => le_rfl
  weight_le := fun _ => hs
  weight_mono := fun _ _ _ => le_rfl
  form := { center := fun _ => 0, degree := fun _ => Submodule.zero_mem _ }
  kernel := localTentKernel d 8 le_rfl

@[simp] theorem unitRank_value {σ : Type*} {p : σ → ℕ} {s d : ℕ} (hs : 1 ≤ s) (t : σ → ℝ) :
    (unitRank σ p s d hs).value t = 1 := by
  change ((unitRank σ p s d hs).form.slots t).patchValue (localTentKernel d 8 le_rfl) = 1
  have hres : ((unitRank σ p s d hs).form.slots t).residual 0 = 0 := by
    ext i
    simp [unitRank, WeightedParameterSlots.slots, TriangularSlots.residual]
  rw [TriangularSlots.patchValue_eq_at_residual (b := 0)]
  · rw [hres]
    norm_num [localTentKernel]
  · intro i
    rw [hres]
    norm_num

@[simp] theorem unitRank_lip {σ : Type*} {p : σ → ℕ} {s d : ℕ} (hs : 1 ≤ s) :
    (unitRank σ p s d hs).kernel.lip = 4 := by
  norm_num [unitRank, localTentKernel]

noncomputable def padRank {σ : Type*} {p : σ → ℕ} {s d D : ℕ}
    (P : WeightedParameterPatch σ p s d) (hs : 1 ≤ s) (hd : d ≤ D) :
    WeightedParameterPatch σ p s D :=
  (P.product (unitRank σ p s (D-d) hs)).castRank (Nat.add_sub_of_le hd)

@[simp] theorem padRank_value {σ : Type*} {p : σ → ℕ} {s d D : ℕ}
    (P : WeightedParameterPatch σ p s d) (hs : 1 ≤ s) (hd : d ≤ D) (t : σ → ℝ) :
    (P.padRank hs hd).value t = P.value t := by
  simp only [padRank, castRank_value, product_value, unitRank_value, mul_one]

@[simp] theorem padRank_lip {σ : Type*} {p : σ → ℕ} {s d D : ℕ}
    (P : WeightedParameterPatch σ p s d) (hs : 1 ≤ s) (hd : d ≤ D) :
    (P.padRank hs hd).kernel.lip = P.kernel.lip + 4 := by
  simp only [padRank, castRank_kernel_lip, product_lip, unitRank_lip]

theorem padRank_score {σ Ω : Type*} {p : σ → ℕ} [Fintype Ω] {s d D : ℕ}
    (P : WeightedParameterPatch σ p s d) (hs : 1 ≤ s) (hd : d ≤ D)
    (t : Ω → σ → ℝ) (f : Ω → ℝ) (a : ℝ) :
    (𝔼 x, (f x - a) * (P.padRank hs hd).value (t x)) =
      𝔼 x, (f x - a) * P.value (t x) := by
  simp only [padRank_value]

noncomputable def padRankFamily {σ H : Type*} {p : σ → ℕ} {s D : ℕ}
    (d : H → ℕ) (P : ∀ h, WeightedParameterPatch σ p s (d h))
    (hs : 1 ≤ s) (hd : ∀ h, d h ≤ D) : H → WeightedParameterPatch σ p s D :=
  fun h => (P h).padRank hs (hd h)

@[simp] theorem padRankFamily_value {σ H : Type*} {p : σ → ℕ} {s D : ℕ}
    (d : H → ℕ) (P : ∀ h, WeightedParameterPatch σ p s (d h))
    (hs : 1 ≤ s) (hd : ∀ h, d h ≤ D) (h : H) (t : σ → ℝ) :
    (padRankFamily d P hs hd h).value t = (P h).value t :=
  padRank_value _ _ _ _

theorem padRankFamily_lip_bound {σ H : Type*} {p : σ → ℕ} {s D : ℕ}
    (d : H → ℕ) (P : ∀ h, WeightedParameterPatch σ p s (d h))
    (hs : 1 ≤ s) (hd : ∀ h, d h ≤ D) {L : ℝ≥0}
    (hL : ∀ h, (P h).kernel.lip ≤ L) (h : H) :
    (padRankFamily d P hs hd h).kernel.lip ≤ L + 4 := by
  exact (padRank_lip (P h) hs (hd h)).le.trans (add_le_add (hL h) le_rfl)

end WeightedParameterPatch
end Erdos3

end

end OAI
