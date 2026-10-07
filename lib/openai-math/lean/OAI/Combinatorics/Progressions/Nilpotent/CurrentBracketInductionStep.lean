/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CurrentLayerPreservation

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

section General

variable {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]

def BasisHomogeneousBrackets (b : Basis ι R L) (w : ι → ℕ) : Prop :=
  ∀ i j k, w k ≠ w i + w j → b.repr ⁅b i, b j⁆ k = 0

theorem BasisHomogeneousBrackets.lie_mem_span (b : Basis ι R L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) {i j : ℕ} {x y : L}
    (hx : x ∈ Submodule.span R (b '' {k | w k = i}))
    (hy : y ∈ Submodule.span R (b '' {k | w k = j})) :
    ⁅x, y⁆ ∈ Submodule.span R (b '' {k | w k = i + j}) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    change w a = i at ha
    change w c = j at hc
    apply (basis_mem_span_image_iff b _ _).mpr
    intro k hk
    change w k ≠ i + j at hk
    exact hb a c k (by simpa only [ha, hc] using hk)
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left r x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ r h
  | smul_right r x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ r h

theorem BasisHomogeneousBrackets.projection_lie (b : Basis ι R L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) {i j : ℕ} {x y : L}
    (hx : basisGradeProjection b w i x = x) (hy : basisGradeProjection b w j y = y) :
    basisGradeProjection b w (i + j) ⁅x, y⁆ = ⁅x, y⁆ := by
  apply basisCoordinateProjection_eq_self
  apply hb.lie_mem_span b w
  · rw [← hx]
    exact basisCoordinateProjection_mem_span b _ _
  · rw [← hy]
    exact basisCoordinateProjection_mem_span b _ _

end General

theorem BasisHomogeneousBrackets.baseChange {L ι : Type*} [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (w : ι → ℕ) (hb : BasisHomogeneousBrackets b w) :
    BasisHomogeneousBrackets (b.baseChange ℝ) w := by
  intro i j k hk
  rw [Basis.baseChange_apply, Basis.baseChange_apply,
    LieAlgebra.ExtendScalars.bracket_tmul, one_mul, Basis.baseChange_repr_tmul, hb i j k hk]
  exact zero_smul ℚ (1 : ℝ)

namespace NilpotentLieFiltration

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem associatedGradedBasis_homogeneous_brackets :
    BasisHomogeneousBrackets (F.associatedGradedBasis b w hlayers) w := by
  intro i j k hk
  rw [F.associatedGradedBasis_bracket b w hlayers, ite_eq_right (Ne.symm hk)]

theorem realAssociatedGradedBasis_homogeneous_brackets :
    BasisHomogeneousBrackets ((F.associatedGradedBasis b w hlayers).baseChange ℝ) w :=
  (F.associatedGradedBasis_homogeneous_brackets b w hlayers).baseChange _ _

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module

variable {σ : Type*} [Fintype σ]

@[simp] theorem weightedBasis_inl_base [DecidableEq σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (i : σ) : (weightedBasis w d hw (Sum.inl i)).val.base = Pi.single i 1 := by
  classical
  unfold weightedBasis
  erw [Basis.map_apply]
  rw [Basis.prod_apply]
  simp [weightedCoordinatesEquiv]
  rfl

@[simp] theorem weightedBasis_inl_polynomial (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (i : σ) :
    (weightedBasis w d hw (Sum.inl i)).val.polynomial = 0 := by
  unfold weightedBasis
  erw [Basis.map_apply]
  rw [Basis.prod_apply]
  simp [weightedCoordinatesEquiv]
  rfl

@[simp] theorem weightedBasis_inr_base (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (weightedBasis w d hw (Sum.inr a)).val.base = 0 := by
  unfold weightedBasis
  erw [Basis.map_apply]
  rw [Basis.prod_apply]
  simp [weightedCoordinatesEquiv]
  rfl

@[simp] theorem weightedBasis_inr_polynomial (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (weightedBasis w d hw (Sum.inr a)).val.polynomial = monomial a.val 1 := by
  classical
  apply MvPolynomial.ext
  intro t
  by_cases ht : Finsupp.weight w t < d
  · rw [← weightedBasis_repr_inr w d hw _ ⟨t, ht⟩]
    simp [Basis.repr_self, Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]
  · have hcoeff : (weightedBasis w d hw (Sum.inr a)).val.polynomial.coeff t = 0 := by
      by_contra hn
      have hh := (weightedBasis w d hw (Sum.inr a)).property.2 (mem_support_iff.mpr hn)
      change Finsupp.weight w t + 1 ≤ d at hh
      omega
    rw [hcoeff, coeff_monomial]
    have hne : a.val ≠ t := by
      intro he
      exact ht (he ▸ a.property)
    simp [hne]

private theorem single_direction_derivative [DecidableEq σ] (i : σ)
    (P : MvPolynomial σ ℚ) : scalarDirectionalDerivative (Pi.single i 1) P = pderiv i P := by
  classical
  simp [scalarDirectionalDerivative_apply, Pi.single_apply]

omit [Fintype σ] in
private theorem coeff_pderiv_monomial_grade (w : σ → ℕ) (d : ℕ)
    (i : σ) (a c : {a : σ →₀ ℕ | Finsupp.weight w a < d})
    (h : d - Finsupp.weight w c.val ≠ w i + (d - Finsupp.weight w a.val)) :
    (pderiv i (monomial a.val (1 : ℚ))).coeff c.val = 0 := by
  classical
  have hne : a.val ≠ c.val + Finsupp.single i 1 := by
    intro he
    have hh := congrArg (Finsupp.weight w) he
    simp only [map_add, Finsupp.weight_single, one_smul] at hh
    have ha : Finsupp.weight w a.val < d := a.property
    have hc : Finsupp.weight w c.val < d := c.property
    omega
  rw [coeff_pderiv, coeff_monomial, ite_eq_right hne, zero_mul]

theorem weightedBasis_homogeneous_brackets (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) :
    BasisHomogeneousBrackets (weightedBasis w d hw) (weightedBasisGrade w d) := by
  classical
  intro i j k hk
  cases k with
  | inl k =>
      rw [weightedBasis_repr_inl]
      rfl
  | inr c =>
      rw [weightedBasis_repr_inr]
      change (scalarDirectionalDerivative (weightedBasis w d hw i).val.base
        (weightedBasis w d hw j).val.polynomial -
        scalarDirectionalDerivative (weightedBasis w d hw j).val.base
          (weightedBasis w d hw i).val.polynomial).coeff c.val = 0
      cases i with
      | inl i =>
          cases j with
          | inl j => simp
          | inr a =>
              simp only [weightedBasis_inl_base, weightedBasis_inr_polynomial,
                weightedBasis_inr_base, weightedBasis_inl_polynomial,
                scalarDirectionalDerivative_direction_zero, sub_zero,
                single_direction_derivative]
              exact coeff_pderiv_monomial_grade w d i a c hk
      | inr a =>
          cases j with
          | inl i =>
              simp only [weightedBasis_inl_base, weightedBasis_inr_polynomial,
                weightedBasis_inr_base, weightedBasis_inl_polynomial,
                scalarDirectionalDerivative_direction_zero, zero_sub,
                single_direction_derivative, coeff_neg, neg_eq_zero]
              exact coeff_pderiv_monomial_grade w d i a c (by
                simpa only [weightedBasisGrade_inl, weightedBasisGrade_inr, Nat.add_comm] using hk)
          | inr b => simp

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem real_bracket_induction_step (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (hK : ∀ k ∈ K, basisGradeProjection (b.baseChange ℝ) w 1 k = k)
    {j : ℕ} (hj : 2 ≤ j) (g a c : F.realification.Group)
    (hg : g.coord ∈ U) (haU : a.coord ∈ U) (hcU : c.coord ∈ U)
    (ha : basisGradeProjection (b.baseChange ℝ) w (j - 1) a.coord = a.coord)
    (hc : basisGradeProjection (b.baseChange ℝ) w (j - 1) c.coord = c.coord)
    (S R : K → ℝ ⊗[ℚ] L) (hSR : ∀ k, S k = dualAdjoint g (R k))
    (hR : ∀ k, R k - k.val ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ k : K,
      ⁅basisGradeProjection (b.baseChange ℝ) w d g.coord, k.val⁆ ∈ V)
    (hleft : ∀ k, S k - k.val - ⁅a.coord, k.val⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hright : ∀ k, R k - k.val + ⁅c.coord, k.val⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let g' := a⁻¹ * g * c⁻¹
    let S' := fun k => dualAdjoint a⁻¹ (S k)
    let R' := fun k => dualAdjoint c (R k)
    a * g' * c = g ∧ g'.coord ∈ U ∧
      (∀ d < j - 1, basisGradeProjection (b.baseChange ℝ) w d g'.coord =
        basisGradeProjection (b.baseChange ℝ) w d g.coord) ∧
      (∀ d < j, ∀ k : K, ⁅basisGradeProjection (b.baseChange ℝ) w d g'.coord, k.val⁆ ∈ V) ∧
      (∀ k, S' k = dualAdjoint g' (R' k)) ∧
      ∀ k, S' k - k.val ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        R' k - k.val ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        ⁅g'.coord, k.val⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro g' S' R'
  have hW (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ V.restrictScalars ℚ ⊔ F.realification.layer d ↔
        x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  let p := basisGradeProjection (b.baseChange ℝ) w (j - 1) g.coord
  have hstep : j - 1 + 2 = j + 1 := by omega
  have hp : p ∈ F.realification.layer (j - 1) :=
    F.realGradeProjection_mem_layer b w hlayers (j - 1) g.coord
  have hal : a.coord ∈ F.realification.layer (j - 1) := by
    simpa only [ha] using F.realGradeProjection_mem_layer b w hlayers (j - 1) a.coord
  have hcl : c.coord ∈ F.realification.layer (j - 1) := by
    simpa only [hc] using F.realGradeProjection_mem_layer b w hlayers (j - 1) c.coord
  have hkl (k : K) : k.val ∈ F.realification.layer 1 := by
    rw [F.realification.one_eq_top]
    trivial
  have hrem (k : K) : ⁅g.coord - p, k.val⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    have h := F.real_current_bracket_remainder b w hlayers V (j - 1) g.coord k.val (hkl k)
      (fun d hd => hlower d hd k)
    simpa only [hstep] using h
  have hnorm := F.realification.current_layer_normalization hs U (V.restrictScalars ℚ)
    hUV hj g a c hg haU hcU hal hcl S R (fun k => k.val) p hp hSR
    (fun k => (hW j _).mpr (hR k)) (fun k => (hW (j + 1) _).mpr (hrem k))
    (fun k => (hW (j + 1) _).mpr (hleft k)) (fun k => (hW (j + 1) _).mpr (hright k))
  obtain ⟨hprod, hg', _, _, hSR', hcurrent⟩ := hnorm
  have hbelow := F.real_correction_preserves_grades_below b w hlayers (j - 1) a g c hal hcl
  have hgrade : basisGradeProjection (b.baseChange ℝ) w (j - 1) g'.coord = p - a.coord - c.coord := by
    have h := F.real_correction_current_grade b w hlayers (j - 1) a g c hal hcl
    simpa only [ha, hc] using h
  have hcur (k : K) : ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) g'.coord, k.val⁆ ∈ V := by
    apply F.real_mem_of_homogeneous_mem_sup_next b w hlayers V hV j
    · have h := (hgraded.baseChange b w).projection_lie (b.baseChange ℝ) w
        (basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j - 1} g'.coord)
        (hK k.val k.property)
      simp only [Nat.sub_add_cancel (by omega : 1 ≤ j)] at h
      exact h
    · rw [hgrade]
      exact (hW (j + 1) _).mp (hcurrent k).2.2
  have hall (d : ℕ) (hd : d < j) (k : K) :
      ⁅basisGradeProjection (b.baseChange ℝ) w d g'.coord, k.val⁆ ∈ V := by
    rcases lt_or_eq_of_le (show d ≤ j - 1 by omega) with hlt | rfl
    · rw [hbelow d hlt]
      exact hlower d hlt k
    · exact hcur k
  refine ⟨hprod, hg', hbelow, hall, hSR', fun k =>
    ⟨(hW (j + 1) _).mp (hcurrent k).1, (hW (j + 1) _).mp (hcurrent k).2.1, ?_⟩⟩
  have hrem' := F.real_current_bracket_remainder b w hlayers V (j - 1) g'.coord k.val (hkl k)
    (fun d hd => hall d (by omega) k)
  rw [hstep] at hrem'
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem hrem'
    (Submodule.mem_sup_left (hcur k))
  simpa only [sub_lie, sub_add_cancel] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
