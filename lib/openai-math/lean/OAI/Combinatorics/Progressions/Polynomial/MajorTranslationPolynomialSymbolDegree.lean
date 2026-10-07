/- Modified for ProveIt: Use MvPolynomial coefficient lemmas explicitly on Lean 4.32; statements unchanged. -/
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import OAI.Combinatorics.Progressions.Estimates.WeightedAxisScaling

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem sumExponent_injective (β : τ →₀ ℕ) :
    Function.Injective (fun α : σ →₀ ℕ => α.sumElim β) := by
  intro α γ h
  ext i
  exact congrArg (fun a : σ ⊕ τ →₀ ℕ => a (Sum.inl i)) h

noncomputable def polynomialSlotCoefficient (β : τ →₀ ℕ) :
    MvPolynomial (σ ⊕ τ) R →ₗ[R] MvPolynomial σ R :=
  (MvPolynomial.basisMonomials σ R).repr.symm.toLinearMap.comp
    ((Finsupp.lcomapDomain (fun α : σ →₀ ℕ => α.sumElim β) (sumExponent_injective β)).comp
      (MvPolynomial.basisMonomials (σ ⊕ τ) R).repr.toLinearMap)

theorem polynomialSlotCoefficient_coeff (β : τ →₀ ℕ) (α : σ →₀ ℕ)
    (P : MvPolynomial (σ ⊕ τ) R) :
    (polynomialSlotCoefficient β P).coeff α = P.coeff (α.sumElim β) := by
  change ((MvPolynomial.basisMonomials σ R).repr
    ((MvPolynomial.basisMonomials σ R).repr.symm _)) α = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem sumExponent_weight (v : σ → ℕ) (w : τ → ℕ) (α : σ →₀ ℕ) (β : τ →₀ ℕ) :
    Finsupp.weight (Sum.elim v w) (α.sumElim β) =
      Finsupp.weight v α + Finsupp.weight w β := by
  simp only [Finsupp.weight_apply, Finsupp.sum_sumElim, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr]

theorem polynomialSlotCoefficient_degree (v : σ → ℕ) (w : τ → ℕ)
    {n : ℕ} {P : MvPolynomial (σ ⊕ τ) R}
    (hP : P ∈ weightedSupportLE (Sum.elim v w) n) (β : τ →₀ ℕ) :
    polynomialSlotCoefficient β P ∈ weightedSupportLE v (n - Finsupp.weight w β) := by
  intro α hα
  change α ∈ (polynomialSlotCoefficient β P).support at hα
  have hne : (polynomialSlotCoefficient β P).coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  rw [polynomialSlotCoefficient_coeff] at hne
  have h : Finsupp.weight (Sum.elim v w) (α.sumElim β) ≤ n :=
    hP (MvPolynomial.mem_support_iff.mpr hne)
  rw [sumExponent_weight] at h
  change Finsupp.weight v α ≤ n - Finsupp.weight w β
  omega

theorem polynomialSlotCoefficient_monomial [DecidableEq τ] (α : σ →₀ ℕ) (β γ : τ →₀ ℕ) (c : R) :
    polynomialSlotCoefficient β (monomial (α.sumElim γ) c) =
      if γ = β then monomial α c else 0 := by
  classical
  ext δ
  rw [polynomialSlotCoefficient_coeff]
  by_cases hγ : γ = β
  · subst γ
    simp only [ite_true, coeff_monomial]
    simp only [(sumExponent_injective β).eq_iff]
  · have hne : α.sumElim γ ≠ δ.sumElim β := by
      intro h
      apply hγ
      ext i
      exact congrArg (fun a : σ ⊕ τ →₀ ℕ => a (Sum.inr i)) h
    simp only [hγ, ite_false, MvPolynomial.coeff_zero,
      coeff_monomial, hne]

theorem polynomialParameterEval_monomial (t : σ → R)
    (α : σ →₀ ℕ) (β : τ →₀ ℕ) (c : R) :
    aeval (Sum.elim (fun i => C (t i)) X) (monomial (α.sumElim β) c) =
      monomial β (aeval t (monomial α c)) := by
  classical
  simp only [aeval_monomial, Finsupp.prod_sumElim, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  simp only [← map_pow, ← map_finsuppProd, Algebra.algebraMap_self, RingHom.id_apply]
  rw [← mul_assoc, ← map_mul]
  rw [← monomial_eq]

theorem polynomialSlotCoefficient_eval (t : σ → R) (β : τ →₀ ℕ)
    (P : MvPolynomial (σ ⊕ τ) R) :
    aeval t (polynomialSlotCoefficient β P) =
      (aeval (Sum.elim (fun i => C (t i)) X) P).coeff β := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    let e : (σ ⊕ τ →₀ ℕ) ≃ (σ →₀ ℕ) × (τ →₀ ℕ) := Finsupp.sumFinsuppEquivProdFinsupp
    obtain ⟨⟨α, γ⟩, hm⟩ := e.symm.surjective m
    change α.sumElim γ = m at hm
    rw [← hm, polynomialSlotCoefficient_monomial, polynomialParameterEval_monomial]
    by_cases h : γ = β <;> simp [h, coeff_monomial]
  | add P Q hP hQ =>
    simp only [map_add, MvPolynomial.coeff_add, hP, hQ]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem polynomialSlotCoefficient_weightedHomogeneousComponent
    {U B R : Type*} [CommRing R] (v : U → ℕ) (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial (U ⊕ B) R}
    (hP : P ∈ weightedSupportLE (Sum.elim v w) d) (α : B →₀ ℕ) :
    weightedHomogeneousComponent v (d - Finsupp.weight w α) (polynomialSlotCoefficient α P) =
      polynomialSlotCoefficient α (weightedHomogeneousComponent (Sum.elim v w) d P) := by
  classical
  ext β
  rw [coeff_weightedHomogeneousComponent, polynomialSlotCoefficient_coeff,
    polynomialSlotCoefficient_coeff, coeff_weightedHomogeneousComponent, sumExponent_weight]
  by_cases hc : P.coeff (β.sumElim α) = 0
  · simp only [hc, ite_self]
  · have hdegree : Finsupp.weight (Sum.elim v w) (β.sumElim α) ≤ d :=
      hP (mem_support_iff.mpr hc)
    rw [sumExponent_weight] at hdegree
    have heq : Finsupp.weight v β = d - Finsupp.weight w α ↔
        Finsupp.weight v β + Finsupp.weight w α = d := by omega
    simp only [heq]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B : Type*}

theorem polynomialSlotCoefficient_eq_zero_of_weight_ge (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial (U ⊕ B) ℝ}
    (hP : P ∈ weightedSupportLT (Sum.elim (fun _ : U => 0) w) d)
    (α : B →₀ ℕ) (hd : d ≤ Finsupp.weight w α) :
    polynomialSlotCoefficient α P = 0 := by
  ext β
  rw [polynomialSlotCoefficient_coeff, MvPolynomial.coeff_zero]
  by_contra hne
  have hlt : Finsupp.weight (Sum.elim (fun _ : U => 0) w) (β.sumElim α) < d :=
    hP (mem_support_iff.mpr hne)
  rw [sumExponent_weight] at hlt
  have hz : Finsupp.weight (fun _ : U => (0 : ℕ)) β = 0 := by
    simp [Finsupp.weight_apply]
  rw [hz, zero_add] at hlt
  exact (not_lt_of_ge hd) hlt

theorem specializeMajorParameters_mem_weightedSupportLT (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial (U ⊕ B) ℝ}
    (hP : P ∈ weightedSupportLT (Sum.elim (fun _ : U => 0) w) d)
    (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d := by
  change aeval (Sum.elim (fun i => C (u i)) X) P ∈ weightedSupportLT w d
  apply weightedSupportLT_aeval _ _ _ _ hP
  intro i
  cases i with
  | inl j => exact weightedSupportLE_C w 0 (u j)
  | inr j => exact weightedSupportLE_X w j

theorem polynomialSlotCoefficient_totalDegree_le (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial (U ⊕ B) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (α : B →₀ ℕ) :
    (polynomialSlotCoefficient α P).totalDegree ≤ d - Finsupp.weight w α := by
  exact (mem_weightedSupportLE_one_iff _ _).mp
    (polynomialSlotCoefficient_degree (fun _ : U => 1) w hP α)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B : Type*}

noncomputable def majorTranslationJointPolynomial
    (D : MvPolynomial (U ⊕ B) ℝ) (x : B → MvPolynomial U ℝ) :
    MvPolynomial (U ⊕ B) ℝ :=
  D - eval₂Hom C (fun j => X (Sum.inr j) - rename Sum.inl (x j))
    (specializeMajorParameters (RingHom.id ℝ) D 0)

theorem majorTranslationJointPolynomial_eq_sub_aeval
    (D : MvPolynomial (U ⊕ B) ℝ) (x : B → MvPolynomial U ℝ) :
    majorTranslationJointPolynomial D x =
      D - aeval (Sum.elim (fun _ : U => 0)
        (fun j => X (Sum.inr j) - rename Sum.inl (x j))) D := by
  have hfreeze : specializeMajorParameters (RingHom.id ℝ) D 0 =
      aeval (R := ℝ) (Sum.elim (fun _ : U => 0) (X : B → MvPolynomial B ℝ)) D := by
    simp only [specializeMajorParameters, RingHom.comp_id, Pi.zero_apply, map_zero]
    rfl
  rw [majorTranslationJointPolynomial, hfreeze]
  congr 1
  change aeval (R := ℝ) (fun j => X (Sum.inr j) - rename Sum.inl (x j))
      (aeval (Sum.elim (fun _ : U => 0) X) D) = _
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => aeval f D)
  funext i
  cases i <;> simp

theorem majorTranslationJointPolynomial_specialize
    (D : MvPolynomial (U ⊕ B) ℝ) (x : B → MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) (majorTranslationJointPolynomial D x) u =
      (algebraicMajorSymbol D (specializeMajorParameters (RingHom.id ℝ) D 0) x u).polynomial := by
  have hsub : specializeMajorParameters (RingHom.id ℝ) (majorTranslationJointPolynomial D x) u =
      specializeMajorParameters (RingHom.id ℝ) D u -
      specializeMajorParameters (RingHom.id ℝ)
        (eval₂Hom C (fun j => X (Sum.inr j) - rename Sum.inl (x j))
          (specializeMajorParameters (RingHom.id ℝ) D 0)) u := by
    simp only [majorTranslationJointPolynomial, specializeMajorParameters, map_sub]
  rw [hsub, specializeMajorParameters_translatedSlice]
  rfl

theorem majorParameterRename_degree (v : U → ℕ) (w : B → ℕ)
    {P : MvPolynomial U ℝ} {d : ℕ} (hP : P ∈ weightedSupportLE v d) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLE (Sum.elim v w) d := by
  apply polynomialHom_preserves_weightedDegree v (Sum.elim v w) (rename Sum.inl) _ hP
  intro i
  simpa only [rename_X, Sum.elim_inl] using
    weightedSupportLE_X (R := ℝ) (Sum.elim v w) (Sum.inl i)

theorem majorParameterRename_slot_degree_zero (w : B → ℕ) (P : MvPolynomial U ℝ) :
    rename (Sum.inl : U → U ⊕ B) P ∈
      weightedSupportLE (Sum.elim (fun _ : U => 0) w) 0 := by
  apply majorParameterRename_degree
  intro α _
  simp [Finsupp.weight_apply]

theorem majorTranslationJointPolynomial_degree (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) (hx : ∀ j, (x j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D x ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply (weightedSupportLE _ _).sub_mem hD
  apply weightedSupportLE_aeval _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr j =>
      exact (weightedSupportLE _ _).sub_mem
        (weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inr j))
        (majorParameterRename_degree (fun _ => 1) w
          ((mem_weightedSupportLE_one_iff (x j) (w j)).mpr (hx j)))

theorem majorTranslationJointPolynomial_slot_lower (w : B → ℕ) (hw : ∀ j, 0 < w j)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) :
    majorTranslationJointPolynomial D x ∈
      weightedSupportLT (Sum.elim (fun _ : U => 0) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply weightedComparison_difference (Sum.elim (fun _ : U => 1) w)
    (Sum.elim (fun _ : U => 0) w) (AlgHom.id ℝ _)
    (aeval (Sum.elim (fun _ : U => 0)
      (fun j => X (Sum.inr j) - rename Sum.inl (x j)))) _ _ _ hD
  · intro i
    cases i with
    | inl i =>
        exact weightedSupportLE_mono (by decide : 0 ≤ 1)
          (weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inl i))
    | inr j => exact weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inr j)
  · intro i
    simp only [aeval_X]
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr j =>
        exact (weightedSupportLE _ _).sub_mem
          (weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inr j))
          (weightedSupportLE_mono (Nat.zero_le _) (majorParameterRename_slot_degree_zero w (x j)))
  · intro i
    simp only [AlgHom.id_apply, aeval_X]
    cases i with
    | inl i =>
        simp only [Sum.elim_inl, sub_zero]
        exact weightedSupportLE_lt_succ
          (weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inl i))
    | inr j =>
        simp only [Sum.elim_inr, sub_sub_cancel]
        intro α hα
        exact (majorParameterRename_slot_degree_zero w (x j) hα).trans_lt (hw j)

theorem majorTranslationJointPolynomial_coefficient_eq_zero (w : B → ℕ)
    (hw : ∀ j, 0 < w j) {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) (α : B →₀ ℕ) (hα : d ≤ Finsupp.weight w α) :
    polynomialSlotCoefficient α (majorTranslationJointPolynomial D x) = 0 :=
  polynomialSlotCoefficient_eq_zero_of_weight_ge w
    (majorTranslationJointPolynomial_slot_lower w hw hD x) α hα

theorem majorTranslationJointPolynomial_specialize_lower (w : B → ℕ)
    (hw : ∀ j, 0 < w j) {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) (majorTranslationJointPolynomial D x) u ∈
      weightedSupportLT w d :=
  specializeMajorParameters_mem_weightedSupportLT w
    (majorTranslationJointPolynomial_slot_lower w hw hD x) u

theorem majorTranslationJointPolynomial_coefficient_totalDegree (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) (hx : ∀ j, (x j).totalDegree ≤ w j) (α : B →₀ ℕ) :
    (polynomialSlotCoefficient α (majorTranslationJointPolynomial D x)).totalDegree ≤
      d - Finsupp.weight w α :=
  polynomialSlotCoefficient_totalDegree_le w (majorTranslationJointPolynomial_degree w hD x hx) α

theorem majorTranslationJointPolynomial_bounds (w : B → ℕ) (hw : ∀ j, 0 < w j)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) (hx : ∀ j, (x j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D x ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
    (∀ α, d ≤ Finsupp.weight w α →
      polynomialSlotCoefficient α (majorTranslationJointPolynomial D x) = 0) ∧
    (∀ u, specializeMajorParameters (RingHom.id ℝ) (majorTranslationJointPolynomial D x) u ∈
      weightedSupportLT w d) ∧
    (∀ α, (polynomialSlotCoefficient α (majorTranslationJointPolynomial D x)).totalDegree ≤
      d - Finsupp.weight w α) := by
  have hle : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
    fun _ hα => (hD (mem_support_iff.mp hα)).le
  exact ⟨majorTranslationJointPolynomial_degree w hle x hx,
    majorTranslationJointPolynomial_coefficient_eq_zero w hw hle x,
    majorTranslationJointPolynomial_specialize_lower w hw hle x,
    majorTranslationJointPolynomial_coefficient_totalDegree w hle x hx⟩

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B : Type*}

noncomputable def majorTranslationTopCoordinates (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (j : B) : MvPolynomial U ℝ :=
  weightedHomogeneousComponent (fun _ : U => 1) (w j) (A j)

theorem majorTranslationTopCoordinates_homogeneous (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (j : B) :
    (majorTranslationTopCoordinates w A j).IsWeightedHomogeneous (fun _ : U => 1) (w j) :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem majorTranslationTopCoordinates_degree (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (j : B) :
    (majorTranslationTopCoordinates w A j).totalDegree ≤ w j := by
  apply (mem_weightedSupportLE_one_iff _ _).mp
  intro α hα
  exact (majorTranslationTopCoordinates_homogeneous w A j (mem_support_iff.mp hα)).le

theorem majorTranslationTopCoordinates_remainder (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) (j : B) :
    A j - majorTranslationTopCoordinates w A j ∈ weightedSupportLT (fun _ : U => 1) (w j) :=
  weightedTopPart_remainder_lt (fun _ : U => 1)
    ((mem_weightedSupportLE_one_iff _ _).mpr (hA j))

theorem majorParameterRename_lower (v : U → ℕ) (w : B → ℕ)
    {P : MvPolynomial U ℝ} {d : ℕ} (hP : P ∈ weightedSupportLT v d) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLT (Sum.elim v w) d := by
  apply weightedSupportLT_map v (Sum.elim v w) (rename Sum.inl) _ hP
  intro i
  simpa only [rename_X, Sum.elim_inl] using
    weightedSupportLE_X (R := ℝ) (Sum.elim v w) (Sum.inl i)

theorem majorParameterRename_homogeneous (v : U → ℕ) (w : B → ℕ)
    {P : MvPolynomial U ℝ} {d : ℕ} (hP : P.IsWeightedHomogeneous v d) :
    (rename (Sum.inl : U → U ⊕ B) P).IsWeightedHomogeneous (Sum.elim v w) d := by
  rw [rename_eq_aeval]
  exact aeval_isWeightedHomogeneous v (Sum.elim v w) (X ∘ Sum.inl)
    (fun i => isWeightedHomogeneous_X (R := ℝ) (Sum.elim v w) (Sum.inl i)) hP

theorem majorTranslationJointPolynomial_top_homogeneous (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) :
    (majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A)).IsWeightedHomogeneous
      (Sum.elim (fun _ : U => 1) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply hD.sub
  apply aeval_isWeightedHomogeneous _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact isWeightedHomogeneous_zero ℝ _ _
  | inr j =>
      exact (isWeightedHomogeneous_X (R := ℝ) (Sum.elim (fun _ : U => 1) w) (Sum.inr j)).sub
        (majorParameterRename_homogeneous (fun _ => 1) w
          (majorTranslationTopCoordinates_homogeneous w A j))

theorem majorTranslationJointPolynomial_sub_top_lower (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D A -
      majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A) ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  let v := Sum.elim (fun _ : U => 1) w
  let F := aeval (R := ℝ) (Sum.elim (fun _ : U => 0)
    (fun j => X (Sum.inr j) - rename Sum.inl (A j)))
  let G := aeval (R := ℝ) (Sum.elim (fun _ : U => 0)
    (fun j => X (Sum.inr j) - rename Sum.inl (majorTranslationTopCoordinates w A j)))
  have hF : ∀ i, F (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simp only [F, aeval_X]
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr j =>
        exact (weightedSupportLE _ _).sub_mem (weightedSupportLE_X v (Sum.inr j))
          (majorParameterRename_degree (fun _ => 1) w
            ((mem_weightedSupportLE_one_iff _ _).mpr (hA j)))
  have hG : ∀ i, G (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simp only [G, aeval_X]
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr j =>
        exact (weightedSupportLE _ _).sub_mem (weightedSupportLE_X v (Sum.inr j))
          (majorParameterRename_degree (fun _ => 1) w
            ((mem_weightedSupportLE_one_iff _ _).mpr (majorTranslationTopCoordinates_degree w A j)))
  have hdiff : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT v (v i) := by
    intro i
    simp only [F, G, aeval_X]
    cases i with
    | inl i => simp only [Sum.elim_inl, sub_self]; exact Submodule.zero_mem _
    | inr j =>
        have h := (weightedSupportLT v (w j)).neg_mem
          (majorParameterRename_lower (fun _ => 1) w (majorTranslationTopCoordinates_remainder w A hA j))
        change (X (Sum.inr j) - rename Sum.inl (A j)) -
          (X (Sum.inr j) - rename Sum.inl (majorTranslationTopCoordinates w A j)) ∈
            weightedSupportLT v (w j)
        have he : (X (Sum.inr j) - rename Sum.inl (A j)) -
            (X (Sum.inr j) - rename Sum.inl (majorTranslationTopCoordinates w A j)) =
            -rename (Sum.inl : U → U ⊕ B) (A j - majorTranslationTopCoordinates w A j) := by
          rw [map_sub]
          abel
        rw [he]
        exact h
  have h := (weightedSupportLT v d).neg_mem (weightedComparison_difference v v F G hF hG hdiff hD)
  rw [majorTranslationJointPolynomial_eq_sub_aeval, majorTranslationJointPolynomial_eq_sub_aeval]
  change (D - F D) - (D - G D) ∈ weightedSupportLT v d
  convert h using 1
  abel

theorem majorTranslationJointPolynomial_weightedHomogeneousComponent (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (majorTranslationJointPolynomial D A) =
      majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A) := by
  have hle : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
    fun _ hα => (hD (mem_support_iff.mp hα)).le
  have hlower := majorTranslationJointPolynomial_sub_top_lower w hle A hA
  have hzero : weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
      (majorTranslationJointPolynomial D A -
        majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A)) = 0 :=
    weightedHomogeneousComponent_eq_zero' d _ (fun α hα => (hlower hα).ne)
  rw [map_sub, (majorTranslationJointPolynomial_top_homogeneous w hD A).weightedHomogeneousComponent_same,
    sub_eq_zero] at hzero
  exact hzero

theorem majorTranslationJointPolynomial_slot_top (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) (α : B →₀ ℕ) :
    weightedHomogeneousComponent (fun _ : U => 1) (d - Finsupp.weight w α)
        (polynomialSlotCoefficient α (majorTranslationJointPolynomial D A)) =
      polynomialSlotCoefficient α
        (majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A)) := by
  have hle : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
    fun _ hβ => (hD (mem_support_iff.mp hβ)).le
  rw [polynomialSlotCoefficient_weightedHomogeneousComponent (fun _ : U => 1) w
    (majorTranslationJointPolynomial_degree w hle A hA),
    majorTranslationJointPolynomial_weightedHomogeneousComponent w hD A hA]

end Erdos3

end

end OAI
