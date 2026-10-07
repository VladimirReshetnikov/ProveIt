import Mathlib.Algebra.MvPolynomial.Funext
import OAI.Combinatorics.Progressions.Estimates.WeightedAxisScaling
import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential

namespace OAI

section

namespace Erdos3.PolynomialSlots

open MvPolynomial

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem parameterSubstitution_slot_homogeneous
    (f : σ → MvPolynomial τ ℝ) (i : Fin d) (v : σ ⊕ Fin i.val) :
    (parameterSubstitution f i v).IsWeightedHomogeneous
      (patchSlotWeight w i) (patchSlotWeight w i v) := by
  cases v with
  | inl a =>
    apply aeval_isWeightedHomogeneous (fun _ : τ => 0) (patchSlotWeight w i)
    · intro b
      exact isWeightedHomogeneous_X ℝ _ (Sum.inl b)
    · intro α _
      simp [Finsupp.weight_apply, Finsupp.sum, patchSlotWeight]
  | inr j => exact isWeightedHomogeneous_X ℝ _ (Sum.inr j)

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def residualCoordinate (A : PolynomialSlots σ d w) (i : Fin d) :
    MvPolynomial (σ ⊕ Fin d) ℝ := X (Sum.inr i) - slotPolynomialLift i (A.center i)

noncomputable def residualHom (A : PolynomialSlots σ d w) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (σ ⊕ Fin d) ℝ := aeval A.residualCoordinate

theorem residualHom_X (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualHom (X i) = A.residualCoordinate i := by
  simp only [residualHom, aeval_X]

theorem residualCoordinate_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualCoordinate i ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w i) :=
  (weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ (Sum.inr i))
    (slotPolynomialLift_degree (fun _ => 1) w i (A.degree i))

theorem residualCoordinate_slot_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualCoordinate i ∈ weightedSupportLE (Sum.elim (fun _ : σ => 0) w) (w i) := by
  apply weightedSupportLE_of_weight_le _ (A.residualCoordinate_degree i)
  intro a
  cases a <;> simp

theorem residualCoordinate_sub_topPart_lower (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualCoordinate i - A.topPart.residualCoordinate i ∈
      weightedSupportLT (Sum.elim (fun _ : σ => 0) w) (w i) := by
  have he : A.residualCoordinate i - A.topPart.residualCoordinate i =
      -slotPolynomialLift i (A.center i - A.topPart.center i) := by
    simp only [residualCoordinate, slotPolynomialLift, map_sub]
    abel
  rw [he]
  exact (weightedSupportLT _ _).neg_mem
    (slotPolynomialLift_lower (fun _ => 0) w i (A.sub_topPart_lower i))

theorem residualHom_sub_topPart_lower (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.residualHom p - A.topPart.residualHom p ∈
      weightedSupportLT (Sum.elim (fun _ : σ => 0) w) n := by
  apply weightedComparison_difference w _ A.residualHom A.topPart.residualHom _ _ _ hp
  · intro i
    rw [residualHom_X]
    exact A.residualCoordinate_slot_degree i
  · intro i
    rw [residualHom_X]
    exact A.topPart.residualCoordinate_slot_degree i
  · intro i
    rw [residualHom_X, residualHom_X]
    exact A.residualCoordinate_sub_topPart_lower i

theorem residualCoordinate_eval (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (b : Fin d → ℝ) (i : Fin d) :
    aeval (Sum.elim t b) (A.residualCoordinate i) =
      b i - (A.slots t).center b i := by
  rw [residualCoordinate, map_sub, aeval_X, slotPolynomialLift_eval]
  rfl

theorem residualCoordinate_eval_int (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (b : Fin d → ℤ) (i : Fin d) :
    aeval (Sum.elim t (fun j => (b j : ℝ))) (A.residualCoordinate i) =
      (A.slots t).residual b i :=
  A.residualCoordinate_eval t (fun j => (b j : ℝ)) i

theorem residualHom_eval (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (b : Fin d → ℝ) (P : MvPolynomial (Fin d) ℝ) :
    aeval (Sum.elim t b) (A.residualHom P) =
      aeval (fun i => b i - (A.slots t).center b i) P := by
  rw [residualHom, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => aeval f P)
  funext i
  exact A.residualCoordinate_eval t b i

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem topResidualShift_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    rename (earlierSlot i) (-A.topPart.specializeCenter 0 i) ∈ weightedSupportLE w (w i) := by
  simpa only [map_neg] using (weightedSupportLE w (w i)).neg_mem
    (A.topPart.specializeCenter_full_degree 0 i)

noncomputable def topResidualEquiv (A : PolynomialSlots σ d w) :
    MvPolynomial (Fin d) ℝ ≃ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  triangularPolynomialEquiv w (fun i => -A.topPart.specializeCenter 0 i) A.topResidualShift_degree

theorem topResidualEquiv_X (A : PolynomialSlots σ d w) (i : Fin d) :
    A.topResidualEquiv (X i) = X i - rename (earlierSlot i) (A.topPart.specializeCenter 0 i) := by
  rw [topResidualEquiv, triangularPolynomialEquiv_X, map_neg, ← sub_eq_add_neg]

theorem topResidualEquiv_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.topResidualEquiv p ∈ weightedSupportLE w n :=
  triangularPolynomialEquiv_degree w _ A.topResidualShift_degree hp

theorem topResidualEquiv_inverse_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.topResidualEquiv.symm p ∈ weightedSupportLE w n :=
  triangularPolynomialEquiv_inverse_degree w _ A.topResidualShift_degree hp

theorem topResidualEquiv_lift (A : PolynomialSlots σ d w) :
    (rename (Sum.inr : Fin d → σ ⊕ Fin d)).comp A.topResidualEquiv.toAlgHom =
      A.topPart.residualHom := by
  apply MvPolynomial.algHom_ext
  intro i
  change rename Sum.inr (A.topResidualEquiv (X i)) = A.topPart.residualHom (X i)
  rw [topResidualEquiv_X, map_sub, rename_X, residualHom_X, residualCoordinate,
    topPart_lift_specialize]

noncomputable def loweringHom (A : PolynomialSlots σ d w) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (σ ⊕ Fin d) ℝ :=
  A.residualHom.comp A.topResidualEquiv.symm.toAlgHom

theorem loweringHom_comp_top (A : PolynomialSlots σ d w) :
    A.loweringHom.comp A.topResidualEquiv.toAlgHom = A.residualHom := by
  apply AlgHom.ext
  intro p
  change A.residualHom (A.topResidualEquiv.symm (A.topResidualEquiv p)) = A.residualHom p
  rw [AlgEquiv.symm_apply_apply]

theorem loweringHom_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.loweringHom p ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n := by
  change A.residualHom (A.topResidualEquiv.symm p) ∈ _
  apply polynomialHom_preserves_weightedDegree w _ A.residualHom _
    (A.topResidualEquiv_inverse_degree hp)
  intro i
  rw [residualHom_X]
  exact A.residualCoordinate_degree i

theorem loweringHom_X_lower (A : PolynomialSlots σ d w) (i : Fin d) :
    A.loweringHom (X i) - X (Sum.inr i) ∈
      weightedSupportLT (Sum.elim (fun _ : σ => 0) w) (w i) := by
  have h := A.residualHom_sub_topPart_lower
    (A.topResidualEquiv_inverse_degree (weightedSupportLE_X w i))
  have he : A.topPart.residualHom (A.topResidualEquiv.symm (X i)) = X (Sum.inr i) := by
    rw [← A.topResidualEquiv_lift]
    change rename Sum.inr (A.topResidualEquiv (A.topResidualEquiv.symm (X i))) = _
    rw [AlgEquiv.apply_symm_apply, rename_X]
  rw [he] at h
  exact h

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} {d : ℕ}

noncomputable def patchParameterSpecialization (t : σ → ℝ) :
    MvPolynomial (σ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  aeval (Sum.elim (fun a => C (t a)) X)

theorem patchParameterSpecialization_X_slot (t : σ → ℝ) (i : Fin d) :
    patchParameterSpecialization t (X (Sum.inr i)) = X i := by
  simp only [patchParameterSpecialization, aeval_X, Sum.elim_inr]

theorem patchParameterSpecialization_degree (v : σ → ℕ) (w : Fin d → ℕ) (t : σ → ℝ)
    {n : ℕ} {P : MvPolynomial (σ ⊕ Fin d) ℝ} (hP : P ∈ weightedSupportLE (Sum.elim v w) n) :
    patchParameterSpecialization t P ∈ weightedSupportLE w n := by
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro a
  cases a with
  | inl j => exact weightedSupportLE_C w (v j) (t j)
  | inr j => exact weightedSupportLE_X w j

theorem patchParameterSpecialization_lower (v : σ → ℕ) (w : Fin d → ℕ) (t : σ → ℝ)
    {n : ℕ} {P : MvPolynomial (σ ⊕ Fin d) ℝ} (hP : P ∈ weightedSupportLT (Sum.elim v w) n) :
    patchParameterSpecialization t P ∈ weightedSupportLT w n := by
  apply weightedSupportLT_map _ _ (patchParameterSpecialization t) _ hP
  intro a
  cases a with
  | inl j =>
      simp only [patchParameterSpecialization, aeval_X, Sum.elim_inl]
      exact weightedSupportLE_C w (v j) (t j)
  | inr j =>
      rw [patchParameterSpecialization_X_slot]
      exact weightedSupportLE_X w j

theorem patchParameterSpecialization_eval (t : σ → ℝ) (b : Fin d → ℝ)
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    aeval b (patchParameterSpecialization t P) = aeval (Sum.elim t b) P := by
  rw [patchParameterSpecialization, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => aeval f P)
  funext a
  cases a with
  | inl j => simp only [Sum.elim_inl, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  | inr j => simp only [Sum.elim_inr, aeval_X]

namespace PolynomialSlots

variable {w : Fin d → ℕ}

noncomputable def loweringAtHom (A : PolynomialSlots σ d w) (t : σ → ℝ) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  (patchParameterSpecialization t).comp A.loweringHom

theorem loweringAtHom_lower (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    A.loweringAtHom t (X i) - X i ∈ weightedSupportLT w (w i) := by
  have h := patchParameterSpecialization_lower (fun _ => 0) w t (A.loweringHom_X_lower i)
  rw [map_sub, patchParameterSpecialization_X_slot] at h
  exact h

noncomputable def loweringAt (A : PolynomialSlots σ d w) (t : σ → ℝ) :
    WeightedLoweringAut w ℝ :=
  WeightedLoweringAut.ofHom w (A.loweringAtHom t) (A.loweringAtHom_lower t)

theorem loweringAt_apply (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (P : MvPolynomial (Fin d) ℝ) : (A.loweringAt t).val P = A.loweringAtHom t P := rfl

theorem loweringAt_comp_top (A : PolynomialSlots σ d w) (t : σ → ℝ) :
    (A.loweringAt t).val.toAlgHom.comp A.topResidualEquiv.toAlgHom =
      (patchParameterSpecialization t).comp A.residualHom := by
  apply AlgHom.ext
  intro P
  change patchParameterSpecialization t (A.loweringHom (A.topResidualEquiv P)) =
    patchParameterSpecialization t (A.residualHom P)
  exact congrArg (patchParameterSpecialization t) (DFunLike.congr_fun A.loweringHom_comp_top P)

noncomputable def loweringPoint (A : PolynomialSlots σ d w) (t : σ → ℝ) (b : Fin d → ℝ) :
    Fin d → ℝ := fun i => aeval b ((A.loweringAt t).val (X i))

theorem loweringAt_aeval (A : PolynomialSlots σ d w) (t : σ → ℝ) (b : Fin d → ℝ)
    (P : MvPolynomial (Fin d) ℝ) :
    aeval b ((A.loweringAt t).val P) = aeval (A.loweringPoint t b) P := by
  change aeval b ((A.loweringAt t).val.toAlgHom P) = _
  rw [MvPolynomial.aeval_unique (A.loweringAt t).val.toAlgHom, MvPolynomial.comp_aeval_apply]
  rfl

theorem top_factorization_coordinate (A : PolynomialSlots σ d w)
    (t : σ → ℝ) (b : Fin d → ℝ) (i : Fin d) :
    aeval (A.loweringPoint t b) (A.topResidualEquiv (X i)) =
      b i - (A.slots t).center b i := by
  have he := congrArg (fun F : MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ =>
    aeval b (F (X i))) (A.loweringAt_comp_top t)
  change aeval b ((A.loweringAt t).val (A.topResidualEquiv (X i))) =
    aeval b (patchParameterSpecialization t (A.residualHom (X i))) at he
  rw [A.loweringAt_aeval, patchParameterSpecialization_eval, residualHom_X,
    residualCoordinate_eval] at he
  exact he

theorem top_factorization_residual (A : PolynomialSlots σ d w)
    (t : σ → ℝ) (b : Fin d → ℤ) :
    (fun i => aeval (A.loweringPoint t (fun j => (b j : ℝ))) (A.topResidualEquiv (X i))) =
      (A.slots t).residual b := by
  funext i
  exact A.top_factorization_coordinate t (fun j => (b j : ℝ)) i

end PolynomialSlots

namespace PolynomialPatch

variable {s : ℕ}

theorem value_top_factorization (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t = ∑' b : Fin d → ℤ,
      A.kernel.value (fun i => aeval (A.form.loweringPoint t (fun j => (b j : ℝ)))
        (A.form.topResidualEquiv (X i))) := by
  simp_rw [PolynomialSlots.top_factorization_residual]
  rfl

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open MvPolynomial

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem reparam_topPart_center (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin d) :
    (A.reparam f hf).topPart.center i =
      aeval (parameterSubstitution f i) (A.topPart.center i) := by
  exact (aeval_weightedHomogeneousComponent (patchSlotWeight w i)
    (patchSlotWeight w i) (parameterSubstitution f i)
    (parameterSubstitution_slot_homogeneous f i) (w i) (A.center i)).symm

theorem reparam_topPart_specializeCenter (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin d) :
    (A.reparam f hf).topPart.specializeCenter 0 i =
      A.topPart.specializeCenter 0 i := by
  unfold specializeCenter
  rw [A.reparam_topPart_center f hf, MvPolynomial.comp_aeval_apply]
  let q : σ → MvPolynomial (Fin i.val) ℝ := fun a =>
    aeval (Sum.elim (fun _ : τ => 0) X) (parameterSubstitution f i (Sum.inl a))
  have hinput :
      (fun a => aeval (Sum.elim (fun j : τ => C ((0 : τ → ℝ) j)) X)
        (parameterSubstitution f i a)) = Sum.elim q X := by
    funext a
    cases a <;> simp [q, parameterSubstitution]
  rw [hinput]
  exact A.topPart_aeval_independent i q (fun a => C ((0 : σ → ℝ) a)) X

theorem reparam_topResidualEquiv (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) :
    (A.reparam f hf).topResidualEquiv = A.topResidualEquiv := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  change (A.reparam f hf).topResidualEquiv (X i) = A.topResidualEquiv (X i)
  rw [topResidualEquiv_X, topResidualEquiv_X,
    A.reparam_topPart_specializeCenter f hf]

theorem reparam_specialized_residualHom (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (patchParameterSpecialization t).comp (A.reparam f hf).residualHom =
      (patchParameterSpecialization (fun a => aeval t (f a))).comp A.residualHom := by
  apply MvPolynomial.algHom_ext
  intro i
  apply MvPolynomial.funext
  intro x
  simp only [AlgHom.comp_apply, ← MvPolynomial.aeval_eq_eval]
  rw [patchParameterSpecialization_eval, patchParameterSpecialization_eval,
    residualHom_X, residualHom_X, residualCoordinate_eval, residualCoordinate_eval,
    reparam_slots]

theorem reparam_loweringAt (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (A.reparam f hf).loweringAt t = A.loweringAt (fun a => aeval t (f a)) := by
  have hc := (A.reparam f hf).loweringAt_comp_top t
  rw [A.reparam_topResidualEquiv f hf, A.reparam_specialized_residualHom f hf,
    ← A.loweringAt_comp_top] at hc
  apply Subtype.ext
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.ext
  intro P
  have h := congrArg (fun F : MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ =>
    F (A.topResidualEquiv.symm P)) hc
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using h

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def symbolicShearHom (A : PolynomialSlots σ d w) :
    MvPolynomial (σ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (σ ⊕ Fin d) ℝ :=
  aeval (Sum.elim (fun a => X (Sum.inl a)) (fun i => A.loweringHom (X i)))

theorem symbolicShearHom_parameter (A : PolynomialSlots σ d w) (a : σ) :
    A.symbolicShearHom (X (Sum.inl a)) = X (Sum.inl a) := by
  simp only [symbolicShearHom, aeval_X, Sum.elim_inl]

theorem symbolicShearHom_slot (A : PolynomialSlots σ d w) (i : Fin d) :
    A.symbolicShearHom (X (Sum.inr i)) = A.loweringHom (X i) := by
  simp only [symbolicShearHom, aeval_X, Sum.elim_inr]

theorem symbolicShearHom_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {P : MvPolynomial (σ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n) :
    A.symbolicShearHom P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n := by
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro j
  cases j with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr i => exact A.loweringHom_degree (weightedSupportLE_X w i)

theorem symbolicShearHom_specialization (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (A.symbolicShearHom P) =
      A.loweringAtHom t (patchParameterSpecialization t P) := by
  have h : (patchParameterSpecialization t).comp A.symbolicShearHom =
      (A.loweringAtHom t).comp (patchParameterSpecialization t) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | inl a =>
      simp [AlgHom.comp_apply, symbolicShearHom_parameter, patchParameterSpecialization,
        loweringAtHom]
    | inr i =>
      change patchParameterSpecialization t (A.symbolicShearHom (X (Sum.inr i))) =
        A.loweringAtHom t (patchParameterSpecialization t (X (Sum.inr i)))
      rw [symbolicShearHom_slot, patchParameterSpecialization_X_slot]
      rfl
  exact DFunLike.congr_fun h P

theorem symbolicShearDifference_specialization (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (polynomialHomDifference A.symbolicShearHom P) =
      polynomialHomDifference (A.loweringAt t).val.toAlgHom (patchParameterSpecialization t P) := by
  change patchParameterSpecialization t (A.symbolicShearHom P - P) =
    A.loweringAtHom t (patchParameterSpecialization t P) - patchParameterSpecialization t P
  rw [map_sub, symbolicShearHom_specialization]

theorem symbolicShearDifference_pow_specialization (A : PolynomialSlots σ d w)
    (t : σ → ℝ) (k : ℕ) (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t ((polynomialHomDifference A.symbolicShearHom ^ k) P) =
      (polynomialHomDifference (A.loweringAt t).val.toAlgHom ^ k)
        (patchParameterSpecialization t P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, symbolicShearDifference_specialization, ih,
      pow_succ', Module.End.mul_apply]

theorem symbolicShearDifference_pow_degree (A : PolynomialSlots σ d w) (k : ℕ)
    {n : ℕ} {P : MvPolynomial (σ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n) :
    (polynomialHomDifference A.symbolicShearHom ^ k) P ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (weightedSupportLE _ n).sub_mem (A.symbolicShearHom_degree ih) ih

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open MvPolynomial

variable {σ τ R : Type*} [CommRing R] [Algebra ℚ R]
variable {w₀ w₁ : σ → ℕ} {v₀ : τ → ℕ}

theorem polynomialShearExp_weightedSupportLE
    (D : PolynomialShearLieAlgebra w₀ R)
    (hD : ∀ i, D.val (X i) ∈ weightedSupportLE w₁ (w₁ i))
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w₁ n) :
    polynomialShearExp D P ∈ weightedSupportLE w₁ n := by
  have hP₀ : P ∈ weightedSupportLE w₀ (P.weightedTotalDegree w₀) :=
    (mem_weightedSupportLE_iff w₀ _ P).mpr le_rfl
  have hD₁ : ∀ i, D.val (X i) ∈ weightedSupportDrop w₁ (w₁ i) 0 := by
    simpa only [weightedSupportDrop_zero] using hD
  have hP₁ : P ∈ weightedSupportDrop w₁ n 0 := by
    simpa only [weightedSupportDrop_zero] using hP
  rw [polynomialShearExp_eq_sum D hP₀]
  apply ((weightedSupportLE (R := R) w₁ n).restrictScalars ℚ).sum_mem
  intro k hk
  apply ((weightedSupportLE (R := R) w₁ n).restrictScalars ℚ).smul_mem
  change (D.val.toLinearMap ^ k) P ∈ weightedSupportLE w₁ n
  simpa only [Nat.mul_zero, Nat.add_zero, weightedSupportDrop_zero] using
    weightedDerivation_pow w₁ D.val 0 hD₁ hP₁ k

omit [Algebra ℚ R] in

theorem polynomialShear_pow_intertwine
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (D : PolynomialShearLieAlgebra w₀ R) (E : PolynomialShearLieAlgebra v₀ R)
    (hφ : ∀ P, φ (D.val P) = E.val (φ P)) (k : ℕ) (P : MvPolynomial σ R) :
    φ ((D.val.toLinearMap ^ k) P) = (E.val.toLinearMap ^ k) (φ P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      change φ (D.val ((D.val.toLinearMap ^ k) P)) =
        E.val ((E.val.toLinearMap ^ k) (φ P))
      rw [hφ, ih]

theorem polynomialShearExp_intertwine_of_degree
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (D : PolynomialShearLieAlgebra w₀ R) (E : PolynomialShearLieAlgebra v₀ R)
    (hφ : ∀ P, φ (D.val P) = E.val (φ P))
    {P : MvPolynomial σ R} {n : ℕ}
    (hP : P ∈ weightedSupportLE w₀ n) (hφP : φ P ∈ weightedSupportLE v₀ n) :
    φ (polynomialShearExp D P) = polynomialShearExp E (φ P) := by
  rw [polynomialShearExp_eq_sum D hP, polynomialShearExp_eq_sum E hφP, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_rat_smul, polynomialShear_pow_intertwine φ D E hφ]

theorem polynomialShearExp_intertwine
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (D : PolynomialShearLieAlgebra w₀ R) (E : PolynomialShearLieAlgebra v₀ R)
    (hφ : ∀ P, φ (D.val P) = E.val (φ P)) (P : MvPolynomial σ R) :
    φ (polynomialShearExp D P) = polynomialShearExp E (φ P) := by
  let n := max (P.weightedTotalDegree w₀) ((φ P).weightedTotalDegree v₀)
  have hP : P ∈ weightedSupportLE w₀ n :=
    (mem_weightedSupportLE_iff w₀ n P).mpr (le_max_left _ _)
  have hφP : φ P ∈ weightedSupportLE v₀ n :=
    (mem_weightedSupportLE_iff v₀ n (φ P)).mpr (le_max_right _ _)
  exact polynomialShearExp_intertwine_of_degree φ D E hφ hP hφP

end Erdos3

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators

variable {σ : Type*} {d : ℕ} (w : Fin d → ℕ)
variable [Fintype (PolynomialShearIndex w)]
variable (c : PolynomialShearIndex w → MvPolynomial σ ℝ)

noncomputable def polynomialSymbolicShearTerm (a : PolynomialShearIndex w) :
    MvPolynomial (σ ⊕ Fin d) ℝ :=
  rename Sum.inl (c a) * rename Sum.inr (monomial a.2.val 1)

private theorem symbolic_rename_degree {ι κ : Type*} (v : ι → ℕ) (z : κ → ℕ)
    (f : ι → κ) (hf : ∀ i, z (f i) = v i)
    {P : MvPolynomial ι ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE v n) :
    rename f P ∈ weightedSupportLE z n := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval v z _ _ hP
  intro i
  simpa only [Function.comp_apply, hf] using weightedSupportLE_X (R := ℝ) z (f i)

omit [Fintype (PolynomialShearIndex w)] in
theorem polynomialSymbolicShearTerm_slot_degree (a : PolynomialShearIndex w) :
    polynomialSymbolicShearTerm w c a ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 0) w) (Finsupp.weight w a.2.val) := by
  have hp : c a ∈ weightedSupportLE (fun _ : σ => 0) 0 := by
    intro α hα
    simp [Finsupp.weight_apply, Finsupp.sum]
  have hc := symbolic_rename_degree (fun _ : σ => 0)
    (Sum.elim (fun _ : σ => 0) w) Sum.inl (fun _ => rfl) hp
  have hm := symbolic_rename_degree w (Sum.elim (fun _ : σ => 0) w)
    Sum.inr (fun _ => rfl) (weightedSupportLE_monomial w a.2.val (1 : ℝ))
  exact (by simpa only [zero_add, polynomialSymbolicShearTerm] using weightedSupportLE_mul hc hm)

omit [Fintype (PolynomialShearIndex w)] in
theorem polynomialSymbolicShearTerm_total_degree
    (hc : ∀ a, c a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a))
    (a : PolynomialShearIndex w) :
    polynomialSymbolicShearTerm w c a ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w a.1) := by
  have hp := symbolic_rename_degree (fun _ : σ => 1)
    (Sum.elim (fun _ : σ => 1) w) Sum.inl (fun _ => rfl) (hc a)
  have hm := symbolic_rename_degree w (Sum.elim (fun _ : σ => 1) w)
    Sum.inr (fun _ => rfl) (weightedSupportLE_monomial w a.2.val (1 : ℝ))
  apply weightedSupportLE_mono _ (weightedSupportLE_mul hp hm)
  have ha := a.2.property
  unfold polynomialShearDeficit
  omega

noncomputable def polynomialSymbolicShearSlot (i : Fin d) : MvPolynomial (σ ⊕ Fin d) ℝ :=
  ∑ a : PolynomialShearIndex w, if a.1 = i then polynomialSymbolicShearTerm w c a else 0

theorem polynomialSymbolicShearSlot_lower (i : Fin d) :
    polynomialSymbolicShearSlot w c i ∈
      weightedSupportDrop (Sum.elim (fun _ : σ => 0) w) (w i) 1 := by
  classical
  apply Submodule.sum_mem
  intro a ha
  split_ifs with hi
  · intro α hα
    have h := polynomialSymbolicShearTerm_slot_degree w c a hα
    change Finsupp.weight (Sum.elim (fun _ : σ => 0) w) α ≤ Finsupp.weight w a.2.val at h
    have hb := a.2.property
    change Finsupp.weight (Sum.elim (fun _ : σ => 0) w) α + 1 ≤ w i
    have hiw := congrArg w hi
    omega
  · exact Submodule.zero_mem _

noncomputable def polynomialSymbolicShearDerivation :
    PolynomialShearLieAlgebra (Sum.elim (fun _ : σ => 0) w) ℝ := by
  refine ⟨MvPolynomial.mkDerivation ℝ (Sum.elim (fun _ => 0) (polynomialSymbolicShearSlot w c)), ?_⟩
  intro i
  rw [MvPolynomial.mkDerivation_X]
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr i => exact polynomialSymbolicShearSlot_lower w c i

theorem polynomialSymbolicShearDerivation_X_parameter (i : σ) :
    (polynomialSymbolicShearDerivation w c).val (X (Sum.inl i)) = 0 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem polynomialSymbolicShearDerivation_X_slot (i : Fin d) :
    (polynomialSymbolicShearDerivation w c).val (X (Sum.inr i)) =
      polynomialSymbolicShearSlot w c i := MvPolynomial.mkDerivation_X _ _ _

theorem polynomialSymbolicShearDerivation_total_degree
    (hc : ∀ a, c a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a))
    (i : σ ⊕ Fin d) :
    (polynomialSymbolicShearDerivation w c).val (X i) ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (Sum.elim (fun _ : σ => 1) w i) := by
  classical
  cases i with
  | inl i => rw [polynomialSymbolicShearDerivation_X_parameter]; exact Submodule.zero_mem _
  | inr i =>
    rw [polynomialSymbolicShearDerivation_X_slot]
    apply Submodule.sum_mem
    intro a ha
    split_ifs with hi
    · simpa only [hi, Sum.elim_inr] using polynomialSymbolicShearTerm_total_degree w c hc a
    · exact Submodule.zero_mem _

theorem polynomialSymbolicShearExp_total_degree
    (hc : ∀ a, c a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a))
    {P : MvPolynomial (σ ⊕ Fin d) ℝ} {n : ℕ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n) :
    polynomialShearExp (polynomialSymbolicShearDerivation w c) P ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n :=
  polynomialShearExp_weightedSupportLE _ (polynomialSymbolicShearDerivation_total_degree w c hc) hP

end Erdos3

end

section

namespace Erdos3
open MvPolynomial
variable {σ : Type*} {d : ℕ} (p : σ → ℕ) (w : Fin d → ℕ)
variable [Fintype (PolynomialShearIndex w)]
variable (c : PolynomialShearIndex w → MvPolynomial σ ℝ)

private theorem weighted_symbolic_rename_degree {ι κ : Type*} (v : ι → ℕ) (z : κ → ℕ)
    (f : ι → κ) (hf : ∀ i, z (f i) = v i)
    {P : MvPolynomial ι ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE v n) :
    rename f P ∈ weightedSupportLE z n := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval v z _ _ hP
  intro i
  simpa only [Function.comp_apply, hf] using weightedSupportLE_X (R := ℝ) z (f i)

omit [Fintype (PolynomialShearIndex w)] in
theorem polynomialSymbolicShearTerm_weighted_degree
    (hc : ∀ a, c a ∈ weightedSupportLE p (polynomialShearDeficit w a))
    (a : PolynomialShearIndex w) :
    polynomialSymbolicShearTerm w c a ∈
      weightedSupportLE (Sum.elim p w) (w a.1) := by
  have hp := weighted_symbolic_rename_degree p
    (Sum.elim p w) Sum.inl (fun _ => rfl) (hc a)
  have hm := weighted_symbolic_rename_degree w (Sum.elim p w)
    Sum.inr (fun _ => rfl) (weightedSupportLE_monomial w a.2.val (1 : ℝ))
  apply weightedSupportLE_mono _ (weightedSupportLE_mul hp hm)
  have ha := a.2.property
  unfold polynomialShearDeficit
  omega

theorem polynomialSymbolicShearDerivation_weighted_degree
    (hc : ∀ a, c a ∈ weightedSupportLE p (polynomialShearDeficit w a))
    (i : σ ⊕ Fin d) :
    (polynomialSymbolicShearDerivation w c).val (X i) ∈
      weightedSupportLE (Sum.elim p w) (Sum.elim p w i) := by
  classical
  cases i with
  | inl i => rw [polynomialSymbolicShearDerivation_X_parameter]; exact Submodule.zero_mem _
  | inr i =>
    rw [polynomialSymbolicShearDerivation_X_slot]
    apply Submodule.sum_mem
    intro a ha
    split_ifs with hi
    · simpa only [hi, Sum.elim_inr] using polynomialSymbolicShearTerm_weighted_degree p w c hc a
    · exact Submodule.zero_mem _

theorem polynomialSymbolicShearExp_weighted_degree
    (hc : ∀ a, c a ∈ weightedSupportLE p (polynomialShearDeficit w a))
    {P : MvPolynomial (σ ⊕ Fin d) ℝ} {n : ℕ}
    (hP : P ∈ weightedSupportLE (Sum.elim p w) n) :
    polynomialShearExp (polynomialSymbolicShearDerivation w c) P ∈
      weightedSupportLE (Sum.elim p w) n :=
  polynomialShearExp_weightedSupportLE _ (polynomialSymbolicShearDerivation_weighted_degree p w c hc) hP

end Erdos3

end

end OAI
