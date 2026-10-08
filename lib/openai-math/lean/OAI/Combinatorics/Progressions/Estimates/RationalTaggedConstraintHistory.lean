/- Modified for ProveIt: import Lean 4.32 compatibility declarations and give the
full tagged detection conversion a finite local checking budget.
Statements and mathematical proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import Mathlib.Algebra.MvPolynomial.Rename
import OAI.Combinatorics.Progressions.Estimates.RestrictedGradeMajorMatching

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem lowTaggedIndex_injective (d : ℕ) :
    Function.Injective (lowTaggedIndex J d) := by
  intro i k h
  apply (Fintype.equivFin (LowTaggedIndex J d)).symm.injective
  apply Subtype.ext
  exact h

theorem lowTaggedIndex_mem_range_iff (d : ℕ) (i : Σ j, J j) :
    i ∈ Set.range (lowTaggedIndex J d) ↔ i.1.val + 1 ≤ d := by
  constructor
  · rintro ⟨k, rfl⟩
    exact lowTaggedIndex_property J d k
  · intro hi
    refine ⟨lowTaggedSlot J d i.1 hi i.2, ?_⟩
    exact lowTaggedIndex_slot J d i.1 hi i.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

abbrev fullTaggedVariableWeight : X ⊕ (Σ j, J j) → ℕ :=
  Sum.elim (fun _ => 1) (fun i => i.1.val + 1)

noncomputable abbrev lowTaggedVariableWeight (d : ℕ) :
    X ⊕ Fin (Fintype.card (LowTaggedIndex J d)) → ℕ :=
  Sum.elim (fun _ => 1) (lowTaggedWeight J d)

noncomputable def lowTaggedVariableEmbedding (d : ℕ) :
    (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ↪ (X ⊕ (Σ j, J j)) :=
  (Function.Embedding.refl X).sumMap ⟨lowTaggedIndex J d, lowTaggedIndex_injective J d⟩

@[simp] theorem lowTaggedVariableEmbedding_inl (d : ℕ) (x : X) :
    lowTaggedVariableEmbedding (X := X) J d (Sum.inl x) = Sum.inl x := rfl

@[simp] theorem lowTaggedVariableEmbedding_inr (d : ℕ)
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedVariableEmbedding (X := X) J d (Sum.inr i) =
      Sum.inr (lowTaggedIndex J d i) := rfl

theorem lowTaggedVariableEmbedding_injective (d : ℕ) :
    Function.Injective (lowTaggedVariableEmbedding (X := X) J d) :=
  (lowTaggedVariableEmbedding J d).injective

@[simp] theorem lowTaggedVariableEmbedding_weight (d : ℕ)
    (v : X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) :
    fullTaggedVariableWeight J (lowTaggedVariableEmbedding J d v) =
      lowTaggedVariableWeight J d v := by
  cases v <;> rfl

omit [∀ j, Fintype (J j)] in
theorem fullTaggedVariableWeight_pos (v : X ⊕ (Σ j, J j)) :
    0 < fullTaggedVariableWeight J v := by
  cases v with
  | inl x => exact Nat.zero_lt_one
  | inr i => exact Nat.succ_pos _

@[simp] theorem lowTaggedVariableEmbedding_slot (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (k : J j) :
    lowTaggedVariableEmbedding (X := X) J d (Sum.inr (lowTaggedSlot J d j hj k)) =
      Sum.inr ⟨j, k⟩ := by
  simp only [lowTaggedVariableEmbedding_inr, lowTaggedIndex_slot]

theorem lowTaggedVariableEmbedding_inr_mem_range_iff (d : ℕ) (i : Σ j, J j) :
    (Sum.inr i : X ⊕ (Σ j, J j)) ∈ Set.range (lowTaggedVariableEmbedding J d) ↔
      i.1.val + 1 ≤ d := by
  constructor
  · rintro ⟨v, hv⟩
    cases v with
    | inl x => simp only [lowTaggedVariableEmbedding_inl, Sum.inl_ne_inr] at hv
    | inr n =>
      have hn : lowTaggedIndex J d n = i := Sum.inr.inj hv
      rw [← hn]
      exact lowTaggedIndex_property J d n
  · intro hi
    exact ⟨Sum.inr (lowTaggedSlot J d i.1 hi i.2), lowTaggedVariableEmbedding_slot J d i.1 hi i.2⟩

theorem lowTaggedVariableEmbedding_high_not_mem_range (d : ℕ) (j : Fin m)
    (hj : d < j.val + 1) (k : J j) :
    (Sum.inr ⟨j, k⟩ : X ⊕ (Σ j, J j)) ∉ Set.range (lowTaggedVariableEmbedding J d) := by
  rw [lowTaggedVariableEmbedding_inr_mem_range_iff]
  exact not_le_of_gt hj

theorem lowTaggedVariableEmbedding_mem_range_of_weight_le (d : ℕ)
    (v : X ⊕ (Σ j, J j)) (hv : fullTaggedVariableWeight J v ≤ d) :
    v ∈ Set.range (lowTaggedVariableEmbedding J d) := by
  cases v with
  | inl x => exact ⟨Sum.inl x, rfl⟩
  | inr i => exact (lowTaggedVariableEmbedding_inr_mem_range_iff J d i).mpr hv

theorem lowTaggedVariableEmbedding_comp_sum_elim {A : Type*} (d : ℕ)
    (u : X → A) (z : (Σ j, J j) → A) :
    (Sum.elim u z) ∘ lowTaggedVariableEmbedding J d =
      Sum.elim u (z ∘ lowTaggedIndex J d) := by
  funext v
  cases v <;> rfl

theorem lowTaggedVariableEmbedding_eval_coordinates (d : ℕ)
    (u : X → ℝ) (z : ∀ j, J j → ℝ) :
    (Sum.elim u (fun i : Σ j, J j => z i.1 i.2)) ∘ lowTaggedVariableEmbedding J d =
      Sum.elim u (lowTaggedCoordinates J d z) := by
  funext v
  cases v <;> rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R : Type*} [CommRing R]

noncomputable def lowTaggedRestrictionVariables (k : ℕ) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R := by
  classical
  exact Sum.elim (fun x => MvPolynomial.X (Sum.inl x))
    (fun a => if h : a.1.val + 1 ≤ k then
      MvPolynomial.X (Sum.inr (lowTaggedSlot J k a.1 h a.2)) else 0)

noncomputable def lowTaggedRestrict (k : ℕ) :
    MvPolynomial (X ⊕ (Σ j, J j)) R →ₐ[R]
      MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R :=
  aeval (lowTaggedRestrictionVariables (X := X) (R := R) J k)

 theorem lowTaggedRestrictionVariables_isWeightedHomogeneous (k : ℕ)
    (i : X ⊕ (Σ j, J j)) :
    (lowTaggedRestrictionVariables (R := R) J k i).IsWeightedHomogeneous
      (lowTaggedVariableWeight J k) (fullTaggedVariableWeight J i) := by
  classical
  cases i with
  | inl x => exact isWeightedHomogeneous_X (R := R) (lowTaggedVariableWeight J k) (Sum.inl x)
  | inr a =>
    by_cases h : a.1.val + 1 ≤ k
    · simp only [lowTaggedRestrictionVariables, Sum.elim_inr, dite_eq_left h]
      have he : lowTaggedVariableWeight (X := X) J k (Sum.inr (lowTaggedSlot J k a.1 h a.2)) =
          a.1.val + 1 := by
        simp only [lowTaggedVariableWeight, Sum.elim_inr, lowTaggedWeight, lowTaggedIndex_slot]
      exact he ▸ isWeightedHomogeneous_X (R := R) (lowTaggedVariableWeight J k)
        (Sum.inr (lowTaggedSlot J k a.1 h a.2))
    · simp only [lowTaggedRestrictionVariables, Sum.elim_inr, dite_eq_right h]
      exact isWeightedHomogeneous_zero R _ _

 theorem lowTaggedRestrict_isWeightedHomogeneous (k : ℕ)
    {P : MvPolynomial (X ⊕ (Σ j, J j)) R} {n : ℕ}
    (hP : P.IsWeightedHomogeneous (fullTaggedVariableWeight J) n) :
    (lowTaggedRestrict J k P).IsWeightedHomogeneous (lowTaggedVariableWeight J k) n :=
  aeval_isWeightedHomogeneous _ _ _ (lowTaggedRestrictionVariables_isWeightedHomogeneous J k) hP

 theorem lowTaggedRestrict_weightedSupportLE (k : ℕ)
    {P : MvPolynomial (X ⊕ (Σ j, J j)) R} {n : ℕ}
    (hP : P ∈ weightedSupportLE (fullTaggedVariableWeight J) n) :
    lowTaggedRestrict J k P ∈ weightedSupportLE (lowTaggedVariableWeight J k) n := by
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro i α hα
  exact (lowTaggedRestrictionVariables_isWeightedHomogeneous (R := R) J k i
    (mem_support_iff.mp hα)).le

 theorem lowTaggedRestrict_weightedHomogeneousComponent (k n : ℕ)
    (P : MvPolynomial (X ⊕ (Σ j, J j)) R) :
    lowTaggedRestrict J k (weightedHomogeneousComponent (fullTaggedVariableWeight J) n P) =
      weightedHomogeneousComponent (lowTaggedVariableWeight J k) n (lowTaggedRestrict J k P) :=
  aeval_weightedHomogeneousComponent _ _ _ (lowTaggedRestrictionVariables_isWeightedHomogeneous J k) n P

 theorem rename_lowTaggedRestrictionVariables_of_weight_le (k : ℕ)
    (i : X ⊕ (Σ j, J j)) (hi : fullTaggedVariableWeight J i ≤ k) :
    rename (lowTaggedVariableEmbedding J k) (lowTaggedRestrictionVariables (R := R) J k i) = MvPolynomial.X i := by
  classical
  cases i with
  | inl x => simp only [lowTaggedRestrictionVariables, Sum.elim_inl, rename_X,
      lowTaggedVariableEmbedding_inl]
  | inr a =>
    have ha : a.1.val + 1 ≤ k := hi
    simp only [lowTaggedRestrictionVariables, Sum.elim_inr, dite_eq_left ha, rename_X,
      lowTaggedVariableEmbedding_slot]

theorem rename_lowTaggedRestrict (k : ℕ) (P : MvPolynomial (X ⊕ (Σ j, J j)) R)
    (hP : P ∈ weightedSupportLE (fullTaggedVariableWeight J) k) :
    rename (lowTaggedVariableEmbedding J k) (lowTaggedRestrict J k P) = P := by
  classical
  have hcomp : (rename (R := R) (lowTaggedVariableEmbedding (X := X) J k)).comp
      (lowTaggedRestrict J k) =
      aeval (fun i => rename (lowTaggedVariableEmbedding J k)
        (lowTaggedRestrictionVariables (R := R) J k i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, lowTaggedRestrict, aeval_X]
  change ((rename (lowTaggedVariableEmbedding J k)).comp (lowTaggedRestrict J k)) P = P
  rw [hcomp]
  calc
    _ = aeval (MvPolynomial.X : (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) R) P :=
      aeval_eq_of_weightedSupportLE hP _ _
        (rename_lowTaggedRestrictionVariables_of_weight_le J k)
    _ = P := by simp

 theorem lowTaggedRestrict_eval (k : ℕ) (P : MvPolynomial (X ⊕ (Σ j, J j)) R)
    (hP : P ∈ weightedSupportLE (fullTaggedVariableWeight J) k)
    (u : X → R) (z : (Σ j, J j) → R) :
    MvPolynomial.eval (Sum.elim u z) P =
      MvPolynomial.eval (Sum.elim u (z ∘ lowTaggedIndex J k)) (lowTaggedRestrict J k P) := by
  conv_lhs => rw [← rename_lowTaggedRestrict J k P hP]
  rw [eval_rename, lowTaggedVariableEmbedding_comp_sum_elim]

 theorem lowTaggedRestrict_eval_coordinates (k : ℕ)
    (P : MvPolynomial (X ⊕ (Σ j, J j)) ℝ)
    (hP : P ∈ weightedSupportLE (fullTaggedVariableWeight J) k)
    (u : X → ℝ) (z : ∀ j, J j → ℝ) :
    MvPolynomial.eval (Sum.elim u (fun a : Σ j, J j => z a.1 a.2)) P =
      MvPolynomial.eval (Sum.elim u (lowTaggedCoordinates J k z)) (lowTaggedRestrict J k P) :=
  lowTaggedRestrict_eval J k P hP u (fun a => z a.1 a.2)

 theorem lowTaggedRestrict_eval₂ {S : Type*} [CommRing S] (φ : R →+* S)
    (k : ℕ) (P : MvPolynomial (X ⊕ (Σ j, J j)) R)
    (hP : P ∈ weightedSupportLE (fullTaggedVariableWeight J) k)
    (u : X → S) (z : (Σ j, J j) → S) :
    MvPolynomial.eval₂ φ (Sum.elim u z) P =
      MvPolynomial.eval₂ φ (Sum.elim u (z ∘ lowTaggedIndex J k)) (lowTaggedRestrict J k P) := by
  conv_lhs => rw [← rename_lowTaggedRestrict J k P hP]
  rw [MvPolynomial.eval₂_rename, lowTaggedVariableEmbedding_comp_sum_elim]

 theorem lowTaggedRestrict_eval₂_coordinates (φ : R →+* ℝ) (k : ℕ)
    (P : MvPolynomial (X ⊕ (Σ j, J j)) R)
    (hP : P ∈ weightedSupportLE (fullTaggedVariableWeight J) k)
    (u : X → ℝ) (z : ∀ j, J j → ℝ) :
    MvPolynomial.eval₂ φ (Sum.elim u (fun a : Σ j, J j => z a.1 a.2)) P =
      MvPolynomial.eval₂ φ (Sum.elim u (lowTaggedCoordinates J k z)) (lowTaggedRestrict J k P) :=
  lowTaggedRestrict_eval₂ J φ k P hP u (fun a => z a.1 a.2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R : Type*} [CommRing R]

theorem lowTaggedRestrict_eq_killCompl (k : ℕ) :
    lowTaggedRestrict (X := X) (R := R) J k =
      killCompl (lowTaggedVariableEmbedding (X := X) J k).injective := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl x =>
    simp only [lowTaggedRestrict, aeval_X, lowTaggedRestrictionVariables, Sum.elim_inl]
    simpa only [rename_X, lowTaggedVariableEmbedding_inl] using
      (killCompl_rename_app (lowTaggedVariableEmbedding (X := X) J k).injective
        (MvPolynomial.X (Sum.inl x) : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R)).symm
  | inr a =>
    by_cases ha : a.1.val + 1 ≤ k
    · simp only [lowTaggedRestrict, aeval_X, lowTaggedRestrictionVariables,
        Sum.elim_inr, dite_eq_left ha]
      simpa only [rename_X, lowTaggedVariableEmbedding_slot] using
        (killCompl_rename_app (lowTaggedVariableEmbedding (X := X) J k).injective
          (MvPolynomial.X (Sum.inr (lowTaggedSlot J k a.1 ha a.2)) :
            MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R)).symm
    · have hn : (Sum.inr a : X ⊕ (Σ j, J j)) ∉
          Set.range (lowTaggedVariableEmbedding J k) := by
        rwa [lowTaggedVariableEmbedding_inr_mem_range_iff]
      simp only [lowTaggedRestrict, aeval_X, lowTaggedRestrictionVariables,
        Sum.elim_inr, dite_eq_right ha, killCompl, aeval_X, dite_eq_right hn]

@[simp] theorem lowTaggedRestrict_rename (k : ℕ)
    (Q : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R) :
    lowTaggedRestrict J k (rename (lowTaggedVariableEmbedding J k) Q) = Q := by
  rw [lowTaggedRestrict_eq_killCompl, killCompl_rename_app]

theorem lowTaggedRestrict_coeff (k : ℕ)
    (P : MvPolynomial (X ⊕ (Σ j, J j)) R)
    (α : (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) →₀ ℕ) :
    (lowTaggedRestrict J k P).coeff α =
      P.coeff (α.embDomain (lowTaggedVariableEmbedding J k)) := by
  rw [lowTaggedRestrict_eq_killCompl, coeff_killCompl, Finsupp.embDomain_eq_mapDomain]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R S V : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V]

noncomputable def lowTaggedVectorRestrict (k : ℕ) :
    VectorPolynomial (X ⊕ (Σ j, J j)) R V →ₗ[R]
      VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V :=
  (lowTaggedRestrict (X := X) (R := R) J k).toLinearMap.rTensor V

noncomputable def lowTaggedVectorExtend (k : ℕ) :
    VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V →ₗ[R]
      VectorPolynomial (X ⊕ (Σ j, J j)) R V :=
  (MvPolynomial.rename (R := R) (lowTaggedVariableEmbedding (X := X) J k)).toLinearMap.rTensor V

@[simp] theorem lowTaggedVectorRestrict_tmul (k : ℕ)
    (P : MvPolynomial (X ⊕ (Σ j, J j)) R) (v : V) :
    lowTaggedVectorRestrict J k (P ⊗ₜ[R] v) = lowTaggedRestrict J k P ⊗ₜ[R] v := rfl

@[simp] theorem lowTaggedVectorExtend_tmul (k : ℕ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R) (v : V) :
    lowTaggedVectorExtend J k (P ⊗ₜ[R] v) =
      MvPolynomial.rename (lowTaggedVariableEmbedding J k) P ⊗ₜ[R] v := rfl

theorem lowTaggedVectorExtend_restrict (k : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : DegreeLE (fullTaggedVariableWeight J) k P) :
    lowTaggedVectorExtend J k (lowTaggedVectorRestrict J k P) = P := by
  classical
  rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have hαk : Finsupp.weight (fullTaggedVariableWeight J) α ≤ k :=
    (degreeLE_iff _ _ P).mp hP α hα
  rw [monomial, lowTaggedVectorRestrict_tmul, lowTaggedVectorExtend_tmul]
  rw [rename_lowTaggedRestrict J k]
  exact weightedSupportLE_mono hαk
    (weightedSupportLE_monomial (fullTaggedVariableWeight J) α (1 : R))

theorem lowTaggedVectorRestrict_weightedHomogeneousPart (k n : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V) :
    lowTaggedVectorRestrict J k (weightedHomogeneousPart (fullTaggedVariableWeight J) n P) =
      weightedHomogeneousPart (lowTaggedVariableWeight J k) n (lowTaggedVectorRestrict J k P) := by
  induction P using TensorProduct.inductionOn with
  | tmul P v =>
    rw [weightedHomogeneousPart_tmul, lowTaggedVectorRestrict_tmul,
      lowTaggedVectorRestrict_tmul, weightedHomogeneousPart_tmul,
      lowTaggedRestrict_weightedHomogeneousComponent]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem lowTaggedVectorExtend_weightedHomogeneousPart (k n : ℕ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V) :
    lowTaggedVectorExtend J k (weightedHomogeneousPart (lowTaggedVariableWeight J k) n P) =
      weightedHomogeneousPart (fullTaggedVariableWeight J) n (lowTaggedVectorExtend J k P) := by
  have hX (i : X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) :
      (MvPolynomial.X (lowTaggedVariableEmbedding J k i) :
        MvPolynomial (X ⊕ (Σ j, J j)) R).IsWeightedHomogeneous
        (fullTaggedVariableWeight J) (lowTaggedVariableWeight J k i) := by
    rw [← lowTaggedVariableEmbedding_weight J k i]
    exact MvPolynomial.isWeightedHomogeneous_X (R := R)
      (fullTaggedVariableWeight J) (lowTaggedVariableEmbedding J k i)
  induction P using TensorProduct.inductionOn with
  | tmul P v =>
    rw [weightedHomogeneousPart_tmul, lowTaggedVectorExtend_tmul,
      lowTaggedVectorExtend_tmul, weightedHomogeneousPart_tmul]
    simp only [MvPolynomial.rename_eq_aeval]
    exact congrArg (fun Q => Q ⊗ₜ[R] v)
      (aeval_weightedHomogeneousComponent (lowTaggedVariableWeight J k)
        (fullTaggedVariableWeight J) (MvPolynomial.X ∘ lowTaggedVariableEmbedding J k)
        hX n P)
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem lowTaggedVectorRestrict_homogeneous (k : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : ∀ α, Finsupp.weight (fullTaggedVariableWeight J) α ≠ k → coefficients P α = 0)
    (α : (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) →₀ ℕ)
    (hα : Finsupp.weight (lowTaggedVariableWeight J k) α ≠ k) :
    coefficients (lowTaggedVectorRestrict J k P) α = 0 := by
  have h := lowTaggedVectorRestrict_weightedHomogeneousPart J k k P
  rw [weightedHomogeneousPart_eq_self hP] at h
  rw [h]
  exact weightedHomogeneousPart_homogeneous _ _ _ _ hα

section Evaluation

variable [Algebra R S] [Module S V] [IsScalarTower R S V]

theorem lowTaggedVectorExtend_eval₂ (k : ℕ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (x : X ⊕ (Σ j, J j) → S) :
    eval₂ x (lowTaggedVectorExtend J k P) =
      eval₂ (x ∘ lowTaggedVariableEmbedding J k) P := by
  induction P using TensorProduct.inductionOn with
  | tmul P v =>
    rw [lowTaggedVectorExtend_tmul, eval₂_tmul, eval₂_tmul, MvPolynomial.aeval_rename]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem lowTaggedVectorRestrict_eval₂ (k : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : DegreeLE (fullTaggedVariableWeight J) k P)
    (x : X ⊕ (Σ j, J j) → S) :
    eval₂ x P = eval₂ (x ∘ lowTaggedVariableEmbedding J k) (lowTaggedVectorRestrict J k P) := by
  rw [← lowTaggedVectorExtend_eval₂, lowTaggedVectorExtend_restrict J k P hP]

end Evaluation

theorem lowTaggedVectorRestrict_eval_real [Algebra R ℝ] [Module ℝ V] [IsScalarTower R ℝ V]
    (k : ℕ) (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : DegreeLE (fullTaggedVariableWeight J) k P)
    (u : X → ℝ) (z : ∀ j, J j → ℝ) :
    eval₂ (Sum.elim u (fun a : Σ j, J j => z a.1 a.2)) P =
      eval₂ (Sum.elim u (lowTaggedCoordinates J k z)) (lowTaggedVectorRestrict J k P) := by
  rw [lowTaggedVectorRestrict_eval₂ J k P hP, lowTaggedVariableEmbedding_eval_coordinates]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realSymbolGradeQuotientPolynomial_degreeLE
    (w : σ → ℕ) (fast : Submodule ℚ F.AssociatedGraded) (k : ℕ)
    (residual : F.RealPolynomialSymbol w) :
    DegreeLE w k (F.realSymbolGradeQuotientPolynomial b ω hF w fast k residual) := by
  rw [degreeLE_iff]
  intro α hα
  by_contra hle
  exact Finsupp.mem_support_iff.mp hα
    (F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF w fast k residual α
      (ne_of_gt (Nat.lt_of_not_ge hle)))

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded) (k : ℕ)
    (residual : F.RealPolynomialSymbol (fullTaggedVariableWeight (X := X) J))

theorem fullRestrictedGradeQuotient_homogeneous
    (α : (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) →₀ ℕ)
    (hα : Finsupp.weight (lowTaggedVariableWeight J k) α ≠ k) :
    coefficients (lowTaggedVectorRestrict J k
      (F.realSymbolGradeQuotientPolynomial b ω hF
        (fullTaggedVariableWeight J) fast k residual)) α = 0 :=
  lowTaggedVectorRestrict_homogeneous J k _
    (F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF
      (fullTaggedVariableWeight J) fast k residual) α hα

theorem fullRestrictedGradeQuotient_coordinate_homogeneous
    (η : (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) →ₗ[ℝ] ℝ) :
    (coordinate η.toAddMonoidHom (lowTaggedVectorRestrict J k
      (F.realSymbolGradeQuotientPolynomial b ω hF
        (fullTaggedVariableWeight J) fast k residual))).IsWeightedHomogeneous
      (lowTaggedVariableWeight J k) k := by
  intro α hα
  by_contra hweight
  apply hα
  rw [coeff_coordinate,
    F.fullRestrictedGradeQuotient_homogeneous b ω hF J fast k residual α hweight, map_zero]

theorem fullRestrictedGradeQuotient_coordinate_supportLE
    (η : (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) →ₗ[ℝ] ℝ) :
    coordinate η.toAddMonoidHom (lowTaggedVectorRestrict J k
      (F.realSymbolGradeQuotientPolynomial b ω hF
        (fullTaggedVariableWeight J) fast k residual)) ∈
      weightedSupportLE (lowTaggedVariableWeight J k) k := by
  intro α hα
  exact (F.fullRestrictedGradeQuotient_coordinate_homogeneous b ω hF J fast k residual η
    (MvPolynomial.mem_support_iff.mp hα)).le

theorem fullRestrictedGradeQuotient_eval (u : X → ℝ) (z : ∀ j, J j → ℝ) :
    eval₂ (Sum.elim u (fun a : Σ j, J j => z a.1 a.2))
      (F.realSymbolGradeQuotientPolynomial b ω hF
        (fullTaggedVariableWeight J) fast k residual) =
    eval₂ (Sum.elim u (lowTaggedCoordinates J k z))
      (lowTaggedVectorRestrict J k
        (F.realSymbolGradeQuotientPolynomial b ω hF
          (fullTaggedVariableWeight J) fast k residual)) :=
  lowTaggedVectorRestrict_eval_real J k _
    (F.realSymbolGradeQuotientPolynomial_degreeLE b ω hF
      (fullTaggedVariableWeight J) fast k residual) u z

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R S V : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V]

theorem lowTaggedVectorRestrict_coeff (k : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (α : (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) →₀ ℕ) :
    coefficients (lowTaggedVectorRestrict J k P) α =
      coefficients P (α.embDomain (lowTaggedVariableEmbedding J k)) := by
  induction P using TensorProduct.inductionOn with
  | tmul P v =>
    rw [lowTaggedVectorRestrict_tmul, coefficients_tmul, lowTaggedRestrict_coeff,
      coefficients_tmul]
  | add P Q hP hQ => simp only [map_add, Finsupp.add_apply, hP, hQ]

theorem coordinate_lowTaggedVectorRestrict (k : ℕ) (f : V →+ S)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V) :
    coordinate f (lowTaggedVectorRestrict J k P) = lowTaggedRestrict J k (coordinate f P) := by
  ext α
  rw [coeff_coordinate, lowTaggedVectorRestrict_coeff, lowTaggedRestrict_coeff, coeff_coordinate]

@[simp] theorem lowTaggedVectorExtend_monomial (k : ℕ)
    (α : (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) →₀ ℕ) (v : V) :
    lowTaggedVectorExtend J k (monomial (R := R) α v) =
      monomial (α.mapDomain (lowTaggedVariableEmbedding J k)) v := by
  rw [monomial, lowTaggedVectorExtend_tmul, MvPolynomial.rename_monomial]
  rfl

theorem coordinate_lowTaggedVectorExtend (k : ℕ) (f : V →+ S)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V) :
    coordinate f (lowTaggedVectorExtend J k P) =
      MvPolynomial.rename (lowTaggedVariableEmbedding J k) (coordinate f P) := by
  classical
  rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum, coordinate_sum, lowTaggedVectorExtend_monomial,
    coordinate_monomial, MvPolynomial.rename_monomial]

@[simp] theorem lowTaggedVectorRestrict_extend (k : ℕ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V) :
    lowTaggedVectorRestrict J k (lowTaggedVectorExtend J k P) = P := by
  induction P using TensorProduct.inductionOn with
  | tmul P v =>
    rw [lowTaggedVectorExtend_tmul, lowTaggedVectorRestrict_tmul, lowTaggedRestrict_rename]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem lowTaggedVectorExtend_injective (k : ℕ) :
    Function.Injective (lowTaggedVectorExtend (X := X) (R := R) (V := V) J k) := by
  intro P Q h
  have he := congrArg (lowTaggedVectorRestrict J k) h
  simpa only [lowTaggedVectorRestrict_extend] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem abs_coeff_rename_le {σ τ : Type*} (e : σ ↪ τ)
    (P : MvPolynomial σ ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ α, |P.coeff α| ≤ C) (β : τ →₀ ℕ) :
    |(MvPolynomial.rename e P).coeff β| ≤ C := by
  by_cases hz : (MvPolynomial.rename e P).coeff β = 0
  · simpa only [hz, abs_zero] using hC
  · obtain ⟨α, hα, _⟩ := MvPolynomial.coeff_rename_ne_zero e P β hz
    rw [← hα, MvPolynomial.coeff_rename_mapDomain e e.injective]
    exact hP α

namespace VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
  {X R V η : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem lowTaggedVectorExtend_coordinate_coefficient_bound (k : ℕ)
    (f : η → V →+ ℝ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ j α, |f j (coefficients P α)| ≤ C) :
    ∀ α j, |f j (coefficients (lowTaggedVectorExtend J k P) α)| ≤ C := by
  intro α j
  rw [← coeff_coordinate, coordinate_lowTaggedVectorExtend]
  exact abs_coeff_rename_le (lowTaggedVariableEmbedding J k) (coordinate (f j) P)
    C hC (fun β => by simpa only [coeff_coordinate] using hP j β) α

theorem lowTaggedVectorExtend_coordinate_grid (k : ℕ)
    (f : η → V →+ ℝ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (q : ℕ) (hP : ∀ j, realPolynomialCoefficientGrid q (coordinate (f j) P)) :
    ∀ j, realPolynomialCoefficientGrid q (coordinate (f j) (lowTaggedVectorExtend J k P)) := by
  intro j
  rw [coordinate_lowTaggedVectorExtend]
  exact realPolynomialCoefficientGrid_rename (lowTaggedVariableEmbedding J k) (hP j)

theorem lowTaggedVectorExtend_coefficients_grid (k : ℕ)
    (f : η → V →+ ℝ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (q : ℕ) (hP : ∀ j, realPolynomialCoefficientGrid q (coordinate (f j) P)) :
    ∀ α, (fun j => f j (coefficients (lowTaggedVectorExtend J k P) α)) ∈
      realDenominatorGrid q := by
  intro α
  have hj : ∀ j, ∃ z : ℤ, (z : ℝ) =
      (q : ℝ) * f j (coefficients (lowTaggedVectorExtend J k P) α) := by
    intro j
    obtain ⟨z, hz⟩ := lowTaggedVectorExtend_coordinate_grid J k f P q hP j
    exact ⟨z α, by simpa only [coeff_coordinate, Pi.smul_apply, smul_eq_mul] using congrFun hz α⟩
  choose z hz using hj
  exact ⟨z, funext hz⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {X κ : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

def fullTaggedGradedBaseIntersection (k : ℕ)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
    (K : κ → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)) :
    Set (X ⊕ (Σ j, J j) → ℝ) :=
  {t | t ∈ K₀ ∧ ∀ i, (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) ∈ K i}

theorem fullTaggedGradedBaseIntersection_subset (k : ℕ)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
    (K : κ → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)) :
    fullTaggedGradedBaseIntersection J k K₀ K ⊆ K₀ := fun _ ht => ht.1

theorem fullTaggedGradedBaseIntersection_rat_dilation (k : ℕ)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
    (K : κ → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ))
    (hK : ∀ i, BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J k) (K i))
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
      (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K₀)
    (t : X ⊕ (Σ j, J j) → ℝ) (ht : t ∈ fullTaggedGradedBaseIntersection J k K₀ K)
    (r : ℚ) :
    (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈
      fullTaggedGradedBaseIntersection J k K₀ K := by
  refine ⟨hK₀ t ht.1 r, ?_⟩
  intro i
  change (fun b => (r : ℝ) ^ fullTaggedVariableWeight J
    (lowTaggedVariableEmbedding J k (Sum.inr b)) *
      t (lowTaggedVariableEmbedding J k (Sum.inr b))) ∈ K i
  simpa only [lowTaggedVariableEmbedding_weight, lowTaggedVariableWeight, Sum.elim_inr] using
    (hK i).coordinate_dilation_mem (lowTaggedWeight J k) (K i) (r : ℝ)
      (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) (ht.2 i)

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)

local notation "base" => Fin (Fintype.card (LowTaggedIndex J k))
local notation "w" => lowTaggedWeight J k
local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)

variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (N : X → ℕ) (budget : ℝ)

local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (majorTranslationTopCoordinates w
    (fun i => lowTaggedPolynomial J k poly i - MvPolynomial.C (c i)))

def FullTaggedDetectedMajorGradeConclusion : Prop :=
  ∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra w k))
    (gen : η → Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w k) M)) → weightedSubalgebra w k)
    (slow rat : VectorPolynomial (X ⊕ base) ℚ quotientReal) (q : ℕ),
    (∀ i, (finrank ℚ (PairAlgebra (weightedSubalgebra w k) M) : ℝ) ≤ budget ∧
      Submodule.span ℚ (Set.range (gen i)) = (detectedfast i).toSubmodule ∧
      BasisGradedSubmodule (weightedBasis w k (lowTaggedWeight_pos J k))
        (weightedBasisGrade w k) (detectedfast i).toSubmodule ∧
      ∀ j a, rationalLogHeight
        ((weightedBasis w k (lowTaggedWeight_pos J k)).repr (gen i j) a) ≤ budget) ∧
    (∀ i, BasisGradedSubmodule (Pi.basisFun ℝ base) w
      (majorPhaseDetectedRealBase J k (detectedfast i))) ∧
    (∀ i h, lowTaggedRetained J k Utag h ≤ majorPhaseDetectedRealBase J k (detectedfast i)) ∧
    (∀ i α, |basis.coord i (coefficients slow α)| ≤ Real.exp budget) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
    (∀ i, realPolynomialCoefficientGrid q (coordinate (basis.coord i).toAddMonoidHom rat)) ∧
    RestrictedMajorGradeCorrectionConclusion (σ := X ⊕ (Σ j, J j)) F b ω hF wt fast lift k Z left right
      (fullTaggedGradedBaseIntersection J k K₀ (fun i => majorPhaseDetectedRealBase J k (detectedfast i)))
      (lowTaggedVectorExtend J k (realChartSubstitute chart slow)) (lowTaggedVectorExtend J k rat)

set_option maxHeartbeats 400000 in
theorem fullTaggedDetectedMajorGradeConclusion_of_vector_detection
    (hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
    (hsection : ∀ y, fast.mkQ (lift y) = y)
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
      (fun i => (r : ℝ) ^ wt i * t i) ∈ K₀)
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation (σ := X ⊕ (Σ j, J j)) b ω hF wt j t
        (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
    (hdetected : MajorPhaseVectorDetectedConclusion (L := M) J k Utag poly c N budget basis
      (lowTaggedVectorRestrict J k
        (F.realSymbolGradeQuotientPolynomial (σ := X ⊕ (Σ j, J j)) b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord))) :
    FullTaggedDetectedMajorGradeConclusion (M := M)
      F b ω hF J k fast basis lift Z left right K₀ Utag poly c N budget := by
  obtain ⟨detectedfast, gen, slow, rat, q, hgen, hgrade, hretain, _, hcoeff,
    hq, hqB, hgrid, _, _, hvalue⟩ := hdetected
  let K := fun i => majorPhaseDetectedRealBase J k (detectedfast i)
  let P := F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord
  have hP : DegreeLE wt k P := by
    rw [degreeLE_iff]
    intro α hα
    by_contra hle
    have hz := F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF wt fast k
      (left⁻¹ * Z * right⁻¹).coord α (ne_of_gt (Nat.lt_of_not_ge hle))
    exact Finsupp.mem_support_iff.mp hα hz
  have hquot : ∀ t ∈ fullTaggedGradedBaseIntersection J k K₀ K,
      fast.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF wt k t (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (lowTaggedVectorExtend J k (realChartSubstitute chart slow)) +
          eval₂ t (lowTaggedVectorExtend J k rat) := by
    intro t ht
    have h := hvalue (fun i => t (Sum.inl i))
      (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) ht.2
    have hsplit : Sum.elim (fun i => t (Sum.inl i))
        (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) =
        t ∘ lowTaggedVariableEmbedding J k := by
      funext i
      cases i <;> rfl
    rw [hsplit] at h
    rw [← F.realSymbolGradeQuotientPolynomial_eval,
      lowTaggedVectorRestrict_eval₂ J k _ hP, lowTaggedVectorExtend_eval₂,
      lowTaggedVectorExtend_eval₂]
    with_reducible exact h
  have hstep := F.restricted_symbol_major_grade_step b ω hF wt fast hfast lift hsection
    k Z left right K₀ (fullTaggedGradedBaseIntersection J k K₀ K)
    (fullTaggedGradedBaseIntersection_subset J k K₀ K)
    (fullTaggedGradedBaseIntersection_rat_dilation J k K₀ K hgrade hK₀)
    (lowTaggedVectorExtend J k (realChartSubstitute chart slow))
    (lowTaggedVectorExtend J k rat) hlower hquot
  unfold FullTaggedDetectedMajorGradeConclusion
  refine ⟨detectedfast, gen, slow, rat, q, hgen, hgrade, hretain,
    hcoeff, hq, hqB, hgrid, ?_⟩
  unfold RestrictedMajorGradeCorrectionConclusion
  with_reducible exact hstep

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open Module RationalFilteredNilmanifold PolynomialTranslationLie

variable {m : ℕ} (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)

noncomputable def majorPhaseRationalTagConstraint {η : Type*} {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k)
    (a : η × {j : Fin m // j.val + 1 ≤ k}) : RationalTagConstraint J where
  tag := a.2.val
  count := count
  generators := majorPhaseTaggedGenerators J k (gen a.1) a.2.val a.2.property

noncomputable def majorPhaseRationalTagConstraints {η : Type*} [Fintype η] {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k) :
    List (RationalTagConstraint J) := by
  classical
  exact (Finset.univ : Finset (η × {j : Fin m // j.val + 1 ≤ k})).toList.map
    (majorPhaseRationalTagConstraint J k gen)

theorem majorPhaseRationalTagConstraints_length {η : Type*} [Fintype η] {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k) :
    (majorPhaseRationalTagConstraints J k gen).length ≤ Fintype.card η * m := by
  classical
  have htag : Fintype.card {j : Fin m // j.val + 1 ≤ k} ≤ m := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun j : Fin m => j.val + 1 ≤ k)
  simpa only [majorPhaseRationalTagConstraints, List.length_map, Finset.length_toList,
    Finset.card_univ, Fintype.card_prod] using Nat.mul_le_mul_left (Fintype.card η) htag

theorem majorPhaseRationalTagConstraints_budget {η : Type*} [Fintype η] {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k) (B : ℝ)
    (hcount : ∀ _a : η, (count : ℝ) ≤ B)
    (hheight : ∀ a i j, rationalLogHeight
      ((weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k)).repr (gen a i) j) ≤ B) :
    ∀ c ∈ majorPhaseRationalTagConstraints J k gen, c.BudgetLE B := by
  classical
  intro c hc
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  refine ⟨hcount a.1, ?_⟩
  exact majorPhaseTaggedGenerators_logHeight J k (gen a.1) (hheight a.1) a.2.val a.2.property

theorem majorPhaseRationalTagConstraints_set_eq
    {X η : Type*} [Fintype η] {count : ℕ}
    (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k)
    (hspan : ∀ a, Submodule.span ℚ (Set.range (gen a)) = (detectedfast a).toSubmodule)
    (hgraded : ∀ a, BasisGradedSubmodule
      (weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k))
      (weightedBasisGrade (lowTaggedWeight J k) k) (detectedfast a).toSubmodule)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ)) :
    fullTaggedGradedBaseIntersection J k K₀
      (fun a => majorPhaseDetectedRealBase J k (detectedfast a)) =
      K₀ ∩ {t | ∀ c ∈ majorPhaseRationalTagConstraints J k gen, c.member t} := by
  classical
  ext t
  change (t ∈ K₀ ∧ ∀ a,
      lowTaggedCoordinates J k (fun j i => t (Sum.inr ⟨j, i⟩)) ∈
        majorPhaseDetectedRealBase J k (detectedfast a)) ↔
    t ∈ K₀ ∧ ∀ c ∈ majorPhaseRationalTagConstraints J k gen, c.member t
  constructor
  · rintro ⟨ht, hmem⟩
    refine ⟨ht, ?_⟩
    intro c hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    exact (majorPhaseTaggedGenerators_mem_iff J k (detectedfast a.1) (gen a.1)
      (hspan a.1) (hgraded a.1) (fun j i => t (Sum.inr ⟨j, i⟩))).mp
      (hmem a.1) a.2.val a.2.property
  · rintro ⟨ht, hmem⟩
    refine ⟨ht, ?_⟩
    intro a
    apply (majorPhaseTaggedGenerators_mem_iff J k (detectedfast a) (gen a)
      (hspan a) (hgraded a) (fun j i => t (Sum.inr ⟨j, i⟩))).mpr
    intro j hj
    apply hmem (majorPhaseRationalTagConstraint J k gen (a, ⟨j, hj⟩))
    exact List.mem_map.mpr ⟨(a, ⟨j, hj⟩), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩

theorem majorPhase_rationalTaggedConstraintCertificate
    {X η : Type*} [Fintype η] {count : ℕ}
    (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ)) (B : ℝ)
    (hgen : ∀ a, (count : ℝ) ≤ B ∧
      Submodule.span ℚ (Set.range (gen a)) = (detectedfast a).toSubmodule ∧
      BasisGradedSubmodule (weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k))
        (weightedBasisGrade (lowTaggedWeight J k) k) (detectedfast a).toSubmodule ∧
      ∀ i j, rationalLogHeight
        ((weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k)).repr (gen a i) j) ≤ B) :
    RationalTaggedConstraintCertificate J K₀
      (fullTaggedGradedBaseIntersection J k K₀
        (fun a => majorPhaseDetectedRealBase J k (detectedfast a))) B (Fintype.card η * m) := by
  refine ⟨majorPhaseRationalTagConstraints J k gen,
    majorPhaseRationalTagConstraints_length J k gen,
    majorPhaseRationalTagConstraints_budget J k gen B (fun a => (hgen a).1)
      (fun a => (hgen a).2.2.2), ?_⟩
  exact majorPhaseRationalTagConstraints_set_eq J k detectedfast gen
    (fun a => (hgen a).2.1) (fun a => (hgen a).2.2.1) K₀

end Erdos3.VectorPolynomial

end

end OAI
