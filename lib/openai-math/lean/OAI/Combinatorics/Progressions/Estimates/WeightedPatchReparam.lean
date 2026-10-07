/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget

namespace OAI

section

namespace Erdos3

open MvPolynomial

theorem aeval_eq_of_weightedSupport {σ R : Type*} [CommRing R]
    {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (x y : σ → R)
    (hxy : ∀ i, w i ≤ d → x i = y i) : aeval x p = aeval y p := by
  classical
  rw [← p.support_sum_monomial_coeff]
  simp only [map_sum, aeval_monomial]
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun z => z ^ α i)
    (hxy i ((Finsupp.le_weight_of_ne_zero' w (Finsupp.mem_support_iff.mp hi)).trans (hp hα)))

def weightedPatchVariableWeight {σ : Type*} {d : ℕ}
    (p : σ → ℕ) (w : Fin d → ℕ) (i : Fin d) : σ ⊕ Fin i.val → ℕ :=
  Sum.elim p (fun j => w (earlierSlot i j))

structure WeightedParameterSlots (σ : Type*) (p : σ → ℕ) (d : ℕ) (w : Fin d → ℕ) where
  center : (i : Fin d) → MvPolynomial (σ ⊕ Fin i.val) ℝ
  degree : ∀ i, center i ∈ weightedSupportLE (weightedPatchVariableWeight p w i) (w i)

namespace WeightedParameterSlots

variable {σ : Type*} {p : σ → ℕ} {d : ℕ} {w : Fin d → ℕ}

noncomputable def slots (A : WeightedParameterSlots σ p d w) (t : σ → ℝ) :
    TriangularSlots d where
  center x i := aeval (Sum.elim t (fun j => x (earlierSlot i j))) (A.center i)
  lower i x y hxy := by
    apply congrArg (fun f : σ ⊕ Fin i.val → ℝ => aeval f (A.center i))
    funext v
    cases v with
    | inl a => rfl
    | inr j => exact hxy (earlierSlot i j) j.isLt

end WeightedParameterSlots

structure WeightedParameterPatch (σ : Type*) (p : σ → ℕ) (s d : ℕ) where
  weight : Fin d → ℕ
  weight_pos : ∀ i, 1 ≤ weight i
  weight_le : ∀ i, weight i ≤ s
  weight_mono : Monotone weight
  form : WeightedParameterSlots σ p d weight
  kernel : PatchKernel d

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

noncomputable def value (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) : ℝ :=
  (A.form.slots t).patchValue A.kernel

theorem value_mem_Icc (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end WeightedParameterPatch

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

def weightedParameters (A : PolynomialPatch σ s d) :
    WeightedParameterPatch σ (fun _ => 1) s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := { center := A.form.center, degree := A.form.degree }
  kernel := A.kernel

@[simp] theorem weightedParameters_value (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.weightedParameters.value t = A.value t := rfl

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace SlotInterleaving

theorem sorted_left_lt_right {D E : ℕ} (w : Fin D → ℕ) (v : Fin E → ℕ)
    (hw : Monotone w) (hv : Monotone v) (i : Fin D) (j : Fin E) (h : w i ≤ v j) :
    (sorted w v hw hv).left i < (sorted w v hw hv).right j := by
  apply stable_sort_symm_lt (Fin.append w v)
  · simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  · simpa only [Fin.append_left, Fin.append_right] using h

end SlotInterleaving

namespace WeightedParameterSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

noncomputable def insertSubstitution (I : SlotInterleaving D E) (k : Fin (D + E))
    (i : Fin E) : (σ ⊕ Fin D) ⊕ Fin i.val → MvPolynomial (σ ⊕ Fin k.val) ℝ :=
  Sum.elim
    (Sum.elim (fun a => X (Sum.inl a))
      (fun j => if h : (I.left j).val < k.val then X (Sum.inr ⟨_, h⟩) else 0))
    (fun j => PolynomialSlots.placementSubstitution I.right k i (Sum.inr j))

theorem insertSubstitution_degree (I : SlotInterleaving D E) (k : Fin (D + E))
    (i : Fin E) (a : (σ ⊕ Fin D) ⊕ Fin i.val) :
    insertSubstitution I k i a ∈ weightedSupportLE (patchVariableWeight (I.fill w v) k)
      (weightedPatchVariableWeight (Sum.elim (fun _ : σ => 1) w) v i a) := by
  rcases a with (a | j) | j
  · exact weightedSupportLE_X _ (Sum.inl a)
  · simp only [insertSubstitution, Sum.elim_inl, Sum.elim_inr]
    split_ifs with h
    · have hX := weightedSupportLE_X (R := ℝ) (patchVariableWeight (σ := σ) (I.fill w v) k)
        (Sum.inr (⟨(I.left j).val, h⟩ : Fin k.val))
      change _ ∈ weightedSupportLE _ (I.fill w v (I.left j)) at hX
      rw [I.fill_left] at hX
      exact hX
    · exact (weightedSupportLE _ _).zero_mem
  · exact PolynomialSlots.placementSubstitution_degree I.right
      (fun j => I.fill_right w v j) k i (Sum.inr j)

noncomputable def insertCenter
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (k : Fin (D + E)) (i : Fin E) :
    MvPolynomial (σ ⊕ Fin k.val) ℝ := aeval (insertSubstitution I k i) (B.center i)

theorem insertCenter_degree
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (k : Fin (D + E)) (i : Fin E) :
    B.insertCenter I k i ∈ weightedSupportLE (patchVariableWeight (I.fill w v) k) (v i) :=
  weightedSupportLE_aeval _ _ _ (insertSubstitution_degree I k i) (B.degree i)

theorem insertCenter_eval
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (hbefore : ∀ j i, w j ≤ v i → I.left j < I.right i)
    (i : Fin E) (t : σ → ℝ) (x : Fin (D + E) → ℝ) :
    aeval (Sum.elim t (fun j => x (earlierSlot (I.right i) j)))
        (B.insertCenter I (I.right i) i) =
      (B.slots (Sum.elim t (fun j => x (I.left j)))).center (fun j => x (I.right j)) i := by
  simp only [insertCenter, MvPolynomial.comp_aeval_apply, slots]
  apply aeval_eq_of_weightedSupport (B.degree i)
  intro a ha
  rcases a with (a | j) | j
  · simp [insertSubstitution]
  · have h : (I.left j).val < (I.right i).val := hbefore j i ha
    simp only [insertSubstitution, Sum.elim_inl, Sum.elim_inr, dite_eq_left h, aeval_X]
    rfl
  · have h : (I.right (earlierSlot i j)).val < (I.right i).val :=
      I.right_strictMono j.isLt
    simp only [insertSubstitution, Sum.elim_inr, PolynomialSlots.placementSubstitution,
      dite_eq_left h, aeval_X]
    rfl

end WeightedParameterSlots

namespace PolynomialSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

noncomputable def insertLifts (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) : PolynomialSlots σ (D + E) (I.fill w v) where
  center k := Fin.addCases (A.placeCenter I.left k) (B.insertCenter I k) (I.perm k)
  degree k := by
    change Fin.addCases (A.placeCenter I.left k) (B.insertCenter I k) (I.perm k) ∈
      weightedSupportLE (patchVariableWeight (I.fill w v) k) (Fin.append w v (I.perm k))
    generalize I.perm k = z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) z
    · simpa only [Fin.addCases_left, Fin.append_left] using
        A.placeCenter_degree I.left (fun j => I.fill_left w v j) k i
    · simpa only [Fin.addCases_right, Fin.append_right] using B.insertCenter_degree I k i

theorem insertLifts_center_left (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (t : σ → ℝ) (x : Fin (D + E) → ℝ) (i : Fin D) :
    ((A.insertLifts B I).slots t).center x (I.left i) =
      (A.slots t).center (fun j => x (I.left j)) i := by
  change aeval _ (Fin.addCases _ _ (I.perm (I.left i))) = _
  rw [show I.perm (I.left i) = i.castAdd E from I.perm.apply_symm_apply _, Fin.addCases_left]
  exact A.placeCenter_eval I.left I.left_strictMono i t x

theorem insertLifts_center_right (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (hbefore : ∀ j i, w j ≤ v i → I.left j < I.right i)
    (t : σ → ℝ) (x : Fin (D + E) → ℝ) (i : Fin E) :
    ((A.insertLifts B I).slots t).center x (I.right i) =
      (B.slots (Sum.elim t (fun j => x (I.left j)))).center (fun j => x (I.right j)) i := by
  change aeval _ (Fin.addCases _ _ (I.perm (I.right i))) = _
  rw [show I.perm (I.right i) = i.natAdd D from I.perm.apply_symm_apply _, Fin.addCases_right]
  exact B.insertCenter_eval I hbefore i t x

theorem insertLifts_residual_left (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (t : σ → ℝ) (z : Fin (D + E) → ℤ) (i : Fin D) :
    ((A.insertLifts B I).slots t).residual z (I.left i) =
      (A.slots t).residual (fun j => z (I.left j)) i := by
  simp only [TriangularSlots.residual, insertLifts_center_left]

theorem insertLifts_residual_right (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (hbefore : ∀ j i, w j ≤ v i → I.left j < I.right i)
    (t : σ → ℝ) (z : Fin (D + E) → ℤ) (i : Fin E) :
    ((A.insertLifts B I).slots t).residual z (I.right i) =
      (B.slots (Sum.elim t (fun j => (z (I.left j) : ℝ)))).residual
        (fun j => z (I.right j)) i := by
  simp only [TriangularSlots.residual, insertLifts_center_right A B I hbefore]

end PolynomialSlots
end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace WeightedParameterSlots

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {d : ℕ} {w : Fin d → ℕ}

noncomputable def parameterSubstitution (f : σ → MvPolynomial τ ℝ) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (τ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => aeval (fun b => X (Sum.inl b)) (f a)) (fun j => X (Sum.inr j))

theorem parameterSubstitution_degree (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) (i : Fin d) (a : σ ⊕ Fin i.val) :
    parameterSubstitution f i a ∈ weightedSupportLE (weightedPatchVariableWeight q w i)
      (weightedPatchVariableWeight p w i a) := by
  cases a with
  | inl a =>
    apply weightedSupportLE_aeval q (weightedPatchVariableWeight q w i)
    · intro b
      exact weightedSupportLE_X _ (Sum.inl b)
    · exact hf a
  | inr j => exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def reparam (A : WeightedParameterSlots σ p d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) : WeightedParameterSlots τ q d w where
  center i := aeval (parameterSubstitution f i) (A.center i)
  degree i := weightedSupportLE_aeval _ _ _ (parameterSubstitution_degree f hf i) (A.degree i)

theorem reparam_slots (A : WeightedParameterSlots σ p d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) (t : τ → ℝ) :
    (A.reparam f hf).slots t = A.slots (fun a => aeval t (f a)) := by
  apply TriangularSlots.ext
  intro x i
  simp only [slots, reparam, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun g : σ ⊕ Fin i.val → ℝ => aeval g (A.center i))
  funext a
  cases a with
  | inl a =>
    simp only [parameterSubstitution, Sum.elim_inl, MvPolynomial.comp_aeval_apply, aeval_X]
  | inr j => simp [parameterSubstitution]

end WeightedParameterSlots

namespace WeightedParameterPatch

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {s d : ℕ}

noncomputable def reparam (A : WeightedParameterPatch σ p s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) : WeightedParameterPatch τ q s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.form.reparam f hf
  kernel := A.kernel

@[simp] theorem reparam_lip (A : WeightedParameterPatch σ p s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) :
    (A.reparam f hf).kernel.lip = A.kernel.lip := rfl

theorem reparam_value (A : WeightedParameterPatch σ p s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) (t : τ → ℝ) :
    (A.reparam f hf).value t = A.value (fun a => aeval t (f a)) := by
  change ((A.form.reparam f hf).slots t).patchValue A.kernel = _
  rw [WeightedParameterSlots.reparam_slots]
  rfl

end WeightedParameterPatch
end Erdos3

end

end OAI
