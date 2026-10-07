import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {D : ℕ} {R : Type*} [CommRing R]

noncomputable def earlierSlotMatrix (m : (i : Fin D) → Fin i.val → R) :
    Matrix (Fin D) (Fin D) R := fun i j =>
  ∑ k : Fin i.val, if earlierSlot i k = j then m i k else 0

theorem earlierSlotMatrix_strict (m : (i : Fin D) → Fin i.val → R)
    (i j : Fin D) (hij : i ≤ j) : earlierSlotMatrix m i j = 0 := by
  classical
  have hne (k : Fin i.val) : earlierSlot i k ≠ j := by
    intro heq
    have hval := congrArg Fin.val heq
    have hi := k.isLt
    change k.val = j.val at hval
    change i.val ≤ j.val at hij
    omega
  simp [earlierSlotMatrix, hne]

theorem earlierSlotMatrix_mulVec (m : (i : Fin D) → Fin i.val → R)
    (x : Fin D → R) (i : Fin D) :
    (earlierSlotMatrix m).mulVec x i = ∑ k : Fin i.val, m i k * x (earlierSlot i k) := by
  classical
  simp only [earlierSlotMatrix, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [ite_mul, zero_mul]
  simp

theorem det_one_sub_strictLower (M : Matrix (Fin D) (Fin D) R)
    (hM : ∀ i j, i ≤ j → M i j = 0) : (1 - M).det = 1 := by
  have htri : (1 - M).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    simp [Matrix.sub_apply, hM i j hij.le, Matrix.one_apply_ne hij.ne]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  apply Finset.prod_eq_one
  intro i _
  simp [Matrix.sub_apply, hM i i le_rfl]

variable {σ : Type*}

noncomputable def polynomialMatrixAction (M : Matrix (Fin D) (Fin D) R)
    (C₀ : Fin D → MvPolynomial σ R) : Fin D → MvPolynomial σ R :=
  fun i => ∑ j, M i j • C₀ j

theorem polynomialMatrixAction_degree (M : Matrix (Fin D) (Fin D) R)
    (C₀ : Fin D → MvPolynomial σ R) {h : ℕ}
    (hC : ∀ i, C₀ i ∈ weightedSupportLE (fun _ : σ => 1) h) :
    ∀ i, polynomialMatrixAction M C₀ i ∈ weightedSupportLE (fun _ : σ => 1) h := by
  intro i
  exact (weightedSupportLE _ _).sum_mem
    (fun j _ => (weightedSupportLE _ _).smul_mem _ (hC j))

theorem polynomialMatrixAction_eval (M : Matrix (Fin D) (Fin D) R)
    (C₀ : Fin D → MvPolynomial σ R) (t : σ → R) :
    (fun i => aeval t (polynomialMatrixAction M C₀ i)) =
      M.mulVec (fun i => aeval t (C₀ i)) := by
  ext i
  simp [polynomialMatrixAction, Matrix.mulVec, dotProduct]

theorem polynomial_affine_origin (M : Matrix (Fin D) (Fin D) R)
    (hM : ∀ i j, i ≤ j → M i j = 0)
    (C₀ : Fin D → MvPolynomial σ R) {h : ℕ}
    (hC : ∀ i, C₀ i ∈ weightedSupportLE (fun _ : σ => 1) h) :
    ∃ P : Fin D → MvPolynomial σ R,
      (∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) h) ∧
      ∀ t : σ → R, (1 - M).mulVec (fun i => aeval t (P i)) =
        (fun i => aeval t (C₀ i)) := by
  refine ⟨polynomialMatrixAction (1 - M)⁻¹ C₀,
    polynomialMatrixAction_degree _ C₀ hC, ?_⟩
  intro t
  rw [polynomialMatrixAction_eval, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (by rw [det_one_sub_strictLower M hM]; exact isUnit_one),
    Matrix.one_mulVec]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

namespace PolynomialSlots

variable {σ : Type*} {D E : ℕ} {w : Fin (D + E) → ℕ}

theorem lowest_prefix_slotAffine (A : PolynomialSlots σ (D + E) w)
    {h : ℕ} (hh : 0 < h) (hw : ∀ i : Fin D, w (i.castAdd E) = h) (i : Fin D) :
    SlotAffine h (A.center (i.castAdd E)) := by
  apply slotAffine_of_weightedSupport hh
  have hweight : patchVariableWeight w (i.castAdd E) =
      lowestSlotWeight (σ := σ) (τ := Fin i.val) h := by
    funext v
    cases v with
    | inl a => rfl
    | inr j =>
      exact hw ⟨j.val, lt_trans j.isLt i.isLt⟩
  rw [← hweight, ← hw i]
  exact A.degree (i.castAdd E)

theorem exists_lowest_affine_prefix (A : PolynomialSlots σ (D + E) w)
    {h : ℕ} (hh : 0 < h) (hw : ∀ i : Fin D, w (i.castAdd E) = h) :
    ∃ (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
      (P : Fin D → MvPolynomial σ ℝ),
      (∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) h) ∧
      ∀ t : σ → ℝ, (A.slots t).takePrefix =
        TriangularSlots.affineBlock M hM (fun i => aeval t (P i)) := by
  classical
  have hrows := A.lowest_prefix_slotAffine hh hw
  choose C₀ m hC hrow using hrows
  let M := earlierSlotMatrix m
  have hM : ∀ i j, i ≤ j → M i j = 0 := earlierSlotMatrix_strict m
  have hcenter (t : σ → ℝ) (x : Fin D → ℝ) (i : Fin D) :
      (A.slots t).takePrefix.center x i = aeval t (C₀ i) + M.mulVec x i := by
    change aeval (Sum.elim t (fun j =>
      Fin.append x 0 (earlierSlot (i.castAdd E) j))) (A.center (i.castAdd E)) = _
    have hargs : (fun j : Fin i.val => Fin.append x 0 (earlierSlot (i.castAdd E) j)) =
        (fun j => x (earlierSlot i j)) := by
      funext j
      change Fin.append x 0 ((earlierSlot i j).castAdd E) = _
      exact Fin.append_left _ _ _
    calc
      _ = aeval (Sum.elim t (fun j => x (earlierSlot i j))) (A.center (i.castAdd E)) :=
        congrArg (fun f : Fin i.val → ℝ => aeval (Sum.elim t f) (A.center (i.castAdd E))) hargs
      _ = aeval t (C₀ i) + ∑ j, m i j * x (earlierSlot i j) := hrow i t _
      _ = _ := congrArg (fun z => aeval t (C₀ i) + z) (earlierSlotMatrix_mulVec m x i).symm
  obtain ⟨P, hP, hsolve⟩ := polynomial_affine_origin M hM C₀ hC
  refine ⟨M, hM, P, hP, ?_⟩
  intro t
  apply TriangularSlots.ext
  intro x i
  rw [hcenter]
  change aeval t (C₀ i) + M.mulVec x i =
    aeval t (P i) + M.mulVec (x - fun j => aeval t (P j)) i
  rw [Matrix.mulVec_sub]
  have hs := hsolve t
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hs
  have hi := congrFun hs i
  simp only [Pi.sub_apply] at hi ⊢
  linarith

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E h : ℕ}

structure LowestLayerModel (A : PolynomialPatch σ s (D + E)) (h : ℕ) where
  matrix : Matrix (Fin D) (Fin D) ℝ
  strict : ∀ i j, i ≤ j → matrix i j = 0
  origin : Fin D → MvPolynomial σ ℝ
  degree : ∀ i, origin i ∈ weightedSupportLE (fun _ : σ => 1) h
  weights : ∀ i : Fin D, A.weight (i.castAdd E) = h
  form_eq : ∀ t : σ → ℝ, (A.form.slots t).takePrefix =
    TriangularSlots.affineBlock matrix strict (fun i => aeval t (origin i))

theorem nonempty_lowestLayerModel (A : PolynomialPatch σ s (D + E))
    (hh : 0 < h) (hw : ∀ i : Fin D, A.weight (i.castAdd E) = h) :
    Nonempty (A.LowestLayerModel h) := by
  obtain ⟨M, hM, P, hP, heq⟩ := A.form.exists_lowest_affine_prefix hh hw
  exact ⟨⟨M, hM, P, hP, hw, heq⟩⟩

noncomputable def lowestLayerModel (A : PolynomialPatch σ s (D + E))
    (hh : 0 < h) (hw : ∀ i : Fin D, A.weight (i.castAdd E) = h) :
    A.LowestLayerModel h := Classical.choice (A.nonempty_lowestLayerModel hh hw)

theorem LowestLayerModel.exists_freeze (A : PolynomialPatch σ s (D + E))
    (L : A.LowestLayerModel h) (U : Set (σ → ℝ))
    (I : Fin D → MvPolynomial σ ℝ) (v : (σ → ℝ) → Fin D → ℤ)
    (hI : ∀ i, I i ∈ weightedSupportLE (fun _ : σ => 1) h)
    (hint : ∀ t ∈ U, ∀ i, aeval t (I i) = (v t i : ℝ))
    (t₀ : σ → ℝ) (ht₀ : t₀ ∈ U) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots t₀).residual bref) ≠ 0)
    {ε : ℝ} (hε : ε < 1 / 12)
    (hosc : ∀ t ∈ U, ‖(1 - L.matrix).mulVec
      ((fun i => aeval t (L.origin i) - aeval t (I i)) -
        (fun i => aeval t₀ (L.origin i) - aeval t₀ (I i)))‖ ≤ ε) :
    ∃ F : PolynomialPatch σ s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ t ∈ U, dist (A.value t) (F.value t) ≤ A.kernel.lip * ε := by
  apply A.exists_freeze_affine_layer L.matrix L.strict U
    (fun t i => aeval t (L.origin i)) I v
    (fun i => by rw [L.weights i]; exact hI i) hint
    (fun t _ => L.form_eq t) t₀ ht₀ bref href hε
  exact hosc

end PolynomialPatch
end Erdos3

end

end OAI
