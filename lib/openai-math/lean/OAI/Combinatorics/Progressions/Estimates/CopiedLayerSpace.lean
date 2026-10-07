import Mathlib.LinearAlgebra.Dimension.Constructions
import OAI.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

def copiedLayerSpace {J K : Type*} (W : Submodule ℝ (J → ℝ)) (V : Submodule ℝ (K → ℝ)) :
    Submodule ℝ (J ⊕ K → ℝ) where
  carrier := {x | (fun j => x (.inl j)) ∈ W ∧ (fun k => x (.inr k)) ∈ V}
  zero_mem' := ⟨W.zero_mem, V.zero_mem⟩
  add_mem' hx hy := ⟨W.add_mem hx.1 hy.1, V.add_mem hx.2 hy.2⟩
  smul_mem' r _ hx := ⟨W.smul_mem r hx.1, V.smul_mem r hx.2⟩

noncomputable def copiedLayerSpaceEquiv {J K : Type*}
    (W : Submodule ℝ (J → ℝ)) (V : Submodule ℝ (K → ℝ)) :
    copiedLayerSpace W V ≃ₗ[ℝ] W × V where
  toFun x := (⟨fun j => x.val (.inl j), x.property.1⟩, ⟨fun k => x.val (.inr k), x.property.2⟩)
  invFun x := ⟨Sum.elim x.1.val x.2.val, x.1.property, x.2.property⟩
  left_inv x := by ext j; cases j <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem copiedLayerSpace_finrank {J K : Type*} [Fintype J] [Fintype K]
    (W : Submodule ℝ (J → ℝ)) (V : Submodule ℝ (K → ℝ)) :
    Module.finrank ℝ (copiedLayerSpace W V) = Module.finrank ℝ W + Module.finrank ℝ V := by
  rw [(copiedLayerSpaceEquiv W V).finrank_eq, Module.finrank_prod]

theorem copiedLayerSpace_line_finrank {J K : Type*} [Fintype J] [Fintype K]
    (W : Submodule ℝ (J → ℝ)) (e : K → ℝ) (he : e ≠ 0) :
    Module.finrank ℝ (copiedLayerSpace W (Submodule.span ℝ {e})) = Module.finrank ℝ W + 1 := by
  rw [copiedLayerSpace_finrank, finrank_span_singleton he]

def copiedLayerMatrix {J K C : Type*} (B : Matrix J C ℚ) (e : K → ℚ) :
    Matrix (J ⊕ K) (Option C) ℚ :=
  Matrix.of (fun j c => match j, c with
    | .inl j, .some c => B j c
    | .inr k, .none => e k
    | _, _ => 0)

def copiedLayerRows {J K V : Type*} (A : Matrix V J ℚ) : Matrix V (J ⊕ K) ℚ :=
  Matrix.of (fun r j => Sum.elim (A r) (fun _ => 0) j)

theorem copiedLayerMatrix_height {J K C : Type*} (B : Matrix J C ℚ) (e : K → ℚ)
    {H He : ℕ} (hH : 1 ≤ H) (hB : ∀ j c, RationalHeightLE (B j c) H)
    (he : ∀ k, RationalHeightLE (e k) He) :
    ∀ j c, RationalHeightLE (copiedLayerMatrix B e j c) (max H He) := by
  intro j c
  cases j <;> cases c
  · exact rationalHeightLE_zero (hH.trans (le_max_left _ _))
  · exact (hB _ _).mono (le_max_left _ _)
  · exact (he _).mono (le_max_right _ _)
  · exact rationalHeightLE_zero (hH.trans (le_max_left _ _))

theorem copiedLayerRows_height {J K V : Type*} (A : Matrix V J ℚ)
    {R : ℕ} (hR : 1 ≤ R) (hA : ∀ r j, RationalHeightLE (A r j) R) :
    ∀ r j, RationalHeightLE (copiedLayerRows (K := K) A r j) R := by
  intro r j
  cases j with
  | inl j => exact hA r j
  | inr _ => exact rationalHeightLE_zero hR

theorem copiedLayerMatrix_real_mulVec {J K C : Type*} [Fintype C]
    (B : Matrix J C ℚ) (e : K → ℚ) (z : Option C → ℝ) :
    Matrix.of (fun j c => (copiedLayerMatrix B e j c : ℝ)) *ᵥ z =
      Sum.elim (Matrix.of (fun j c => (B j c : ℝ)) *ᵥ (fun c => z (some c)))
        (fun k => z none * (e k : ℝ)) := by
  classical
  ext j
  cases j <;> simp [Matrix.mulVec, dotProduct, copiedLayerMatrix, Fintype.sum_option, mul_comm]

theorem copiedLayerRows_real_mulVec {J K V : Type*} [Fintype J] [Fintype K]
    (A : Matrix V J ℚ) (x : J ⊕ K → ℝ) :
    Matrix.of (fun r j => (copiedLayerRows A r j : ℝ)) *ᵥ x =
      Matrix.of (fun r j => (A r j : ℝ)) *ᵥ (fun j => x (.inl j)) := by
  classical
  ext r
  simp [Matrix.mulVec, dotProduct, copiedLayerRows, Fintype.sum_sum_type]

theorem jointRationalSpace_copiedLayer {J K C V : Type*}
    [Fintype J] [Fintype K] [Fintype C]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) (e : K → ℚ) :
    jointRationalSpace (copiedLayerMatrix B e) (copiedLayerRows A) =
      copiedLayerSpace (jointRationalSpace B A) (Submodule.span ℝ {fun k => (e k : ℝ)}) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz⟩, hA⟩
    change Matrix.of (fun j c => (copiedLayerMatrix B e j c : ℝ)) *ᵥ z = x at hz
    rw [copiedLayerMatrix_real_mulVec] at hz
    change Matrix.of (fun r j => (copiedLayerRows A r j : ℝ)) *ᵥ x = 0 at hA
    rw [copiedLayerRows_real_mulVec] at hA
    refine ⟨⟨⟨fun c => z (some c), ?_⟩, hA⟩, ?_⟩
    · ext j
      exact congrFun hz (.inl j)
    · apply Submodule.mem_span_singleton.mpr
      refine ⟨z none, ?_⟩
      ext k
      exact congrFun hz (.inr k)
  · rintro ⟨⟨⟨z, hz⟩, hA⟩, he⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp he
    refine ⟨⟨Option.elim' t z, ?_⟩, ?_⟩
    · change Matrix.of (fun j c => (copiedLayerMatrix B e j c : ℝ)) *ᵥ Option.elim' t z = x
      rw [copiedLayerMatrix_real_mulVec]
      ext j
      cases j with
      | inl j => exact congrFun hz j
      | inr k => exact congrFun ht k
    · change Matrix.of (fun r j => (copiedLayerRows A r j : ℝ)) *ᵥ x = 0
      rw [copiedLayerRows_real_mulVec]
      exact hA

def copyLeft {J K : Type*} : (J → ℝ) →ₗ[ℝ] (J ⊕ K → ℝ) where
  toFun v := Sum.elim v 0
  map_add' _ _ := by ext j; cases j <;> simp
  map_smul' _ _ := by ext j; cases j <;> simp

def copyRight {J K : Type*} : (K → ℝ) →ₗ[ℝ] (J ⊕ K → ℝ) where
  toFun v := Sum.elim 0 v
  map_add' _ _ := by ext j; cases j <;> simp
  map_smul' _ _ := by ext j; cases j <;> simp

noncomputable def copiedLayerPolynomial {I J K : Type*}
    (p : VectorPolynomial I ℝ (J → ℝ)) (q : VectorPolynomial I ℝ (K → ℝ)) :
    VectorPolynomial I ℝ (J ⊕ K → ℝ) := map copyLeft p + map copyRight q

theorem coefficients_copiedLayerPolynomial {I J K : Type*}
    (p : VectorPolynomial I ℝ (J → ℝ)) (q : VectorPolynomial I ℝ (K → ℝ)) (α : I →₀ ℕ) :
    coefficients (copiedLayerPolynomial p q) α = Sum.elim (coefficients p α) (coefficients q α) := by
  ext j
  cases j <;> simp [copiedLayerPolynomial, copyLeft, copyRight]

theorem copiedLayerPolynomial_mem {I J K : Type*}
    (W : Submodule ℝ (J → ℝ)) (V : Submodule ℝ (K → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) (q : VectorPolynomial I ℝ (K → ℝ))
    (hp : ∀ α, coefficients p α ∈ W) (hq : ∀ α, coefficients q α ∈ V) :
    ∀ α, coefficients (copiedLayerPolynomial p q) α ∈ copiedLayerSpace W V := by
  intro α
  rw [coefficients_copiedLayerPolynomial]
  exact ⟨hp α, hq α⟩

theorem copiedLayerPolynomial_degree {I J K : Type*}
    {p : VectorPolynomial I ℝ (J → ℝ)} {q : VectorPolynomial I ℝ (K → ℝ)}
    {w : I → ℕ} {h : ℕ} (hp : DegreeLE w h p) (hq : DegreeLE w h q) :
    DegreeLE w h (copiedLayerPolynomial p q) := by
  intro α hα
  rw [coefficients_copiedLayerPolynomial, hp α hα, hq α hα]
  ext j
  cases j <;> rfl

theorem eval_copiedLayerPolynomial {I J K : Type*}
    (p : VectorPolynomial I ℝ (J → ℝ)) (q : VectorPolynomial I ℝ (K → ℝ)) (x : I → ℝ) :
    eval x (copiedLayerPolynomial p q) = Sum.elim (eval x p) (eval x q) := by
  ext j
  cases j <;> simp [copiedLayerPolynomial, copyLeft, copyRight]

end Erdos3.VectorPolynomial

end

end OAI
