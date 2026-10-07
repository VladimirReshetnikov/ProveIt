import OAI.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery

namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (q : ℕ) [NeZero q]

noncomputable def normalizedDeckResidueRead (a : D → ZMod q) : Fin n ⊕ I → ZMod q :=
  integerResidueMatrix (Classical.choose (standardLatticeCoordinates_residue W bW b hb q)) q
    *ᵥ (-a)

theorem normalizedDeckResidueRead_neg_integer (β : D → ℤ) :
    normalizedDeckResidueRead W bW b hb q (fun i => -(β i : ZMod q)) =
      integerResidueMap (Fin n ⊕ I) q (standardLatticeCoordinates W bW b hb β) := by
  have hres := (Classical.choose_spec (standardLatticeCoordinates_residue W bW b hb q)).2 β
  unfold normalizedDeckResidueRead
  rw [show -(fun i => -(β i : ZMod q)) = integerResidueMap D q β by
    funext i
    exact neg_neg _]
  exact hres.symm

theorem normalizedDeckResidueRead_latticeDeckInteger (z : Fin n → ℤ) (w : I → ℤ) :
    normalizedDeckResidueRead W bW b hb q
        (fun i => -(latticeDeckInteger W bW b hb z w i : ZMod q)) =
      Sum.elim (fun i => (z i : ZMod q)) (fun i => (w i : ZMod q)) := by
  rw [normalizedDeckResidueRead_neg_integer, latticeDeckInteger_coordinates]
  funext i
  cases i <;> rfl

theorem normalizedDeckResidueRead_neg_latticeDeckInteger (z : Fin n → ℤ) (w : I → ℤ) :
    normalizedDeckResidueRead W bW b hb q
        (integerResidueMap D q (-latticeDeckInteger W bW b hb z w)) =
      Sum.elim (fun i => (z i : ZMod q)) (fun i => (w i : ZMod q)) := by
  convert normalizedDeckResidueRead_latticeDeckInteger W bW b hb q z w using 1
  congr 1
  funext i
  change ((-(latticeDeckInteger W bW b hb z w i) : ℤ) : ZMod q) = _
  exact Int.cast_neg _

noncomputable def normalizedDeckResidueMask {V : Type*}
    (mask : (Fin n ⊕ I → ZMod q) → V) : (D → ZMod q) → V :=
  fun a => mask (normalizedDeckResidueRead W bW b hb q a)

theorem normalizedDeckResidueMask_latticeDeckInteger {V : Type*}
    (mask : (Fin n ⊕ I → ZMod q) → V) (z : Fin n → ℤ) (w : I → ℤ) :
    normalizedDeckResidueMask W bW b hb q mask
        (fun i => -(latticeDeckInteger W bW b hb z w i : ZMod q)) =
      mask (Sum.elim (fun i => (z i : ZMod q)) (fun i => (w i : ZMod q))) := by
  unfold normalizedDeckResidueMask
  rw [normalizedDeckResidueRead_latticeDeckInteger]

theorem normalizedDeckResidueRead_curried_mask {V : Type*}
    (mask : (Fin n → ZMod q) → (I → ZMod q) → V)
    (z : Fin n → ℤ) (w : I → ℤ) :
    mask
        (fun i => normalizedDeckResidueRead W bW b hb q
          (fun j => -(latticeDeckInteger W bW b hb z w j : ZMod q)) (Sum.inl i))
        (fun i => normalizedDeckResidueRead W bW b hb q
          (fun j => -(latticeDeckInteger W bW b hb z w j : ZMod q)) (Sum.inr i)) =
      mask (fun i => (z i : ZMod q)) (fun i => (w i : ZMod q)) := by
  simp only [normalizedDeckResidueRead_latticeDeckInteger, Sum.elim_inl, Sum.elim_inr]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

abbrev CoefficientChartResidues (K : Type*) {m : ℕ} (n : Fin m → ℕ) (E : Fin m → Type*) (q : ℕ) :=
  ∀ j, BoundedCoefficientExponent K (j.val + 1) → (Fin (n j) ⊕ E j) → ZMod q

noncomputable def coefficientDeckResidueRead (q : ℕ) [NeZero q]
    (a : CoefficientAmbientIndex K J → ZMod q) : CoefficientChartResidues K n E q :=
  fun j e => normalizedDeckResidueRead (euclideanSubspace (U j)) (bW j) (b j) (hb j) q
    (fun i => a ⟨⟨j, e⟩, i⟩)

def coefficientSamplerChartResidues (q : ℕ)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) E q) :
    CoefficientChartResidues K n E q :=
  fun j e => Sum.elim (fun i => ((x j).2 i e : ZMod q)) (r j e)

omit [Fintype K] [∀ j, Fintype (I j)] in
theorem coefficientDeckResidueRead_integer_chart (q : ℕ) [NeZero q]
    (x : CoefficientSamplerArrays (K := K) I n)
    (w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ) :
    coefficientDeckResidueRead U bW b hb q
      (fun a => (-coefficientSamplerDeckInteger U bW b hb x w a : ZMod q)) =
      coefficientSamplerChartResidues q x (fun j e => integerResidueMap (E j) q (w j e)) := by
  funext j e
  exact normalizedDeckResidueRead_latticeDeckInteger (euclideanSubspace (U j))
    (bW j) (b j) (hb j) q (fun i => (x j).2 i e) (w j e)

noncomputable def coefficientDeckResidueMask (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues K n E q → ℝ) :
    (CoefficientAmbientIndex K J → ZMod q) → ℝ :=
  fun a => test (coefficientDeckResidueRead U bW b hb q a)

omit [Fintype K] [∀ j, Fintype (I j)] in
theorem coefficientDeckResidueMask_integer_chart (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues K n E q → ℝ)
    (x : CoefficientSamplerArrays (K := K) I n)
    (w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ) :
    coefficientDeckResidueMask U bW b hb q test
      (fun a => (-coefficientSamplerDeckInteger U bW b hb x w a : ZMod q)) =
      test (coefficientSamplerChartResidues q x (fun j e => integerResidueMap (E j) q (w j e))) := by
  unfold coefficientDeckResidueMask
  rw [coefficientDeckResidueRead_integer_chart]

end Erdos3.VectorPolynomial

end

end OAI
