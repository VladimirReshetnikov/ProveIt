import Mathlib.LinearAlgebra.Dimension.Constructions
import OAI.Combinatorics.Progressions.Fourier.LatticeCoordinateResidueFourier

namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Classical

theorem standardLatticeCoordinates_card {D I J : Type*}
    [Fintype D] [Fintype I] [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) :
    Fintype.card (J ⊕ I) = Fintype.card D := by
  simpa only [Module.finrank_fintype_fun_eq_card] using
    (standardLatticeCoordinates W bW bP hP).finrank_eq.symm

theorem latticeCoordinate_frequency_count {D I J : Type*}
    [Fintype D] [Fintype I] [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (M : ℕ) :
    Fintype.card ((J ⊕ I) → Fin M) = M ^ Fintype.card D := by
  rw [Fintype.card_fun, Fintype.card_fin, standardLatticeCoordinates_card W bW bP hP]

theorem latticeCoordinate_congruence_fourier_ambient_bound {D I J : Type*}
    [Fintype D] [DecidableEq D] [Fintype I] [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W)
    (M : ℕ) [NeZero M] (Good : (J ⊕ I → ZMod M) → Prop) [DecidablePred Good] :
    ∃ (c : ((J ⊕ I) → Fin M) → ℂ) (ell : ((J ⊕ I) → Fin M) → D → Fin M),
      (∑ k, ‖c k‖) ≤ (M : ℝ) ^ Fintype.card D ∧
      (∀ k j, 0 ≤ ((ell k j).val : ℝ) / M ∧ ((ell k j).val : ℝ) / M < 1) ∧
      ∀ β, (if Good (integerResidueMap (J ⊕ I) M (standardLatticeCoordinates W bW bP hP β))
        then (1 : ℂ) else 0) =
        ∑ k, c k * CircleFourier.character
          ((∑ j, (((ell k j).val : ℝ) / M) * (β j : ℝ) : ℝ) : CircleFourier.Circle) := by
  simpa only [standardLatticeCoordinates_card W bW bP hP] using
    latticeCoordinate_congruence_fourier_expansion W bW bP hP M Good

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include hb bW in
theorem allocatedResidueLabel_card (period : ℕ) [NeZero period] :
    Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) =
      period ^ (∑ j, Fintype.card (J j)) := by
  have hc (j) : n j + Fintype.card (E j) = Fintype.card (J j) := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      standardLatticeCoordinates_card (euclideanSubspace (U j)) (bW j) (b j) (hb j)
  simp only [Fintype.card_prod, Fintype.card_pi, ZMod.card,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← pow_add, hc]
  exact Finset.prod_pow_eq_pow_sum _ _ _

include hb bW in
theorem allocatedResidueLabels_le_exp {S : Type*} [Fintype S]
    (period : ℕ) [NeZero period] {P : ℝ} (hperiod : (period : ℝ) ≤ Real.exp P) :
    (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card S ≤
      Real.exp (Fintype.card S * ((∑ j, Fintype.card (J j) : ℕ) * P)) := by
  rw [allocatedResidueLabel_card U b hb bW, Nat.cast_pow, Real.exp_nat_mul, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by positivity)
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hperiod _) _

end Erdos3.VectorPolynomial

end

end OAI
