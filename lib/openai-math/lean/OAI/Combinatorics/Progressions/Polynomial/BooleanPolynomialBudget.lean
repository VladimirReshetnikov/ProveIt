/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.BooleanMinorDimension

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_mass_le {I α : Type*} [DecidableEq α]
    (p : Finset α → MvPolynomial I ℝ) (s : Finset α) {M : ℝ}
    (hp : ∀ t ∈ s.powerset, realPolynomialMass (p t) ≤ M) :
    realPolynomialMass (booleanCoefficient p s) ≤ (2 : ℝ) ^ s.card * M := by
  classical
  unfold booleanCoefficient
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      have he : (-1 : MvPolynomial I ℝ) ^ (s \ t).card =
          MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
      rw [he]
      exact (realPolynomialMass_C_mul_le _ _).trans (by simpa using hp t ht)
    _ = _ := by simp

theorem booleanCoefficient_totalDegree_le {I α : Type*} [DecidableEq α]
    (p : Finset α → MvPolynomial I ℝ) (s : Finset α) {d : ℕ}
    (hp : ∀ t ∈ s.powerset, (p t).totalDegree ≤ d) :
    (booleanCoefficient p s).totalDegree ≤ d := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro t ht
  have he : (-1 : MvPolynomial I ℝ) ^ (s \ t).card =
      MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
  rw [he]
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using hp t ht)

theorem booleanAffinePolynomial_mass_le {B F α : Type*} [Fintype α] [DecidableEq α]
    (b : B) (v : F) (t : Finset α) :
    realPolynomialMass (booleanAffinePolynomial b v t) ≤ (Fintype.card α : ℝ) + 1 := by
  classical
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _r : Option α, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      exact (realPolynomialMass_C_mul_le _ _).trans (by
        simpa only [realPolynomialMass_X, mul_one] using booleanFeature_abs_le_one r t)
    _ = _ := by simp

theorem booleanAffinePolynomial_totalDegree_le {B F α : Type*} [Fintype α] [DecidableEq α]
    (b : B) (v : F) (t : Finset α) : (booleanAffinePolynomial b v t).totalDegree ≤ 1 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem booleanBlockPolynomial_mass_le {B F α : Type*} [Fintype F] [Fintype α] [DecidableEq α]
    (b : B) (t : Finset α) :
    realPolynomialMass (booleanBlockPolynomial (F := F) b t) ≤
      ((Fintype.card α : ℝ) + 1) ^ Fintype.card F := by
  classical
  apply (realPolynomialMass_prod_le _ _).trans
  calc
    _ ≤ ∏ _v : F, ((Fintype.card α : ℝ) + 1) :=
      Finset.prod_le_prod₀ (fun _ _ => realPolynomialMass_nonneg _)
        (fun v _ => booleanAffinePolynomial_mass_le b v t)
    _ = _ := by simp

theorem booleanBlockPolynomial_totalDegree_le {B F α : Type*} [Fintype F] [Fintype α] [DecidableEq α]
    (b : B) (t : Finset α) : (booleanBlockPolynomial (F := F) b t).totalDegree ≤ Fintype.card F := by
  classical
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _v : F, 1 := Finset.sum_le_sum (fun v _ => booleanAffinePolynomial_totalDegree_le b v t)
    _ = _ := by simp

theorem booleanSamplerPolynomial_mass_le {B F α : Type*}
    [Fintype B] [Fintype F] [Fintype α] [DecidableEq α] (c : B → ℝ) (s : Finset α) :
    realPolynomialMass (booleanSamplerPolynomial (F := F) c s) ≤
      (2 : ℝ) ^ s.card * ((∑ b, |c b|) * ((Fintype.card α : ℝ) + 1) ^ Fintype.card F) := by
  classical
  apply booleanCoefficient_mass_le
  intro t _
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ b, |c b| * ((Fintype.card α : ℝ) + 1) ^ Fintype.card F := by
      apply Finset.sum_le_sum
      intro b _
      exact (realPolynomialMass_C_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (booleanBlockPolynomial_mass_le b t) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem booleanSamplerPolynomial_totalDegree_le {B F α : Type*}
    [Fintype B] [Fintype F] [Fintype α] [DecidableEq α] (c : B → ℝ) (s : Finset α) :
    (booleanSamplerPolynomial (F := F) c s).totalDegree ≤ Fintype.card F := by
  classical
  apply booleanCoefficient_totalDegree_le
  intro t _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro b _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using booleanBlockPolynomial_totalDegree_le b t)

end Erdos3

end

end OAI
