import GowersSzemeredi.Proofs13FeatureRelations
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-! A quadratic polynomial realizing each balanced feature relation.
The variables are the free horizontal coordinates, all vertical base
coordinates, and the common height. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open MvPolynomial

abbrev BalancedFeatureVariable (I : Type*) := Option (I ⊕ Option I)

def balancedFeaturePolynomial {I R : Type*} [Fintype I] [CommRing R]
    (sign : I → R) (u₀ u₁ : Option I → R) : MvPolynomial (BalancedFeatureVariable I) R :=
  balancedFeatureRelation (fun i => C (sign i)) (fun i => C (u₀ i)) (fun i => C (u₁ i))
    (fun i => X (some (Sum.inl i))) (fun i => X (some (Sum.inr i))) (X none)

def balancedFeatureAssignment {I R : Type*} (x : I → R) (y : Option I → R)
    (h : R) : BalancedFeatureVariable I → R
  | none => h
  | some (Sum.inl i) => x i
  | some (Sum.inr i) => y i

theorem balancedFeaturePolynomial_eval {I R : Type*} [Fintype I] [CommRing R]
    (sign : I → R) (u₀ u₁ : Option I → R) (x : I → R) (y : Option I → R) (h : R) :
    eval (balancedFeatureAssignment x y h) (balancedFeaturePolynomial sign u₀ u₁) =
      balancedFeatureRelation sign u₀ u₁ x y h := by
  classical
  simp [balancedFeaturePolynomial, balancedFeatureRelation, balancedFeatureAssignment]

theorem balancedFeaturePolynomial_ne_zero {I R : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Field R]
    (sign : I → R) (hsign : ∀ i, sign i ≠ 0) (u₀ u₁ : Option I → R)
    (hnot : ¬ ∃ c : R, u₀ none = c ∧ u₁ none = -c ∧
      (∀ i, u₀ (some i) = -(sign i * c)) ∧
      (∀ i, u₁ (some i) = sign i * c)) :
    balancedFeaturePolynomial sign u₀ u₁ ≠ 0 := by
  obtain ⟨x, y, h, hw⟩ := balancedFeatureRelation_nonzero_witness sign hsign u₀ u₁ hnot
  intro hp
  apply hw
  rw [← balancedFeaturePolynomial_eval, hp, map_zero]

theorem balancedFeaturePolynomial_eq_zero_iff {I R : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Field R]
    (sign : I → R) (hsign : ∀ i, sign i ≠ 0) (u₀ u₁ : Option I → R) :
    balancedFeaturePolynomial sign u₀ u₁ = 0 ↔
      ∃ c : R, u₀ none = c ∧ u₁ none = -c ∧
        (∀ i, u₀ (some i) = -(sign i * c)) ∧
        (∀ i, u₁ (some i) = sign i * c) := by
  classical
  constructor
  · intro hp
    apply (balancedFeatureRelation_universal_iff sign hsign u₀ u₁).mp
    intro x y h
    rw [← balancedFeaturePolynomial_eval, hp, map_zero]
  · rintro ⟨c, h₀, h₁, h₀s, h₁s⟩
    simp only [balancedFeaturePolynomial, balancedFeatureRelation, h₀, h₁, h₀s, h₁s,
      map_neg, map_mul, neg_add_cancel, add_neg_cancel, zero_mul, zero_add]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    ring

theorem balancedFeaturePolynomial_totalDegree {I R : Type*}
    [Fintype I] [CommRing R] [Nontrivial R]
    (sign : I → R) (u₀ u₁ : Option I → R) :
    (balancedFeaturePolynomial sign u₀ u₁).totalDegree ≤ 2 := by
  classical
  have hlinear (j : Option I) :
      ((C (u₀ j) + C (u₁ j)) * X (some (Sum.inr j)) +
        C (u₁ j) * X (none : BalancedFeatureVariable I)).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_mul _ _).trans
      have hc := totalDegree_add (C (u₀ j) : MvPolynomial (BalancedFeatureVariable I) R) (C (u₁ j))
      simp only [totalDegree_C, max_self] at hc
      simp only [totalDegree_X]
      omega
    · apply (totalDegree_mul _ _).trans
      simp
  unfold balancedFeaturePolynomial balancedFeatureRelation
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply totalDegree_finsetSum_le
    intro i _
    apply (totalDegree_mul _ _).trans
    have hi := hlinear (some i)
    simp only [totalDegree_X]
    omega
  · apply (totalDegree_mul _ _).trans
    have hs : (∑ i, C (sign i) * X (some (Sum.inl i)) :
        MvPolynomial (BalancedFeatureVariable I) R).totalDegree ≤ 1 := by
      apply totalDegree_finsetSum_le
      intro i _
      apply (totalDegree_mul _ _).trans
      simp
    exact Nat.add_le_add hs (hlinear none)

theorem balancedFeatureVariable_card {I : Type*} [Fintype I] :
    Fintype.card (BalancedFeatureVariable I) = 2 * Fintype.card I + 2 := by
  simp only [BalancedFeatureVariable, Fintype.card_option, Fintype.card_sum]
  omega

end LeanProofs.GowersSzemeredi
