import Surreal.Algebra.QuarticPolynomial
import Surreal.Algebra.QuarticVariantPolynomial
import Surreal.Algebra.ConstantTermGraph

/-!
# The two seven-witness quartics for the constant-term graph

The variants in `odg:def:cor:ctquartic` obtained from
`odg:eq:standardquartic` and `odg:def:eq:F4`. The Boolean selector is
false for the original Pell-coordinate bound and true for its square.
-/

namespace Surreal.ConstantTermQuartic

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Select one of the two source quartics defining integer constants. -/
def constantValue (squared : Bool) (n u v : R) (s : Fin 4 → R) : R :=
  if squared then QuarticVariant.value n u v s else QuarticConstants.value n u v s

/-- The selected constant definition plus the squared quadratic kernel equation. -/
def value (squared : Bool) (x n u v : R) (s : Fin 4 → R) (y : R) : R :=
  constantValue squared n u v s + ((x - n) ^ 2 - 2 * y ^ 2) ^ 2

/-- Seven existential witnesses: a Pell pair, four squares, and the kernel witness. -/
def Graph (squared : Bool) (x n : R) : Prop :=
  ∃ u v : R, ∃ s : Fin 4 → R, ∃ y : R, value squared x n u v s y = 0

/-- Each selected value is a sum of two squares, so the added third square separates. -/
theorem value_eq_zero_iff [LinearOrder S] [IsStrictOrderedRing S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (squared : Bool) (x n u v : R) (s : Fin 4 → R) (y : R) :
    value squared x n u v s y = 0 ↔
      constantValue squared n u v s = 0 ∧ (x - n) ^ 2 = 2 * y ^ 2 := by
  constructor
  · intro he
    cases squared
    · have h := QuinticConstants.three_squares_zero φ hφ _ _ _ he
      refine ⟨?_, sub_eq_zero.mp h.2.2⟩
      simp only [constantValue, Bool.false_eq_true, ↓reduceIte, QuarticConstants.value, h.1,
        h.2.1, zero_pow (by decide : 2 ≠ 0), add_zero]
    · have h := QuinticConstants.three_squares_zero φ hφ _ _ _ he
      refine ⟨?_, sub_eq_zero.mp h.2.2⟩
      simp only [constantValue, ↓reduceIte, QuarticVariant.value, h.1,
        h.2.1, zero_pow (by decide : 2 ≠ 0), add_zero]
  · rintro ⟨hp, hy⟩
    simp [value, hp, hy]

/-- The polynomial graph reduces to the selected integer definition and the kernel test. -/
theorem graph_iff [LinearOrder S] [IsStrictOrderedRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (squared : Bool) (x n : R) :
    Graph squared x n ↔
      (if squared then QuarticVariant.Defines n else QuarticConstants.Defines n) ∧
        ∃ y : R, (x - n) ^ 2 = 2 * y ^ 2 := by
  have hs : (∃ u v : R, ∃ s : Fin 4 → R, constantValue squared n u v s = 0) ↔
      (if squared then QuarticVariant.Defines n else QuarticConstants.Defines n) := by
    cases squared <;> rfl
  constructor
  · rintro ⟨u, v, s, y, he⟩
    obtain ⟨hp, hy⟩ := (value_eq_zero_iff φ hφ squared x n u v s y).mp he
    exact ⟨hs.mp ⟨u, v, s, hp⟩, y, hy⟩
  · rintro ⟨hp, y, hy⟩
    obtain ⟨u, v, s, hp⟩ := hs.mpr hp
    exact ⟨u, v, s, y, (value_eq_zero_iff φ hφ squared x n u v s y).mpr ⟨hp, hy⟩⟩

open MvPolynomial

/-- Nine variables: the original seven, input x, and the last witness y. -/
abbrev Variables := Fin 7 ⊕ Fin 2

/-- The selected native integer polynomial defining constants. -/
def constantPolynomial (squared : Bool) : MvPolynomial (Fin 7) ℤ :=
  if squared then QuarticVariant.polynomial else QuarticConstants.polynomial

/-- The literal quadratic kernel equation in the nine-variable ring. -/
def kernelPolynomial : MvPolynomial Variables ℤ :=
  (X (Sum.inr 0) - X (Sum.inl 0)) ^ 2 - C 2 * X (Sum.inr 1) ^ 2

/-- The two native integer quartics for the graph, selected by their original bound. -/
def polynomial (squared : Bool) : MvPolynomial Variables ℤ :=
  rename Sum.inl (constantPolynomial squared) + kernelPolynomial ^ 2

/-- Evaluation recovers exactly the displayed source expression. -/
theorem eval₂_polynomial (squared : Bool) (a : Variables → R) :
    (polynomial squared).eval₂ (Int.castRingHom R) a =
      value squared (a (Sum.inr 0)) (a (Sum.inl 0)) (a (Sum.inl 1)) (a (Sum.inl 2))
        (fun j => a (Sum.inl ⟨j.val + 3, by omega⟩)) (a (Sum.inr 1)) := by
  cases squared <;>
    simp [polynomial, constantPolynomial, kernelPolynomial, value, constantValue,
      eval₂_rename, QuarticConstants.eval₂_polynomial, QuarticVariant.eval₂_polynomial,
      Function.comp_def]

theorem kernelPolynomial_totalDegree_le : kernelPolynomial.totalDegree ≤ 2 := by
  have h₁ := totalDegree_sub (X (Sum.inr 0) : MvPolynomial Variables ℤ) (X (Sum.inl 0))
  have h₂ := totalDegree_pow (X (Sum.inr 0) - X (Sum.inl 0) : MvPolynomial Variables ℤ) 2
  have h₃ := totalDegree_mul (C 2 : MvPolynomial Variables ℤ) (X (Sum.inr 1) ^ 2)
  have h₄ := totalDegree_sub ((X (Sum.inr 0) - X (Sum.inl 0)) ^ 2 : MvPolynomial Variables ℤ)
    (C 2 * X (Sum.inr 1) ^ 2)
  simp only [totalDegree_X, totalDegree_X_pow, totalDegree_C] at h₁ h₃
  dsimp [kernelPolynomial]
  omega

private theorem degreeOf_sub_left {p q : MvPolynomial Variables ℤ}
    (h : q.degreeOf (Sum.inr 0) < p.degreeOf (Sum.inr 0)) :
    (p - q).degreeOf (Sum.inr 0) = p.degreeOf (Sum.inr 0) := by
  rw [sub_eq_add_neg, degreeOf_add_eq_of_degreeOf_lt (by simpa only [degreeOf_neg] using h)]

theorem kernelPolynomial_degreeOf_input : kernelPolynomial.degreeOf (Sum.inr 0) = 2 := by
  have hd : (X (Sum.inr 0) - X (Sum.inl 0) : MvPolynomial Variables ℤ).degreeOf (Sum.inr 0) = 1 := by
    rw [degreeOf_sub_left (by
      simp only [degreeOf_X_self, degreeOf_X_of_ne
        (by decide : (Sum.inr 0 : Variables) ≠ Sum.inl 0)]; decide), degreeOf_X_self]
  have hn : (X (Sum.inr 0) - X (Sum.inl 0) : MvPolynomial Variables ℤ) ≠ 0 := by
    intro h
    simp [h] at hd
  have hp := degreeOf_pow_eq (Sum.inr 0) _ 2 hn
  rw [hd] at hp
  have hq := degreeOf_mul_le (Sum.inr 0) (C 2 : MvPolynomial Variables ℤ) (X (Sum.inr 1) ^ 2)
  simp only [degreeOf_C, degreeOf_X_pow_of_ne 2 (by decide : (Sum.inr 0 : Variables) ≠ Sum.inr 1),
    zero_add] at hq
  unfold kernelPolynomial
  rw [degreeOf_sub_left (by omega), hp]

/-- The fresh input variable occurs to degree four in each graph polynomial. -/
theorem polynomial_degreeOf_input (squared : Bool) : (polynomial squared).degreeOf (Sum.inr 0) = 4 := by
  have h₀ : (rename Sum.inl (constantPolynomial squared) : MvPolynomial Variables ℤ).degreeOf
      (Sum.inr 0) = 0 := by
    simp [degreeOf, degrees_rename_of_injective Sum.inl_injective]
  have hn : kernelPolynomial ≠ 0 := by
    intro h
    have hd := kernelPolynomial_degreeOf_input
    simp [h] at hd
  have hk := degreeOf_pow_eq (Sum.inr 0) kernelPolynomial 2 hn
  rw [kernelPolynomial_degreeOf_input] at hk
  unfold polynomial
  rw [add_comm, degreeOf_add_eq_of_degreeOf_lt (by omega), hk]

/-- Each graph polynomial has total degree exactly four. -/
theorem polynomial_totalDegree (squared : Bool) : (polynomial squared).totalDegree = 4 := by
  have hc : (constantPolynomial squared).totalDegree = 4 := by
    cases squared
    · exact QuarticConstants.polynomial_totalDegree
    · exact QuarticVariant.polynomial_totalDegree
  have h₁ := totalDegree_rename_le (R := ℤ) (Sum.inl : Fin 7 → Variables) (constantPolynomial squared)
  rw [hc] at h₁
  have h₂ := totalDegree_pow kernelPolynomial 2
  have h₃ := kernelPolynomial_totalDegree_le
  have h₄ := totalDegree_add (rename Sum.inl (constantPolynomial squared) : MvPolynomial Variables ℤ)
    (kernelPolynomial ^ 2)
  have hl := degreeOf_le_totalDegree (polynomial squared) (Sum.inr 0)
  rw [polynomial_degreeOf_input] at hl
  change (polynomial squared).totalDegree ≤ _ at h₄
  omega

end
end Surreal.ConstantTermQuartic
