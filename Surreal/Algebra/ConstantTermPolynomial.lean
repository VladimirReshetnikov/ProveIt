import Surreal.Algebra.QuinticPolynomial
import Surreal.Algebra.ConstantTermGraph

/-!
# The degree-ten polynomial for the constant-term graph

The single real polynomial following `odg:def:thm:ctgraph` is the square
of the quintic plus the square of the quadratic kernel equation.
Its eight witnesses are u, v, w, four square coordinates, and y.
-/

namespace Surreal.ConstantTermPolynomial

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The literal single-polynomial value printed after the graph theorem. -/
def value (x n u v w : R) (s : Fin 4 → R) (y : R) : R :=
  QuinticConstants.value n u v w s ^ 2 + ((x - n) ^ 2 - 2 * y ^ 2) ^ 2

/-- The graph predicate with precisely eight existential witnesses. -/
def Graph (x n : R) : Prop :=
  ∃ u v w : R, ∃ s : Fin 4 → R, ∃ y : R, value x n u v w s y = 0

/-- A faithful ordered-ring interpretation separates the two squared equations. -/
theorem value_eq_zero_iff [LinearOrder S] [IsStrictOrderedRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (x n u v w : R) (s : Fin 4 → R) (y : R) :
    value x n u v w s y = 0 ↔
      QuinticConstants.value n u v w s = 0 ∧ (x - n) ^ 2 = 2 * y ^ 2 := by
  constructor
  · intro h
    have he : QuinticConstants.value n u v w s ^ 2 +
        ((x - n) ^ 2 - 2 * y ^ 2) ^ 2 + (0 : R) ^ 2 = 0 := by
      simpa only [value, zero_pow (by decide : 2 ≠ 0), add_zero] using h
    have hz := QuinticConstants.three_squares_zero φ hφ _ _ _ he
    exact ⟨hz.1, sub_eq_zero.mp hz.2.1⟩
  · rintro ⟨hp, hy⟩
    simp [value, hp, hy]

/-- Separating the squares gives the quintic standardness test and the quadratic kernel test. -/
theorem graph_iff [LinearOrder S] [IsStrictOrderedRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (x n : R) :
    Graph x n ↔ QuinticConstants.Defines n ∧ ∃ y : R, (x - n) ^ 2 = 2 * y ^ 2 := by
  constructor
  · rintro ⟨u, v, w, s, y, h⟩
    obtain ⟨hp, hy⟩ := (value_eq_zero_iff φ hφ x n u v w s y).mp h
    exact ⟨⟨u, v, w, s, hp⟩, y, hy⟩
  · rintro ⟨⟨u, v, w, s, hp⟩, y, hy⟩
    exact ⟨u, v, w, s, y, (value_eq_zero_iff φ hφ x n u v w s y).mpr ⟨hp, hy⟩⟩

open MvPolynomial

/-- Ten variables: the original eight quintic variables, followed by input x and witness y. -/
abbrev Variables := Fin 8 ⊕ Fin 2

/-- The original quintic with its variables included in the ten-variable ring. -/
def liftedQuintic : MvPolynomial Variables ℤ := rename Sum.inl QuinticConstants.polynomial

/-- The quadratic kernel equation in the same native integer polynomial ring. -/
def kernelPolynomial : MvPolynomial Variables ℤ :=
  (X (Sum.inr 0) - X (Sum.inl 0)) ^ 2 - C 2 * X (Sum.inr 1) ^ 2

/-- The source's parameter-free integer polynomial for the real constant-term graph. -/
def polynomial : MvPolynomial Variables ℤ := liftedQuintic ^ 2 + kernelPolynomial ^ 2

/-- Evaluation agrees with the printed scalar expression. -/
theorem eval₂_polynomial (a : Variables → R) :
    polynomial.eval₂ (Int.castRingHom R) a =
      value (a (Sum.inr 0)) (a (Sum.inl 0)) (a (Sum.inl 1)) (a (Sum.inl 2))
        (a (Sum.inl 3)) (fun j => a (Sum.inl ⟨j.val + 4, by omega⟩)) (a (Sum.inr 1)) := by
  simp [polynomial, liftedQuintic, kernelPolynomial, value,
    eval₂_rename, QuinticConstants.eval₂_polynomial, Function.comp_def]

theorem liftedQuintic_totalDegree : liftedQuintic.totalDegree = 5 := by
  have h₁ := totalDegree_rename_le (R := ℤ) (Sum.inl : Fin 8 → Variables) QuinticConstants.polynomial
  have h₂ := totalDegree_rename_le (R := ℤ)
    (Sum.elim id (fun _ : Fin 2 => (0 : Fin 8))) liftedQuintic
  have he : rename (Sum.elim id (fun _ : Fin 2 => (0 : Fin 8))) liftedQuintic =
      QuinticConstants.polynomial := by
    simp only [liftedQuintic, rename_rename, Function.comp_def, Sum.elim_inl, id_eq]
    exact rename_id_apply _
  rw [he, QuinticConstants.polynomial_totalDegree] at h₂
  rw [QuinticConstants.polynomial_totalDegree] at h₁
  exact Nat.le_antisymm h₁ h₂

theorem kernelPolynomial_totalDegree_le : kernelPolynomial.totalDegree ≤ 2 := by
  have h₁ := totalDegree_sub (X (Sum.inr 0) : MvPolynomial Variables ℤ) (X (Sum.inl 0))
  have h₂ := totalDegree_pow (X (Sum.inr 0) - X (Sum.inl 0) : MvPolynomial Variables ℤ) 2
  have h₃ := totalDegree_mul (C 2 : MvPolynomial Variables ℤ) (X (Sum.inr 1) ^ 2)
  have h₄ := totalDegree_sub ((X (Sum.inr 0) - X (Sum.inl 0)) ^ 2 : MvPolynomial Variables ℤ)
    (C 2 * X (Sum.inr 1) ^ 2)
  simp only [totalDegree_X, totalDegree_X_pow, totalDegree_C] at h₁ h₃
  dsimp [kernelPolynomial]
  omega

/-- The degree is exactly ten: the squared quintic cannot cancel against the quartic term. -/
theorem polynomial_totalDegree : polynomial.totalDegree = 10 := by
  have hp : liftedQuintic ≠ 0 := by
    intro h
    have hd := liftedQuintic_totalDegree
    simp [h] at hd
  have hq : (liftedQuintic ^ 2).totalDegree = 10 := by
    rw [pow_two, totalDegree_mul_of_isDomain hp hp, liftedQuintic_totalDegree]
  have hk := totalDegree_pow kernelPolynomial 2
  have hk' := kernelPolynomial_totalDegree_le
  unfold polynomial
  rw [totalDegree_add_eq_left_of_totalDegree_lt (by omega), hq]

end
end Surreal.ConstantTermPolynomial
