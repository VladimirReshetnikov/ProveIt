import Surreal.Surcomplex.SineLaurentPolynomial

/-!
# Sharpness of the angular root bound

For every ordinary positive integer `n`, `sin(nθ)` has exactly `2n`
finite-angle classes modulo ordinary full turns. The representatives are
`jπ/n`, and each has native angular-series order one. This proves the
sharpness clause of `trigonometry:thm:polyroots`.
-/

universe u
namespace Surreal.Surcomplex.SineLaurent

open Foundations

noncomputable section

/-- The ordinary representatives of the roots of `sin(nθ)`. -/
def angle (n j : ℕ) : SignSequence.FiniteElement.{u} :=
  SignSequence.finiteOfReal ((j : ℝ) * Real.pi / n)

/-- The representatives have the consecutive powers of a primitive `2n`-th root as phases. -/
theorem phase_angle (n j : ℕ) (hn : 0 < n) :
    finitePhase (angle n j) = FiniteFourier.zeta (2 * n) ^ j := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : angle n j = j • SignSequence.finiteOfReal (2 * Real.pi / (2 * n)) := by
    rw [← map_nsmul, nsmul_eq_mul]
    unfold angle
    congr 1
    field_simp
  rw [he, finitePhase_nsmul, FiniteFourier.zeta]
  push_cast
  rfl

/-- Distinct indices in the range give distinct angle classes. -/
theorem phase_angle_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (fun j : Fin (2 * n) => finitePhase (angle n j.val : SignSequence.FiniteElement.{u})) := by
  intro i j he
  dsimp only at he
  rw [phase_angle n i.val hn, phase_angle n j.val hn] at he
  exact Fin.ext ((FiniteFourier.isPrimitiveRoot_zeta (by omega)).pow_inj i.isLt j.isLt he)

/-- Each displayed representative is an actual root of the native sine Laurent polynomial. -/
theorem root_angle (n j : ℕ) (hn : 0 < n) :
    trigonometricPolynomial (fourier n) (angle n j : SignSequence.FiniteElement.{u}) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : n • (angle n j : SignSequence.FiniteElement.{u}) =
      SignSequence.finiteOfReal ((j : ℝ) * Real.pi) := by
    rw [angle, ← map_nsmul, nsmul_eq_mul]
    congr 1
    field_simp
  rw [evaluate, he, finiteSin_constant, Real.sin_nat_mul_pi, map_zero, map_zero]

/-- Every finite-angle root is simple for the verified native angular germ. -/
theorem order_germ_at_root (n : ℕ) (hn : 0 < n)
    (θ : SignSequence.FiniteElement.{u}) (hθ : trigonometricPolynomial (fourier n) θ = 0) :
    (AngularLaurent.germ (fourier n) (phaseUnit θ)).order = 1 := by
  rw [AngularLaurent.order_germ_at_finite_angle (fourier n) (fourier_ne_zero n hn) n (frequency_bound n)]
  have hr := (laurentSum_zero_iff_polynomial_root n (fourier n).coeff θ).mp
    (by rw [← trigonometricPolynomial_eq_laurentSum (fourier n) n (frequency_bound n)]; exact hθ)
  rw [multiplicity_one n hn _
    (FiniteFourier.ne_zero_of_modulus_eq_one (modulus_finitePhase θ)) hr]
  rfl

/-- In particular, every displayed representative has angular order one. -/
theorem order_germ_angle (n j : ℕ) (hn : 0 < n) :
    (AngularLaurent.germ (fourier n) (phaseUnit (angle n j : SignSequence.FiniteElement.{u}))).order = 1 :=
  order_germ_at_root n hn (angle n j) (root_angle n j hn)

/-- Every finite-angle zero has exactly one of the displayed phase classes. -/
theorem root_iff_exists_unique_index (n : ℕ) (hn : 0 < n)
    (θ : SignSequence.FiniteElement.{u}) :
    trigonometricPolynomial (fourier n) θ = 0 ↔
      ∃! j : Fin (2 * n), finitePhase θ = finitePhase (angle n j.val) := by
  classical
  haveI : NeZero (2 * n) := ⟨by omega⟩
  constructor
  · intro h
    have hr := (laurentSum_zero_iff_polynomial_root n (fourier n).coeff θ).mp
      (by rw [← trigonometricPolynomial_eq_laurentSum (fourier n) n (frequency_bound n)]; exact h)
    rw [Polynomial.IsRoot, cleared_polynomial, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at hr
    have he : finitePhase θ ^ (2 * n) = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left amplitude_ne_zero)
    obtain ⟨j, hj, he⟩ := (FiniteFourier.isPrimitiveRoot_zeta (by omega : 0 < 2 * n)).eq_pow_of_pow_eq_one he
    refine ⟨⟨j, hj⟩, ?_, ?_⟩
    · change finitePhase θ = finitePhase (angle n j)
      rw [phase_angle n j hn]
      exact he.symm
    · intro k hk
      apply phase_angle_injective n hn
      exact hk.symm.trans (by
        change finitePhase θ = finitePhase (angle n j)
        rw [phase_angle n j hn]
        exact he.symm)
  · rintro ⟨j, hj, _⟩
    rw [trigonometricPolynomial_eq_laurentSum (fourier n) n (frequency_bound n), hj,
      ← trigonometricPolynomial_eq_laurentSum (fourier n) n (frequency_bound n)]
    exact root_angle n j.val hn

/-- An explicit finite set attains the bound with distinct phase classes and simple angular zeros. -/
theorem exists_sharp_root_set (n : ℕ) (hn : 0 < n) :
    ∃ S : Finset SignSequence.FiniteElement.{u}, S.card = 2 * n ∧
      Set.InjOn finitePhase (S : Set SignSequence.FiniteElement.{u}) ∧
      ∀ θ ∈ S, trigonometricPolynomial (fourier n) θ = 0 ∧
        (AngularLaurent.germ (fourier n) (phaseUnit θ)).order = 1 := by
  classical
  let f := fun j : Fin (2 * n) => (angle n j.val : SignSequence.FiniteElement.{u})
  have hf : Function.Injective f := fun i j he =>
    phase_angle_injective n hn (congrArg finitePhase he)
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  · intro θ hθ φ hφ he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hφ
    exact congrArg f (phase_angle_injective n hn he)
  · intro θ hθ
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hθ
    exact ⟨root_angle n j.val hn, order_germ_angle n j.val hn⟩

end
end Surreal.Surcomplex.SineLaurent
