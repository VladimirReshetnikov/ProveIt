import FabiusFunction.CombDefectSeries
import FabiusFunction.RvachevPolynomialSynthesis

/-!
# Parity-selected superconvergent Rvachev synthesis

For a nonzero natural mesh `M`, put `d = v₂(M)`.  The shifted Rvachev comb is
exact on every polynomial of degree at most `d`, at every phase.  At degree
`d + 1`, the first surviving Fourier aliases have odd frequency.  Their parity
selects four phases where they cancel:

* phases `0` and `1/2` when `d + 1` is odd;
* phases `1/4` and `3/4` when `d + 1` is even.

This module packages that one-extra-degree exactness first for monomials and
arbitrary polynomials, then transports it through Rvachev moment
deconvolution.  Thus the phased synthesis theorem reconstructs every
polynomial of degree at most `v₂(M) + 1` at exactly the parity-selected
phases.  No assertion is made that these are the only superconvergent phases.

## Main declarations

* `IsRvachevSuperconvergentPhase`: the four parity-selected phases.
* `isRvachevSuperconvergentPhase_two_pow_iff`: their dyadic-mesh form.
* `tsum_quarter_monomial_eq_integral_of_even_deg` and
  `tsum_three_quarters_monomial_eq_integral_of_even_deg`: the missing
  even-threshold cancellations.
* `tsum_shifted_monomial_eq_integral_superconvergent`: the unified threshold
  monomial theorem.
* `tsum_shifted_polynomial_eq_integral_superconvergent`: exactness through
  degree `v₂(M) + 1`.
* `integral_polynomial_mul_rvachevUp_eq_normalized_tsum_superconvergent`:
  the corresponding physical-coordinate quadrature.
* `normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp_superconvergent`:
  the corresponding phased deconvolved-polynomial synthesis.
* `normalized_tsum_shifted_rvachevAppellPolynomial_mul_rvachevUp_superconvergent`:
  its explicit monomial/Rvachev--Appell specialization.
-/

set_option autoImplicit false

open MeasureTheory Real Complex Set
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

open Polynomial

/-- The parity-selected phases for one-extra-degree Rvachev comb exactness.
For threshold degree `v₂(M) + 1`, these are `0, 1/2` in the odd case and
`1/4, 3/4` in the even case. -/
def IsRvachevSuperconvergentPhase (M : ℕ) (θ : ℝ) : Prop :=
  (Odd (padicValNat 2 M + 1) ∧ (θ = 0 ∨ θ = 1 / 2)) ∨
    (Even (padicValNat 2 M + 1) ∧ (θ = 1 / 4 ∨ θ = 3 / 4))

/-- On the dyadic mesh `2 ^ N`, the selected phases are the endpoints
`0, 1/2` for even `N` and the quarter points `1/4, 3/4` for odd `N`. -/
@[simp]
theorem isRvachevSuperconvergentPhase_two_pow_iff (N : ℕ) (θ : ℝ) :
    IsRvachevSuperconvergentPhase (2 ^ N) θ ↔
      (Even N ∧ (θ = 0 ∨ θ = 1 / 2)) ∨
        (Odd N ∧ (θ = 1 / 4 ∨ θ = 3 / 4)) := by
  simp only [IsRvachevSuperconvergentPhase,
    padicValNat_base_pow (by decide : 1 < 2), Nat.odd_add_one,
    Nat.even_add_one, Nat.not_odd_iff_even, Nat.not_even_iff_odd]

private theorem tsum_three_quarters_eq_quarter_of_even_deg
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    (heven : Even (padicValNat 2 M + 1)) :
    (∑' k : ℤ, monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
        (3 / 4 + k)) =
      ∑' k : ℤ, monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
        (1 / 4 + k) := by
  let e : ℤ ≃ ℤ :=
    { toFun := fun k => -k - 1
      invFun := fun k => -k - 1
      left_inv := by
        intro k
        simp
      right_inv := by
        intro k
        simp }
  let f : ℤ → ℂ := fun k =>
    monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
      ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
      (3 / 4 + k)
  calc
    (∑' k : ℤ, monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
        (3 / 4 + k)) = ∑' k : ℤ, f k := rfl
    _ = ∑' k : ℤ, f (e k) := (e.tsum_eq f).symm
    _ = ∑' k : ℤ, monomialRvachevSchwartz F hF
        (padicValNat 2 M + 1) ((M : ℝ))⁻¹
        (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (1 / 4 + k) := by
      refine tsum_congr fun k => ?_
      change monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
          ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
          ((3 / 4 : ℝ) + ((-k - 1 : ℤ) : ℝ)) =
        monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
          ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
          ((1 / 4 : ℝ) + (k : ℝ))
      simp only [monomialRvachevSchwartz_apply]
      have hx : (3 / 4 : ℝ) + ((-k - 1 : ℤ) : ℝ) =
          -((1 / 4 : ℝ) + (k : ℝ)) := by
        push_cast
        ring
      rw [hx, heven.neg_pow, mul_neg, rvachevUp_even F]

/-- **Quarter-phase super-exactness at even threshold degree.**  If
`v₂(M) + 1` is even, the degree-`v₂(M)+1` comb at phase `1/4` equals its
integral.  The surviving aliases have odd frequency; reflection identifies
the `1/4` and `3/4` combs, while half-period antisymmetry negates their
defects. -/
theorem tsum_quarter_monomial_eq_integral_of_even_deg
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    (heven : Even (padicValNat 2 M + 1)) :
    (∑' k : ℤ, monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
        (1 / 4 + k)) =
      ∫ x : ℝ, ((x ^ (padicValNat 2 M + 1) *
        rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) := by
  have hanti :=
    tsum_shifted_monomial_sub_integral_add_half F hF hM (1 / 4)
  have hphase : (1 / 4 : ℝ) + 1 / 2 = 3 / 4 := by norm_num
  rw [hphase, tsum_three_quarters_eq_quarter_of_even_deg F hF hM heven] at hanti
  exact sub_eq_zero.mp ((CharZero.eq_neg_self_iff).mp hanti)

/-- **Three-quarter-phase super-exactness at even threshold degree.**  Under
the same parity condition as the quarter theorem, reflection of the even
threshold integrand transfers exactness from phase `1/4` to phase `3/4`. -/
theorem tsum_three_quarters_monomial_eq_integral_of_even_deg
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    (heven : Even (padicValNat 2 M + 1)) :
    (∑' k : ℤ, monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
        (3 / 4 + k)) =
      ∫ x : ℝ, ((x ^ (padicValNat 2 M + 1) *
        rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) :=
  (tsum_three_quarters_eq_quarter_of_even_deg F hF hM heven).trans
    (tsum_quarter_monomial_eq_integral_of_even_deg F hF hM heven)

/-- **Unified parity-selected threshold exactness.**  At every nonzero mesh,
the monomial comb of degree `v₂(M)+1` is exact at phases `0,1/2` when that
degree is odd, and at phases `1/4,3/4` when it is even. -/
theorem tsum_shifted_monomial_eq_integral_superconvergent
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {θ : ℝ} (hθ : IsRvachevSuperconvergentPhase M θ) :
    (∑' k : ℤ, monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
        (θ + k)) =
      ∫ x : ℝ, ((x ^ (padicValNat 2 M + 1) *
        rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) := by
  rcases hθ with ⟨hodd, hzero | hhalf⟩ | ⟨heven, hquarter | hthreeQuarter⟩
  · subst θ
    simpa only [zero_add] using
      tsum_monomial_eq_integral_of_odd_deg F hF hM hodd
  · subst θ
    exact tsum_half_monomial_eq_integral_of_odd_deg F hF hM hodd
  · subst θ
    exact tsum_quarter_monomial_eq_integral_of_even_deg F hF hM heven
  · subst θ
    exact tsum_three_quarters_monomial_eq_integral_of_even_deg F hF hM heven

private theorem real_tsum_shifted_monomial_eq_integral_of_complex
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    (p : ℕ) (θ : ℝ)
    (hcomplex :
      (∑' k : ℤ, monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (θ + k)) =
        ∫ x : ℝ, ((x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ)) :
    (∑' k : ℤ, (θ + k) ^ p *
        rvachevUp F (((M : ℝ))⁻¹ * (θ + k))) =
      ∫ x : ℝ, x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  calc
    (∑' k : ℤ, (((θ + k) ^ p *
        rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) : ℝ) : ℂ)) =
        ∑' k : ℤ, monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (θ + k) := rfl
    _ = ∫ x : ℝ,
          ((x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) := hcomplex
    _ = ((∫ x : ℝ,
          x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) := integral_ofReal

/-- **Full parity-selected polynomial superconvergence.**  For every nonzero
natural mesh `M`, a selected phase integrates every real polynomial through
degree `v₂(M)+1`.  Degrees at most `v₂(M)` use composite-mesh alias
vanishing; only the top monomial uses the parity cancellation. -/
theorem tsum_shifted_polynomial_eq_integral_superconvergent
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {P : ℝ[X]} (hdeg : P.natDegree ≤ padicValNat 2 M + 1)
    (θ : ℝ) (hθ : IsRvachevSuperconvergentPhase M θ) :
    ∑' k : ℤ, P.eval (θ + k) *
        rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) =
      ∫ x : ℝ, P.eval x * rvachevUp F (((M : ℝ))⁻¹ * x) := by
  refine tsum_shifted_polynomial_eq_integral_of_forall_monomial F hF
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)) θ fun i hi => ?_
  by_cases hlow : i ≤ padicValNat 2 M
  · exact tsum_shifted_monomial_eq_integral_nat_real F hF hM hlow θ
  · have hitop : i = padicValNat 2 M + 1 := by omega
    subst i
    exact real_tsum_shifted_monomial_eq_integral_of_complex F hF hM
      (padicValNat 2 M + 1) θ
      (tsum_shifted_monomial_eq_integral_superconvergent F hF hM hθ)

/-- **Physical-coordinate superconvergent quadrature.**  At a selected phase
of a nonzero natural mesh `M`, the normalized samples of the Rvachev density
integrate every real polynomial through degree `v₂(M)+1`.  Both the lattice
spacing and the quadrature weight are `1/M`. -/
theorem integral_polynomial_mul_rvachevUp_eq_normalized_tsum_superconvergent
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {P : ℝ[X]} (hdeg : P.natDegree ≤ padicValNat 2 M + 1)
    (θ : ℝ) (hθ : IsRvachevSuperconvergentPhase M θ) :
    (∫ x : ℝ, P.eval x * rvachevUp F x) =
      ((M : ℝ))⁻¹ *
        ∑' k : ℤ,
          P.eval (((M : ℝ))⁻¹ * (θ + k)) *
            rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) := by
  let Q : ℝ[X] :=
    P.comp (C ((M : ℝ))⁻¹ * X + C 0)
  have hQdeg : Q.natDegree ≤ padicValNat 2 M + 1 := by
    calc
      Q.natDegree ≤ P.natDegree *
          (C ((M : ℝ))⁻¹ * X + C 0).natDegree := by
        exact Polynomial.natDegree_comp_le
      _ ≤ P.natDegree * 1 := by
        exact Nat.mul_le_mul_left P.natDegree Polynomial.natDegree_linear_le
      _ = P.natDegree := by omega
      _ ≤ padicValNat 2 M + 1 := hdeg
  have hcomb := tsum_shifted_polynomial_eq_integral_superconvergent
    F hF hM hQdeg θ hθ
  have hMreal : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hscale := MeasureTheory.Measure.integral_comp_inv_mul_left
    (fun x : ℝ => P.eval x * rvachevUp F x) (M : ℝ)
  have hintegral :
      (∫ z : ℝ, Q.eval z * rvachevUp F (((M : ℝ))⁻¹ * z)) =
        (M : ℝ) * ∫ x : ℝ, P.eval x * rvachevUp F x := by
    calc
      (∫ z : ℝ, Q.eval z * rvachevUp F (((M : ℝ))⁻¹ * z)) =
          ∫ z : ℝ,
            P.eval (((M : ℝ))⁻¹ * z) *
              rvachevUp F (((M : ℝ))⁻¹ * z) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [Q, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          add_zero]
      _ = (M : ℝ) * ∫ x : ℝ, P.eval x * rvachevUp F x := by
        simpa only [abs_of_nonneg
          (show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M), smul_eq_mul] using
          hscale
  calc
    (∫ x : ℝ, P.eval x * rvachevUp F x) =
        ((M : ℝ))⁻¹ *
          ((M : ℝ) * ∫ x : ℝ, P.eval x * rvachevUp F x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hMreal, one_mul]
    _ = ((M : ℝ))⁻¹ *
          ∫ z : ℝ, Q.eval z * rvachevUp F (((M : ℝ))⁻¹ * z) := by
      rw [hintegral]
    _ = ((M : ℝ))⁻¹ *
          ∑' k : ℤ,
            Q.eval (θ + k) *
              rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) := by
      rw [hcomb]
    _ = ((M : ℝ))⁻¹ *
          ∑' k : ℤ,
            P.eval (((M : ℝ))⁻¹ * (θ + k)) *
              rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) := by
      apply congrArg (fun s : ℝ => ((M : ℝ))⁻¹ * s)
      exact tsum_congr fun k => by
        simp only [Q, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          add_zero]

/-- **Parity-selected deconvolved Rvachev synthesis.**  At a selected phase,
every polynomial of degree at most `v₂(M)+1` is reconstructed by sampling its
Rvachev moment deconvolution against the shifted density lattice.  The formula
is normalized by the mesh spacing `1/M`; it strengthens the arbitrary-phase
degree-`v₂(M)` theorem by exactly one degree. -/
theorem normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp_superconvergent
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {P : ℝ[X]} (hdeg : P.natDegree ≤ padicValNat 2 M + 1)
    (θ : ℝ) (hθ : IsRvachevSuperconvergentPhase M θ) (x : ℝ) :
    ((M : ℝ))⁻¹ *
        ∑' k : ℤ,
          (rvachevDeconvolvedPolynomial P).eval
              (x - ((M : ℝ))⁻¹ * (θ + k)) *
            rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) =
      P.eval x := by
  let Q : ℝ[X] := rvachevDeconvolvedPolynomial P
  let R : ℝ[X] :=
    Q.comp (C (-((M : ℝ))⁻¹) * X + C x)
  have hRdeg : R.natDegree ≤ padicValNat 2 M + 1 := by
    calc
      R.natDegree ≤
          Q.natDegree * (C (-((M : ℝ))⁻¹) * X + C x).natDegree := by
        exact Polynomial.natDegree_comp_le
      _ ≤ Q.natDegree * 1 := by
        exact Nat.mul_le_mul_left Q.natDegree Polynomial.natDegree_linear_le
      _ = Q.natDegree := by omega
      _ ≤ P.natDegree := by
        simpa only [Q] using natDegree_rvachevDeconvolvedPolynomial_le P
      _ ≤ padicValNat 2 M + 1 := hdeg
  have hcomb := tsum_shifted_polynomial_eq_integral_superconvergent
    F hF hM hRdeg θ hθ
  have hMreal : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hsummand : ∀ k : ℤ,
      R.eval (θ + k) *
          rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) =
        Q.eval (x - ((M : ℝ))⁻¹ * (θ + k)) *
          rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) := by
    intro k
    simp only [R, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have harg : -((M : ℝ))⁻¹ * (θ + (k : ℝ)) + x =
        x - ((M : ℝ))⁻¹ * (θ + (k : ℝ)) := by ring
    rw [harg]
  have hintegral :
      (∫ z : ℝ, R.eval z * rvachevUp F (((M : ℝ))⁻¹ * z)) =
        (M : ℝ) * P.eval x := by
    have hscale := MeasureTheory.Measure.integral_comp_inv_mul_left
      (fun y : ℝ => Q.eval (x - y) * rvachevUp F y) (M : ℝ)
    have hsmooth :
        (∫ y : ℝ, Q.eval (x - y) * rvachevUp F y) = P.eval x := by
      simpa only [Q] using
        integral_eval_rvachevDeconvolvedPolynomial_sub_mul_rvachev
          F hF P x
    calc
      (∫ z : ℝ, R.eval z * rvachevUp F (((M : ℝ))⁻¹ * z)) =
          ∫ z : ℝ,
            Q.eval (x - ((M : ℝ))⁻¹ * z) *
              rvachevUp F (((M : ℝ))⁻¹ * z) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [R, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        congr 2
        ring
      _ = (M : ℝ) *
          ∫ y : ℝ, Q.eval (x - y) * rvachevUp F y := by
        simpa only [abs_of_nonneg
          (show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M), smul_eq_mul] using
          hscale
      _ = (M : ℝ) * P.eval x := by rw [hsmooth]
  calc
    ((M : ℝ))⁻¹ *
        ∑' k : ℤ,
          (rvachevDeconvolvedPolynomial P).eval
              (x - ((M : ℝ))⁻¹ * (θ + k)) *
            rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) =
        ((M : ℝ))⁻¹ *
          ∑' k : ℤ,
            R.eval (θ + k) *
              rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) := by
      apply congrArg (fun s : ℝ => ((M : ℝ))⁻¹ * s)
      exact tsum_congr fun k => (hsummand k).symm
    _ = ((M : ℝ))⁻¹ *
          ∫ z : ℝ, R.eval z * rvachevUp F (((M : ℝ))⁻¹ * z) := by
      rw [hcomb]
    _ = ((M : ℝ))⁻¹ * ((M : ℝ) * P.eval x) := by
      rw [hintegral]
    _ = P.eval x := by
      rw [← mul_assoc, inv_mul_cancel₀ hMreal, one_mul]

/-- **Parity-selected Rvachev--Appell synthesis.**  If
`n ≤ v₂(M)+1`, the normalized selected-phase lattice convolution of the
`n`-th Rvachev--Appell polynomial with the Rvachev density reconstructs the
monomial `x ^ n`. -/
theorem normalized_tsum_shifted_rvachevAppellPolynomial_mul_rvachevUp_superconvergent
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {n : ℕ} (hn : n ≤ padicValNat 2 M + 1)
    (θ : ℝ) (hθ : IsRvachevSuperconvergentPhase M θ) (x : ℝ) :
    ((M : ℝ))⁻¹ *
        ∑' k : ℤ,
          (rvachevAppellPolynomial n).eval
              (x - ((M : ℝ))⁻¹ * (θ + k)) *
            rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) =
      x ^ n := by
  have hdeg : (X ^ n : ℝ[X]).natDegree ≤ padicValNat 2 M + 1 := by
    simpa only [Polynomial.natDegree_X_pow] using hn
  simpa only [rvachevDeconvolvedPolynomial_X_pow,
    Polynomial.eval_pow, Polynomial.eval_X] using
    (normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp_superconvergent
      F hF hM (P := X ^ n) hdeg θ hθ x)

end Fabius
