import FabiusFunction.ThueMorseGDirichlet

/-!
# The first two laws of the Thue--Morse Gamma tower

For a positive real parameter, the entire shifted Dirichlet continuation

`D(s,a) = Γ(s)⁻¹ * mellin (mellinKernel a) s`

vanishes at every nonpositive integer.  The exact reciprocal-Gamma jet from
`ReciprocalGammaJets` identifies its first surviving derivative:

`D'(-r,a) = (-1)^r r! * M(-r,a)`.

Differentiating the already-formalized dyadic equation in the spectral
variable then gives the dyadic law for these derivatives.  Exponentiating
packages them as the first two rigorous laws of the Thue--Morse Gamma tower.

The parameter differential ladder in `a` is deliberately not asserted here;
it additionally requires a parameter-under-the-Mellin-integral theorem.

## Main results

* `hasDerivAt_dirichletMellinContinuation_neg_nat` and
  `deriv_dirichletMellinContinuation_neg_nat` identify every trivial-zero jet.
* `thueMorseGammaLog` and `thueMorseGammaTower` define the logarithmic and
  exponentiated tower levels.
* `thueMorseGammaLog_eq_mellin` is the exact Mellin formula.
* `thueMorseGammaLog_dyadic` and `thueMorseGammaTower_dyadic` are the dyadic
  parameter laws.
* `ofReal_exp_mpLimit_eq_gammaTower_div` identifies the master-product limit
  with the quotient of level-zero tower values.
-/

set_option autoImplicit false

open Complex

namespace Fabius

/-- The exact derivative of the entire Dirichlet--Mellin continuation at its
trivial zero `-r`. -/
theorem hasDerivAt_dirichletMellinContinuation_neg_nat
    (a : ℝ) (ha : 0 < a) (r : ℕ) :
    HasDerivAt (dirichletMellinContinuation a)
      (((-1 : ℂ) ^ r * r.factorial) *
        mellin (mellinKernel a) (-(r : ℂ))) (-(r : ℂ)) := by
  show HasDerivAt
    (fun s : ℂ => (Complex.Gamma s)⁻¹ * mellin (mellinKernel a) s) _ _
  have hd := (hasDerivAt_Gamma_inv_neg_nat r).mul
    (mellin_mellinKernel_differentiable a ha (-(r : ℂ))).hasDerivAt
  simpa [Pi.mul_def, Complex.Gamma_neg_nat_eq_zero] using hd

/-- `deriv` form of the exact trivial-zero jet. -/
theorem deriv_dirichletMellinContinuation_neg_nat
    (a : ℝ) (ha : 0 < a) (r : ℕ) :
    deriv (dirichletMellinContinuation a) (-(r : ℂ)) =
      ((-1 : ℂ) ^ r * r.factorial) *
        mellin (mellinKernel a) (-(r : ℂ)) :=
  (hasDerivAt_dirichletMellinContinuation_neg_nat a ha r).deriv

/-- The logarithmic level `r` of the Thue--Morse Gamma tower.

This definition is total in `a`; its Mellin, integral, and dyadic laws below
assume `a > 0`. -/
noncomputable def thueMorseGammaLog (r : ℕ) (a : ℝ) : ℂ :=
  deriv (dirichletMellinContinuation a) (-(r : ℂ))

/-- The exponentiated level `r` of the Thue--Morse Gamma tower.

This definition is total in `a`; its analytic identifications below assume
`a > 0`. -/
noncomputable def thueMorseGammaTower (r : ℕ) (a : ℝ) : ℂ :=
  Complex.exp (thueMorseGammaLog r a)

/-- Exact Mellin formula for the logarithmic tower level:
`L_r(a) = (-1)^r r! M(-r,a)`. -/
theorem thueMorseGammaLog_eq_mellin (r : ℕ) (a : ℝ) (ha : 0 < a) :
    thueMorseGammaLog r a =
      ((-1 : ℂ) ^ r * r.factorial) *
        mellin (mellinKernel a) (-(r : ℂ)) := by
  exact deriv_dirichletMellinContinuation_neg_nat a ha r

/-- Integral form of the logarithmic tower level.  The real integral is the
Mellin value at exponent `-r`; boundary flatness makes it convergent for every
`r` when `a > 0`. -/
theorem thueMorseGammaLog_eq_integral (r : ℕ) (a : ℝ) (ha : 0 < a) :
    thueMorseGammaLog r a =
      ((-1 : ℂ) ^ r * r.factorial) *
        (((∫ t in Set.Ioi (0 : ℝ),
          t ^ ((-(r : ℝ)) - 1) *
            (Real.exp (-(a * t)) * lacunaryExpProduct t) : ℝ)) : ℂ) := by
  rw [thueMorseGammaLog_eq_mellin r a ha]
  rw [show (-(r : ℂ)) = ((-(r : ℝ) : ℝ) : ℂ) by push_cast; rfl,
    mellin_mellinKernel_ofReal]

/-- Differentiating the entire dyadic equation at `s = -r` gives the exact
dyadic law for logarithmic tower levels. -/
theorem thueMorseGammaLog_dyadic (r : ℕ) (a : ℝ) (ha : 0 < a) :
    thueMorseGammaLog r a =
      (2 : ℂ) ^ r *
        (thueMorseGammaLog r (a / 2) -
          thueMorseGammaLog r ((a + 1) / 2)) := by
  have ha2 : (0 : ℝ) < a / 2 := by linarith
  have ha3 : (0 : ℝ) < (a + 1) / 2 := by linarith
  let s0 : ℂ := -(r : ℂ)
  have hpow : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (-s)) s0 :=
    (differentiable_neg.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))) s0
  have hdiff : HasDerivAt
      (fun s : ℂ => dirichletMellinContinuation (a / 2) s -
        dirichletMellinContinuation ((a + 1) / 2) s)
      (thueMorseGammaLog r (a / 2) -
        thueMorseGammaLog r ((a + 1) / 2)) s0 := by
    exact ((dirichletMellinContinuation_differentiable (a / 2) ha2 s0).hasDerivAt).sub
      ((dirichletMellinContinuation_differentiable
        ((a + 1) / 2) ha3 s0).hasDerivAt)
  have hprodDeriv :
      deriv (fun s : ℂ => (2 : ℂ) ^ (-s) *
        (dirichletMellinContinuation (a / 2) s -
          dirichletMellinContinuation ((a + 1) / 2) s)) s0 =
        deriv (fun s : ℂ => (2 : ℂ) ^ (-s)) s0 *
            (dirichletMellinContinuation (a / 2) s0 -
              dirichletMellinContinuation ((a + 1) / 2) s0) +
          (2 : ℂ) ^ (-s0) *
            (thueMorseGammaLog r (a / 2) -
              thueMorseGammaLog r ((a + 1) / 2)) := by
    have hraw := (hpow.hasDerivAt.mul hdiff).deriv
    have hmul :
        (fun s : ℂ => (2 : ℂ) ^ (-s)) *
            (fun s : ℂ => dirichletMellinContinuation (a / 2) s -
              dirichletMellinContinuation ((a + 1) / 2) s) =
          fun s : ℂ => (2 : ℂ) ^ (-s) *
            (dirichletMellinContinuation (a / 2) s -
              dirichletMellinContinuation ((a + 1) / 2) s) := by
      funext s
      rfl
    rw [hmul] at hraw
    exact hraw
  have hfun : dirichletMellinContinuation a =
      fun s : ℂ => (2 : ℂ) ^ (-s) *
        (dirichletMellinContinuation (a / 2) s -
          dirichletMellinContinuation ((a + 1) / 2) s) := by
    funext s
    exact dirichletMellinContinuation_dyadic a ha s
  rw [thueMorseGammaLog, hfun]
  change deriv (fun s : ℂ => (2 : ℂ) ^ (-s) *
    (dirichletMellinContinuation (a / 2) s -
      dirichletMellinContinuation ((a + 1) / 2) s)) s0 = _
  rw [hprodDeriv]
  simp only [s0, dirichletMellinContinuation_neg_natCast, sub_self,
    mul_zero, zero_add, neg_neg, Complex.cpow_natCast]

/-- Exponentiated dyadic law for the Thue--Morse Gamma tower. -/
theorem thueMorseGammaTower_dyadic (r : ℕ) (a : ℝ) (ha : 0 < a) :
    thueMorseGammaTower r a =
      (thueMorseGammaTower r (a / 2) /
        thueMorseGammaTower r ((a + 1) / 2)) ^ (2 ^ r) := by
  rw [thueMorseGammaTower, thueMorseGammaLog_dyadic r a ha,
    thueMorseGammaTower, thueMorseGammaTower, ← Complex.exp_sub,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The real master-product limit, after the canonical embedding into
`ℂ`, is the quotient of the level-zero Gamma-tower values. -/
theorem ofReal_exp_mpLimit_eq_gammaTower_div
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((Real.exp (mpLimit a b) : ℝ) : ℂ) =
      thueMorseGammaTower 0 b / thueMorseGammaTower 0 a := by
  rw [Complex.ofReal_exp, mpLimit_eq_deriv_sub a b ha hb]
  simp only [thueMorseGammaTower, thueMorseGammaLog, Nat.cast_zero,
    neg_zero, Complex.exp_sub]

end Fabius
