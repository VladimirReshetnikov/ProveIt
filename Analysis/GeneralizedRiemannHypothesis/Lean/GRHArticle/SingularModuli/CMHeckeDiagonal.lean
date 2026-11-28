import GRHArticle.SingularModuli.ClassPolynomialQEnclosure

/-!
# Hecke diagonals at the quartic CM points

For the reduced forms of discriminant -55 and -68, an explicit integral
Möbius transformation connects each point to one of its degree-59 or
degree-17 Hecke translates. The analytic orbit polynomial therefore
vanishes at the original modular invariant on the diagonal.
-/

namespace GRHArticle.SingularModuli

open Polynomial UpperHalfPlane
open scoped MatrixGroups BigOperators

/-- The upper half-plane point with coordinate `(z + t) / p`. -/
noncomputable def heckeShiftPoint (p : ℕ+) (t : ℕ) (z : ℍ) : ℍ :=
  ⟨((z : ℂ) + (t : ℂ)) / (p : ℝ), by
    rw [Complex.div_ofReal_im, Complex.add_im, Complex.natCast_im, add_zero]
    change 0 < z.im / (p : ℝ)
    exact div_pos z.im_pos (show (0 : ℝ) < p by positivity)⟩

/-- The upper half-plane point with coordinate `p * z`. -/
noncomputable def heckeScaledPoint (p : ℕ+) (z : ℍ) : ℍ :=
  ⟨(p : ℝ) * (z : ℂ), by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    change 0 < (p : ℝ) * z.im
    exact mul_pos (show (0 : ℝ) < p by positivity) z.im_pos⟩

/-- The analytic orbit polynomial for the standard prime-level translates.
Its coefficients are complex functions of the input point. -/
noncomputable def analyticPrimeHeckePolynomial (p : ℕ+) (z : ℍ) : ℂ[X] :=
  (X - C (modularInvariant (heckeScaledPoint p z))) *
    ∏ t ∈ Finset.range (p : ℕ), (X - C (modularInvariant (heckeShiftPoint p t z)))

private def modularMatrix (a b c d : ℤ) (h : a * d - b * c = 1) : SL(2, ℤ) :=
  ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two] using h⟩

/-- A determinant-one matrix certificate exhibiting a prime Hecke translate
of a quadratic point with the same modular invariant. -/
theorem modularInvariant_heckeShift_of_form (D p : ℕ+) (f : FormCoefficients)
    (hf : f.b ^ 2 - 4 * (f.a : ℤ) * f.c = -(D : ℤ)) (t : ℕ)
    (a b c d k : ℤ) (hdet : a * d - b * c = 1)
    (h₂ : c = k * (f.a : ℤ))
    (h₁ : c * (t : ℤ) + d - (p : ℤ) * a = k * f.b)
    (h₀ : d * (t : ℤ) - (p : ℤ) * b = k * f.c) :
    modularInvariant (heckeShiftPoint p t (quadraticPoint D f.a f.b)) =
      modularInvariant (quadraticPoint D f.a f.b) := by
  let z := quadraticPoint D f.a f.b
  let g := modularMatrix a b c d hdet
  have hroot : (f.a : ℂ) * (z : ℂ) ^ 2 + (f.b : ℂ) * (z : ℂ) + (f.c : ℂ) = 0 :=
    quadraticPoint_isRoot D f.a f.b f.c hf
  have hc₂ : (c : ℂ) = (k : ℂ) * (f.a : ℂ) := by exact_mod_cast h₂
  have hc₁ : (c : ℂ) * (t : ℂ) + (d : ℂ) - (p : ℂ) * (a : ℂ) = (k : ℂ) * (f.b : ℂ) := by
    exact_mod_cast h₁
  have hc₀ : (d : ℂ) * (t : ℂ) - (p : ℂ) * (b : ℂ) = (k : ℂ) * (f.c : ℂ) := by
    exact_mod_cast h₀
  have hrel : ((c : ℂ) * (z : ℂ) + (d : ℂ)) * ((z : ℂ) + (t : ℂ)) -
      (p : ℂ) * ((a : ℂ) * (z : ℂ) + (b : ℂ)) = 0 := by
    calc
      _ = (c : ℂ) * (z : ℂ) ^ 2 +
          ((c : ℂ) * (t : ℂ) + (d : ℂ) - (p : ℂ) * (a : ℂ)) * (z : ℂ) +
          ((d : ℂ) * (t : ℂ) - (p : ℂ) * (b : ℂ)) := by ring
      _ = (k : ℂ) * ((f.a : ℂ) * (z : ℂ) ^ 2 + (f.b : ℂ) * (z : ℂ) + (f.c : ℂ)) := by
        rw [hc₁, hc₀, hc₂]
        ring
      _ = 0 := by rw [hroot, mul_zero]
  have hden : (c : ℂ) * (z : ℂ) + (d : ℂ) ≠ 0 := by
    have hh := denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) z
    simpa [denom, g, modularMatrix, Matrix.SpecialLinearGroup.mapGL] using hh
  have hp : ((p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (0 : ℝ) < p by positivity).ne'
  have hshift : heckeShiftPoint p t z = g • z := by
    rw [UpperHalfPlane.ext_iff, coe_specialLinearGroup_apply]
    change ((z : ℂ) + (t : ℂ)) / ((p : ℝ) : ℂ) =
      (((Int.castRingHom ℝ) a : ℂ) * (z : ℂ) + ((Int.castRingHom ℝ) b : ℂ)) /
      (((Int.castRingHom ℝ) c : ℂ) * (z : ℂ) + ((Int.castRingHom ℝ) d : ℂ))
    simp only [Int.coe_castRingHom, Complex.ofReal_intCast]
    apply (div_eq_div_iff hp hden).2
    have hpcast : ((p : ℝ) : ℂ) = (p : ℂ) := Complex.ofReal_natCast (p : ℕ)
    rw [hpcast]
    simpa only [mul_comm] using (sub_eq_zero.mp hrel)
  change modularInvariant (heckeShiftPoint p t z) = modularInvariant z
  rw [hshift]
  exact modularInvariant_smul g z

def quartic55HeckeShift : Fin 4 → ℕ := ![31, 15, 45, 8]

def quartic68HeckeShift : Fin 4 → ℕ := ![0, 9, 11, 6]

theorem quartic55_heckeShift_invariant (i : Fin 4) :
    let f := quartic55Form i
    let z := quadraticPoint 55 f.a f.b
    modularInvariant (heckeShiftPoint 59 (quartic55HeckeShift i) z) = modularInvariant z := by
  fin_cases i
  · exact modularInvariant_heckeShift_of_form 55 59 _ (by decide) _
      (-1) 1 (-2) 1 (-2) (by decide) (by decide) (by decide) (by decide)
  · exact modularInvariant_heckeShift_of_form 55 59 _ (by decide) _
      (-1) 1 (-4) 3 (-2) (by decide) (by decide) (by decide) (by decide)
  · exact modularInvariant_heckeShift_of_form 55 59 _ (by decide) _
      (-3) 1 (-4) 1 (-2) (by decide) (by decide) (by decide) (by decide)
  · exact modularInvariant_heckeShift_of_form 55 59 _ (by decide) _
      (-1) 0 (-8) (-1) (-2) (by decide) (by decide) (by decide) (by decide)

theorem quartic68_heckeShift_invariant (i : Fin 4) :
    let f := quartic68Form i
    let z := quadraticPoint 68 f.a f.b
    modularInvariant (heckeShiftPoint 17 (quartic68HeckeShift i) z) = modularInvariant z := by
  fin_cases i
  · exact modularInvariant_heckeShift_of_form 68 17 _ (by decide) _
      0 1 (-1) 0 (-1) (by decide) (by decide) (by decide) (by decide)
  · exact modularInvariant_heckeShift_of_form 68 17 _ (by decide) _
      (-1) 0 (-2) (-1) (-1) (by decide) (by decide) (by decide) (by decide)
  · exact modularInvariant_heckeShift_of_form 68 17 _ (by decide) _
      (-2) 1 (-3) 1 (-1) (by decide) (by decide) (by decide) (by decide)
  · exact modularInvariant_heckeShift_of_form 68 17 _ (by decide) _
      (-1) 0 (-3) (-1) (-1) (by decide) (by decide) (by decide) (by decide)

/-- A translate with the same invariant gives diagonal vanishing of the orbit product. -/
theorem analyticPrimeHeckePolynomial_diagonal_of_shift {p : ℕ+} {t : ℕ} {z : ℍ}
    (ht : t < (p : ℕ)) (hj : modularInvariant (heckeShiftPoint p t z) = modularInvariant z) :
    (analyticPrimeHeckePolynomial p z).eval (modularInvariant z) = 0 := by
  simp only [analyticPrimeHeckePolynomial, eval_mul, eval_prod, eval_sub, eval_X, eval_C]
  apply mul_eq_zero_of_right
  exact Finset.prod_eq_zero (Finset.mem_range.mpr ht) (sub_eq_zero.mpr hj.symm)

theorem quartic55_analyticPrimeHeckePolynomial_diagonal (i : Fin 4) :
    let f := quartic55Form i
    let z := quadraticPoint 55 f.a f.b
    (analyticPrimeHeckePolynomial 59 z).eval (modularInvariant z) = 0 :=
  analyticPrimeHeckePolynomial_diagonal_of_shift
    (by fin_cases i <;> decide) (quartic55_heckeShift_invariant i)

theorem quartic68_analyticPrimeHeckePolynomial_diagonal (i : Fin 4) :
    let f := quartic68Form i
    let z := quadraticPoint 68 f.a f.b
    (analyticPrimeHeckePolynomial 17 z).eval (modularInvariant z) = 0 :=
  analyticPrimeHeckePolynomial_diagonal_of_shift
    (by fin_cases i <;> decide) (quartic68_heckeShift_invariant i)

end GRHArticle.SingularModuli
