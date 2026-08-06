import PolynomialFormulas.GaussianCubicSolver
import PolynomialFormulas.Quartic

/-!
# A coefficient-only quartic formula over the Gaussian rationals

This module constructs Ferrari's parameters, and hence all four roots, as
actual `ExplicitRadical` expressions.  The only equality test in the Ferrari
construction is the decidable test whether the depressed linear coefficient
`q` is zero.  When it is nonzero, the parameter `m` is the first root returned
by the coefficient-only cubic solver for Ferrari's resolvent cubic.
-/

namespace LeanProofs.PolynomialFormulas

noncomputable section

namespace GaussianQuarticSolver

open ExplicitRadical

/-! ## Gaussian normalization -/

/-- The depressed quadratic coefficient of a Gaussian-rational quartic. -/
def normalizedQuarticP (a b c : GaussianRat) : GaussianRat :=
  quarticP (b / a) (c / a)

/-- The depressed linear coefficient of a Gaussian-rational quartic. -/
def normalizedQuarticQ (a b c d : GaussianRat) : GaussianRat :=
  quarticQ (b / a) (c / a) (d / a)

/-- The depressed constant coefficient of a Gaussian-rational quartic. -/
def normalizedQuarticR (a b c d e : GaussianRat) : GaussianRat :=
  quarticR (b / a) (c / a) (d / a) (e / a)

@[simp]
theorem toComplex_normalizedQuarticP (a b c : GaussianRat) :
    GaussianRat.toComplex (normalizedQuarticP a b c) =
      quarticP (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a) := by
  simp [normalizedQuarticP, quarticP]

@[simp]
theorem toComplex_normalizedQuarticQ (a b c d : GaussianRat) :
    GaussianRat.toComplex (normalizedQuarticQ a b c d) =
      quarticQ (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a)
        (GaussianRat.toComplex d / GaussianRat.toComplex a) := by
  simp [normalizedQuarticQ, quarticQ]

@[simp]
theorem toComplex_normalizedQuarticR (a b c d e : GaussianRat) :
    GaussianRat.toComplex (normalizedQuarticR a b c d e) =
      quarticR (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a)
        (GaussianRat.toComplex d / GaussianRat.toComplex a)
        (GaussianRat.toComplex e / GaussianRat.toComplex a) := by
  simp [normalizedQuarticR, quarticR]

/-! ## A constructive Ferrari certificate -/

/-- Explicit radicals satisfying the five equations needed by Ferrari's
factorization of `y⁴ + p y² + q y + r`. -/
structure FerrariCertificate (p q r : GaussianRat) where
  m : ExplicitRadical
  s : ExplicitRadical
  t : ExplicitRadical
  rho : ExplicitRadical
  sigma : ExplicitRadical
  squareS : s.value ^ 2 = 2 * m.value - GaussianRat.toComplex p
  productST : 2 * s.value * t.value = -GaussianRat.toComplex q
  squareT : t.value ^ 2 = m.value ^ 2 - GaussianRat.toComplex r
  squareRho : rho.value ^ 2 = s.value ^ 2 - 4 * (m.value - t.value)
  squareSigma : sigma.value ^ 2 = s.value ^ 2 - 4 * (m.value + t.value)

/-- Construct Ferrari parameters for a depressed Gaussian-rational quartic.

If `q = 0`, take `m = p/2` and `s = 0`.  Otherwise, take `m` to be the first
radical root of the resolvent cubic
`-8m³ + 4pm² + 8rm + (q² - 4pr)`, then define `s` and `t` in the usual
way. -/
def ferrariCertificate (p q r : GaussianRat) : FerrariCertificate p q r := by
  by_cases hq : q = 0
  · let m := ofGaussian (p / 2)
    let s : ExplicitRadical := 0
    let t := squareRoot (m ^ 2 - ofGaussian r)
    let rho := squareRoot (s ^ 2 - rational 4 * (m - t))
    let sigma := squareRoot (s ^ 2 - rational 4 * (m + t))
    refine
      { m := m
        s := s
        t := t
        rho := rho
        sigma := sigma
        squareS := ?_
        productST := ?_
        squareT := ?_
        squareRho := ?_
        squareSigma := ?_ }
    · simp [m, s]
      ring
    · simp [s, hq]
    · simp [t]
    · simp [rho]
    · simp [sigma]
  · let m := GaussianCubicSolver.cubicRoots (-8) (4 * p) (8 * r)
        (q ^ 2 - 4 * p * r) 0
    have hmCubic :
        cubic (GaussianRat.toComplex (-8 : GaussianRat))
          (GaussianRat.toComplex (4 * p)) (GaussianRat.toComplex (8 * r))
          (GaussianRat.toComplex (q ^ 2 - 4 * p * r)) m.value = 0 := by
      exact GaussianCubicSolver.cubicRoots_sound (by norm_num) 0
    have hres :
        ferrariResolvent (GaussianRat.toComplex p) (GaussianRat.toComplex q)
          (GaussianRat.toComplex r) m.value = 0 := by
      simp only [cubic] at hmCubic
      simp at hmCubic
      unfold ferrariResolvent
      linear_combination hmCubic
    let s := squareRoot (rational 2 * m - ofGaussian p)
    have hs : s.value ^ 2 =
        2 * m.value - GaussianRat.toComplex p := by
      simp [s]
    have hs0 : s.value ≠ 0 := by
      intro hsZero
      have hfactor : 2 * m.value - GaussianRat.toComplex p = 0 := by
        rw [← hs, hsZero]
        norm_num
      have hqSq : GaussianRat.toComplex q ^ 2 = 0 := by
        unfold ferrariResolvent at hres
        rw [hfactor] at hres
        simpa using hres
      have hqComplex : GaussianRat.toComplex q ≠ 0 :=
        GaussianRat.toComplex_ne_zero_of_ne_zero hq
      exact hqComplex ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hqSq)
    let t := -ofGaussian q / (rational 2 * s)
    have hparameters := ferrari_parameters_of_resolvent hres hs hs0
    have hst : 2 * s.value * t.value = -GaussianRat.toComplex q := by
      simpa [t] using hparameters.1
    have ht : t.value ^ 2 = m.value ^ 2 - GaussianRat.toComplex r := by
      simpa [t] using hparameters.2
    let rho := squareRoot (s ^ 2 - rational 4 * (m - t))
    let sigma := squareRoot (s ^ 2 - rational 4 * (m + t))
    refine
      { m := m
        s := s
        t := t
        rho := rho
        sigma := sigma
        squareS := hs
        productST := hst
        squareT := ht
        squareRho := ?_
        squareSigma := ?_ }
    · simp [rho]
    · simp [sigma]

/-- Ferrari data for the depressed form of a Gaussian-rational quartic. -/
def quarticCertificate (a b c d e : GaussianRat) :
    FerrariCertificate (normalizedQuarticP a b c)
      (normalizedQuarticQ a b c d) (normalizedQuarticR a b c d e) :=
  ferrariCertificate _ _ _

/-! ## Four explicit roots -/

/-- The four Ferrari values for a genuine Gaussian-rational quartic, each
carrying an explicit radical expression. -/
def quarticRoots (a b c d e : GaussianRat) (_ha : a ≠ 0) :
    Fin 4 → ExplicitRadical :=
  let w := quarticCertificate a b c d e
  let shift := ofGaussian ((b / a) / 4)
  ![(w.s + w.rho) / rational 2 - shift,
    (w.s - w.rho) / rational 2 - shift,
    (-w.s + w.sigma) / rational 2 - shift,
    (-w.s - w.sigma) / rational 2 - shift]

/-- Evaluating a returned expression gives the corresponding entry of the
abstract Ferrari solver. -/
@[simp]
theorem quarticRoots_value (a b c d e : GaussianRat) (ha : a ≠ 0)
    (i : Fin 4) :
    (quarticRoots a b c d e ha i).value =
      let w := quarticCertificate a b c d e
      solveQuartic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
        (GaussianRat.toComplex c) (GaussianRat.toComplex d)
        (GaussianRat.toComplex e) w.m.value w.s.value w.t.value
        w.rho.value w.sigma.value i := by
  fin_cases i <;> simp [quarticRoots, solveQuartic, solveDepressedQuartic]

/-- Every radical returned by `quarticRoots` is a root of the input quartic. -/
theorem quarticRoots_sound {a b c d e : GaussianRat} (ha : a ≠ 0)
    (i : Fin 4) :
    quartic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) (GaussianRat.toComplex d)
      (GaussianRat.toComplex e) (quarticRoots a b c d e ha i).value = 0 := by
  let w := quarticCertificate a b c d e
  rw [quarticRoots_value]
  exact solveQuartic_correct
    (GaussianRat.toComplex_ne_zero_of_ne_zero ha)
    (by simpa [w] using w.squareS)
    (by simpa [w] using w.productST)
    (by simpa [w] using w.squareT)
    w.squareRho w.squareSigma i

/-- Every complex root of a genuine Gaussian-rational quartic occurs in the
four-entry radical collection. -/
theorem quarticRoots_exhaustive {a b c d e : GaussianRat} (ha : a ≠ 0)
    {x : ℂ}
    (hx : quartic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) (GaussianRat.toComplex d)
      (GaussianRat.toComplex e) x = 0) :
    ∃ i, (quarticRoots a b c d e ha i).value = x := by
  let w := quarticCertificate a b c d e
  obtain ⟨i, hi⟩ := solveQuartic_exhaustive
    (m := w.m.value) (s := w.s.value) (t := w.t.value)
    (ρ := w.rho.value) (σ := w.sigma.value)
    (GaussianRat.toComplex_ne_zero_of_ne_zero ha)
    (by simpa [w] using w.squareS)
    (by simpa [w] using w.productST)
    (by simpa [w] using w.squareT)
    w.squareRho w.squareSigma hx
  refine ⟨i, ?_⟩
  rw [quarticRoots_value]
  exact hi

/-- Exact root characterization for the coefficient-only quartic solver. -/
theorem quartic_eq_zero_iff_roots {a b c d e : GaussianRat} (ha : a ≠ 0)
    (x : ℂ) :
    quartic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) (GaussianRat.toComplex d)
      (GaussianRat.toComplex e) x = 0 ↔
        ∃ i, (quarticRoots a b c d e ha i).value = x := by
  constructor
  · exact quarticRoots_exhaustive ha
  · rintro ⟨i, rfl⟩
    exact quarticRoots_sound ha i

/-- The quartic is its leading coefficient times the four linear factors
supplied by the coefficient-only radical solver. -/
theorem quarticRoots_factorization {a b c d e : GaussianRat} (ha : a ≠ 0)
    (x : ℂ) :
    quartic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) (GaussianRat.toComplex d)
      (GaussianRat.toComplex e) x =
        GaussianRat.toComplex a *
          ((x - (quarticRoots a b c d e ha 0).value) *
            (x - (quarticRoots a b c d e ha 1).value) *
            (x - (quarticRoots a b c d e ha 2).value) *
            (x - (quarticRoots a b c d e ha 3).value)) := by
  let w := quarticCertificate a b c d e
  rw [quarticRoots_value, quarticRoots_value, quarticRoots_value,
    quarticRoots_value]
  exact LeanProofs.PolynomialFormulas.quartic_factorization
    (m := w.m.value) (s := w.s.value) (t := w.t.value)
    (ρ := w.rho.value) (σ := w.sigma.value)
    (GaussianRat.toComplex_ne_zero_of_ne_zero ha)
    (by simpa [w] using w.squareS)
    (by simpa [w] using w.productST)
    (by simpa [w] using w.squareT)
    w.squareRho w.squareSigma

end GaussianQuarticSolver

end

end LeanProofs.PolynomialFormulas
