import IPRADerivations.Analysis.GaussianBetaFiniteEulerComparison
import IPRADerivations.Analysis.GaussianGammaRightHalfPlane

/-!
# Cofinal original beta quadrature converges to the original Gamma name

The finite beta quadrature is compared to the finite Euler reciprocal
at an intermediate precision. The original C15 rate then compares
the reciprocal to the original right-half-plane Gamma observation.
The degree, mesh and evaluation precision have explicit sufficient
thresholds, with no restriction on the requested Gamma precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaFiniteGammaComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerInverseConvergence (coefficientNumerator coefficientDenominator)
open GaussianGammaReciprocalInverse (gammaF gammaData lambdaNumerator lambda_positive)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianBetaFiniteEulerComparison (observation slack)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏ le one R
def minimumDegree (t R A : PTm n) : PTm n :=
  two*R+GaussianGammaPerturbationExponent.numerator R+coefficientNumerator R A*unit (slack t)
def minimumCells (t z R B A N : PTm n) : PTm n :=
  GaussianBetaFiniteEulerComparison.minimumCells (slack t) z R B A N
def minimumPrecision (t z R B A N M : PTm n) : PTm n :=
  GaussianBetaFiniteEulerComparison.minimumPrecision (slack t) z R B A N M

theorem degree_budgets (t R A N : PTm n) (h : Γ ⊢[PRAAx] le (minimumDegree t R A) N) :
    Γ ⊢[PRAAx] le (two*R) N ⋏
      le (GaussianGammaPerturbationExponent.numerator R) N ⋏
      le (coefficientNumerator R A*unit (slack t)) N := by
  let L := two*R
  let C := GaussianGammaPerturbationExponent.numerator R
  let D := coefficientNumerator R A*unit (slack t)
  have hL : Γ ⊢[PRAAx] le L ((L+C)+D) := le_trans (le_add_right _ _) (le_add_right _ _)
  have hC : Γ ⊢[PRAAx] le C ((L+C)+D) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_add_right C (L+D))
  have hD : Γ ⊢[PRAAx] le D ((L+C)+D) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_add_right D (L+C))
  exact .andI (le_trans hL h) (.andI (le_trans hC h) (le_trans hD h))

/-- Compare any actual point within two observation units of the
original finite Euler reciprocal to the original Gamma observation. -/
theorem from_finite_euler_error (t q z R B A N Q : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (hN : Γ ⊢[PRAAx] le (minimumDegree t R A) N)
    (near : Γ ⊢[PRAAx] distanceBounded Q
      (ap2 eulerF (slack t) (eulerData z R B A N)) two (unit (slack t))) :
    Γ ⊢[PRAAx] distanceBounded Q (ap2 gammaF q (gammaData z R B A)) (unit t+unit q) (unit t*unit q) := by
  let j := slack t
  let U := unit j
  let V := unit q
  let D := coefficientDenominator R one N
  let S := coefficientNumerator R A
  let X := ap2 eulerF j (eulerData z R B A N)
  let Y := ap2 gammaF q (gammaData z R B A)
  have degree := degree_budgets t R A N hN
  have bits : Γ ⊢[PRAAx] GaussianBetaFiniteEulerComparison.source z R B A N :=
    .andI h.andE₁ (.andI h.andE₂ degree.andE₁)
  have positive_degree := GaussianBetaFiniteEulerComparison.degree_positive z R B A N bits
  have hU := unit_positive (Γ := Γ) j
  have hV := unit_positive (Γ := Γ) q
  have hUV : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ hU hV
  have lam := (lambda_positive R one A (le_refl one) h.andE₁.andE₁).andE₁
  have square := positive_product _ _ lam lam
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ square positive_degree
  have qNear : Γ ⊢[PRAAx] distanceBounded Q X (two*V) (U*V) :=
    distance_radius_mono _ _ _ _ _ _ hU hUV (le_of_eq_add (d := zero) (by ipra_ring)) near
  have s0 : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B :=
    .andI h.andE₂ h.andE₁.andE₂.andE₁
  have rate := GaussianGammaRightHalfPlane.original_right_half_plane_euler_rate z R B A N s0
    h.andE₁.andE₁ h.andE₁.andE₂.andE₂ (.andI degree.andE₁ degree.andE₂.andE₁)
  have obs := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ j q rate
  have budget : Γ ⊢[PRAAx] le (S*U) D :=
    le_trans degree.andE₂.andE₂
      (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N square))
  have growth :
      Γ ⊢[PRAAx] le (GaussianNamedInverseRate.rateNumerator S D j q*(U*V))
        ((two*V+U)*GaussianNamedInverseRate.rateDenominator D j q) := by
    change Γ ⊢[PRAAx] le ((S*U*V+D*(U+V))*(U*V)) ((two*V+U)*(D*U*V))
    exact le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (D*(U+V)*(U*V)) (mul_le_mul_right (U*V*V) budget))
  have next : Γ ⊢[PRAAx] distanceBounded X Y (two*V+U) (U*V) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hD hU) hV) hUV growth obs
  have both := distance_triangle_same Q X Y (two*V) (two*V+U) (U*V) hUV qNear next
  have units : Γ ⊢[PRAAx] U ≐ num 4*unit t := by
    change Γ ⊢[PRAAx] pw two (succ (succ t)) ≐ num 4*pw two t
    exact (pw_succ two (succ t)).eqTrans ((congrMul (pw_succ two t) (.eqRefl _)).eqTrans (by ipra_ring))
  have exactRate : Γ ⊢[PRAAx] le ((two*V+(two*V+U))*(unit t*V)) ((unit t+V)*(U*V)) := by
    let W := num 4*unit t
    have lhs : Γ ⊢[PRAAx] (two*V+(two*V+U))*(unit t*V) ≐ (two*V+(two*V+W))*(unit t*V) :=
      congrMul (congrAdd (.eqRefl _) (congrAdd (.eqRefl _) units)) (.eqRefl _)
    have rhs : Γ ⊢[PRAAx] (unit t+V)*(U*V) ≐ (unit t+V)*(W*V) :=
      congrMul (.eqRefl _) (congrMul units (.eqRefl _))
    exact le_congr lhs.eqSymm rhs.eqSymm (le_of_eq_add (d := zero) (by dsimp only [W]; ipra_ring))
  exact distance_radius_mono _ _ _ _ _ _ hUV (positive_product _ _ (unit_positive t) hV) exactRate both

theorem original_quadrature_gamma_error (t p q z R B A N M : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le (minimumDegree t R A) N)
    (hM : Γ ⊢[PRAAx] le (minimumCells t z R B A N) M)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t z R B A N M) p) :
    Γ ⊢[PRAAx] distanceBounded (observation (slack t) p z R B A N M)
      (ap2 gammaF q (gammaData z R B A)) (unit t+unit q) (unit t*unit q) := by
  let j := slack t
  let U := unit j
  have bits : Γ ⊢[PRAAx] GaussianBetaFiniteEulerComparison.source z R B A N :=
    .andI h.andE₁ (.andI h.andE₂ (degree_budgets t R A N hN).andE₁)
  have hU := unit_positive (Γ := Γ) j
  have raw := GaussianBetaFiniteEulerComparison.original_quadrature_euler_error j p j z R B A N M bits hM hp
  exact from_finite_euler_error t q z R B A N _ h hN
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hU
      (le_of_eq_add (d := zero) (by ipra_ring)) raw)

theorem computed_quadrature_gamma_error (t q z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx]
    let N := minimumDegree t R A
    let M := minimumCells t z R B A N
    let p := minimumPrecision t z R B A N M
    distanceBounded (observation (slack t) p z R B A N M) (ap2 gammaF q (gammaData z R B A))
      (unit t+unit q) (unit t*unit q) :=
  original_quadrature_gamma_error _ _ _ _ _ _ _ _ _ h (le_refl _) (le_refl _) (le_refl _)

theorem original_refinable_finite_beta_quadrature_Gamma_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 3) (var 4) (var 5) (var 6) ⋏
      le (minimumDegree (var 0) (var 4) (var 6)) (var 7) ⋏
      le (minimumCells (var 0) (var 3) (var 4) (var 5) (var 6) (var 7)) (var 8) ⋏
      le (minimumPrecision (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) (var 1)) ⟶
      distanceBounded (observation (slack (var 0)) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (ap2 gammaF (var 2) (gammaData (var 3) (var 4) (var 5) (var 6)))
        (unit (var 0)+unit (var 2)) (unit (var 0)*unit (var 2))) :=
  closeUniv 9 (.impI (original_quadrature_gamma_error _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

theorem original_computed_finite_beta_quadrature_Gamma_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶
      let N := minimumDegree (var 0) (var 3) (var 5)
      let M := minimumCells (var 0) (var 2) (var 3) (var 4) (var 5) N
      let p := minimumPrecision (var 0) (var 2) (var 3) (var 4) (var 5) N M
      distanceBounded (observation (slack (var 0)) p (var 2) (var 3) (var 4) (var 5) N M)
        (ap2 gammaF (var 1) (gammaData (var 2) (var 3) (var 4) (var 5)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (computed_quadrature_gamma_error _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaFiniteGammaComparison
