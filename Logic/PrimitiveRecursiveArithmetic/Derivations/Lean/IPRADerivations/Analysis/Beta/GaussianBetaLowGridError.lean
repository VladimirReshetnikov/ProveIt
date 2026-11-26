import IPRADerivations.Analysis.Beta.GaussianBetaLowRowError

/-!
# The literal beta and Euler quadratures below time one

Every actual shared-grid point inherits the original input certificate,
positive time and beta half-support from the supplied numerical endpoint
and degree bounds. The original finite sum distance and original weight
preserve the exact coefficient one in the 1/N row error. Width zero is
allowed; the two independent observation errors remain explicit.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaLowGridError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaKernelGridComparison (evaluatorF sampleDataBeta row_at)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight_bound)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem row_source (i M a C E z R B A N : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hN : Γ ⊢[PRAAx] le two N) (hRight : Γ ⊢[PRAAx] le (a+C) E) (hi : Γ ⊢[PRAAx] lt i M) : Γ ⊢[PRAAx]
    GaussianBetaLowRowError.source z R B A (a*M+C*i) (E*M) N := by
  let u := a*M+C*i
  let v := E*M
  have hu : Γ ⊢[PRAAx] le one u := le_trans (positive_product _ _ ha hM) (le_add_right _ _)
  have hv : Γ ⊢[PRAAx] le one v := positive_product _ _ hE hM
  have within : Γ ⊢[PRAAx] le u v :=
    le_trans (add_le_add₂ (le_refl (a*M)) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl C) (le_of_lt hi)))
      (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right M hRight))
  have support : Γ ⊢[PRAAx] le (two*u) (v*N) := le_trans (le_congr (mul_comm u two) (mul_comm v two) (mul_le_mul_right two within))
    (le_congr (.eqRefl _) (mul_comm N v) (mul_le_mul_right v hN))
  exact .andI (.andI h (.andI (.andI hu hv) within))
    (.andI hv (.andI (le_trans (le_succ_self one) hN) support))

theorem row_distance (i p v M a C E z R B A N : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hN : Γ ⊢[PRAAx] le two N) (hRight : Γ ⊢[PRAAx] le (a+C) E) (hi : Γ ⊢[PRAAx] lt i M) : Γ ⊢[PRAAx]
    distanceBounded
      (inst2 (sampleBody evaluatorF) i (sampleData p M a C E (sampleDataBeta z B N)))
      (inst2 (sampleBody GaussianEulerIntegrandName.evaluatorF) i (sampleData v M a C E (GaussianEulerIntegrandName.fixedData z B)))
      (unit p*unit v+N*(unit p+unit v)) (N*unit p*unit v) := by
  have left := (sample_body_at (Γ := Γ) evaluatorF i p M a C E (sampleDataBeta z B N)).eqTrans
    (row_at p z B (a*M+C*i) (E*M) N)
  have right := sample_body_at (Γ := Γ) GaussianEulerIntegrandName.evaluatorF i v M a C E (GaussianEulerIntegrandName.fixedData z B)
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianBetaLowRowError.original_low_row_error p v z R B A (a*M+C*i) (E*M) N
      (row_source i M a C E z R B A N hM ha hE h hN hRight hi))

theorem all_rows (p v M a C E z R B A N : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hN : Γ ⊢[PRAAx] le two N) (hRight : Γ ⊢[PRAAx] le (a+C) E) : Γ ⊢[PRAAx]
    termsDistance (sampleBody evaluatorF) (sampleBody GaussianEulerIntegrandName.evaluatorF) M
      (sampleData p M a C E (sampleDataBeta z B N)) (sampleData v M a C E (GaussianEulerIntegrandName.fixedData z B))
      (unit p*unit v+N*(unit p+unit v)) (N*unit p*unit v) := by
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
  have as' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using ha.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le two (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a+Syn.shift C) (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hRight.shift
  refine .allI (.impI ?_)
  simpa only [termsDistance,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
    GaussianBetaKernelGridComparison.subst_sampleDataBeta,GaussianEulerIntegrandName.subst_fixedData,
    GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul] using
    row_distance (var 0) (Syn.shift p) (Syn.shift v) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E)
      (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift N) ms.wk as'.wk es.wk hs.wk ns.wk rs.wk Prf.hyp0

/-- Actual shared-mesh quadratures have error at most
(C/E)*(1/N+eps_p+eps_v), including C=0. -/
theorem original_low_grid_error (p v M a C E z R B A N : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hN : Γ ⊢[PRAAx] le two N) (hRight : Γ ⊢[PRAAx] le (a+C) E) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF p M a C E (sampleDataBeta z B N))
      (quadrature GaussianEulerIntegrandName.evaluatorF v M a C E (GaussianEulerIntegrandName.fixedData z B))
      (C*(unit p*unit v+N*(unit p+unit v))) (E*(N*unit p*unit v)) := by
  let D := N*unit p*unit v
  have n := le_trans (le_succ_self one) hN
  have hd := positive_product (Γ := Γ) _ _ (positive_product _ _ n (unit_positive p)) (unit_positive v)
  have sum := sum_distance _ _ M _ _ _ D hd (all_rows p v M a C E z R B A N hM ha hE h hN hRight)
  have raw := GaussianRationalReciprocal.bounded_product _ _ C (E*M) _ D (positive_product _ _ hE hM) hd
    (weight_bound C E M hE hM) sum
  have scaled := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (GaussianRationalRiemannRefinement.weight C E M) _ _).eqSymm
    (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hE hM) hd) (positive_product _ _ hE hd)
    (le_of_eq_add (d := zero) (by ipra_ring)) scaled

/-- The interval is contained below one, so its width is at most one. -/
theorem original_low_grid_unit_error (p v M a C E z R B A N : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hN : Γ ⊢[PRAAx] le two N) (hRight : Γ ⊢[PRAAx] le (a+C) E) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF p M a C E (sampleDataBeta z B N))
      (quadrature GaussianEulerIntegrandName.evaluatorF v M a C E (GaussianEulerIntegrandName.fixedData z B))
      (unit p*unit v+N*(unit p+unit v)) (N*unit p*unit v) := by
  have hd := positive_product (Γ := Γ) _ _
    (positive_product _ _ (le_trans (le_succ_self one) hN) (unit_positive p)) (unit_positive v)
  have width : Γ ⊢[PRAAx] le C E := le_trans (le_of_eq_add (d := a) (by ipra_ring)) hRight
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE hd) hd _
    (original_low_grid_error p v M a C E z R B A N hM ha hE h hN hRight)
  exact le_congr (by ipra_ring) (by ipra_ring)
    (mul_le_mul_right ((unit p*unit v+N*(unit p+unit v))*(N*unit p*unit v)) width)

theorem original_low_interval_beta_Euler_finite_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((le one (var 2) ⋏ le one (var 3) ⋏ le one (var 5) ⋏
      GaussianEulerLowerPowerCoefficients.source (var 6) (var 7) (var 8) (var 9) ⋏ le two (var 10) ⋏ le (var 3+var 4) (var 5)) ⟶
      distanceBounded (quadrature evaluatorF (var 0) (var 2) (var 3) (var 4) (var 5) (sampleDataBeta (var 6) (var 8) (var 10)))
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 1) (var 2) (var 3) (var 4) (var 5) (GaussianEulerIntegrandName.fixedData (var 6) (var 8)))
        ((var 4)*(unit (var 0)*unit (var 1)+(var 10)*(unit (var 0)+unit (var 1)))) ((var 5)*((var 10)*unit (var 0)*unit (var 1)))) :=
  closeUniv 11 (.impI (original_low_grid_error _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaLowGridError
