import IPRADerivations.Analysis.Integration.Moments.GaussianOddMomentSignedGrid
import IPRADerivations.Analysis.Integration.Moments.GaussianEvenMomentWholeLine

/-!
# Literal signed odd Gaussian quadratures on cofinal whole-line panels

The program uses the original quadratic improper cutoffs at N+1,
the actual signed odd row evaluator on the two reflected panels,
and the original width, mesh and precision. Positive-half errors
retain the original lower and upper omitted-tail bounds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianOddMomentWholeLine

open_ipra
open GaussianOddMomentIntegrand (argument radius)
open GaussianOddMomentSignedGrid (evaluatorF symmetricGrid)
open GaussianOddSymmetricQuadrature (fixedData)
open GaussianGammaIntegralCutoffs (etaDen height)
open GaussianEulerQuadraticUpperEndpoint (preimage)
open GaussianEulerQuadraticCutoffGeometry (width)
open GaussianCompactRiemannName (precision mesh dyadic_monotone quadrature)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

abbrev clock := @GaussianEvenMomentWholeLine.clock
abbrev halfF : PR 2 := GaussianEulerQuadraticImproperKernel.nameF
def halfData (N c d : PTm n) : PTm n := GaussianEulerQuadraticImproperKernel.data (argument N) (radius N) one one c d
abbrev referenceF : PR 2 := GaussianEulerQuadraticImproperKernel.referenceF
def referenceData (N c d : PTm n) : PTm n := GaussianEulerQuadraticImproperKernel.referenceData (argument N) (radius N) one one c d
def cutoff (p N c d : PTm n) : PTm n := GaussianEulerQuadraticImproperSchedule.index p one
  (GaussianEulerQuadraticImproperKernel.invBound (argument N) one c d) c d
def lowerDenominator (p N c d : PTm n) : PTm n := etaDen (cutoff p N c d) one (radius N)
def upperEndpoint (p N c d : PTm n) : PTm n := preimage (cutoff p N c d) one (radius N) d
def span (p N c d : PTm n) : PTm n := width (cutoff p N c d) one (radius N) d
def count (p N c d : PTm n) : PTm n := mesh (succ p)
  (GaussianEulerQuadraticKernelCompactName.lipschitz (radius N) (lowerDenominator p N c d) (upperEndpoint p N c d) c d)
  (upperEndpoint p N c d)
def query (p N c d : PTm n) : PTm n := precision (succ p) (upperEndpoint p N c d)
def gridWith (F : PR 3) (p N c d : PTm n) : PTm n :=
  quadrature F (query p N c d) (count p N c d) one (span p N c d) (lowerDenominator p N c d) (fixedData N c d)
def sample (p N c d : PTm n) : PTm n := symmetricGrid (query (clock p) N c d) (count (clock p) N c d)
  one (span (clock p) N c d) (lowerDenominator (clock p) N c d) (fixedData N c d)

theorem signed_sample_exact_zero (p N c d : PTm n) : Γ ⊢[PRAAx] sample p N c d ≐ qzero :=
  GaussianOddMomentSignedGrid.symmetric_grid_zero _ _ _ _ _ _

private theorem cutoff_later (p N c d : PTm n) : Γ ⊢[PRAAx] le p (cutoff p N c d) := by
  unfold cutoff GaussianEulerQuadraticImproperSchedule.index
    GaussianEulerQuadraticImproperSchedule.threshold GaussianEulerQuadraticLowerEndpoint.minimumIndex GaussianFastValueCut.exponent
  exact le_trans (le_succ_self p) (le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _)))

theorem endpoints_cofinal (p N c d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    le (unit p) (lowerDenominator p N c d) ⋏ le p (upperEndpoint p N c d) := by
  let j := cutoff p N c d
  let H := height j one (radius N)
  have hj : Γ ⊢[PRAAx] le j H := by
    unfold H height
    exact le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have hH : Γ ⊢[PRAAx] le H (two*H) := le_congr (one_mul H) (.eqRefl _)
    (mul_le_mul_right H (zero_lt_succ one))
  have hT : Γ ⊢[PRAAx] le (two*H) (upperEndpoint p N c d) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (two*H) hd)
  have h := le_trans (cutoff_later p N c d) (le_trans hj hH)
  exact .andI (dyadic_monotone _ _ (le_congr (.eqRefl _) (one_mul H).eqSymm
    (le_trans (cutoff_later p N c d) hj))) (le_trans h hT)


theorem original_quadrature (p N c d : PTm n) : Γ ⊢[PRAAx]
    ap2 halfF p (halfData N c d) ≐ quadrature GaussianEulerQuadraticKernelCompactName.evaluatorF (query p N c d)
      (count p N c d) one (span p N c d) (lowerDenominator p N c d)
      (GaussianEulerPositiveScalingIntegrand.fixedData (argument N) one c d) :=
  (GaussianEulerQuadraticImproperKernel.name_at p (argument N) (radius N) one one c d).eqTrans
    (GaussianEulerQuadraticKernelCompactName.name_at (succ p) (argument N) (radius N) one c d one
      (span p N c d) (lowerDenominator p N c d) (upperEndpoint p N c d))

theorem grid_source (p N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    GaussianOddMomentSignedGrid.source one (span p N c d) (lowerDenominator p N c d) (upperEndpoint p N c d) c d := by
  have e := GaussianEulerQuadraticCutoffGeometry.exact_right_endpoint (cutoff p N c d) one (radius N) d hd
  exact .andI (.andI (GaussianGammaIntegralCutoffs.eta_den_positive _ _ _) (.andI (le_refl _)
    (le_congr e.eqSymm (.eqRefl _) (le_refl _)))) (.andI hc hd)

theorem count_positive (p N c d : PTm n) : Γ ⊢[PRAAx] le one (count p N c d) :=
  GaussianCompactRiemannName.mesh_positive _ _ _

theorem query_budget (p N c d K : PTm n) (hK : Γ ⊢[PRAAx] le K (unit (succ p+num 6))) :
    Γ ⊢[PRAAx] le (K*upperEndpoint p N c d) (unit (query p N c d)) :=
  le_trans (mul_le_mul_right _ hK) (GaussianCompactRiemannName.precision_lower (succ p) (upperEndpoint p N c d))

theorem finite_half_error (p N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 halfF p (halfData N c d)) (gridWith (evaluatorF false) p N c d) one (unit p) := by
  let E := lowerDenominator p N c d
  let T := upperEndpoint p N c d
  let W := span p N c d
  let q := query p N c d
  let U := unit q
  let V := unit p
  have source := grid_source p N c d hc hd
  have comparison := GaussianOddMomentSignedGrid.original_grid_distance q q (count p N c d) one W E T N c d
    source (count_positive _ _ _ _)
  have wider : Γ ⊢[PRAAx] le (unit (succ p)) (unit (succ p+num 6)) :=
    dyadic_monotone (succ p) (succ p+num 6) (le_add_right _ _)
  have e : Γ ⊢[PRAAx] unit (succ p) ≐ two*V :=
    (pw_succ two p).eqTrans (mul_comm V two)
  have scale : Γ ⊢[PRAAx] le (two*V*T) U := query_budget p N c d _ (le_congr e (.eqRefl _) wider)
  have budget : Γ ⊢[PRAAx] le ((W*(U+U))*V) (one*(E*(U*U))) := by
    ipra_le 2*𝔞 V*𝔞 U*sl (le_trans (le_add_left W one) source.andE₁.andE₂.andE₂)+𝔞 E*𝔞 U*sl scale
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ source.andE₁.andE₁ (positive_product _ _ (unit_positive _) (unit_positive _)))
    (unit_positive p) budget (distance_congr (original_quadrature p N c d).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) comparison)

theorem original_half_reference (p q N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 halfF p (halfData N c d)) (ap2 referenceF q (referenceData N c d))
      (unit p+unit q) (unit p*unit q) :=
  GaussianEulerQuadraticImproperKernel.original_observations p q (argument N) (radius N) one one c d
    (GaussianOddMomentIntegrand.quadratic_source N c d hc hd)

theorem finite_half_reference (p q N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    distanceBounded (gridWith (evaluatorF false) p N c d) (ap2 referenceF q (referenceData N c d))
      (unit p+two*unit q) (unit p*unit q) := by
  let P := unit p
  let Q := unit q
  have hP : Γ ⊢[PRAAx] le one P := unit_positive p
  have hPQ : Γ ⊢[PRAAx] le one (P*Q) := positive_product _ _ hP (unit_positive q)
  have initial := distance_symmetric _ _ _ _ hP (finite_half_error p N c d hc hd)
  have finer := distance_radius_mono _ _ _ _ Q (P*Q) hP hPQ (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) initial
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ (ap2 halfF p (halfData N c d)) _ Q (P+Q) _ hPQ finer
      (original_half_reference p q N c d hc hd))

theorem actual_odd_Gaussian_whole_endpoints_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 3) ⟶ le (unit (var 0)) (lowerDenominator (var 0) (var 1) (var 2) (var 3)) ⋏
        le (var 0) (upperEndpoint (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (endpoints_cofinal _ _ _ _ Prf.hyp0))

theorem actual_original_whole_line_Gaussian_odd_symmetric_sample_zero_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (sample (var 0) (var 1) (var 2) (var 3) ≐ qzero) :=
  closeUniv 4 (signed_sample_exact_zero _ _ _ _)

theorem actual_literal_odd_Gaussian_positive_half_reference_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 3) ⟶ le one (var 4) ⟶
        distanceBounded (gridWith (evaluatorF false) (var 0) (var 2) (var 3) (var 4))
          (ap2 referenceF (var 1) (referenceData (var 2) (var 3) (var 4)))
          (unit (var 0)+two*unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 5 (.impI (.impI (finite_half_reference _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianOddMomentWholeLine
