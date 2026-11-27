import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveGridUnscale
import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveLowerEndpointRefinement
import IPRADerivations.Analysis.Beta.Endpoints.Upper.GaussianBetaUpperGridEndpoint
import IPRADerivations.Analysis.Beta.Partitions.Splits.GaussianBetaFiniteEndpointTelescope

/-!
# The original full finite beta quadrature and the finite Euler reciprocal

At a computed lower cutoff, the original beta quadrature on the
positive interval from that cutoff to the finite support endpoint
approximates the original finite Euler reciprocal. Both comparison
errors are dyadic. The true mesh and the original evaluation precision
can be increased independently beyond the given sufficient bounds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaFiniteEulerComparison

open_ipra
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianBetaPrimitiveGridTelescope (gridEndpoint endpoint)
open GaussianBetaPrimitiveGridUnscale (quadrature scaledEndpoint demand)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A N : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏ le one R ⋏ le (two*R) N
def slack (t : PTm n) : PTm n := succ (succ t)
def lowerCutoff (t z B N : PTm n) : PTm n := GaussianBetaPrimitiveLowerEndpoint.precision (slack t) z B N
def denominator (t z R B A N : PTm n) : PTm n := etaDen (lowerCutoff t z B N) A R
def supportWidth (E N : PTm n) : PTm n := monus (E*N) one
def width (t z R B A N : PTm n) : PTm n := supportWidth (denominator t z R B A N) N

def supportCells (t z R B E N : PTm n) : PTm n :=
  GaussianBetaPrimitiveCompactGridAccuracy.cells (demand (slack t) N) z R B (supportWidth E N) E N N

def minimumCells (t z R B A N : PTm n) : PTm n :=
  supportCells t z R B (denominator t z R B A N) N
def gridPrecision (t z B N M : PTm n) : PTm n :=
  GaussianBetaPrimitiveCompactGridAccuracy.precisionAt (demand (slack t) N) z B N M
def upperPrecision (t z R B A N M : PTm n) : PTm n :=
  GaussianBetaUpperGridEndpoint.precision (slack t) z B (denominator t z R B A N*M) N
def minimumPrecision (t z R B A N M : PTm n) : PTm n :=
  gridPrecision t z B N M+lowerCutoff t z B N+upperPrecision t z R B A N M
def observation (t p z R B A N M : PTm n) : PTm n :=
  quadrature p z B one (width t z R B A N) (denominator t z R B A N) M N

theorem degree_positive (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) :
    Γ ⊢[PRAAx] le one N :=
  le_trans h.andE₂.andE₁ (le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right R R)) h.andE₂.andE₂)

theorem support_width_endpoint (E N : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] one+supportWidth E N ≐ E*N :=
  (eq_add_of_le (positive_product _ _ hE hN)).eqSymm

theorem width_endpoint (t z R B A N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] one+width t z R B A N ≐ denominator t z R B A N*N :=
  support_width_endpoint _ _ (eta_den_positive _ _ _) hN

private theorem endpoint_numerator_congr (p z B b N u v : PTm n) (h : Γ ⊢[PRAAx] u ≐ v) :
    Γ ⊢[PRAAx] endpoint p z B u b N ≐ endpoint p z B v b N := by
  have lastIn : ![p,z,B,u,b,N] (5 : Fin 6) = N := rfl
  have lastOut : ![p,z,B,v,b,N] (5 : Fin 6) = N := rfl
  ipra_congr (endpoint (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [.eqRefl p, .eqRefl z, .eqRefl B, h, .eqRefl b, .eqRefl N] using [lastIn, lastOut]

theorem cutoff_lower_endpoint_code (k p z R B A N M : PTm n) :
    Γ ⊢[PRAAx] scaledEndpoint zero p z B one (supportWidth (etaDen k A R) N) (etaDen k A R) M N ≐
      GaussianBetaPrimitiveEndpointEncoding.clockScaledEndpoint p z B k A R N M :=
  qmul_congr (.eqRefl _) (endpoint_numerator_congr p z B _ _ _ _ (by ipra_ring))

theorem lower_endpoint_code (t p z R B A N M : PTm n) :
    Γ ⊢[PRAAx] scaledEndpoint zero p z B one (width t z R B A N) (denominator t z R B A N) M N ≐
      GaussianBetaPrimitiveEndpointEncoding.clockScaledEndpoint p z B (lowerCutoff t z B N) A R N M :=
  cutoff_lower_endpoint_code _ _ _ _ _ _ _ _

theorem support_upper_endpoint_code (p z B E N M : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] scaledEndpoint M p z B one (supportWidth E N) E M N ≐
      GaussianBetaUpperGridEndpoint.scaledEndpoint p z B (E*M) N := by
  let C := supportWidth E N
  have eq : Γ ⊢[PRAAx] one*M+C*M ≐ (E*M)*N :=
    (show Γ ⊢[PRAAx] one*M+C*M ≐ (one+C)*M from by ipra_ring).eqTrans
      ((congrMul (support_width_endpoint E N hE hN) (.eqRefl M)).eqTrans (by ipra_ring))
  exact qmul_congr (.eqRefl _) (endpoint_numerator_congr p z B _ _ _ _ eq)

theorem upper_endpoint_code (t p z R B A N M : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] scaledEndpoint M p z B one (width t z R B A N) (denominator t z R B A N) M N ≐
      GaussianBetaUpperGridEndpoint.scaledEndpoint p z B (denominator t z R B A N*M) N :=
  support_upper_endpoint_code _ _ _ _ _ _ (eta_den_positive _ _ _) hN

private theorem next_clock_errors (t z R B A N M : PTm n) :
    Γ ⊢[PRAAx] le (gridPrecision t z B N M) (minimumPrecision t z R B A N M) ⋏
      le (lowerCutoff t z B N) (minimumPrecision t z R B A N M) ⋏
      le (upperPrecision t z R B A N M) (minimumPrecision t z R B A N M) := by
  let P := gridPrecision t z B N M
  let K := lowerCutoff t z B N
  let U := upperPrecision t z R B A N M
  have first : Γ ⊢[PRAAx] le P ((P+K)+U) := le_trans (le_add_right _ _) (le_add_right _ _)
  have second : Γ ⊢[PRAAx] le K ((P+K)+U) :=
    le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right K P)) (le_add_right _ _)
  have third : Γ ⊢[PRAAx] le U ((P+K)+U) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_add_right U (P+K))
  exact .andI first (.andI second third)

theorem upper_error_at (t p q z R B A b N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBetaUpperEndpointInverse.source z R B A b N)
    (hp : Γ ⊢[PRAAx] le (GaussianBetaUpperGridEndpoint.precision t z B b N) p) :
    Γ ⊢[PRAAx] distanceBounded (GaussianBetaUpperGridEndpoint.scaledEndpoint p z B b N)
      (ap2 eulerF q (eulerData z R B A N)) (unit t+unit q) (unit t*unit q) := by
  let U := unit p
  let Q := unit q
  let T := unit t
  let F := GaussianBetaUpperGridEndpoint.factor z B b N
  have budget : Γ ⊢[PRAAx] le (F*T) U :=
    le_trans (GaussianBetaUpperGridEndpoint.precision_budget t z B b N) (GaussianExponentialReference.unit_monotone hp)
  have leRate : Γ ⊢[PRAAx] le ((GaussianBetaUpperGridEndpoint.numerator p q z B b N)*(T*Q))
      ((T+Q)*(U*Q)) :=
    le_congr (by unfold GaussianBetaUpperGridEndpoint.numerator; ipra_ring) (by ipra_ring)
      (add_le_add_right (U*T*Q) (mul_le_mul_right (Q*Q) budget))
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (positive_product _ _ (unit_positive t) (unit_positive q)) leRate
    (GaussianBetaUpperGridEndpoint.sampled_endpoint_error p q z R B A b N h)

/-- The finite telescope and upper endpoint work at every positive
encoded cutoff. Its actual lower endpoint is the remaining input. -/
theorem full_support_euler_error (t p q z R B A E N M : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) (hE : Γ ⊢[PRAAx] le one E)
    (hm : Γ ⊢[PRAAx] le (supportCells t z R B E N) M)
    (hgrid : Γ ⊢[PRAAx] le (gridPrecision t z B N M) p)
    (hupper : Γ ⊢[PRAAx] le (GaussianBetaUpperGridEndpoint.precision (slack t) z B (E*M) N) p)
    (lower : Γ ⊢[PRAAx] bounded (scaledEndpoint zero p z B one (supportWidth E N) E M N) one (unit (slack t))) :
    Γ ⊢[PRAAx] distanceBounded (quadrature p z B one (supportWidth E N) E M N) (ap2 eulerF q (eulerData z R B A N))
      (unit t+unit q) (unit t*unit q) := by
  let k := slack t
  let C := supportWidth E N
  have hN := degree_positive z R B A N h
  have hM : Γ ⊢[PRAAx] le one M :=
    le_trans (GaussianBetaPrimitiveCompactGridAccuracy.mesh_positive (demand k N) z R B C E N N) hm
  have endEq : Γ ⊢[PRAAx] one+C ≐ E*N := support_width_endpoint E N hE hN
  have atEnd : Γ ⊢[PRAAx] le (one+C) (E*N) := le_congr endEq.eqSymm (.eqRefl _) (le_refl _)
  have compact : Γ ⊢[PRAAx] GaussianBetaPrimitiveCompactGridAccuracy.source z R B A one C E N N :=
    .andI h.andE₁ (.andI hE (.andI hN (.andI (le_refl _) (.andI atEnd atEnd))))
  have upper := distance_congr (support_upper_endpoint_code p z B E N M hE hN).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (upper_error_at k p q z R B A (E*M) N
      (.andI h.andE₁ (.andI h.andE₂.andE₁ (.andI (positive_product _ _ hE hM) (.andI hN h.andE₂.andE₂))))
      hupper)
  exact GaussianBetaFiniteEndpointTelescope.grid_to_certified_endpoint t p q z R B A one C E N M _
    compact hm hgrid lower upper

theorem original_quadrature_euler_error (t p q z R B A N M : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) (hm : Γ ⊢[PRAAx] le (minimumCells t z R B A N) M)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t z R B A N M) p) : Γ ⊢[PRAAx]
    distanceBounded (observation t p z R B A N M) (ap2 eulerF q (eulerData z R B A N))
      (unit t+unit q) (unit t*unit q) := by
  let k := slack t
  let E := denominator t z R B A N
  let C := width t z R B A N
  have hN := degree_positive z R B A N h
  have hM : Γ ⊢[PRAAx] le one M :=
    le_trans (GaussianBetaPrimitiveCompactGridAccuracy.mesh_positive (demand k N) z R B C E N N) hm
  have hp0 := next_clock_errors (Γ := Γ) t z R B A N M
  have lower : Γ ⊢[PRAAx] bounded (scaledEndpoint zero p z B one C E M N) one (unit k) :=
    GaussianRationalReciprocal.bound_congr (lower_endpoint_code t p z R B A N M).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianBetaPrimitiveLowerEndpointRefinement.constructive_endpoint_small_at k p z R B A N M
        h.andE₁ hN hM (le_trans hp0.andE₂.andE₁ hp))
  exact full_support_euler_error t p q z R B A E N M h (eta_den_positive _ _ _) hm
    (le_trans hp0.andE₁ hp) (le_trans hp0.andE₂.andE₂ hp) lower

theorem computed_quadrature_euler_error (t q z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    let M := minimumCells t z R B A N
    let p := minimumPrecision t z R B A N M
    distanceBounded (observation t p z R B A N M) (ap2 eulerF q (eulerData z R B A N))
      (unit t+unit q) (unit t*unit q) :=
  original_quadrature_euler_error _ _ _ _ _ _ _ _ _ h (le_refl _) (le_refl _)

theorem original_beta_quadrature_finite_Euler_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) ⋏
      le (minimumCells (var 0) (var 3) (var 4) (var 5) (var 6) (var 7)) (var 8) ⋏
      le (minimumPrecision (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) (var 1)) ⟶
      distanceBounded (observation (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (ap2 eulerF (var 2) (eulerData (var 3) (var 4) (var 5) (var 6) (var 7)))
        (unit (var 0)+unit (var 2)) (unit (var 0)*unit (var 2))) :=
  closeUniv 9 (.impI (original_quadrature_euler_error _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem original_computed_beta_quadrature_finite_Euler_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      let M := minimumCells (var 0) (var 2) (var 3) (var 4) (var 5) (var 6)
      let p := minimumPrecision (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) M
      distanceBounded (observation (var 0) p (var 2) (var 3) (var 4) (var 5) (var 6) M)
        (ap2 eulerF (var 1) (eulerData (var 2) (var 3) (var 4) (var 5) (var 6)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 7 (.impI (computed_quadrature_euler_error _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaFiniteEulerComparison
