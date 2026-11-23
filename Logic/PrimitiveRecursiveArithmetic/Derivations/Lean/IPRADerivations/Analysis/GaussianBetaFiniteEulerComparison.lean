import IPRADerivations.Analysis.GaussianBetaPrimitiveGridUnscale
import IPRADerivations.Analysis.GaussianBetaPrimitiveLowerEndpointRefinement
import IPRADerivations.Analysis.GaussianBetaUpperGridEndpoint

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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (positive_product qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianBetaPrimitiveGridTelescope (gridEndpoint endpoint)
open GaussianBetaPrimitiveGridUnscale (quadrature scaledEndpoint demand)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A N : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏ le one R ⋏ le (two*R) N
def slack (t : PTm n) : PTm n := succ (succ t)
def lowerCutoff (t z B N : PTm n) : PTm n := GaussianBetaPrimitiveLowerEndpoint.precision (slack t) z B N
def denominator (t z R B A N : PTm n) : PTm n := etaDen (lowerCutoff t z B N) A R
def width (t z R B A N : PTm n) : PTm n := monus (denominator t z R B A N*N) one

def minimumCells (t z R B A N : PTm n) : PTm n :=
  GaussianBetaPrimitiveCompactGridAccuracy.cells (demand (slack t) N) z R B
    (width t z R B A N) (denominator t z R B A N) N N
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

theorem width_endpoint (t z R B A N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] one+width t z R B A N ≐ denominator t z R B A N*N :=
  (eq_add_of_le (positive_product _ _ (eta_den_positive _ _ _) hN)).eqSymm

private theorem endpoint_numerator_congr (p z B b N u v : PTm n) (h : Γ ⊢[PRAAx] u ≐ v) :
    Γ ⊢[PRAAx] endpoint p z B u b N ≐ endpoint p z B v b N := by
  have lastIn : ![p,z,B,u,b,N] (5 : Fin 6) = N := rfl
  have lastOut : ![p,z,B,v,b,N] (5 : Fin 6) = N := rfl
  simpa only [GaussianBetaPrimitiveGridTelescope.subst_endpoint, Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,lastIn,lastOut] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (endpoint (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
        (σ := ![p,z,B,u,b,N]) (σ' := ![p,z,B,v,b,N])
        (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact h; exact .eqRefl _; exact .eqRefl _)

theorem lower_endpoint_code (t p z R B A N M : PTm n) :
    Γ ⊢[PRAAx] scaledEndpoint zero p z B one (width t z R B A N) (denominator t z R B A N) M N ≐
      GaussianBetaPrimitiveEndpointEncoding.clockScaledEndpoint p z B (lowerCutoff t z B N) A R N M :=
  qmul_congr (.eqRefl _) (endpoint_numerator_congr p z B _ _ _ _ (by ipra_ring))

theorem upper_endpoint_code (t p z R B A N M : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] scaledEndpoint M p z B one (width t z R B A N) (denominator t z R B A N) M N ≐
      GaussianBetaUpperGridEndpoint.scaledEndpoint p z B (denominator t z R B A N*M) N := by
  let D := denominator t z R B A N
  let C := width t z R B A N
  have eq : Γ ⊢[PRAAx] one*M+C*M ≐ (D*M)*N :=
    (show Γ ⊢[PRAAx] one*M+C*M ≐ (one+C)*M from by ipra_ring).eqTrans
      ((congrMul (width_endpoint t z R B A N hN) (.eqRefl M)).eqTrans (by ipra_ring))
  exact qmul_congr (.eqRefl _) (endpoint_numerator_congr p z B _ _ _ _ eq)

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

private theorem distance_drop_subtrahend (u v B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] GaussianRationalHorner.canonical u)
    (hv : Γ ⊢[PRAAx] GaussianRationalHorner.canonical v)
    (h : Γ ⊢[PRAAx] bounded v one B) : Γ ⊢[PRAAx] distanceBounded (qsub u v) u one B := by
  have undo : Γ ⊢[PRAAx] qsub u (qsub u v) ≐ v :=
    (qsub_congr (GaussianRationalLinearProduct.add_sub_right v u hu).eqSymm (.eqRefl _)).eqTrans
      (GaussianReciprocalHorner.qsub_add_cancel v (qsub u v) hv)
  exact distance_symmetric _ _ _ _ hB
    (GaussianRationalReciprocal.bound_congr undo.eqSymm (.eqRefl _) (.eqRefl _) h)

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

theorem original_quadrature_euler_error (t p q z R B A N M : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) (hm : Γ ⊢[PRAAx] le (minimumCells t z R B A N) M)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t z R B A N M) p) : Γ ⊢[PRAAx]
    distanceBounded (observation t p z R B A N M) (ap2 eulerF q (eulerData z R B A N))
      (unit t+unit q) (unit t*unit q) := by
  let k := slack t
  let E := denominator t z R B A N
  let C := width t z R B A N
  let v := unit k
  let w := unit q
  let D := v*w
  let L := scaledEndpoint zero p z B one C E M N
  let U := scaledEndpoint M p z B one C E M N
  let Q := observation t p z R B A N M
  let Y := ap2 eulerF q (eulerData z R B A N)
  have hN := degree_positive z R B A N h
  have hE : Γ ⊢[PRAAx] le one E := eta_den_positive _ _ _
  have hM : Γ ⊢[PRAAx] le one M :=
    le_trans (GaussianBetaPrimitiveCompactGridAccuracy.mesh_positive (demand k N) z R B C E N N) hm
  have hp0 := next_clock_errors (Γ := Γ) t z R B A N M
  have endEq : Γ ⊢[PRAAx] one+C ≐ E*N := width_endpoint t z R B A N hN
  have atEnd : Γ ⊢[PRAAx] le (one+C) (E*N) := le_congr endEq.eqSymm (.eqRefl _) (le_refl _)
  have compact : Γ ⊢[PRAAx] GaussianBetaPrimitiveCompactGridAccuracy.source z R B A one C E N N :=
    .andI h.andE₁ (.andI hE (.andI hN (.andI (le_refl _) (.andI atEnd atEnd))))
  have hV : Γ ⊢[PRAAx] le one v := unit_positive k
  have hW : Γ ⊢[PRAAx] le one w := unit_positive q
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hV hW
  have integral : Γ ⊢[PRAAx] distanceBounded Q (qsub U L) one v :=
    distance_symmetric _ _ _ _ hV (GaussianBetaPrimitiveGridUnscale.original_dyadic_accuracy k p z R B A one C E N M N
      compact hm (le_trans hp0.andE₁ hp))
  have lower : Γ ⊢[PRAAx] bounded L one v :=
    GaussianRationalReciprocal.bound_congr (lower_endpoint_code t p z R B A N M).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianBetaPrimitiveLowerEndpointRefinement.constructive_endpoint_small_at k p z R B A N M
        h.andE₁ hN hM (le_trans hp0.andE₂.andE₁ hp))
  have small : Γ ⊢[PRAAx] distanceBounded (qsub U L) U one v :=
    distance_drop_subtrahend U L v hV (qmul_canonical _ _) (qmul_canonical _ _) lower
  have upper : Γ ⊢[PRAAx] distanceBounded U Y (v+w) D :=
    distance_congr (upper_endpoint_code t p z R B A N M hN).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (upper_error_at k p q z R B A (E*M) N
        (.andI h.andE₁ (.andI h.andE₂.andE₁ (.andI (positive_product _ _ hE hM) (.andI hN h.andE₂.andE₂))))
        (le_trans hp0.andE₂.andE₂ hp))
  have enlarge : Γ ⊢[PRAAx] le (one*D) (w*v) := le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)
  have intScaled := distance_radius_mono _ _ _ _ _ _ hV hD enlarge integral
  have lowerScaled := distance_radius_mono _ _ _ _ _ _ hV hD enlarge small
  have combine := distance_triangle_same Q (qsub U L) Y w (w+(v+w)) D hD intScaled
    (distance_triangle_same (qsub U L) U Y w (v+w) D hD lowerScaled upper)
  have quad : Γ ⊢[PRAAx] v ≐ (num 4)*unit t := by
    change Γ ⊢[PRAAx] pw two (succ (succ t)) ≐ (num 4)*pw two t
    exact (pw_succ two (succ t)).eqTrans ((congrMul (pw_succ two t) (.eqRefl _)).eqTrans (by ipra_ring))
  have compare : Γ ⊢[PRAAx] le ((w+(w+(v+w)))*(unit t*w)) ((unit t+w)*D) := by
    let V := num 4*unit t
    have lhs : Γ ⊢[PRAAx] (w+(w+(v+w)))*(unit t*w) ≐ (w+(w+(V+w)))*(unit t*w) :=
      congrMul (congrAdd (.eqRefl _) (congrAdd (.eqRefl _) (congrAdd quad (.eqRefl _)))) (.eqRefl _)
    have rhs : Γ ⊢[PRAAx] (unit t+w)*D ≐ (unit t+w)*(V*w) :=
      congrMul (.eqRefl _) (congrMul quad (.eqRefl _))
    have reduced : Γ ⊢[PRAAx] le ((w+(w+(V+w)))*(unit t*w)) ((unit t+w)*(V*w)) :=
      le_of_eq_add (d := unit t*w*w) (by dsimp only [V]; ipra_ring)
    exact le_congr lhs.eqSymm rhs.eqSymm reduced
  exact distance_radius_mono _ _ _ _ _ _ hD (positive_product _ _ (unit_positive t) hW) compare combine

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
