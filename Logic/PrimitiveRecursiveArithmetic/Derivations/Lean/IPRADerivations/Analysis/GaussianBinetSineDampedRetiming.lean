import IPRADerivations.Analysis.GaussianBinetSineDampedQuadrature
import IPRADerivations.Analysis.GaussianBinetSineQuotientClock
import IPRADerivations.Analysis.GaussianBinetLaplaceScalarMajorant

/-!
# Retiming the original damped sine grid on the same physical mesh

The sine rectangle clocks and the antiderivative clocks can be
chosen independently. Moving between the actual weighted panels has
an error independent of the number of integration cells.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineDampedRetiming

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetSineDampedQuadrature (body data value row_at subst_data)
open GaussianBinetSineRealDampedPanels (quotient_bound)
open GaussianBinetOscillatorySineQuotient (quotient)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerDecayMesh (observation)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "panel" => GaussianBinetSineRealDampedPanels.value

theorem panel_distance (r s X D A B a b U T : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (ha : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le one b) (hU : Γ ⊢[PRAAx] le A (U*B)) (hT : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] distanceBounded (panel r X D A B a b U T) (panel s X D A B a b U T)
      ((num 8*B)*(unit r+unit s)) (unit r*unit s) := by
  let C := U*T
  let H := unit r+unit s
  let V := unit r*unit s
  let f := observation (X*a) (D*b) r
  let g := observation (X*a) (D*b) s
  let x := quotient r a b C A B
  let y := quotient s a b C A B
  let z := decayPoint (X*a) (D*b)
  let d := decayData (X*a) (D*b)
  have hV := positive_product (Γ := Γ) _ _ (unit_positive r) (unit_positive s)
  have den := positive_product _ _ hD hb
  have radius : Γ ⊢[PRAAx] le (a*A) (C*(b*B)) :=
    le_congr (.eqRefl _) (by dsimp only [C]; ipra_ring) (le_mul_mono hT hU)
  have quarters := GaussianBinetSineQuotientClock.same_input_rate r s a b C C A B ha hB hb radius radius
  have boundX : Γ ⊢[PRAAx] bounded x (B*num 4) one := quotient_bound r A B a b U T ha hB hb hU hT
  have boundG : Γ ⊢[PRAAx] bounded g two one :=
    bounded_radius_mono _ _ _ _ _ (unit_positive _) (le_refl one) (by ipra_le sl (unit_positive (Γ := Γ) s))
      (GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound s (X*a) (D*b) den)
  have regular : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN decayF d :=
    GaussianRadiusExponentialName.name_regular constantF (GaussianNameBounds.U constantF z) z
      (GaussianGammaFiniteApproximantName.exponential_input _ _ (constant_regular z))
  have decay : Γ ⊢[PRAAx] distanceBounded f g H V := GaussianNameEquivalence.point_at decayF d r s regular
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [H]; ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.product_distance f g x y H (B*(H+H)) V (B*num 4) two hV
      decay quarters boundX boundG)

private theorem cell_error (j r s p X D A B U T N : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (ha : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le A (U*B)) (hj : Γ ⊢[PRAAx] le j N)
    (hr : Γ ⊢[PRAAx] le p r) (hs : Γ ⊢[PRAAx] le p s) :
    Γ ⊢[PRAAx] distanceBounded (inst2 body j (data r X D A B U T N))
      (inst2 body j (data s X D A B U T N)) (num 16*B) (unit p) := by
  have bound : Γ ⊢[PRAAx] le (T*j) (T*N) :=
    le_congr (mul_comm j T) (mul_comm N T) (mul_le_mul_right T hj)
  have hV := positive_product (Γ := Γ) _ _ (unit_positive r) (unit_positive s)
  have first := GaussianExponentialReference.unit_monotone hr
  have last := GaussianExponentialReference.unit_monotone hs
  apply distance_radius_mono _ _ _ _ _ _ hV (unit_positive p) ?_
    (distance_congr (row_at j r X D A B U T N).eqSymm (row_at j s X D A B U T N).eqSymm (.eqRefl _) (.eqRefl _)
      (panel_distance r s X D A B (T*j) N U T hD ha hB hN hU bound))
  ipra_le 𝔞(num 8*B*unit s)*sl first+𝔞(num 8*B*unit r)*sl last

theorem quadrature_distance (r s p X D A B U T N : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (ha : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le A (U*B))
    (hr : Γ ⊢[PRAAx] le p r) (hs : Γ ⊢[PRAAx] le p s) :
    Γ ⊢[PRAAx] distanceBounded (value r X D A B U T N) (value s X D A B U T N)
      (T*(num 16*B)) (unit p) := by
  let x := data r X D A B U T N
  let y := data s X D A B U T N
  let C := num 16*B
  have h := unit_positive (Γ := Γ) p
  have rows : Γ ⊢[PRAAx] termsDistance body body N x y C (unit p) := by
    refine .allI (.impI ?_)
    let t (z : PTm n) := Syn.shift z
    let Δ := Γ.map Fm.shift
    have ds : Δ ⊢[PRAAx] le one (t D) := by simpa [Δ,t,Fm.shift,Syn.shift] using hD.shift
    have as' : Δ ⊢[PRAAx] le one (t A) := by simpa [Δ,t,Fm.shift,Syn.shift] using ha.shift
    have bs : Δ ⊢[PRAAx] le one (t B) := by simpa [Δ,t,Fm.shift,Syn.shift] using hB.shift
    have ns : Δ ⊢[PRAAx] le one (t N) := by simpa [Δ,t,Fm.shift,Syn.shift] using hN.shift
    have us : Δ ⊢[PRAAx] le (t A) (t U*t B) := by simpa [Δ,t,Fm.shift,Syn.shift] using hU.shift
    have rs : Δ ⊢[PRAAx] le (t p) (t r) := by simpa [Δ,t,Fm.shift,Syn.shift] using hr.shift
    have ss : Δ ⊢[PRAAx] le (t p) (t s) := by simpa [Δ,t,Fm.shift,Syn.shift] using hs.shift
    simpa only [x,y,C,t,Δ,Syn.shift,subst_data,PTm.subst_mul,PTm.subst_num,GaussianCoefficientNameBounds.subst_unit] using
      cell_error (var 0) (t r) (t s) (t p) (t X) (t D) (t A) (t B) (t U) (t T) (t N)
        ds.wk as'.wk bs.wk ns.wk us.wk (le_of_lt Prf.hyp0) rs.wk ss.wk
  have raw := GaussianCompactScalarMajorant.common_mesh_distance body body N x y T one C (unit p)
    hN (le_refl one) h rows
  exact distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (one_mul _) raw

end LeanProofs.IPRA.Analysis.GaussianBinetSineDampedRetiming
