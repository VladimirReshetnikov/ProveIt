import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayAddition
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayOrder
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalUpperRepresentation
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumIntervals

/-!
# A strict upper margin for the unchanged original positive-time decay

At the genuine small time 1/(2E), the checked linear remainder gives
exp(-t) <= 1-1/(4E) with two original observation errors. The original
signed-real exponential order extends this to every t >= 1/E. One
finite scalar gap removes the auxiliary small-time observation only.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayCompactUpper

open_ipra
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianRationalHorner (qadd positive_product represents represents_congr)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (qnegative)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper)
open RationalSupMetric (numeratorOf denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def upperPoint (E : PTm n) : PTm n := fraction (monus (two*(two*E)) one) (two*(two*E))
ipra_subst upperPoint

private theorem linear_point_represents (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (qadd qone (decayPoint one B))) (ZT.ofNat B-ZT.ofNat one) B := by
  have neg := GaussianRationalMetric.qnegative_represents _ _ _ (GaussianRationalHorner.ofGaussian_represents
    (Γ := Γ) (ComplexLogarithmRemainder.scale one ComplexLogarithmRemainder.oneCode) B hB)
  have actual := (GaussianRationalHorner.qadd_represents _ _ _ _ B hB
    (GaussianRationalReciprocal.qone_represents_scaled B) neg).andE₁
  exact GaussianRationalHorner.scalar_congr (.eqRefl _) (by
    apply ZT.derive
    simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.re_one,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    ring) (.eqRefl _) actual

/-- The actual small-time observation, with no change of its query. -/
theorem small_time_upper (p B : PTm n) (hB : Γ ⊢[PRAAx] le two B) : Γ ⊢[PRAAx]
    upper (fstT (ap2 decayF p (decayData one B))) (fraction (monus (two*B) one) (two*B)) two (unit p) := by
  let x := fstT (ap2 decayF p (decayData one B))
  let w := fstT (qadd qone (decayPoint one B))
  let c := fraction (monus (two*B) one) (two*B)
  let P := denominatorOf x
  let u := numeratorOf x
  let U := unit p
  let V := ZT.ofNat B-ZT.ofNat one
  let A := U+two*(B*B)
  let D := B*B*U
  let left := ZT.ofNat (D*B)*u
  let right := ZT.ofNat (D*P)*V+ZT.ofNat (A*P*B)
  have hb := le_trans (le_succ_self one) hB
  have hp : Γ ⊢[PRAAx] le one P := RationalArgmin.denominator_positive x
  have hc : Γ ⊢[PRAAx] le one (two*B) := positive_product _ _ (le_succ_self one) hb
  have near := GaussianEulerDecayAddition.original_decay_linear_remainder one B p hb hb
  have raw : Γ ⊢[PRAAx] upper x w A D := by
    exact RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by dsimp only [A]; ipra_ring) (.eqRefl _)
      (RationalValueBounds.upper_of_radius _ _ _ _ (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _
        (positive_product _ _ (positive_product _ _ hb hb) (unit_positive p)) near))
  have native : Γ ⊢[PRAAx] zle left right := RationalUpperRepresentation.upper_from_representations x w P B A D u V
    (RationalRepresentations.represents_self x) (linear_point_represents B hb) raw
  have e := zle_toZ native
  have eb := natEq (eq_add_of_le hB)
  have ec := natEq (eq_add_of_le hc)
  apply RationalCubeInfimumIntervals.upper_of_representations x c u (ZT.ofNat (monus (two*B) one)) P (two*B) two U hp hc
    (RationalRepresentations.represents_self x) (fraction_represents _ _ hc)
  apply PolynomialBisection.zle_scale_cancel (c := B*B) (positive_product _ _ hb hb)
  apply zle_of_toZ (two*PolynomialBisection.slack left right+U*P*B*monus B two)
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat] at e ⊢
  dsimp only [left,right,D,A,V,U,P] at e ⊢
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat,PolynomialBisection.slack] at e ⊢
  ipra_simps
  linear_combination 2*e-𝔞(unit p)*𝔞(denominatorOf x)*𝔞 B*eb+𝔞(unit p)*𝔞(denominatorOf x)*𝔞 B*𝔞 B*ec

/-- Every original observation at t >= 1/E retains only its own dyadic. -/
theorem original_decay_upper (p a b E : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hE : Γ ⊢[PRAAx] le one E) (h : Γ ⊢[PRAAx] le b (E*a)) : Γ ⊢[PRAAx]
    upper (fstT (ap2 decayF p (decayData a b))) (upperPoint E) one (unit p) := by
  let x := fstT (ap2 decayF p (decayData a b))
  let c := upperPoint E
  let q := GaussianNamedRealOrderTransport.precision x c (unit p) (num 3)
  have hB : Γ ⊢[PRAAx] le two (two*E) := le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right two hE)
  have grow : Γ ⊢[PRAAx] le (E*a) (two*(E*a)) := le_of_eq_add (d := E*a) (by ipra_ring)
  have hm : Γ ⊢[PRAAx] le (one*b) (a*(two*E)) := le_congr (one_mul _).eqSymm (by ipra_ring) (le_trans h grow)
  have order := GaussianEulerDecayOrder.decay_order_at one (two*E) a b p q
    (le_trans (le_succ_self one) hB) hb hm
  have small := small_time_upper q (two*E) hB
  have joined := RationalValueBounds.upper_triangle _ _ _ _ _ _ _ order small
  have adjusted : Γ ⊢[PRAAx] GaussianNamedRealOrderTransport.upperSlack x c one (unit p) (num 3) q :=
    RationalValueBounds.upper_mono _ _ _ _ _ _
      (positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive q)) joined
      (le_of_eq_add (d := zero) (by ipra_ring))
  exact GaussianNamedRealOrderTransport.remove_upper_slack x c one (unit p) (num 3) adjusted

theorem actual_original_positive_time_decay_strict_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 2) ⋏ (le one (var 3) ⋏ le (var 2) (var 3*var 1))) ⟶
      upper (fstT (ap2 decayF (var 0) (decayData (var 1) (var 2)))) (upperPoint (var 3)) one (unit (var 0))) :=
  closeUniv 4 (.impI (original_decay_upper _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayCompactUpper
