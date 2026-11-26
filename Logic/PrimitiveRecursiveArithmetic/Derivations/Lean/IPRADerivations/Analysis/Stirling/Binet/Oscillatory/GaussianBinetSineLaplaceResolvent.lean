import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetArctangentCosineLaplace
import IPRADerivations.Analysis.Beta.GaussianEulerBetaProductPascal
import IPRADerivations.Analysis.Trigonometry.GaussianNamedSineFromExponential

/-!
# Cleared sine resolvent for the second Binet formula

The antisymmetric combination of the same two original pole integrals
has the exact rational target `t/(z²+t²)`. In particular the cleared
identity and its uniform finite-panel estimate include the zero
frequency, without requesting an inverse frequency.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineLaplaceResolvent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode normSq eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianBinetArctangentResolvent (pole poleNumerator pole_lower polynomial polynomial_lower product_polynomial signedTimeNumerator)
open GaussianBinetArctangentPoleLaplace (pole_integral_error)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerBetaProductPascal (inverse_unique)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianNamedSineFromExponential (multiplier)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product qmul qmul_canonical ofGaussian_canonical ofGaussian_represents
  qmul_represents represents_congr canonical_unique)
open GaussianRationalLowerBounds (name_lower)
open GaussianRationalMetric (bounded bounded_iff distanceBounded qsub qsub_represents qnegative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_canonical reciprocal_identity bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr qone rescale_to)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRootAlgebra (equal_of_values re_mul im_mul re_sub im_sub re_add im_add re_scale im_scale re_neg im_neg re_one im_one)
open GaussianSineProductImaginaryLogDerivative (axisNumerator)
open GaussianSineProductImaginaryLogDerivativeTail (axis_norm)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "LV" => GaussianBinetExponentialIntegralGrid.value

def value (X Y D sign A B : PTm n) : PTm n :=
  qmul (fraction A B) (reciprocal (polynomial X Y D sign A B))
def antisymmetric (X Y D sign A B : PTm n) : PTm n :=
  qmul multiplier (qsub (reciprocal (pole true X Y D sign A B)) (reciprocal (pole false X Y D sign A B)))
def panelValue (p X Y D sign A B R U L N : PTm n) : PTm n :=
  let T := D*L
  qmul multiplier (qsub (LV (p+N) (qnegative (pole true X Y D sign A B)) ((R+U)*T) T N)
    (LV (p+N) (qnegative (pole false X Y D sign A B)) ((R+U)*T) T N))

private theorem half_turn (X Y D sign A B : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul multiplier (qsub (pole false X Y D sign A B) (pole true X Y D sign A B)) ≐ fraction A B := by
  let P := poleNumerator false X Y D sign A B
  let M := poleNumerator true X Y D sign A B
  let w := (ComplexLogarithmRemainder.neg imaginaryCode : PTm n)
  let E := D*B
  have hE := positive_product D B hD hB
  have h₂ := le_succ_self (Γ := Γ) one
  have h := positive_product two E h₂ hE
  have sub := qsub_represents _ _ P M E hE (ofGaussian_represents P E hE) (ofGaussian_represents M E hE)
  have l := qmul_represents _ _ w _ two E h₂ hE (ofGaussian_represents w two h₂) sub
  have r := rescale_to (fraction A B) (scale A oneCode) B (two*D) (two*E)
    (ofGaussian_represents _ _ hB) (by dsimp only [E]; ipra_ring)
  apply canonical_unique _ _ _ (two*E) (qmul_canonical _ _) (ofGaussian_canonical _ _ hB) h (hrv := r)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := l)
  dsimp only [P,M,w]
  apply equal_of_values
  all_goals simp [poleNumerator,signedTimeNumerator,imaginaryCode,axisNumerator,re_mul,im_mul,re_sub,im_sub,
    re_add,im_add,re_scale,im_scale,re_neg,im_neg,re_one,im_one,eval_re_code,eval_im_code,ZT.toZ_ofNat]
  all_goals ring

/-- The exact antisymmetric pair of reciprocals is the cleared sine kernel. -/
theorem reciprocal_difference (X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] antisymmetric X Y D sign A B ≐ value X Y D sign A B := by
  let a := pole false X Y D sign A B
  let b := pole true X Y D sign A B
  let u := reciprocal a
  let v := reciprocal b
  let Q := polynomial X Y D sign A B
  let d := qsub a b
  have hX := hz.andE₁.andE₁
  have hD := hz.andE₂
  have hd := positive_product D D hD hD
  have na := GaussianNameReciprocal.lower_norm_positive a D hD (name_lower a X D hX hD (pole_lower false X Y D sign A B hD hB))
  have nb := GaussianNameReciprocal.lower_norm_positive b D hD (name_lower b X D hX hD (pole_lower true X Y D sign A B hD hB))
  have nQ := GaussianNameReciprocal.lower_norm_positive Q (D*D) hd
    (name_lower Q (X*X) (D*D) (positive_product X X hX hX) hd (polynomial_lower X Y D sign A B hD hB))
  have ha := reciprocal_identity a na
  have hb := reciprocal_identity b nb
  have hQ := reciprocal_identity Q nQ
  have cancel : Γ ⊢[PRAAx] qmul Q (qmul v u) ≐ qone :=
    (qmul_congr (product_polynomial X Y D sign A B hD hB).eqSymm (.eqRefl _)).eqTrans
      ((qmul_associative (qmul a b) v u).eqSymm.eqTrans
        ((qmul_congr ((qmul_associative a b v).eqTrans ((qmul_congr (.eqRefl _) hb).eqTrans
          (qmul_one_right a (ofGaussian_canonical _ _ (positive_product _ _ hD hB))))) (.eqRefl _)).eqTrans ha))
  have prod := inverse_unique Q (qmul v u) (reciprocal Q) (qmul_canonical _ _) (reciprocal_canonical _) cancel hQ
  have reordered : Γ ⊢[PRAAx] qmul multiplier (qmul (qmul v d) u) ≐ qmul (qmul multiplier d) (qmul v u) :=
    (qmul_congr (.eqRefl _) ((qmul_congr (qmul_commutative v d) (.eqRefl _)).eqTrans (qmul_associative d v u))).eqTrans
      (qmul_associative multiplier d (qmul v u)).eqSymm
  exact (qmul_congr (.eqRefl _) (GaussianNameReciprocal.inverse_difference b a nb na)).eqTrans
    (reordered.eqTrans (qmul_congr (half_turn X Y D sign A B hD hB) prod))

private theorem multiplier_bound : Γ ⊢[PRAAx] bounded (multiplier : PTm n) one two := by
  let w := (ComplexLogarithmRemainder.neg imaginaryCode : PTm n)
  have h₂ := le_succ_self (Γ := Γ) one
  have eq : Γ ⊢[PRAAx] normSq w ≐ one*one :=
    (ComplexLogarithmRemainder.normSq_neg imaginaryCode).eqTrans (axis_norm one)
  exact (bounded_iff _ _ _ _ _ h₂ h₂ (ofGaussian_represents w two h₂)).iffMpr
    (le_congr (congrMul (.eqRefl (two*two)) eq.eqSymm) (by ipra_ring) (le_refl ((two*two)*(one*one))))

theorem finite_error (p X Y D sign A B R U K L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B)
    (hU : Γ ⊢[PRAAx] le A (U*B)) (hm : Γ ⊢[PRAAx] le D (K*X)) (hL : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+U)*(D*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (panelValue p X Y D sign A B R U L N) (value X Y D sign A B)
      (GaussianBinetArctangentCosineLaplace.error p R U K (D*L) L) (unit p*unit L) := by
  let T := D*L
  let E := GaussianBinetArctangentCosineLaplace.error p R U K T L
  let H := unit p*unit L
  let a := pole false X Y D sign A B
  let b := pole true X Y D sign A B
  let l := LV (p+N) (qnegative a) ((R+U)*T) T N
  let r := LV (p+N) (qnegative b) ((R+U)*T) T N
  have hH := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive L)
  have h₂ := le_succ_self (Γ := Γ) one
  have left := pole_integral_error false p X Y D sign A B R U K L N hz hB hU hm hL hN hpN
  have right := pole_integral_error true p X Y D sign A B R U K L N hz hB hU hm hL hN hpN
  have sub := GaussianNamedDifference.difference_distance r (reciprocal b) l (reciprocal a) E E H hH right left
  have product := bounded_product multiplier _ one two (E+E) H h₂ hH multiplier_bound sub
  have difference : Γ ⊢[PRAAx] distanceBounded (panelValue p X Y D sign A B R U L N) (antisymmetric X Y D sign A B)
      (one*(E+E)) (two*H) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference multiplier _ _).eqSymm (.eqRefl _) (.eqRefl _) product
  exact distance_congr (.eqRefl _) (reciprocal_difference X Y D sign A B hz.andE₁ hB) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ E H (positive_product _ _ h₂ hH) hH
      (le_of_eq_add (d := zero) (by dsimp only [H]; ipra_ring)) difference)

end LeanProofs.IPRA.Analysis.GaussianBinetSineLaplaceResolvent
