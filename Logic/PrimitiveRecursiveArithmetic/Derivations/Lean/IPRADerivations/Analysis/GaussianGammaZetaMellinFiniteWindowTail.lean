import IPRADerivations.Analysis.GaussianGammaZetaMellinImproper
import IPRADerivations.Analysis.GaussianGammaZetaMellinFiniteNestedBound
import IPRADerivations.Analysis.GaussianGammaZetaMellinFiniteDampedLower
import IPRADerivations.Analysis.GaussianGammaZetaMellinFiniteCompactUpper

/-!
# The finite damped window error is uniform in the number of terms

Both exterior tails use the same literal finite evaluator and the same
read budget as the full window and the earlier rescaled middle panel.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteWindowTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianGammaCompactCutoffGeometry
  (lowerWidth middleWidth upperWidth lower_endpoint middle_endpoint three_endpoint upper_positive)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaIntegralCutoffs (etaDen top height eta_den_positive top_positive)
open GaussianGammaZetaMellinFiniteDampedEvaluator (evaluatorF budget)
open GaussianGammaZetaMellinFiniteNested (datum data interval_source)
open GaussianGammaZetaMellinImproper (cutoff cutoff_budgets)
open GaussianGammaZetaMellinUpperPoint (coefficientBound degree)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "S" => GaussianEulerLowerPowerCoefficients.source
local notation "F" => GaussianCompactRiemannName.nameF evaluatorF

theorem observation_error (r v z R B j N p q : PTm n)
    (hz : Γ ⊢[PRAAx] S z R B (succ j)) (hpq : Γ ⊢[PRAAx] lt p q)
    (hp : Γ ⊢[PRAAx] le (cutoff v R) p) :
    let A := succ j
    let E := etaDen q A R
    let T := top q A R
    let Q := budget (R+one) E T N
    Γ ⊢[PRAAx] distanceBounded (ap2 F r (datum z R B N Q A q)) (ap2 F r (datum z R B N Q A p))
      (num 5*unit r+num 7*unit v) (unit v*unit r) := by
  intro A E T Q
  let H := unit (height p A R)
  let T₀ := top p A R
  let C₁ := lowerWidth p q A
  let C₂ := middleWidth p q A R
  let C₃ := upperWidth p q A R
  let b := one+(C₁+C₂)
  let K := two*coefficientBound (R+one)
  let J := two*GaussianGammaZetaMellinFiniteDampedUpper.coefficient (R+one)
  let U := unit r
  let V := unit v
  let u := ap2 F r (data (shifted z B) (R+one) B N Q one C₁ E T)
  let w := ap2 F r (data (shifted z B) (R+one) B N Q b C₃ E T)
  have hE := eta_den_positive (Γ := Γ) q A R
  have ht := top_positive (Γ := Γ) q A R
  have hH := unit_positive (Γ := Γ) (height p A R)
  have hu := unit_positive (Γ := Γ) r
  have hv := unit_positive (Γ := Γ) v
  have hQ : Γ ⊢[PRAAx] le N Q :=
    le_of_eq_add (d := N*GaussianGammaZetaMellinDampedPoint.cost (R+one) E T) (by dsimp only [Q,budget]; ipra_ring)
  have edge : Γ ⊢[PRAAx] b ≐ E*T₀ :=
    (by dsimp only [b]; ipra_ring : Γ ⊢[PRAAx] b ≐ (one+C₁)+C₂).eqTrans
      ((congrAdd (lower_endpoint p q A) (.eqRefl _)).eqTrans (middle_endpoint p q A R (le_of_lt hpq)))
  have endEq : Γ ⊢[PRAAx] b+C₃ ≐ E*T :=
    (by dsimp only [b]; ipra_ring : Γ ⊢[PRAAx] b+C₃ ≐ one+(C₁+C₂+C₃)).eqTrans (three_endpoint p q A R (le_of_lt hpq))
  have left : Γ ⊢[PRAAx] intervalSource (shifted z B) (R+one) B one C₁ E T :=
    interval_source z R B A _ _ _ _ hz (le_refl one) hE
      (le_of_eq_add (d := C₂+C₃) (endEq.eqSymm.eqTrans (by dsimp only [b]; ipra_ring)))
  have right : Γ ⊢[PRAAx] intervalSource (shifted z B) (R+one) B b C₃ E T :=
    interval_source z R B A _ _ _ _ hz (le_add_right _ _) hE
      (le_congr endEq.eqSymm (.eqRefl _) (le_refl _))
  have paid := cutoff_budgets (Γ := Γ) v R A p hp
  have lowBase : Γ ⊢[PRAAx] le ((two*A)*V) H := paid.andE₁
  have hlow : Γ ⊢[PRAAx] le ((num 4*A)*V) (two*H) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right two lowBase)
  have low : Γ ⊢[PRAAx] bounded u ((num 4*A)*U+H) (H*U) :=
    GaussianGammaZetaMellinFiniteDampedLower.original_observation_bound r p q j z R (R+one) B T N hpq hz ht left
  have atLeast : Γ ⊢[PRAAx] le E b :=
    le_congr (one_mul E) ((mul_comm T₀ E).eqTrans edge.eqSymm) (mul_le_mul_right E (top_positive p A R))
  have big : Γ ⊢[PRAAx] le two K := by
    have f := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) (degree (R+one))
    dsimp only [K,coefficientBound]
    ipra_le 4*sl f+2
  have boundJ : Γ ⊢[PRAAx] le J (num 3*K) := by
    have h : Γ ⊢[PRAAx] J ≐ two*K+two := by
      dsimp only [J,K,GaussianGammaZetaMellinFiniteDampedUpper.coefficient]
      ipra_ring
    exact le_congr h.eqSymm (.eqRefl _) (by ipra_le sl big)
  have highBase : Γ ⊢[PRAAx] le (K*V) T₀ := paid.andE₂
  have Jv : Γ ⊢[PRAAx] le (J*V) (num 3*T₀) :=
    le_trans (mul_le_mul_right V boundJ)
      (le_congr (by ipra_ring) (mul_comm _ _) (mul_le_mul_right (num 3) highBase))
  have hhigh : Γ ⊢[PRAAx] le ((J*E)*V) (num 3*b) :=
    le_congr (by ipra_ring)
      ((by ipra_ring : Γ ⊢[PRAAx] (num 3*T₀)*E ≐ num 3*(E*T₀)).eqTrans (congrMul (.eqRefl _) edge.eqSymm))
      (mul_le_mul_right E Jv)
  have high : Γ ⊢[PRAAx] bounded w ((J*E)*U+num 3*b) (b*U) :=
    GaussianGammaZetaMellinFiniteCompactUpper.observation_bound r (shifted z B) (R+one) B N b C₃ E T
      right atLeast (upper_positive p q A R hpq)
  have den := positive_product _ _ hv hu
  have lo : Γ ⊢[PRAAx] bounded u (two*U+V) (V*U) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hH hu) den
      (by change Γ ⊢[PRAAx] le ((((num 4*A)*U+H)*(V*U))) ((two*U+V)*(H*U))
          ipra_le 𝔞(U*U)*sl hlow) low
  have hi : Γ ⊢[PRAAx] bounded w (num 3*U+num 3*V) (V*U) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_trans hE atLeast) hu) den
      (by change Γ ⊢[PRAAx] le (((J*E)*U+num 3*b)*(V*U)) ((num 3*U+num 3*V)*(b*U))
          ipra_le 𝔞(U*U)*sl hhigh) high
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianGammaZetaMellinFiniteNestedBound.comparison_from_tails r z R B A N Q p q V _ _ hz hQ hpq hv lo hi)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteWindowTail
