import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Tails.GaussianEulerLowerTailLocalComparison
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Integrands.GaussianEulerLowerTransformedIntegrand
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Tails.GaussianEulerLowerBlockWeight

/-!
# Norms of the actual original rows in the lower-time panels

The checked right-endpoint estimate and the original sampled
modulus give `1/v^k + L S/D + 3·2^-s` for every actual row
in its panel. Here `D` is the root denominator and `S` the root
step numerator times the power exponent.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerTailRowBound

open_ipra
open GaussianEulerLowerTailRootGrid (rootDenominator rootNumerator timeNumerator timeDenominator)
open GaussianEulerLowerTailPartition (rootStep panelWidth totalWidth root_right_guard root_step_exact exact_panel_width)
open GaussianEulerLowerTailLocalComparison (rowTime rightTime widthCap original_row_distance)
open GaussianEulerLowerPowerCoefficients (source)
open GaussianEulerLowerBlockWeight (rowNumerator rowDenominator)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (sampledModulus)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stepScale (p q k : PTm n) : PTm n := succ k*rootStep p q

theorem right_width (i N p q k : PTm n) : Γ ⊢[PRAAx]
    le (panelWidth i N p q (succ k)) (stepScale p q k*pw (rootNumerator (succ i) N p q) k) := by
  have e := natEq (eq_add_of_le (GaussianEulerLowerTailRootGrid.time_monotone (Γ := Γ)
    i (succ i) N p q (succ k) (le_succ_self i)))
  unfold timeNumerator at e
  have gap := PowerGap.power_gap (root_step_exact (Γ := Γ) i N p q) (le_refl _) k
  have cleared : Γ ⊢[PRAAx] le
      (monus (pw (rootNumerator (succ i) N p q) (succ k)) (pw (rootNumerator i N p q) (succ k)))
      (stepScale p q k*pw (rootNumerator (succ i) N p q) k) := by
    unfold stepScale
    ipra_le sl gap using linear_combination e
  exact le_congr (exact_panel_width i N p q (succ k)).eqSymm (.eqRefl _) cleared

theorem time_den_product (N q k R : PTm n) :
    Γ ⊢[PRAAx] timeDenominator N q (succ k) R ≐
      rootDenominator N q (succ k) R*pw (rootDenominator N q (succ k) R) k :=
  (pw_succ _ _).eqTrans (mul_comm _ _)

theorem scale_local_budget (x y s N p q k R L : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded x y (rateNumerator (L*widthCap N p q k R)
        (timeDenominator N q (succ k) R) s s) (rateDenominator (timeDenominator N q (succ k) R) s s)) :
    Γ ⊢[PRAAx] distanceBounded x y
      (L*stepScale p q k*unit s+two*rootDenominator N q (succ k) R) (rootDenominator N q (succ k) R*unit s) := by
  let D := rootDenominator N q (succ k) R
  let E := timeDenominator N q (succ k) R
  let P := unit s
  let S := stepScale p q k
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) hN
  have hE : Γ ⊢[PRAAx] le one E := GaussianPolynomialPerturbation.power_positive _ _ hD
  have hP : Γ ⊢[PRAAx] le one P := unit_positive s
  have den : Γ ⊢[PRAAx] le one (rateDenominator E s s) :=
    positive_product _ _ (positive_product _ _ hE hP) hP
  apply distance_radius_mono _ _ _ _ _ _ den (positive_product _ _ hD hP) _ h
  have product := natEq (time_den_product (Γ := Γ) N q k R)
  apply le_of_eq_add (d := zero)
  apply deriveNat
  dsimp only [rateNumerator,rateDenominator,widthCap,stepScale]
  ipra_simps
  rw [product]
  ring

theorem right_sample_norm (i s N p q k z R B : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i N) (h : Γ ⊢[PRAAx] source z R B (succ k)) :
    Γ ⊢[PRAAx] bounded (ap3 evaluatorF s (rightTime i N p q (succ k) R) (fixedData z B))
      (pw (rootDenominator N q (succ k) R) k*unit s+pw (rootNumerator (succ i) N p q) k)
      (pw (rootNumerator (succ i) N p q) k*unit s) := by
  let A := succ k
  let a := rootNumerator (succ i) N p q
  let b := rootDenominator N q A R
  let P := unit s
  have pos := root_right_guard i N p q A R hN hpq hi
  have hD : Γ ⊢[PRAAx] le one b := positive_product _ _ (unit_positive _) hN
  have hs : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z R B A a b :=
    .andI h (.andI (.andI pos.andE₁ hD) pos.andE₂)
  have obs := GaussianEulerIntegrandName.sample_at (Γ := Γ) s z B (pw a A) (pw b A)
  have e := pred_succ (Γ := Γ) k
  have numEq := congrAdd (congrMul (congrAp2 powF e (.eqRefl b)) (.eqRefl P))
    (congrAp2 powF e (.eqRefl a))
  have denEq := congrMul (congrAp2 powF e (.eqRefl a)) (.eqRefl P)
  exact bound_congr obs.eqSymm numEq denEq
    (GaussianEulerLowerTransformedIntegrand.original_integrand_bound s z R B A a b hs)

theorem actual_row_norm_bound (i j s N p q k z R B L : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i N)
    (hj : Γ ⊢[PRAAx] lt j (panelWidth i N p q (succ k)))
    (hW : Γ ⊢[PRAAx] le one (totalWidth N p q (succ k)))
    (h : Γ ⊢[PRAAx] source z R B (succ k))
    (hm : Γ ⊢[PRAAx] sampledModulus evaluatorF (timeNumerator zero N p q (succ k))
      (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) L (fixedData z B)) :
    Γ ⊢[PRAAx] bounded (ap3 evaluatorF s (rowTime i j N p q (succ k) R) (fixedData z B))
      (rowNumerator (rootDenominator N q (succ k) R) (pw (rootDenominator N q (succ k) R) k)
        (pw (rootNumerator (succ i) N p q) k) (stepScale p q k) L (unit s))
      (rowDenominator (rootDenominator N q (succ k) R) (pw (rootNumerator (succ i) N p q) k) (unit s)) := by
  let D := rootDenominator N q (succ k) R
  let U := pw D k
  let V := pw (rootNumerator (succ i) N p q) k
  let S := stepScale p q k
  let P := unit s
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) hN
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _
    (root_right_guard i N p q (succ k) R hN hpq hi).andE₁
  have hP : Γ ⊢[PRAAx] le one P := unit_positive s
  have hDP := positive_product _ _ hD hP
  have hVP := positive_product _ _ hV hP
  have est := original_row_distance evaluatorF i j N p q k R L (fixedData z B) s s hN hpq hi hj hW hm
  have near := scale_local_budget _ _ s N p q k R L hN est
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hDP hVP near
    (right_sample_norm i s N p q k z R B hN hpq hi h)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hDP hVP)
    (GaussianEulerLowerBlockWeight.row_denominator_positive D V P hD hV hP) _ raw
  exact le_of_eq_add (d := zero) (by unfold rowNumerator rowDenominator; dsimp only [D,U,V,S,P]; ipra_ring)

theorem actual_lower_panel_right_endpoint_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (panelWidth (var 0) (var 1) (var 2) (var 3) (succ (var 4)))
      (stepScale (var 2) (var 3) (var 4)*pw (rootNumerator (succ (var 0)) (var 1) (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (right_width _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerLowerTailRowBound
