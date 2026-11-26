import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerDecayBound
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerTransformedPower

/-!
# Lower-tail pointwise envelope for named damping

On a rational power abscissa `t = (a/b)^A ≤ 1`, the original Euler power
is bounded by `(b/a)^(A-1)`. The unit decay envelope preserves this leading
bound. A separately clocked comparison removes finite product errors at
the original named kernel observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerLowerPointwise

open_ipra
open GaussianNamedDampingPowerIntegrand (nameF data)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianEulerDampedNamedIntegrand (decayF decayData)
open GaussianNameArithmetic (multiplyModulus)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (qmul qmul_canonical positive_product)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSlackRemoval (slack slack_removal_at)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem point_regular (F G : PR 2) (z B x y C₀ C R₀ R E T a b : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hs : Γ ⊢[PRAAx] GaussianNamedDampingPowerChart.source F G x y C₀ C R₀ R E T a b) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN (nameF F G) (data F G z B x y a b) :=
  GaussianEulerDampedNamedIntegrand.name_regular _ z B a b _
    (GaussianNamedDampingPowerChart.name_regular F G x y C₀ C R₀ R E T a b hs)
    (.andI hB hs.andE₂.andE₂.andE₂.andE₁)

private theorem raw_bound (F G : PR 2) (p z Rz B A a b x y C₀ C R₀ R E T : PTm n)
    (hp : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z Rz B A a b)
    (hs : Γ ⊢[PRAAx] GaussianNamedDampingPowerChart.source F G x y C₀ C R₀ R E T (pw a A) (pw b A)) : Γ ⊢[PRAAx]
    bounded (ap2 (nameF F G) p (data F G z B x y (pw a A) (pw b A)))
      (pw b (pred A)*unit p+(pw b (pred A)+two*pw a (pred A))) (pw a (pred A)*unit p) := by
  let c := pw a A
  let d := pw b A
  let H := GaussianNamedDampingPowerChart.nameF F G
  let X := GaussianNamedDampingPowerChart.data F G x y c d
  let Y := powerData z B c d
  let Z := decayData H X
  let j := GaussianFastValueCut.exponent (multiplyModulus powerF (decayF H) Y Z) p
  let U := pw b (pred A)
  let V := pw a (pred A)
  let P := unit p
  let J := unit j
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _ hp.andE₂.andE₁.andE₁
  have hJ := unit_positive (Γ := Γ) j
  have hP := unit_positive (Γ := Γ) p
  have late : Γ ⊢[PRAAx] le P J := GaussianCompactRiemannName.dyadic_monotone p j (le_add_right p _)
  have square : Γ ⊢[PRAAx] le P (J*J) := le_congr (one_mul P) (.eqRefl _)
    (AnalyticNumberTheory.PhiLower.le_mul_mono hJ late)
  have read := (GaussianNameArithmetic.multiply_at (Γ := Γ) powerF (decayF H) Y Z p).eqTrans
    (GaussianExponentialReference.recode_fixed (qmul (ap2 powerF j Y) (ap2 (decayF H) j Z)) (qmul_canonical _ _))
  have raw := bounded_product _ _ _ _ _ _ (positive_product _ _ hV hJ) hJ
    (GaussianEulerLowerTransformedPower.original_power_bound j z Rz B A a b hp)
    (GaussianNamedDampingPowerDecayBound.original_decay_bound F G j x y C₀ C R₀ R E T c d hs)
  refine bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hV hJ) hJ)
    (positive_product _ _ hV hP) ?_ (bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) raw)
  change Γ ⊢[PRAAx] le (((U*J+V)*(J+one))*(V*P)) ((U*P+(U+two*V))*((V*J)*J))
  ipra_le 𝔞(V*(U+V)*J)*sl late+𝔞(V*V)*sl square

theorem original_pointwise_bound (F G : PR 2) (p z Rz B A a b x y C₀ C R₀ R E T : PTm n)
    (hp : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z Rz B A a b)
    (hs : Γ ⊢[PRAAx] GaussianNamedDampingPowerChart.source F G x y C₀ C R₀ R E T (pw a A) (pw b A)) : Γ ⊢[PRAAx]
    bounded (ap2 (nameF F G) p (data F G z B x y (pw a A) (pw b A)))
      (pw b (pred A)*unit p+pw a (pred A)) (pw a (pred A)*unit p) := by
  let H := nameF F G
  let X := data F G z B x y (pw a A) (pw b A)
  let U := pw b (pred A)
  let V := pw a (pred A)
  let P := unit p
  let N := U*P+V
  let D := V*P
  let C₀' := U+num 3*V
  let j := GaussianRationalSlackRemoval.precision (ap2 H p X) N D C₀'
  let J := unit j
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _ hp.andE₂.andE₁.andE₁
  have hP := unit_positive (Γ := Γ) p
  have hJ := unit_positive (Γ := Γ) j
  have hD := positive_product _ _ hV hP
  have hPJ := positive_product _ _ hP hJ
  have hVJ := positive_product _ _ hV hJ
  have regular : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN H X :=
    point_regular F G z B x y C₀ C R₀ R E T (pw a A) (pw b A) hp.andE₁.andE₂.andE₁.andE₁ hs
  have near := GaussianNameEquivalence.point_at H X p j regular
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hPJ hVJ near
    (raw_bound F G j z Rz B A a b x y C₀ C R₀ R E T hp hs)
  apply slack_removal_at _ _ _ C₀' hD
  refine bounded_radius_mono _ _ _ _ _ (positive_product _ _ hPJ hVJ) (positive_product _ _ hD hJ) ?_ raw
  change Γ ⊢[PRAAx] le (((P+J)*(V*J)+(U*J+(U+two*V))*(P*J))*(D*J)) ((N*J+C₀'*D)*((P*J)*(V*J)))
  dsimp only [N,D,C₀']
  ipra_le 𝔞((U+num 3*V)*V*P*P*J*J)*sl hV

theorem actual_named_power_damped_Euler_lower_time_pointwise_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
      (GaussianEulerLowerPowerOrder.source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        GaussianNamedDampingPowerChart.source F G (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)
          (var 13) (var 14) (pw (var 5) (var 4)) (pw (var 6) (var 4)) ⟶
        bounded (ap2 (nameF F G) (var 0) (data F G (var 1) (var 3) (var 7) (var 8) (pw (var 5) (var 4)) (pw (var 6) (var 4))))
          (pw (var 6) (pred (var 4))*unit (var 0)+pw (var 5) (pred (var 4))) (pw (var 5) (pred (var 4))*unit (var 0))) :=
  closeUniv 15 (.impI (.impI (original_pointwise_bound F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerLowerPointwise
