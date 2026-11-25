import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedGamma
import IPRADerivations.Analysis.GaussianRealExponentialCompactLower
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsCaps

/-!
# Real samples and strict sign of the original negative Gamma name

The exponential of the real log magnitude has a positive compact lower
bound. The original interval sign then places the actual Gamma name
strictly below zero for even N and strictly above zero for odd N.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGammaSign

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFactorBudget (power_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianGammaNegativeIntervalNamedGamma (actualF actualData actual_regular signedF signedData signed_real signed_regular)
open GaussianGammaNegativeIntervalNamedSign (even_interval_sign odd_interval_sign sign_cases valueF valueData
  positive_strict_order negative_strict_order)
open GaussianGammaNegativeIntervalProductSign (signUnit)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedStrictOrderDifference (trans_weak)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero)
open GaussianRationalMatrixFiniteSums (minusOne)
open GaussianRationalReciprocal (power_canonical)
open GaussianRationalSyntheticDivision (qone qmul_zero_right)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingMultiplicativeBoundsCaps (strict_fractions)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open RationalGaussianEmbedding (axis axis_congr axis_one axis_negative)
open RationalValueBounds (upper upper_congr upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "EF" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData

theorem actual_real (f : PR 2) (x E N : PTm n) : Γ ⊢[PRAAx] realSamples (actualF f) (actualData f x E N) := by
  have a : Γ ⊢[PRAAx] axis (signUnit (succ N)) :=
    .orE (sign_cases N) (axis_congr Prf.hyp0.eqSymm axis_one) (axis_congr Prf.hyp0.eqSymm (axis_negative qone axis_one))
  have c := GaussianStirlingNames.constant_real _ (power_canonical minusOne (succ N)) a
  exact GaussianStirlingNames.multiply_real _ _ _ _ c (signed_real f x E N)

private def lowerDenominator (f : PR 2) (x : PTm n) : PTm n := pw (num 3) (U f x)

private theorem lower_denominator_positive (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx] le one (lowerDenominator f x) :=
  power_positive _ _ (by ipra_le 2)

private theorem exponential_lower_at (f : PR 2) (x p q : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    upper (fstT (ap2 constantF p (fraction one (lowerDenominator f x)))) (fstT (ap2 (EF f) q (ed f x)))
      (unit p+unit q) (unit p*unit q) := by
  let d := lowerDenominator f x
  let r := fraction one d
  have lower := GaussianRealExponentialCompactLower.original_observation_lower f q (U f x) x (exponential_input f x hf) hr
  have read := (congrFst (constant_at (Γ := Γ) p r)).eqTrans (fraction_real_part one d (lower_denominator_positive f x))
  exact upper_mono _ _ _ _ _ _ (unit_positive q) (upper_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) lower)
    (by ipra_le 𝔞(unit q)^2)

private theorem exponential_lower (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    realOrder constantF (EF f) (fraction one (lowerDenominator f x)) (ed f x) := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let y := Syn.shift (Syn.shift x)
  have hF : Δ ⊢[PRAAx] pointCN f y := by simpa [Δ, Fm.shift, Syn.shift, y] using hf.shift.shift
  have hR : Δ ⊢[PRAAx] realSamples f y := by simpa [Δ, Fm.shift, Syn.shift, y] using hr.shift.shift
  refine .allI (.allI ?_)
  simpa [realOrder, Syn.shift, lowerDenominator, exponentialInputData, pw, one, Δ, y] using
    exponential_lower_at f y (var 1) (var 0) hF hR

private theorem positive_fraction (d : PTm n) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] strictOrder constantF constantF qzero (fraction one d) := by
  have sep : Γ ⊢[PRAAx] lt (d*zero) (one*one) := by unfold lt; ipra_le 0
  have frac : Γ ⊢[PRAAx] strictOrder constantF constantF (fraction zero one) (fraction one d) :=
    .andI (constant_order _ _ (fractions_order zero one one d (le_refl one) hd (le_of_lt sep)))
      (strict_fractions zero one one d (le_refl one) hd sep)
  exact strict_transport _ _ _ _ _ _ _ _
    (constant_data_cross _ _ (GaussianGammaRationalWendelBoundary.fraction_zero one (le_refl one)).eqSymm)
    (cross_refl _ _ (constant_regular _)) frac

theorem signed_positive (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] strictOrder constantF (signedF f) qzero (signedData f x E N) := by
  let F := GaussianGammaNegativeIntervalNamedLog.nameF f
  let y := GaussianGammaNegativeIntervalNamedLog.data x E N
  have lower := exponential_lower F y (GaussianGammaNegativeIntervalNamedLog.name_regular f x E N hs)
    (GaussianGammaNegativeIntervalNamedLog.name_real f x E N)
  exact trans_weak _ _ _ _ _ _ (positive_fraction _ (lower_denominator_positive F y)) lower

private theorem signed_zero_cross (N : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (valueF constantF) constantF (valueData constantF N qzero) qzero :=
  cross_trans _ _ _ _ _ _ (constant_product_cross (signUnit (succ N)) qzero)
    (constant_data_cross _ _ (qmul_zero_right _))

theorem positive_sign (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E) (hOdd : Γ ⊢[PRAAx] par N ≐ one) :
    Γ ⊢[PRAAx] strictOrder constantF (actualF f) qzero (actualData f x E N) := by
  have signOrder := positive_strict_order constantF (signedF f) N qzero (signedData f x E N)
    (constant_regular qzero) (signed_regular f x E N hs) (odd_interval_sign N hOdd) (signed_positive f x E N hs)
  exact strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ (signed_zero_cross N))
    (cross_refl _ _ (actual_regular f x E N hs)) signOrder

theorem negative_sign (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E) (hEven : Γ ⊢[PRAAx] par N ≐ zero) :
    Γ ⊢[PRAAx] strictOrder (actualF f) constantF (actualData f x E N) qzero := by
  have signOrder := negative_strict_order constantF (signedF f) N qzero (signedData f x E N)
    (constant_regular qzero) (signed_regular f x E N hs) (even_interval_sign N hEven) (signed_positive f x E N hs)
  exact strict_transport _ _ _ _ _ _ _ _ (cross_refl _ _ (actual_regular f x E N hs)) (signed_zero_cross N) signOrder

theorem actual_named_negative_Gamma_sign_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (realSamples (actualF f) (actualData f (var 0) (var 1) (var 2)) ⋏
      (source f (var 0) (var 1) ⟶
        (((par (var 2) ≐ one) ⟶ strictOrder constantF (actualF f) qzero (actualData f (var 0) (var 1) (var 2))) ⋏
         ((par (var 2) ≐ zero) ⟶ strictOrder (actualF f) constantF (actualData f (var 0) (var 1) (var 2)) qzero)))) :=
  closeUniv 3 (.andI (actual_real f _ _ _) (.impI (.andI
    (.impI (positive_sign f _ _ _ Prf.hyp1 Prf.hyp0)) (.impI (negative_sign f _ _ _ Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGammaSign
