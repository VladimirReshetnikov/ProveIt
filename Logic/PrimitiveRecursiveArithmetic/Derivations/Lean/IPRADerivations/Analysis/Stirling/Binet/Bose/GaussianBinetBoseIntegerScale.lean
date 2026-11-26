import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianApproximateInverseDistance
import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseExponential
import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianBoundedIntegerExponentialStages
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedProductObservationBound

/-!
# Bind integer scaling to the original signed Pi chart

The natural-scale name and the separately evaluated rational chart
read the same signed coefficient times actual Pi samples. Their two
original clocks compare using the checked Pi regularity.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseIntegerScale

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale eval_re_code eval_im_code)
open GaussianBinetBoseExponential (scaleF scaleData scaleBudget exp_input piClock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedNaturalScale (clock clock_later)
open GaussianPiRationalScale (point native point_bound)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul ofGaussian_canonical ofGaussian_represents canonical_unique represents_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (natScale natScale_congr natScale_product)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal_of_values re_scale im_scale re_neg im_neg)
open GaussianSineProductImaginaryLogDerivative (realNumerator)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Pi" => GaussianGammaHalfPiName.nameF
local notation "SF" => GaussianNamedNaturalScale.nameF scaleF
local notation "sd" => GaussianNamedNaturalScale.data

theorem rational_coefficient (s : Bool) (i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] natScale i (point s (two*A) B) ≐ point s (two*(i*A)) B := by
  let a := native s (two*A)
  let b := native s (two*(i*A))
  have old := GaussianRationalNaturalScale.natScale_represents i (point s (two*A) B) a B hB
    (ofGaussian_represents a B hB)
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (scale i a) b := by
    cases s <;> apply equal_of_values <;>
      simp only [a,b,native,Bool.false_eq_true,if_true,if_false,re_scale,im_scale,re_neg,im_neg,
        realNumerator,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;> ring
  exact canonical_unique _ _ b B (GaussianRationalNaturalScale.natScale_canonical _ _)
    (ofGaussian_canonical b B hB) hB (represents_congr (.eqRefl _) e (.eqRefl _) old)
    (ofGaussian_represents b B hB)

theorem stage_at (s : Bool) (p E i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ap2 SF p (sd E i (scaleData s A B)) ≐
      qmul (point s (two*(i*A)) B) (ap2 Pi (piClock (clock p E) A) zero) := by
  let k := clock p E
  let c := point s (two*A) B
  let v := ap2 Pi (piClock k A) zero
  have read := GaussianBoundedConstantProductName.sample_at (Γ := Γ) Pi k (scaleBudget A) c zero
  have reverse := (natScale_congr (.eqRefl i) (qmul_commutative c v)).eqTrans
    ((natScale_product i v c).eqSymm.eqTrans
      ((qmul_congr (.eqRefl v) (rational_coefficient s i A B hB)).eqTrans (qmul_commutative _ _)))
  exact (GaussianNamedNaturalScale.sample_at scaleF p E i (scaleData s A B)).eqTrans
    ((natScale_congr (.eqRefl i) read).eqTrans reverse)

def comparisonCost (i A : PTm n) : PTm n := (two*(i*A))*(two+two)

@[simp] theorem subst_comparisonCost {m : ℕ} (σ : Fin n → PTm m) (i A : PTm n) :
    Syn.subst σ (comparisonCost i A) = comparisonCost (Syn.subst σ i) (Syn.subst σ A) := by
  simp [comparisonCost,two]

theorem raw_error (s : Bool) (p E i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 SF p (sd E i (scaleData s A B)))
      (ap2 scaleF p (scaleData s (i*A) B)) (comparisonCost i A) (unit p) := by
  let k := piClock (clock p E) A
  let l := piClock p (i*A)
  let c := point s (two*(i*A)) B
  let a := ap2 Pi k zero
  let b := ap2 Pi p zero
  let d := ap2 Pi l zero
  have pk : Γ ⊢[PRAAx] le p k := le_trans (clock_later p E) (le_add_right _ _)
  have pl : Γ ⊢[PRAAx] le p l := le_add_right _ _
  have piReg := GaussianGammaHalfPiName.name_regular (Γ := Γ) zero
  have left := GaussianNamedProductObservationBound.late_observation Pi zero p k piReg pk
  have right := GaussianNamedProductObservationBound.late_observation Pi zero p l piReg pl
  have piError := distance_triangle_same a b d _ _ _ (unit_positive p) left
    (distance_symmetric _ _ _ _ (unit_positive p) right)
  have unitScale : Γ ⊢[PRAAx] le (one*(two*(i*A))) ((two*(i*A))*B) :=
    le_congr (.eqRefl _) (mul_comm B (two*(i*A)))
      (mul_le_mul_right (two*(i*A)) hB)
  have h := point_bound s (two*(i*A)) B (two*(i*A)) one hB (le_refl one) unitScale
  have direct := GaussianBoundedConstantProductName.sample_at (Γ := Γ) Pi p (scaleBudget (i*A)) c zero
  exact distance_congr (stage_at s p E i A B hB).eqSymm direct.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance c a d (two*(i*A)) _ (unit p) (unit_positive p) h piError)

theorem scale_equivalent (s : Bool) (E i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] le i E) :
    Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent SF scaleF (sd E i (scaleData s A B)) (scaleData s (i*A) B) := by
  have h := exp_input s A B hB
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (comparisonCost i A)
    (GaussianNamedNaturalScale.name_regular scaleF E i _ _ h hi)
    (exp_input s (i*A) B hB).andE₁
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  have sb : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by
    simpa [sh,Fm.shift,Syn.shift] using hB.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, sh, Syn.shift,
    GaussianNamedNaturalScale.subst_data, GaussianBinetBoseExponential.subst_scaleData,
    PTm.subst_mul, subst_comparisonCost] using
    raw_error s (var 0) (sh E) (sh i) (sh A) (sh B) sb

theorem exponential_equivalent (s : Bool) (E i A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] le i E) :
    Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent (GaussianBoundedIntegerExponentialStages.expF scaleF)
      GaussianBinetBoseExponential.expF
      (GaussianBoundedIntegerExponentialStages.expData E i (GaussianBinetBoseExponential.expRadius A) (scaleData s A B))
      (GaussianBinetBoseExponential.expData s (i*A) B) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper SF scaleF _ _ _ _
    (GaussianNamedNaturalScale.exponential_input scaleF E i _ _ (exp_input s A B hB) hi)
    (exp_input s (i*A) B hB) (scale_equivalent s E i A B hB hi)

end LeanProofs.IPRA.Analysis.GaussianBinetBoseIntegerScale
