import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Coefficients.GaussianGammaRecurrenceWeights
import IPRADerivations.Analysis.Names.Approximation.GaussianNameBounds
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.Monic.GaussianMonicResidualRadius
import IPRADerivations.Analysis.Names.Arithmetic.RationalGaussianNameEmbedding

/-!
# Actual regular original Gamma recurrence weight names

The unchanged literal source weight at every numeric m is a genuine
regular Gaussian name: one at zero, original gamma at one, and original
signed reconstructed zeta samples at higher degrees. The original sign
has unit numerical norm, so the scalar C17 observation budget is retained
exactly. An actual PR2 name and a computed uniform sample bound are
derived for all N,m, with no regularity or wanted equation as an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRecurrenceWeightName

open_ipra
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianGammaRecurrenceWeights (weight weight_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (radius)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem denominator_positive (p q : PTm n) : Γ ⊢[PRAAx] le one (unit p*unit q) :=
  GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive q)

theorem self_distance (z A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] distanceBounded z z A B :=
  GaussianRationalReciprocal.bound_congr (GaussianCoefficientNormOrder.qsub_self z).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded A B hB)

theorem parity_bound (j : PTm n) : Γ ⊢[PRAAx] bounded (parityPoint j) one one :=
  GaussianMonicResidualRadius.bounded_of_l1 _ _
    (RationalArgmin.rationalLE_congr
      (GaussianFiniteLogarithmWeightedNorm.l1_from_representation _ _ one one (le_refl one)
        (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one))
        (GaussianFiniteLogarithmWeightedNorm.sign_norm1 j)).eqSymm (.eqRefl _)
          (RationalArgmin.reflexive (GaussianEuclideanDistanceName.fraction one one)))

theorem weight_high (p N m : PTm n) (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx]
    weight p N m ≐ qmul (parityPoint (pred m))
      (RationalGaussianEmbedding.embed (RationalReciprocalPowerName.reconstructedSample p m N)) := by
  have first : Γ ⊢[PRAAx] Signum.sg m ≐ one :=
    (GaussianGammaRecurrenceWeights.sg_congr (RationalIntegerNormalization.positive_form (le_trans (le_succ_self one) hm))).eqTrans
      (Signum.sg_succ _)
  have second : Γ ⊢[PRAAx] Signum.sg (pred m) ≐ one :=
    (GaussianGammaRecurrenceWeights.sg_congr (RationalIntegerNormalization.positive_form
      (RationalReciprocalPowerTail.predecessor_positive m hm))).eqTrans (Signum.sg_succ _)
  exact (RationalArithmetic.select_one _ _ _ first).eqTrans (RationalArithmetic.select_one _ _ _ second)

theorem high_distance (p q N M m : PTm n) (hm : Γ ⊢[PRAAx] le two m)
    (h : Γ ⊢[PRAAx] radius (RationalReciprocalPowerName.reconstructedSample p m N)
      (RationalReciprocalPowerName.reconstructedSample q m M) (unit p+unit q) (unit p*unit q)) : Γ ⊢[PRAAx]
    distanceBounded (weight p N m) (weight q M m) (unit p+unit q) (unit p*unit q) :=
  distance_congr (weight_high p N m hm).eqSymm (weight_high q M m hm).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalRoundedPower.multiply_distance_bound _ _ _ _ _ (denominator_positive p q) (parity_bound _)
      (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (denominator_positive p q) h))

theorem from_scalar_error (p q N M m : PTm n)
    (h : Γ ⊢[PRAAx] le two m ⟶ radius (RationalReciprocalPowerName.reconstructedSample p m N)
      (RationalReciprocalPowerName.reconstructedSample q m M) (unit p+unit q) (unit p*unit q)) : Γ ⊢[PRAAx]
    distanceBounded (weight p N m) (weight q M m) (unit p+unit q) (unit p*unit q) := by
  refine .orE (zero_or_succ m) ?_ ?_
  · have left : ((m ≐ zero) :: Γ) ⊢[PRAAx] weight p N m ≐ qone :=
      (weight_congr (.eqRefl p) (.eqRefl N) Prf.hyp0).eqTrans (GaussianGammaRecurrenceWeights.weight_zero p N)
    have right : ((m ≐ zero) :: Γ) ⊢[PRAAx] weight q M m ≐ qone :=
      (weight_congr (.eqRefl q) (.eqRefl M) Prf.hyp0).eqTrans (GaussianGammaRecurrenceWeights.weight_zero q M)
    exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
      (self_distance qone _ _ (denominator_positive p q))
  · refine .orE (zero_or_succ (pred m)) ?_ ?_
    · have form : ((pred m ≐ zero) :: (m ≐ succ (pred m)) :: Γ) ⊢[PRAAx] m ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have left := (weight_congr (.eqRefl p) (.eqRefl N) form).eqTrans (GaussianGammaRecurrenceWeights.weight_one p N)
      have right := (weight_congr (.eqRefl q) (.eqRefl M) form).eqTrans (GaussianGammaRecurrenceWeights.weight_one q M)
      exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
        (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (denominator_positive p q)
          (GammaEulerConstantName.gamma_samples_regularity p q zero))
    · have form : ((pred m ≐ succ (pred (pred m))) :: (m ≐ succ (pred m)) :: Γ) ⊢[PRAAx]
          m ≐ GaussianGammaReciprocalDegreeCells.degree (pred (pred m)) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have positive := le_congr (.eqRefl two) form.eqSymm (GaussianGammaZetaDegreeName.degree_positive _)
      exact high_distance p q N M m positive (.impE h.wk.wk positive)

theorem original_weight_regularity (p q N m : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (weight p N m) (weight q N m) (unit p+unit q) (unit p*unit q) :=
  from_scalar_error p q N N m (.impI (RationalReciprocalPowerName.reconstructed_samples_regularity p q m N Prf.hyp0))

def data (N m : PTm n) : PTm n := pairT N m
def nameF : PR 2 := PTm.toPR (weight (var 0) (fstT (var 1)) (sndT (var 1)))
ipra_subst data

theorem name_at (p N m : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data N m) ≐ weight p N m := by
  simpa only [nameF, data, GaussianGammaRecurrenceWeights.subst_weight, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    (toPR_pair_eq (Γ := Γ) (weight (var 0) (var 1) (var 2)) p N m)

theorem name_regular (N m : PTm n) : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF (data N m) := by
  refine .allI (.allI ?_)
  have h := distance_congr (name_at (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift m))).eqSymm
    (name_at (var 0) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift m))).eqSymm (.eqRefl _) (.eqRefl _)
      (original_weight_regularity _ _ _ _)
  simpa only [GaussianEuclideanDistanceName.pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,subst_data,Syn.shift] using h

theorem sample_bound (p N m : PTm n) : Γ ⊢[PRAAx]
    bounded (weight p N m) (GaussianNameBounds.U nameF (data N m)) one :=
  GaussianRationalReciprocal.bound_congr (name_at p N m) (.eqRefl _) (.eqRefl _)
    (GaussianNameBounds.sample_bound nameF (data N m) p (name_regular N m))

theorem original_Gamma_literal_weight_name_is_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1))) := closeUniv 2 (name_regular _ _)

theorem original_Gamma_literal_weight_samples_have_computed_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (bounded (weight (var 0) (var 1) (var 2)) (GaussianNameBounds.U nameF (data (var 1) (var 2))) one) :=
  closeUniv 3 (sample_bound _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaRecurrenceWeightName
