import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalLogThinChord
import IPRADerivations.Analysis.Names.GaussianNamedNaturalScaleOrder
import IPRADerivations.Analysis.Stirling.GaussianStirlingGlobalBounds

/-!
# Finite observations of the negative thin chord

A common original observation clock gives the chord in differences from
the base. The finite error accounts for the actual addition and scaling
programs and has a numerator fixed before the clock is chosen.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogThinChordReadback

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalLogAbsolute (nameF nameData name_regular name_real)
open GaussianGammaNegativeIntervalLogStrongConvexity (scaledF)
open GaussianGammaNegativeIntervalLogThinChord (centerData lowerData weightedData margin center_regular strong_chord)
open GaussianNameRingLaws (three add_sample_error sum_left_error sum_right_error)
open GaussianNamedNaturalScaleOrder (common_upper cost sample_error)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianNaturalScaleProductName (productData)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical qadd)
open GaussianRationalInverseQuadraticAlgebra (subtract_sum)
open GaussianRationalMetric (distanceBounded qnegative qsub)
open GaussianRationalNaturalScale (natScale natScale_add natScale_as_product natScale_congr natScale_one_canonical)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianReciprocalHorner (qadd_commutative qsub_add_cancel)
open GaussianStirlingGlobalBounds (small_join)
open GaussianStirlingTailComparison (point_add_upper_same point_order_refl)
open RationalValueBounds (upper upper_congr upper_of_order upper_of_radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "G" => nameF

def budget (a c b N W : PTm n) : PTm n :=
  cost G W (centerData a c b N W)+cost G (pred W) (nameData a b N)+num 8

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (a c b N W : PTm n) :
    Syn.subst σ (budget a c b N W) =
      budget (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ N) (Syn.subst σ W) := by
  simp [budget]

private theorem scale_subtract (W x y : PTm n) :
    Γ ⊢[PRAAx] qsub (natScale W x) (natScale W y) ≐ natScale W (qsub x y) :=
  (qsub_congr (natScale_as_product W x) (natScale_as_product W y)).eqTrans
    ((GaussianRationalRoundedPower.multiplication_difference _ _ _).eqTrans (natScale_as_product W _).eqSymm)

private theorem cancel_scaled_base (W x y : PTm n) (hx : Γ ⊢[PRAAx] canonical x)
    (hy : Γ ⊢[PRAAx] canonical y) (hW : Γ ⊢[PRAAx] le two W) : Γ ⊢[PRAAx]
    qsub (qadd (natScale (pred W) x) y) (natScale W x) ≐ qsub y x := by
  let X := natScale (pred W) x
  have ep := natEq (GaussianOffDominantWeights.positive_succ_pred W (le_trans RationalAlgebra.two_positive hW))
  have ew : Γ ⊢[PRAAx] W ≐ pred W+one := by
    apply deriveNat
    ipra_simps
    linear_combination ep
  have split := (natScale_congr ew (.eqRefl x)).eqTrans
    ((natScale_add (pred W) one x).eqTrans (qadd_congr (.eqRefl X) (natScale_one_canonical x hx)))
  exact (qsub_congr (qadd_commutative X y) split).eqTrans
    ((subtract_sum (qadd y X) X x).eqSymm.eqTrans (qsub_congr (qsub_add_cancel y X hy) (.eqRefl x)))

private theorem translate_chord (m W X Y Z A P : PTm n)
    (hW : Γ ⊢[PRAAx] le two W) (hP : Γ ⊢[PRAAx] le one P)
    (hx : Γ ⊢[PRAAx] canonical X) (hy : Γ ⊢[PRAAx] canonical Y)
    (h : Γ ⊢[PRAAx] upper (fstT (qadd m (natScale W Z)))
      (fstT (qadd (natScale (pred W) X) Y)) A P) :
    Γ ⊢[PRAAx] upper (fstT (qadd m (natScale W (qsub Z X)))) (fstT (qsub Y X)) A P := by
  let v := natScale W X
  have sub : Γ ⊢[PRAAx] upper (fstT (qnegative v)) (fstT (qnegative v)) zero P :=
    upper_of_order _ _ _ _ (point_order_refl _)
  have together := point_add_upper_same _ _ _ _ _ _ _ hP h sub
  have left : Γ ⊢[PRAAx] qsub (qadd m (natScale W Z)) v ≐ qadd m (natScale W (qsub Z X)) :=
    (qadd_associative m (natScale W Z) (qnegative v)).eqTrans (qadd_congr (.eqRefl _) (scale_subtract W Z X))
  exact upper_congr (congrFst left) (congrFst (cancel_scaled_base W X Y hx hy hW))
    (LeanProofs.IPRA.add_zero A) (.eqRefl _) together

theorem difference_at (p a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] upper
      (fstT (qadd (margin a c b) (natScale W (qsub (ap2 G p (centerData a c b N W)) (ap2 G p (nameData a b N))))))
      (fstT (qsub (ap2 G p (nameData c b N)) (ap2 G p (nameData a b N)))) (budget a c b N W) (unit p) := by
  let m := margin a c b
  let x := nameData a b N
  let y := nameData c b N
  let z := centerData a c b N W
  let P := unit p
  let leftRaw := qadd m (natScale W (ap2 G p z))
  let rightRaw := qadd (natScale (pred W) (ap2 G p x)) (ap2 G p y)
  let left := ap2 (GaussianNameArithmetic.addF C scaledF) p (lowerData a c b N W)
  let right := ap2 (GaussianNameArithmetic.addF scaledF G) p (weightedData a c b N W)
  have hP := unit_positive (Γ := Γ) p
  have hx := name_regular a b N ha
  have hy := name_regular c b N hc
  have hz := center_regular a c b N W ha hc hW
  have leftAdd : Γ ⊢[PRAAx] distanceBounded left (qadd m (ap2 scaledF p (productData G W z))) three P :=
    distance_congr (.eqRefl _) (qadd_congr (constant_at p m) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
      (add_sample_error C scaledF m (productData G W z) p (constant_regular m) (GaussianNamedNaturalScaleOrder.regular G W z hz))
  have rightAdd : Γ ⊢[PRAAx] distanceBounded right (qadd (ap2 scaledF p (productData G (pred W) x)) (ap2 G p y)) three P :=
    add_sample_error scaledF G (productData G (pred W) x) y p (GaussianNamedNaturalScaleOrder.regular G (pred W) x hx) hy
  have leftErr : Γ ⊢[PRAAx] distanceBounded left leftRaw (three+cost G W z) P :=
    distance_triangle_same _ _ _ _ _ _ hP leftAdd (sum_right_error m _ _ _ _ hP (sample_error G W z p hz))
  have rightErr : Γ ⊢[PRAAx] distanceBounded right rightRaw (three+cost G (pred W) x) P :=
    distance_triangle_same _ _ _ _ _ _ hP rightAdd (sum_left_error _ _ _ _ _ hP (sample_error G (pred W) x p hx))
  have before := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hP (distance_symmetric _ _ _ _ hP leftErr))
  have after := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hP rightErr)
  have middle := common_upper _ _ _ _ p (strong_chord a c b N W ha hc hW)
  have together : Γ ⊢[PRAAx] upper (fstT leftRaw) (fstT rightRaw) (budget a c b N W) P :=
    upper_congr (.eqRefl _) (.eqRefl _) (by unfold budget three; ipra_ring) (.eqRefl _)
      (small_join _ _ _ _ _ p (small_join _ _ _ _ _ p before middle) after)
  have canX := (GaussianSignedNameExponentialOrder.real_sample_at G x p (name_real (Γ := Γ) a b N)).andE₁
  have canY := (GaussianSignedNameExponentialOrder.real_sample_at G y p (name_real (Γ := Γ) c b N)).andE₁
  exact translate_chord _ _ _ _ _ _ _ hW hP canX canY together

theorem actual_negative_interval_log_absolute_thin_chord_difference_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((guard (var 1) (var 3) ⋏ (guard (var 2) (var 3) ⋏ le two (var 5))) ⟶
        upper
          (fstT (qadd (margin (var 1) (var 2) (var 3)) (natScale (var 5)
            (qsub (ap2 G (var 0) (centerData (var 1) (var 2) (var 3) (var 4) (var 5)))
              (ap2 G (var 0) (nameData (var 1) (var 3) (var 4)))))))
          (fstT (qsub (ap2 G (var 0) (nameData (var 2) (var 3) (var 4)))
            (ap2 G (var 0) (nameData (var 1) (var 3) (var 4)))))
          (budget (var 1) (var 2) (var 3) (var 4) (var 5)) (unit (var 0))) :=
  closeUniv 6 (.impI (difference_at _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogThinChordReadback
