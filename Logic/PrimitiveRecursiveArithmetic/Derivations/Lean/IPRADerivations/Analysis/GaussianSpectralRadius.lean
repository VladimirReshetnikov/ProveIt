import IPRADerivations.Analysis.GaussianCharacteristicAggregate

/-!
# The spectral-radius name for original regular matrix data

The actual supremum program reads the finite characteristic root lists.
Each radius sample is the maximum lower modulus sample of an actual
stored root. The source optimization bound gives a regular value name
and arbitrarily accurate witnesses. Every represented root satisfies the
named upper bound, using its actual finite hits in the same aggregate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSpectralRadius

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCharacteristicRootSupport (data roots)
open GaussianCharacteristicAggregate
  (stageF pointF point_at sample_length sample_entry sample_nonempty stage_regular vector_point_regular member_support)
open GaussianModulusAggregateMap (vector point evaluatorF evaluator_at map_contract)
open AggregateEquality (sample unit)
open AggregateOptimization
  (evaluate negateEvaluator negate_evaluator_at minimumIndex minimumValue minimumPoint
    minimum_index_range minimum_value_le supremumName supremumWitnessValue pointValue)
open RationalValueBounds
  (radius upper negate negate_congr negate_neg negate_pos upper_congr upper_of_order upper_negate upper_unnegate_left)
open RationalSupMetric (denominatorOf)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def witnessShift : PTm n := num 4
def radiusName (a : PR 4) (N k x : PTm n) : PTm n :=
  supremumName (stageF a) evaluatorF k two (data N x)
def radiusF (a : PR 4) : PR 3 := PTm.toPR (radiusName a (var 0) (var 1) (var 2))
def maximizingIndex (a : PR 4) (N k x : PTm n) : PTm n :=
  minimumIndex (stageF a) (negateEvaluator evaluatorF) (k+two) (data N x)
def modulusSample (z s : PTm n) : PTm n := GaussianRationalModulus.lower (point (vector z)) s

@[simp] theorem subst_radiusName {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N k x : PTm n) :
    Syn.subst σ (radiusName a N k x) = radiusName a (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ x) := by
  simp [radiusName]

@[simp] theorem subst_maximizingIndex {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N k x : PTm n) :
    Syn.subst σ (maximizingIndex a N k x) = maximizingIndex a (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ x) := by
  simp [maximizingIndex]

@[simp] theorem subst_modulusSample {l : ℕ} (σ : Fin n → PTm l) (z s : PTm n) :
    Syn.subst σ (modulusSample z s) = modulusSample (Syn.subst σ z) (Syn.subst σ s) := by
  simp [modulusSample]

theorem radius_at (a : PR 4) (N k x : PTm n) : Γ ⊢[PRAAx] ap3 (radiusF a) N k x ≐ radiusName a N k x := by
  simpa [radiusF,ap3] using toPR_eq (Γ := Γ) (radiusName a (var 0) (var 1) (var 2) : PTm 3) ![N,k,x]

private theorem unit_two : Γ ⊢[PRAAx] (unit two : PTm n) ≐ num 4 :=
  (pw_succ two one).eqTrans ((congrMul (pw_one two) (.eqRefl _)).eqTrans (by ipra_ring))

theorem value_budget : Γ ⊢[PRAAx] le (two+one : PTm n) (one*unit two) :=
  le_congr (.eqRefl _) ((congrMul (.eqRefl one) unit_two).eqTrans (one_mul _)).eqSymm
    (le_of_eq_add (d := one) (by ipra_ring))

theorem witness_budget : Γ ⊢[PRAAx] le (num 4*two+two*one : PTm n) (one*unit witnessShift) := by
  have four : Γ ⊢[PRAAx] unit witnessShift ≐ num 16 :=
    (congrAp2 powF (by unfold witnessShift; ipra_ring : Γ ⊢[PRAAx] witnessShift ≐ two+two) (.eqRefl two)).eqTrans
      ((pw_add two two two).eqTrans ((congrMul unit_two unit_two).eqTrans (by ipra_ring)))
  exact le_congr (.eqRefl _) ((congrMul (.eqRefl one) four).eqTrans (one_mul _)).eqSymm
    (le_of_eq_add (d := num 6) (by ipra_ring))

private theorem double_negate (v : PTm n) (h : Γ ⊢[PRAAx] RationalNormalForm.wellFormed v) :
    Γ ⊢[PRAAx] negate (negate v) ≐ v := by
  have tail : Γ ⊢[PRAAx] sndT (negate v) ≐ LeanProofs.IPRA.PTm.pred (denominatorOf v) :=
    (snd_pair _ _).eqTrans (pred_succ _).eqSymm
  exact (congrPairT (congrPairT (negate_neg v) (negate_pos v)) tail).eqTrans (Prf.andE₁ h).eqSymm

theorem list_evaluator (a : PR 4) (N t x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    evaluate evaluatorF (entry (sample (stageF a) t (data N x)) i) t (data N x) ≐
      modulusSample (entry (roots a N t x) i) t := by
  exact (congrAp3 evaluatorF (sample_entry a N t x i hi) (.eqRefl _) (.eqRefl _)).eqTrans (evaluator_at _ _ _)

theorem maximizing_index_range (a : PR 4) (N k x : PTm n) (hn : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] lt (maximizingIndex a N k x) N :=
  lt_congr (.eqRefl _) (sample_length a N (k+two) x)
    (minimum_index_range (stageF a) (negateEvaluator evaluatorF) _ _ (sample_nonempty a N x hn))

theorem actual_max_sample (a : PR 4) (N k x : PTm n) (hn : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] radiusName a N k x ≐ modulusSample (entry (roots a N (k+two) x) (maximizingIndex a N k x)) (k+two) := by
  let t := k+two
  let i := maximizingIndex a N k x
  let Q := minimumPoint (stageF a) (negateEvaluator evaluatorF) t (data N x)
  let m := modulusSample (entry (roots a N t x) i) t
  have expected := list_evaluator a N t x i (maximizing_index_range a N k x hn)
  have h : Γ ⊢[PRAAx] evaluate (negateEvaluator evaluatorF) Q t (data N x) ≐ negate m :=
    (negate_evaluator_at evaluatorF Q t (data N x)).eqTrans (negate_congr expected)
  exact (negate_congr h).eqTrans (double_negate m (GaussianRationalModulus.lower_canonical _ _))

theorem stage_is_maximum (a : PR 4) (N k x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] upper (modulusSample (entry (roots a N (k+two) x) i) (k+two)) (radiusName a N k x) zero one := by
  let s := k+two
  let Q := entry (sample (stageF a) s (data N x)) i
  let v := modulusSample (entry (roots a N s x) i) s
  let M := minimumValue (stageF a) (negateEvaluator evaluatorF) s (data N x)
  have hv : Γ ⊢[PRAAx] evaluate (negateEvaluator evaluatorF) Q s (data N x) ≐ negate v :=
    (negate_evaluator_at evaluatorF Q s (data N x)).eqTrans (negate_congr (list_evaluator a N s x i hi))
  have earlier := minimum_value_le (stageF a) (negateEvaluator evaluatorF) s i (data N x)
    (lt_congr (.eqRefl _) (sample_length a N s x).eqSymm hi)
  have lower : Γ ⊢[PRAAx] upper M (negate v) zero one :=
    upper_congr (.eqRefl _) hv (.eqRefl _) (.eqRefl _) (upper_of_order _ _ _ _ earlier)
  exact upper_unnegate_left _ _ _ _ (upper_negate _ _ _ _ lower)

theorem regular_radius (a : PR 4) (N k l x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) :
    Γ ⊢[PRAAx] radius (radiusName a N k x) (radiusName a N l x) (unit k+unit l) (unit k*unit l) :=
  AggregateOptimization.supremum_name_regular _ _ _ _ _ _ _ _ _ (le_refl one) value_budget
    (sample_nonempty a N x hn) (stage_regular a N x hn hc) (map_contract _)

theorem approximate_maximum (a : PR 4) (N k t l x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    upper (radiusName a N l x) (supremumWitnessValue (stageF a) evaluatorF k t witnessShift two two (data N x))
      (unit t*unit l+unit k*unit l+unit k*unit t) (unit k*unit t*unit l) :=
  AggregateOptimization.supremum_witness_approximate _ _ _ _ _ _ _ _ _ _ _
    (le_refl one) witness_budget value_budget (sample_nonempty a N x hn) (stage_regular a N x hn hc) (map_contract _)

theorem represented_root_upper (a : PR 4) (p : PR 2) (N t l x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hp : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN p (data N x))
    (hm : Γ ⊢[PRAAx] GaussianMonicRootAdequacy.member (GaussianCharacteristicNames.coefficientF a) p N (data N x)) :
    Γ ⊢[PRAAx] upper (modulusSample (ap2 p (t+two) (data N x)) (t+two)) (radiusName a N l x)
      (unit t+unit l) (unit t*unit l) := by
  have exactBound := AggregateOptimization.support_supremum_exact (pointF p) (stageF a) evaluatorF
    t l two two two one (data N x) (le_refl one) value_budget (sample_nonempty a N x hn)
    (stage_regular a N x hn hc) (map_contract _) (vector_point_regular p _ hp) (member_support a p N x hn hc hp hm)
  have exactValue : Γ ⊢[PRAAx] pointValue (pointF p) evaluatorF t two (data N x) ≐ modulusSample (ap2 p (t+two) (data N x)) (t+two) :=
    (congrAp3 evaluatorF (point_at p (t+two) (data N x)) (.eqRefl _) (.eqRefl _)).eqTrans (evaluator_at _ _ _)
  exact upper_congr exactValue (.eqRefl _) (.eqRefl _) (.eqRefl _) exactBound

theorem represented_zero_upper (a : PR 4) (p : PR 2) (N Z t l x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hR : Γ ⊢[PRAAx] le (GaussianCharacteristicRootSupport.radius a N x) Z)
    (hp : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN p (data N x))
    (hDisk : Γ ⊢[PRAAx] GaussianRepresentedPointBounds.normLE p Z (data N x))
    (hz : Γ ⊢[PRAAx] GaussianMonicRootAdequacy.polynomialZero (GaussianCharacteristicNames.coefficientF a) p N Z (data N x)) :
    Γ ⊢[PRAAx] upper (modulusSample (ap2 p (t+two) (data N x)) (t+two)) (radiusName a N l x)
      (unit t+unit l) (unit t*unit l) := by
  have input : Γ ⊢[PRAAx] GaussianMonicRootAdequacy.input (GaussianCharacteristicNames.coefficientF a) p N Z (data N x) :=
    .andI (GaussianCharacteristicRootSupport.coefficient_name a N x hc) (.andI hn (.andI hR (.andI hp hDisk)))
  exact represented_root_upper a p N t l x hn hc hp
    ((GaussianMonicRootAdequacy.member_iff_polynomial_zero _ _ _ _ _ input).iffMpr hz)

theorem actual_spectral_radius_program_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 (radiusF a) (var 0) (var 1) (var 2) ≐ radiusName a (var 0) (var 1) (var 2)) :=
  closeUniv 3 (radius_at a _ _ _)

theorem actual_spectral_radius_regular_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 3) ⟶
      radius (radiusName a (var 0) (var 1) (var 3)) (radiusName a (var 0) (var 2) (var 3))
        (unit (var 1)+unit (var 2)) (unit (var 1)*unit (var 2))) :=
  closeUniv 4 (.impI (.impI (regular_radius a _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_spectral_stage_maximum_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 0) ⟶ upper (modulusSample (entry (roots a (var 0) (var 1+two) (var 2)) (var 3)) (var 1+two))
      (radiusName a (var 0) (var 1) (var 2)) zero one) :=
  closeUniv 4 (.impI (stage_is_maximum a _ _ _ _ Prf.hyp0))

theorem actual_spectral_sample_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ (lt (maximizingIndex a (var 0) (var 1) (var 2)) (var 0) ⋏
      radiusName a (var 0) (var 1) (var 2) ≐ modulusSample
        (entry (roots a (var 0) (var 1+two) (var 2)) (maximizingIndex a (var 0) (var 1) (var 2))) (var 1+two))) :=
  closeUniv 3 (.impI (.andI (maximizing_index_range a _ _ _ Prf.hyp0) (actual_max_sample a _ _ _ Prf.hyp0)))

theorem actual_spectral_witness_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 4) ⟶
      upper (radiusName a (var 0) (var 3) (var 4))
        (supremumWitnessValue (stageF a) evaluatorF (var 1) (var 2) witnessShift two two (data (var 0) (var 4)))
        (unit (var 2)*unit (var 3)+unit (var 1)*unit (var 3)+unit (var 1)*unit (var 2))
        (unit (var 1)*unit (var 2)*unit (var 3))) :=
  closeUniv 5 (.impI (.impI (approximate_maximum a _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_spectral_root_upper_closed (a : PR 4) (p : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 3) ⟶ GaussianEuclideanDistanceName.pointCN p (data (var 0) (var 3)) ⟶
        GaussianMonicRootAdequacy.member (GaussianCharacteristicNames.coefficientF a) p (var 0) (data (var 0) (var 3)) ⟶
        upper (modulusSample (ap2 p (var 1+two) (data (var 0) (var 3))) (var 1+two))
          (radiusName a (var 0) (var 2) (var 3)) (unit (var 1)+unit (var 2)) (unit (var 1)*unit (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI
    (represented_root_upper a p _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_spectral_polynomial_zero_upper_closed (a : PR 4) (p : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 4) ⟶
        le (GaussianCharacteristicRootSupport.radius a (var 0) (var 4)) (var 1) ⟶
        GaussianEuclideanDistanceName.pointCN p (data (var 0) (var 4)) ⟶
        GaussianRepresentedPointBounds.normLE p (var 1) (data (var 0) (var 4)) ⟶
        GaussianMonicRootAdequacy.polynomialZero (GaussianCharacteristicNames.coefficientF a)
          p (var 0) (var 1) (data (var 0) (var 4)) ⟶
        upper (modulusSample (ap2 p (var 2+two) (data (var 0) (var 4))) (var 2+two))
          (radiusName a (var 0) (var 3) (var 4)) (unit (var 2)+unit (var 3)) (unit (var 2)*unit (var 3))) := by
  refine closeUniv 5 (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact represented_zero_upper a p _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianSpectralRadius
