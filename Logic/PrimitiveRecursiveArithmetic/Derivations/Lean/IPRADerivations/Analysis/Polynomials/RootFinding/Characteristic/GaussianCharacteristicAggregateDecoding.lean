import IPRADerivations.Analysis.Polynomials.RootFinding.Characteristic.GaussianCharacteristicAggregate

/-!
# Decoding supported characteristic aggregate points

An arbitrary regular two-coordinate point stream is decoded one precision
later into the original Gaussian point representation. Its sup-coordinate
modulus then gives the original Euclidean point modulus. Vanishing distance
to the actual characteristic array yields actual Gaussian root hits and
hence the original represented-root membership, with explicit stage shifts.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCharacteristicAggregateDecoding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCharacteristicRootSupport (data roots roots_length)
open GaussianCharacteristicAggregate (stageF sample_length sample_entry sample_nonempty stage_regular)
open GaussianModulusAggregateMap (point vector)
open AggregateEquality (sample unit unit_positive)
open AggregateOptimization (pointRegular supportZero)
open GaussianEuclideanDistanceName (pointCN distanceLE)
open GaussianRationalMetric (distanceBounded qsub qsub_represents)
open GaussianRationalHorner (positive_product represents canonical_unique)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalSyntheticDivision (rescale_to)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def decoded (U : PR 2) (s d : PTm n) : PTm n := point (sample U (s+one) d)
def decodedF (U : PR 2) : PR 2 := PTm.toPR (decoded U (var 0) (var 1))

@[simp] theorem subst_decoded {l : ℕ} (σ : Fin n → PTm l) (U : PR 2) (s d : PTm n) :
    Syn.subst σ (decoded U s d) = decoded U (Syn.subst σ s) (Syn.subst σ d) := by
  simp [decoded]

theorem decoded_at (U : PR 2) (s d : PTm n) : Γ ⊢[PRAAx]
    ap2 (decodedF U) s d ≐ decoded U s d := by
  simpa [decodedF,ap2] using toPR_eq (Γ := Γ) (decoded U (var 0) (var 1) : PTm 2) ![s,d]

theorem decoded_real (U : PR 2) (s d : PTm n) : Γ ⊢[PRAAx]
    fstT (ap2 (decodedF U) s d) ≐ entry (sample U (s+one) d) zero :=
  (congrFst (decoded_at U s d)).eqTrans (fst_pair _ _)
theorem decoded_imag (U : PR 2) (s d : PTm n) : Γ ⊢[PRAAx]
    sndT (ap2 (decodedF U) s d) ≐ entry (sample U (s+one) d) one :=
  (congrSnd (decoded_at U s d)).eqTrans (snd_pair _ _)

/-- The normalized differences agree as actual codes; no raw outer eta is used. -/
theorem difference_point_vector (q z : PTm n) : Γ ⊢[PRAAx]
    qsub q (point (vector z)) ≐ qsub q z := by
  let E := rawDen q*rawDen z
  let a := ComplexLogarithmRemainder.scale (rawDen z) (rawGaussian q)
  let b := ComplexLogarithmRemainder.scale (rawDen q) (rawGaussian z)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (raw_den_positive q) (raw_den_positive z)
  have hq : Γ ⊢[PRAAx] represents q a E :=
    rescale_to q (rawGaussian q) (rawDen q) (rawDen z) E (raw_represents q) (.eqRefl _)
  have hz : Γ ⊢[PRAAx] represents z b E :=
    rescale_to z (rawGaussian z) (rawDen z) (rawDen q) E (raw_represents z) (by unfold E; ipra_ring)
  have hv : Γ ⊢[PRAAx] represents (point (vector z)) b E :=
    rescale_to (point (vector z)) (rawGaussian z) (rawDen z) (rawDen q) E
      (GaussianModulusAggregateMap.point_vector_represents z) (by unfold E; ipra_ring)
  exact canonical_unique _ _ _ E (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalMetric.qsub_canonical _ _) hE
    (qsub_represents _ _ a b E hE hq hv) (qsub_represents _ _ a b E hE hq hz)

theorem distance_point_vector (q z A B : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded q (point (vector z)) A B) :
    Γ ⊢[PRAAx] distanceBounded q z A B :=
  GaussianRationalReciprocal.bound_congr (difference_point_vector q z) (.eqRefl _) (.eqRefl _) h

theorem unit_double (s : PTm n) : Γ ⊢[PRAAx] unit (s+one) ≐ two*unit s := by
  simpa only [unit,GaussianCoefficientNameBounds.unit] using
    GaussianRootMembershipBudget.unit_add_one (Γ := Γ) s

theorem decoded_pair (U : PR 2) (d s t : PTm n)
    (h : Γ ⊢[PRAAx] pointRegular U two d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (decodedF U) s d) (ap2 (decodedF U) t d)
      (unit s+unit t) (unit s*unit t) := by
  have hp := AggregateOptimization.pointRegular_at U (s+one) (t+one) two d h
  have hb : Γ ⊢[PRAAx] le one (unit (s+one)*unit (t+one)) :=
    positive_product _ _ (unit_positive (s+one)) (unit_positive (t+one))
  have original : Γ ⊢[PRAAx] distanceBounded (decoded U s d) (decoded U t d)
      (two*(unit (s+one)+unit (t+one))) (unit (s+one)*unit (t+one)) :=
    GaussianModulusAggregateMap.coordinate_to_euclidean _ _ _ _ hb hp
  have eS := natEq (unit_double (Γ := Γ) s)
  have eT := natEq (unit_double (Γ := Γ) t)
  have budget : Γ ⊢[PRAAx] le
      ((two*(unit (s+one)+unit (t+one)))*(unit s*unit t))
      ((unit s+unit t)*(unit (s+one)*unit (t+one))) := by
    apply le_of_eq_add (d := zero)
    apply deriveNat
    ipra_simps
    rw [eS,eT]
    ring
  exact GaussianRationalDistanceOrder.distance_congr (decoded_at U s d).eqSymm (decoded_at U t d).eqSymm
    (.eqRefl _) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ hb
      (positive_product _ _ (unit_positive s) (unit_positive t)) budget original)

theorem decoded_point_cn (U : PR 2) (d : PTm n)
    (h : Γ ⊢[PRAAx] pointRegular U two d) : Γ ⊢[PRAAx] pointCN (decodedF U) d := by
  refine .allI (.allI ?_)
  let x := Syn.shift (Syn.shift d)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have h' : Δ ⊢[PRAAx] pointRegular U two x := by
    simpa [Δ,x,Fm.shift,Syn.shift,two,one] using h.shift.shift
  simpa [Δ,x,Syn.shift,one,two,GaussianEuclideanPointDistance.unit,unit] using
    decoded_pair U x (var 1) (var 0) h'

def hitNumerator (t : PTm n) : PTm n := two*(unit (t+one)+unit t)
def hitDenominator (t : PTm n) : PTm n := unit (t+one)*unit t
def memberStage (k : PTm n) : PTm n := k+two

@[simp] theorem subst_hitNumerator {l : ℕ} (σ : Fin n → PTm l) (t : PTm n) :
    Syn.subst σ (hitNumerator t) = hitNumerator (Syn.subst σ t) := by simp [hitNumerator]
@[simp] theorem subst_hitDenominator {l : ℕ} (σ : Fin n → PTm l) (t : PTm n) :
    Syn.subst σ (hitDenominator t) = hitDenominator (Syn.subst σ t) := by simp [hitDenominator]
@[simp] theorem subst_memberStage {l : ℕ} (σ : Fin n → PTm l) (k : PTm n) :
    Syn.subst σ (memberStage k) = memberStage (Syn.subst σ k) := by simp [memberStage]

theorem hit_denominator_positive (t : PTm n) : Γ ⊢[PRAAx] le one (hitDenominator t) :=
  positive_product _ _ (unit_positive (t+one)) (unit_positive t)

theorem supported_hit (a : PR 4) (U : PR 2) (N x t : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hU : Γ ⊢[PRAAx] pointRegular U two (data N x))
    (hs : Γ ⊢[PRAAx] supportZero U (stageF a) two (data N x)) : Γ ⊢[PRAAx]
    GaussianRationalCover.hit (ap2 (decodedF U) t (data N x)) (roots a N t x)
      (hitNumerator t) (hitDenominator t) := by
  let v := sample U (t+one) (data N x)
  let T := sample (stageF a) t (data N x)
  let j := RationalPointDistance.selected v T two
  have hT : Γ ⊢[PRAAx] le one (length T) := le_congr (.eqRefl _) (sample_length a N t x).eqSymm hn
  have hj : Γ ⊢[PRAAx] lt j N :=
    lt_congr (.eqRefl _) (sample_length a N t x) (RationalPointDistance.selected_spec v T two hT)
  have close : Γ ⊢[PRAAx] RationalHausdorff.pointRadius v (entry T j) two
      (unit (t+one)+unit t) (hitDenominator t) :=
    AggregateOptimization.support_nearby U (stageF a) (t+one) t two (data N x)
      (sample_nonempty a N x hn) (stage_regular a N x hn hc) hU hs
  have stored : Γ ⊢[PRAAx] RationalHausdorff.pointRadius v (vector (entry (roots a N t x) j)) two
      (unit (t+one)+unit t) (hitDenominator t) :=
    GaussianAggregateCoverTransport.point_radius_congr _ _ (.eqRefl _) (sample_entry a N t x j hj) close
  have euclidean : Γ ⊢[PRAAx] distanceBounded (decoded U t (data N x))
      (point (vector (entry (roots a N t x) j))) (hitNumerator t) (hitDenominator t) :=
    GaussianModulusAggregateMap.coordinate_to_euclidean _ _ _ _ (hit_denominator_positive t) stored
  have original : Γ ⊢[PRAAx] distanceBounded (ap2 (decodedF U) t (data N x))
      (entry (roots a N t x) j) (hitNumerator t) (hitDenominator t) :=
    GaussianRationalDistanceOrder.distance_congr (decoded_at U t (data N x)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (distance_point_vector _ _ _ _ euclidean)
  exact GaussianRationalCover.hit_intro _ _ _ _ j
    (lt_congr (.eqRefl _) (roots_length a N t x).eqSymm hj) original

theorem member_stage_value (k : PTm n) : Γ ⊢[PRAAx] unit (memberStage k) ≐ two*(two*unit k) := by
  have time : Γ ⊢[PRAAx] memberStage k ≐ (k+one)+one := by unfold memberStage; ipra_ring
  exact (congrAp2 powF time (.eqRefl _)).eqTrans
    ((GaussianRootMembershipBudget.unit_add_one (k+one)).eqTrans
      (congrMul (.eqRefl _) (GaussianRootMembershipBudget.unit_add_one k)))

theorem member_cut_budget (k : PTm n) : Γ ⊢[PRAAx] le
    ((hitNumerator (memberStage k)*unit (memberStage k)+hitDenominator (memberStage k))*unit k)
    (one*(hitDenominator (memberStage k)*unit (memberStage k))) := by
  have h := natEq (member_stage_value (Γ := Γ) k)
  have h' := natEq (unit_double (Γ := Γ) (memberStage k))
  apply le_of_eq_add (d := zero)
  apply deriveNat
  simp only [hitNumerator,hitDenominator]
  ipra_simps
  rw [h',h]
  ring

theorem support_to_stage (a : PR 4) (U : PR 2) (N x k : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hU : Γ ⊢[PRAAx] pointRegular U two (data N x))
    (hs : Γ ⊢[PRAAx] supportZero U (stageF a) two (data N x)) : Γ ⊢[PRAAx]
    GaussianRootMembership.stageCondition GaussianMonicRD.step (GaussianCharacteristicNames.coefficientF a)
      (decodedF U) N (data N x) k (memberStage k) := by
  refine .andI (le_add_right k two) ?_
  exact GaussianEuclideanDistanceName.finite_hit_to_cut (decodedF U) (roots a N (memberStage k) x)
    (data N x) (memberStage k) (hitNumerator (memberStage k)) (hitDenominator (memberStage k)) one (unit k)
    (decoded_point_cn U (data N x) hU) (hit_denominator_positive _) (unit_positive k)
    (supported_hit a U N x (memberStage k) hn hc hU hs) (member_cut_budget k)

theorem support_decoded_member (a : PR 4) (U : PR 2) (N x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hU : Γ ⊢[PRAAx] pointRegular U two (data N x))
    (hs : Γ ⊢[PRAAx] supportZero U (stageF a) two (data N x)) : Γ ⊢[PRAAx]
    GaussianMonicRootAdequacy.member (GaussianCharacteristicNames.coefficientF a) (decodedF U) N (data N x) := by
  refine .allI ?_
  let M := Syn.shift N
  let y := Syn.shift x
  let Δ := Γ.map Fm.shift
  have n' : Δ ⊢[PRAAx] le one M := by simpa [Δ,M,Fm.shift,Syn.shift,one] using hn.shift
  have c' : Δ ⊢[PRAAx] GaussianMatrixNames.CN a M y := by simpa [Δ,M,y,Fm.shift,Syn.shift] using hc.shift
  have u' : Δ ⊢[PRAAx] pointRegular U two (data M y) := by simpa [Δ,M,y,Fm.shift,Syn.shift,one,two] using hU.shift
  have s' : Δ ⊢[PRAAx] supportZero U (stageF a) two (data M y) := by simpa [Δ,M,y,Fm.shift,Syn.shift,one,two] using hs.shift
  have stage : Δ ⊢[PRAAx] GaussianRootMembership.stageCondition GaussianMonicRD.step
      (GaussianCharacteristicNames.coefficientF a) (decodedF U) M (data M y) (var 0) (memberStage (var 0)) :=
    support_to_stage a U M y (var 0) n' c' u' s'
  have result : Δ ⊢[PRAAx] GaussianRootMembership.atPrecision GaussianMonicRD.step
      (GaussianCharacteristicNames.coefficientF a) (decodedF U) M (data M y) (var 0) :=
    GaussianRootMembership.precision_intro GaussianMonicRD.step (GaussianCharacteristicNames.coefficientF a)
      (decodedF U) M (data M y) (var 0) (memberStage (var 0)) stage
  simpa [Δ,M,y,Syn.shift] using result

/-- The original modulus evaluator reads exactly the decoded observation.
The root and modulus sampling precisions remain separate numerical inputs. -/
theorem decoded_modulus (U : PR 2) (s d p : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalModulus.lower (ap2 (decodedF U) s d) p ≐
      AggregateOptimization.evaluate GaussianModulusAggregateMap.evaluatorF (sample U (s+one) d) p d := by
  have sampled : Γ ⊢[PRAAx] GaussianRationalModulus.lower (ap2 (decodedF U) s d) p ≐
      GaussianRationalModulus.lower (decoded U s d) p :=
    (GaussianRationalModulus.sample_at _ _).eqSymm.eqTrans
      ((congrAp2 GaussianRationalModulus.sampleF (decoded_at U s d) (.eqRefl _)).eqTrans
        (GaussianRationalModulus.sample_at _ _))
  exact sampled.eqTrans (GaussianModulusAggregateMap.evaluator_at _ _ _).eqSymm

theorem returned_certificate (a : PR 4) (U : PR 2) (N x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hU : Γ ⊢[PRAAx] pointRegular U two (data N x))
    (hs : Γ ⊢[PRAAx] supportZero U (stageF a) two (data N x)) : Γ ⊢[PRAAx]
    pointCN (decodedF U) (data N x) ⋏
      GaussianMonicRootAdequacy.member (GaussianCharacteristicNames.coefficientF a) (decodedF U) N (data N x) :=
  .andI (decoded_point_cn U (data N x) hU) (support_decoded_member a U N x hn hc hU hs)

theorem actual_decoded_program_closed (U : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (decodedF U) (var 0) (var 1) ≐ point (sample U (var 0+one) (var 1))) :=
  closeUniv 2 (decoded_at U _ _)

theorem actual_decoded_coordinates_closed (U : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((fstT (ap2 (decodedF U) (var 0) (var 1)) ≐ entry (sample U (var 0+one) (var 1)) zero) ⋏
      sndT (ap2 (decodedF U) (var 0) (var 1)) ≐ entry (sample U (var 0+one) (var 1)) one) :=
  closeUniv 2 (.andI (decoded_real U _ _) (decoded_imag U _ _))

theorem actual_vector_distance_decode_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (distanceBounded (var 0) (point (vector (var 1))) (var 2) (var 3) ⟶
      distanceBounded (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (distance_point_vector _ _ _ _ Prf.hyp0))

theorem actual_decoded_point_name_closed (U : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointRegular U two (var 0) ⟶ pointCN (decodedF U) (var 0)) :=
  closeUniv 1 (.impI (decoded_point_cn U _ Prf.hyp0))

theorem actual_supported_gaussian_hit_closed (a : PR 4) (U : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 1) ⟶
        pointRegular U two (data (var 0) (var 1)) ⟶ supportZero U (stageF a) two (data (var 0) (var 1)) ⟶
          GaussianRationalCover.hit (ap2 (decodedF U) (var 2) (data (var 0) (var 1)))
            (roots a (var 0) (var 2) (var 1)) (hitNumerator (var 2)) (hitDenominator (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI
    (supported_hit a U _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_decoded_member_stage_closed (a : PR 4) (U : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 1) ⟶
        pointRegular U two (data (var 0) (var 1)) ⟶ supportZero U (stageF a) two (data (var 0) (var 1)) ⟶
          GaussianRootMembership.stageCondition GaussianMonicRD.step (GaussianCharacteristicNames.coefficientF a)
            (decodedF U) (var 0) (data (var 0) (var 1)) (var 2) (memberStage (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI
    (support_to_stage a U _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_decoded_characteristic_member_closed (a : PR 4) (U : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 1) ⟶
        pointRegular U two (data (var 0) (var 1)) ⟶ supportZero U (stageF a) two (data (var 0) (var 1)) ⟶
          (pointCN (decodedF U) (data (var 0) (var 1)) ⋏
            GaussianMonicRootAdequacy.member (GaussianCharacteristicNames.coefficientF a)
              (decodedF U) (var 0) (data (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.impI (.impI (.impI
    (returned_certificate a U _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_decoded_modulus_observation_closed (U : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (GaussianRationalModulus.lower (ap2 (decodedF U) (var 0) (var 1)) (var 2) ≐
        AggregateOptimization.evaluate GaussianModulusAggregateMap.evaluatorF
          (sample U (var 0+one) (var 1)) (var 2) (var 1)) :=
  closeUniv 3 (decoded_modulus U _ _ _)

end LeanProofs.IPRA.Analysis.GaussianCharacteristicAggregateDecoding
