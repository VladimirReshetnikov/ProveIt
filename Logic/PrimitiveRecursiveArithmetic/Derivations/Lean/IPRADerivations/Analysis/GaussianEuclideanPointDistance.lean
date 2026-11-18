import IPRADerivations.Analysis.GaussianRationalDistanceOrder
import IPRADerivations.Analysis.GaussianRationalCover

/-!
# Actual Euclidean distance samples to a finite Gaussian-rational list

An actual rational argmin minimizes the original squared Euclidean distances.
The square-root sampler uses the proved integer square root at the requested
runtime precision. Its lower and upper squares bracket the actual minimum,
and original finite hits are related to the sampled distance with explicit
dyadic slack. This is the finite-distance dependency of source04 adequacy;
represented-point names and removal of their rational slack remain separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEuclideanPointDistance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qnormSq distanceBounded squaredTolerance)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalCover (hit hit_intro)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.FiniteHausdorff (index_le_pred index_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (z T : PTm n) : PTm n := pairT z T
def scoreBody : PTm 2 := qnormSq (qsub (fstT (var 1)) (entry (sndT (var 1)) (var 0)))
def scoreF : PR 2 := PTm.toPR scoreBody
def selected (z T : PTm n) : PTm n := RationalArgmin.selected scoreF (pred (length T)) (data z T)
def difference (z T : PTm n) : PTm n := qsub z (entry T (selected z T))
def squaredDistance (z T : PTm n) : PTm n := qnormSq (difference z T)
def numerator (z T : PTm n) : PTm n := ComplexLogarithmRemainder.normSq (rawGaussian (difference z T))
def denominator (z T : PTm n) : PTm n := rawDen (difference z T)
def unit (k : PTm n) : PTm n := pw two k
def radicand (z T k : PTm n) : PTm n := numerator z T*(unit k*unit k)
def root (z T k : PTm n) : PTm n := isqrt (radicand z T k)
def lower (z T k : PTm n) : PTm n := normalize (ZT.ofNat (root z T k)) (denominator z T*unit k)
def upper (z T k : PTm n) : PTm n := normalize (ZT.ofNat (succ (root z T k))) (denominator z T*unit k)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z T : PTm n) :
    Syn.subst σ (data z T) = data (Syn.subst σ z) (Syn.subst σ T) := by simp [data]
@[simp] theorem subst_selected {m : ℕ} (σ : Fin n → PTm m) (z T : PTm n) :
    Syn.subst σ (selected z T) = selected (Syn.subst σ z) (Syn.subst σ T) := by simp [selected]
@[simp] theorem subst_difference {m : ℕ} (σ : Fin n → PTm m) (z T : PTm n) :
    Syn.subst σ (difference z T) = difference (Syn.subst σ z) (Syn.subst σ T) := by simp [difference]
@[simp] theorem subst_squaredDistance {m : ℕ} (σ : Fin n → PTm m) (z T : PTm n) :
    Syn.subst σ (squaredDistance z T) = squaredDistance (Syn.subst σ z) (Syn.subst σ T) := by simp [squaredDistance]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (z T : PTm n) :
    Syn.subst σ (numerator z T) = numerator (Syn.subst σ z) (Syn.subst σ T) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (z T : PTm n) :
    Syn.subst σ (denominator z T) = denominator (Syn.subst σ z) (Syn.subst σ T) := by simp [denominator]
@[simp] theorem subst_unit {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (unit k) = unit (Syn.subst σ k) := by simp [unit]
@[simp] theorem subst_radicand {m : ℕ} (σ : Fin n → PTm m) (z T k : PTm n) :
    Syn.subst σ (radicand z T k) = radicand (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ k) := by simp [radicand]
@[simp] theorem subst_root {m : ℕ} (σ : Fin n → PTm m) (z T k : PTm n) :
    Syn.subst σ (root z T k) = root (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ k) := by simp [root]
@[simp] theorem subst_lower {m : ℕ} (σ : Fin n → PTm m) (z T k : PTm n) :
    Syn.subst σ (lower z T k) = lower (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ k) := by simp [lower]
@[simp] theorem subst_upper {m : ℕ} (σ : Fin n → PTm m) (z T k : PTm n) :
    Syn.subst σ (upper z T k) = upper (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ k) := by simp [upper]

theorem score_at (z T i : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.value scoreF i (data z T) ≐ qnormSq (qsub z (entry T i)) := by
  have reified := toPR_eq (Γ := Γ) scoreBody ![i,data z T]
  have operands := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (qnormSq (qsub (var 0) (entry (var 1) (var 2))) : PTm 3)
    (σ := ![fstT (data z T),sndT (data z T),i]) (σ' := ![z,T,i])
    (fun j => by fin_cases j; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  exact reified.eqTrans (by simpa [scoreBody,scoreF,GaussianRationalMetric.subst_qnormSq,
    GaussianRationalMetric.subst_qsub,subst_entry] using operands)

theorem selected_range (z T : PTm n) (hT : Γ ⊢[PRAAx] le one (length T)) : Γ ⊢[PRAAx]
    lt (selected z T) (length T) := index_lt hT (RationalArgmin.selected_spec _ _ _)

theorem minimum_le (z T i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length T)) : Γ ⊢[PRAAx]
    rationalLE (squaredDistance z T) (qnormSq (qsub z (entry T i))) :=
  RationalArgmin.rationalLE_congr (score_at z T (selected z T)) (score_at z T i)
    (RationalArgmin.selected_minimal scoreF (pred (length T)) i (data z T) (index_le_pred hi))

theorem minimum_of_hit (z T A B : PTm n) (h : Γ ⊢[PRAAx] hit z T A B) : Γ ⊢[PRAAx]
    rationalLE (squaredDistance z T) (squaredTolerance A B) := by
  refine .exE h ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (Syn.shift T)) ⋏
    distanceBounded (Syn.shift z) (entry (Syn.shift T) (var 0)) (Syn.shift A) (Syn.shift B)
  have result : E :: Γ.map Fm.shift ⊢[PRAAx] rationalLE (squaredDistance (Syn.shift z) (Syn.shift T))
      (squaredTolerance (Syn.shift A) (Syn.shift B)) :=
    RationalArgmin.transitive (minimum_le _ _ _ (Prf.andE₁ Prf.hyp0)) (Prf.andE₂ Prf.hyp0)
  simpa only [E,Fm.shift,RationalArgmin.subst_rationalLE,subst_squaredDistance,
    GaussianRationalMetric.subst_squaredTolerance,Syn.shift] using result

theorem hit_iff_minimum (z T A B : PTm n) (hT : Γ ⊢[PRAAx] le one (length T)) : Γ ⊢[PRAAx]
    Fm.iff (hit z T A B) (rationalLE (squaredDistance z T) (squaredTolerance A B)) :=
  .iffI (.impI (minimum_of_hit _ _ _ _ Prf.hyp0))
    (.impI (hit_intro _ _ _ _ (selected z T) (selected_range z T hT.wk) Prf.hyp0))

theorem denominator_positive (z T : PTm n) : Γ ⊢[PRAAx] le one (denominator z T) := raw_den_positive _
theorem unit_positive (k : PTm n) : Γ ⊢[PRAAx] le one (unit k) :=
  GaussianFactorBudget.power_positive _ _ (le_of_eq_add (d := one) (by ipra_ring))

theorem minimum_represents (z T : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (squaredDistance z T) (ZT.ofNat (numerator z T)) (denominator z T*denominator z T) :=
  GaussianRationalMetric.qnormSq_represents _ _ _ (denominator_positive z T) (raw_represents _)

theorem lower_represents (z T k : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (lower z T k) (ZT.ofNat (root z T k)) (denominator z T*unit k) :=
  normalize_preserves_value _ _ (positive_product _ _ (denominator_positive z T) (unit_positive k))
theorem upper_represents (z T k : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (upper z T k) (ZT.ofNat (succ (root z T k))) (denominator z T*unit k) :=
  normalize_preserves_value _ _ (positive_product _ _ (denominator_positive z T) (unit_positive k))

theorem root_lower (z T k : PTm n) : Γ ⊢[PRAAx] le (root z T k*root z T k) (numerator z T*(unit k*unit k)) :=
  isqrt_le _
theorem root_upper (z T k : PTm n) : Γ ⊢[PRAAx] lt (numerator z T*(unit k*unit k))
    (succ (root z T k)*succ (root z T k)) := by
  have h := lt_isqrt_succ_sq (Γ := Γ) (radicand z T k)
  change Γ ⊢[PRAAx] lt (numerator z T*(unit k*unit k)) ((root z T k+one)*(root z T k+one)) at h
  exact lt_congr (.eqRefl _) (by ipra_ring) h

/-- Genuine lower square-root approximation of the actual Euclidean minimum. -/
theorem lower_square (z T k : PTm n) : Γ ⊢[PRAAx]
    rationalLE (RationalArithmetic.multiply (lower z T k) (lower z T k)) (squaredDistance z T) := by
  have d := positive_product (Γ := Γ) _ _ (denominator_positive z T) (unit_positive k)
  have rep := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _ (lower_represents z T k) (lower_represents z T k)
  have natural : Γ ⊢[PRAAx] RationalArithmetic.represents
      (RationalArithmetic.multiply (lower z T k) (lower z T k))
      (ZT.ofNat (root z T k*root z T k))
      ((denominator z T*unit k)*(denominator z T*unit k)) := GaussianRationalHorner.scalar_congr (.eqRefl _) (by
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]) (.eqRefl _) rep
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (positive_product _ _ d d)
    (positive_product _ _ (denominator_positive z T) (denominator_positive z T)) natural (minimum_represents z T)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (denominator z T*denominator z T) (root_lower z T k)))

/-- Genuine upper square-root approximation of that same actual minimum. -/
theorem upper_square (z T k : PTm n) : Γ ⊢[PRAAx]
    rationalLE (squaredDistance z T) (RationalArithmetic.multiply (upper z T k) (upper z T k)) := by
  have d := positive_product (Γ := Γ) _ _ (denominator_positive z T) (unit_positive k)
  have rep := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _ (upper_represents z T k) (upper_represents z T k)
  have natural : Γ ⊢[PRAAx] RationalArithmetic.represents
      (RationalArithmetic.multiply (upper z T k) (upper z T k))
      (ZT.ofNat (succ (root z T k)*succ (root z T k)))
      ((denominator z T*unit k)*(denominator z T*unit k)) := GaussianRationalHorner.scalar_congr (.eqRefl _) (by
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]) (.eqRefl _) rep
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (positive_product _ _ (denominator_positive z T) (denominator_positive z T)) (positive_product _ _ d d)
    (minimum_represents z T) natural
    (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right (denominator z T*denominator z T) (le_of_lt (root_upper z T k))))

/-- An original Euclidean hit bounds the actual lower distance sample
without any loss in its original rational radius. -/
theorem hit_to_lower_bound (z T k A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] hit z T A B) : Γ ⊢[PRAAx]
    rationalLE (lower z T k) (normalize (ZT.ofNat A) B) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (minimum_represents (Γ := Γ) z T) (GaussianRationalMetric.squared_tolerance_represents A B hB)
    (minimum_of_hit z T A B h)
  have floor := mul_le_mul_right (B*B) (root_lower (Γ := Γ) z T k)
  have scaled := mul_le_mul_right (unit k*unit k) raw
  have square : Γ ⊢[PRAAx] le ((B*root z T k)*(B*root z T k))
      ((A*(denominator z T*unit k))*(A*(denominator z T*unit k))) :=
    le_trans (b := (B*B)*numerator z T*(unit k*unit k)) (le_congr (by ipra_ring) (by ipra_ring) floor)
      (le_congr (.eqRefl _) (by ipra_ring) scaled)
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (positive_product _ _ (denominator_positive z T) (unit_positive k)) hB
    (lower_represents z T k) (normalize_preserves_value _ _ hB) (nat_sqrt_mono square)

/-- A bound on the actual computed distance sample supplies an original
stored-point hit with only the stated dyadic square-root error 2^(-k). -/
theorem lower_bound_to_hit (z T k A B : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length T)) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] rationalLE (lower z T k) (normalize (ZT.ofNat A) B)) : Γ ⊢[PRAAx]
    hit z T (A*unit k+B) (B*unit k) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (lower_represents (Γ := Γ) z T k) (normalize_preserves_value _ _ hB) h
  have oneStep : Γ ⊢[PRAAx] le B (B*denominator z T) :=
    le_congr (one_mul B) (mul_comm _ _) (mul_le_mul_right B (denominator_positive z T))
  have step : Γ ⊢[PRAAx] le (B*succ (root z T k)) (denominator z T*(A*unit k+B)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ raw oneStep)
  have square := le_mul_mono step step
  have cap := mul_le_mul_right (B*B) (le_of_lt (root_upper (Γ := Γ) z T k))
  have first : Γ ⊢[PRAAx] le (((B*unit k)*(B*unit k))*numerator z T)
      ((B*succ (root z T k))*(B*succ (root z T k))) := le_congr (by ipra_ring) (by ipra_ring) cap
  have bound : Γ ⊢[PRAAx] distanceBounded z (entry T (selected z T)) (A*unit k+B) (B*unit k) :=
    GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (denominator_positive z T)
      (positive_product _ _ hB (unit_positive k)) (raw_represents _)
      (le_trans first (le_congr (.eqRefl _) (by ipra_ring) square))
  exact hit_intro _ _ _ _ (selected z T) (selected_range z T hT) bound

theorem lower_nonnegative (z T k : PTm n) : Γ ⊢[PRAAx]
    le (RationalSupMetric.numeratorOf (lower z T k)).neg (RationalSupMetric.numeratorOf (lower z T k)).pos :=
  GaussianRationalL1.nonnegative_of_representation _ _ _
    (positive_product _ _ (denominator_positive z T) (unit_positive k)) (lower_represents z T k)

theorem upper_nonnegative (z T k : PTm n) : Γ ⊢[PRAAx]
    le (RationalSupMetric.numeratorOf (upper z T k)).neg (RationalSupMetric.numeratorOf (upper z T k)).pos :=
  GaussianRationalL1.nonnegative_of_representation _ _ _
    (positive_product _ _ (denominator_positive z T) (unit_positive k)) (upper_represents z T k)

/-! The total program returns the original nearest index, its original
point, the actual squared minimum, and the two normalized distance samples. -/
def output (z T k : PTm n) : PTm n := pairT (selected z T)
  (pairT (entry T (selected z T)) (pairT (squaredDistance z T) (pairT (lower z T k) (upper z T k))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (z T k : PTm n) : PTm n := ap3 outputF z T k

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (z T k : PTm n) :
    Syn.subst σ (output z T k) = output (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ k) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (z T k : PTm n) :
    Syn.subst σ (run z T k) = run (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ k) := by simp [run]

theorem program_at (z T k : PTm n) : Γ ⊢[PRAAx] run z T k ≐ output z T k := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![z,T,k]

theorem returned_index (z T k : PTm n) : Γ ⊢[PRAAx] fstT (run z T k) ≐ selected z T :=
  (congrFst (program_at z T k)).eqTrans (fst_pair _ _)
theorem returned_point (z T k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run z T k)) ≐ entry T (fstT (run z T k)) :=
  ((congrFst ((congrSnd (program_at z T k)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)).eqTrans
    (entry_congr (.eqRefl _) (returned_index z T k).eqSymm)

theorem euclidean_minimum_hit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (length (var 1)) ⟶ Fm.iff (hit (var 0) (var 1) (var 2) (var 3))
      (rationalLE (squaredDistance (var 0) (var 1)) (squaredTolerance (var 2) (var 3)))) :=
  closeUniv 4 (.impI (hit_iff_minimum _ _ _ _ Prf.hyp0))

theorem euclidean_sqrt_brackets_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rationalLE (RationalArithmetic.multiply (lower (var 0) (var 1) (var 2)) (lower (var 0) (var 1) (var 2)))
      (squaredDistance (var 0) (var 1)) ⋏
        rationalLE (squaredDistance (var 0) (var 1))
          (RationalArithmetic.multiply (upper (var 0) (var 1) (var 2)) (upper (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (lower_square _ _ _) (upper_square _ _ _))

theorem finite_hit_to_distance_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 4) ⟶ hit (var 0) (var 1) (var 3) (var 4) ⟶
      rationalLE (lower (var 0) (var 1) (var 2)) (normalize (ZT.ofNat (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (hit_to_lower_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem distance_sample_to_finite_hit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 1)) ⟶ le one (var 4) ⟶
      rationalLE (lower (var 0) (var 1) (var 2)) (normalize (ZT.ofNat (var 3)) (var 4)) ⟶
        hit (var 0) (var 1) (var 3*unit (var 2)+var 4) (var 4*unit (var 2))) :=
  closeUniv 5 (.impI (.impI (.impI (lower_bound_to_hit _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem euclidean_distance_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) ⋏
      (le one (length (var 1)) ⟶
        (lt (fstT (run (var 0) (var 1) (var 2))) (length (var 1)) ⋏
          (fstT (sndT (run (var 0) (var 1) (var 2))) ≐ entry (var 1) (fstT (run (var 0) (var 1) (var 2))))))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.impI (.andI
    (lt_congr (returned_index _ _ _).eqSymm (.eqRefl _) (selected_range _ _ Prf.hyp0)) (returned_point _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianEuclideanPointDistance
