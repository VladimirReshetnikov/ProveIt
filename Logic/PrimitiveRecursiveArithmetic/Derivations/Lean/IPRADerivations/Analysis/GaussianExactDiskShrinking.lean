import IPRADerivations.Analysis.GaussianExponentialSmallPerturbation

/-!
# Actual regular names with an exact rational disk

An original observation q_p with radius A/B+C/2^p is multiplied by
A·2^p/(A·2^p+(C+1)B). The output has radius at most A/B and differs
from q_p by at most (C+1)/2^p. The denominator stays positive even
when A=0. Numerical retiming then gives an actual regular PR2 name
cross-equivalent to the supplied original regular name.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianExactDiskShrinking

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (qmul represents represents_congr positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRootAlgebra (equal_of_values re_sub im_sub re_scale im_scale re_mul im_mul re_one im_one)
open ComplexLogarithmRemainder (scale oneCode normSq)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianFastValueCut (rawEnvelope raw_envelope_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def denominator (A B C p : PTm n) : PTm n := A*unit p+(C+one)*B
def factor (A B C p : PTm n) : PTm n :=
  GaussianRationalHorner.ofGaussian (scale (A*unit p) oneCode) (denominator A B C p)
def shrink (q A B C p : PTm n) : PTm n := qmul (factor A B C p) q

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (A B C p : PTm n) :
    Syn.subst σ (denominator A B C p) = denominator (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ p) := by simp [denominator]
@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (A B C p : PTm n) :
    Syn.subst σ (factor A B C p) = factor (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ p) := by simp [factor]
@[simp] theorem subst_shrink {m : ℕ} (σ : Fin n → PTm m) (q A B C p : PTm n) :
    Syn.subst σ (shrink q A B C p) = shrink (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ p) := by simp [shrink]

theorem denominator_positive (A B C p : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (denominator A B C p) := by unfold denominator; ipra_le sl hB+𝔞 A*𝔞 (unit p)+𝔞 C*𝔞 B

theorem envelope_le_denominator (A B C p : PTm n) :
    Γ ⊢[PRAAx] le (A*unit p+C*B) (denominator A B C p) :=
  le_of_eq_add (d := B) (by unfold denominator; ipra_ring)

theorem shrink_represents (q A B C p : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    represents (shrink q A B C p)
      (ComplexLogarithmRemainder.mul (scale (A*unit p) oneCode) (rawGaussian q))
      (denominator A B C p*rawDen q) :=
  GaussianRationalHorner.qmul_represents _ _ _ _ _ _ (denominator_positive A B C p hB) (raw_den_positive q)
    (GaussianRationalHorner.ofGaussian_represents _ _ (denominator_positive A B C p hB)) (raw_represents q)

theorem scalar_product_norm (N a : PTm n) : Γ ⊢[PRAAx]
    normSq (ComplexLogarithmRemainder.mul (scale N oneCode) a) ≐ N*N*normSq a :=
  (ComplexLogarithmRemainder.normSq_mul _ _).eqTrans
    ((congrMul ((ComplexLogarithmRemainder.normSq_scale N oneCode).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))) (.eqRefl _)))

/-- Exact A/B disk, with no positivity assumption on A. -/
theorem shrink_bound (q A B C p : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] bounded q (A*unit p+C*B) (B*unit p)) :
    Γ ⊢[PRAAx] bounded (shrink q A B C p) A B := by
  have raw := GaussianRationalMetric.bounded_to_cleared q (rawGaussian q) (rawDen q)
    (A*unit p+C*B) (B*unit p) (raw_den_positive q) (positive_product _ _ hB (unit_positive p)) (raw_represents q) hq
  have square := le_mul_mono (envelope_le_denominator (Γ := Γ) A B C p) (envelope_le_denominator (Γ := Γ) A B C p)
  have first := le_mul_mono (le_refl (A*A)) raw
  have second := le_mul_mono (le_refl (A*A*(rawDen q*rawDen q))) square
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _
    (positive_product _ _ (denominator_positive A B C p hB) (raw_den_positive q)) hB (shrink_represents q A B C p hB)
  have e := natEq (scalar_product_norm (Γ := Γ) (A*unit p) (rawGaussian q))
  exact le_congr (by apply deriveNat; ipra_simps; rw [e]; ring) (by ipra_ring)
    (le_trans first (le_congr (by ipra_ring) (.eqRefl _) second))

theorem shrink_difference_represents (q A B C p : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    represents (GaussianRationalMetric.qsub q (shrink q A B C p))
      (scale ((C+one)*B) (rawGaussian q)) (denominator A B C p*rawDen q) := by
  have left := GaussianRationalHorner.represents_congr (Γ := Γ) (.eqRefl _) (GaussianRootAlgebra.equal_refl _)
    (mul_comm _ _) (GaussianRationalHorner.represents_rescale q (rawGaussian q) (rawDen q)
      (denominator A B C p) (raw_represents q))
  have sub := GaussianRationalMetric.qsub_represents _ _ _ _ _
    (positive_product _ _ (denominator_positive A B C p hB) (raw_den_positive q)) left (shrink_represents q A B C p hB)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) sub
  apply equal_of_values <;> simp only [re_sub,im_sub,re_scale,im_scale,re_mul,im_mul,re_one,im_one] <;>
    simp only [denominator] <;> ipra_simps <;> ring

/-- Shrinking changes the original raw rational point by at most (C+1)/2^p. -/
theorem shrink_distance (q A B C p : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] bounded q (A*unit p+C*B) (B*unit p)) :
    Γ ⊢[PRAAx] distanceBounded (shrink q A B C p) q (C+one) (unit p) := by
  have raw := GaussianRationalMetric.bounded_to_cleared q (rawGaussian q) (rawDen q)
    (A*unit p+C*B) (B*unit p) (raw_den_positive q) (positive_product _ _ hB (unit_positive p)) (raw_represents q) hq
  have square := le_mul_mono (envelope_le_denominator (Γ := Γ) A B C p) (envelope_le_denominator (Γ := Γ) A B C p)
  have first := le_mul_mono (le_refl ((C+one)*(C+one))) raw
  have second := le_mul_mono (le_refl ((C+one)*(C+one)*(rawDen q*rawDen q))) square
  apply distance_symmetric _ _ _ _ (unit_positive p)
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _
    (positive_product _ _ (denominator_positive A B C p hB) (raw_den_positive q)) (unit_positive p)
    (shrink_difference_represents q A B C p hB)
  have e := natEq (ComplexLogarithmRemainder.normSq_scale (Γ := Γ) ((C+one)*B) (rawGaussian q))
  exact le_congr (by apply deriveNat; ipra_simps; rw [e]; ring) (by ipra_ring)
    (le_trans first (le_congr (by ipra_ring) (.eqRefl _) second))

def rawValue (f : PR 2) (p x A B C : PTm n) : PTm n := shrink (ap2 f p x) A B C p
def clock (C p : PTm n) : PTm n := GaussianFastValueCut.exponent (C+two) p
def value (f : PR 2) (p x A B C : PTm n) : PTm n := rawValue f (clock C p) x A B C
def data (x A B C : PTm n) : PTm n := pairT A (pairT B (pairT C x))
def body (f : PR 2) : PTm 2 := value f (var 0) (sndT (sndT (sndT (var 1))))
  (fstT (var 1)) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1))))
def nameF (f : PR 2) : PR 2 := PTm.toPR (body f)
def sample (f : PR 2) (p x A B C : PTm n) : PTm n := ap2 (nameF f) p (data x A B C)

@[simp] theorem subst_rawValue {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x A B C : PTm n) :
    Syn.subst σ (rawValue f p x A B C) = rawValue f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) := by simp [rawValue]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (C p : PTm n) :
    Syn.subst σ (clock C p) = clock (Syn.subst σ C) (Syn.subst σ p) := by simp [clock]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x A B C : PTm n) :
    Syn.subst σ (value f p x A B C) = value f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) := by simp [value]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (x A B C : PTm n) :
    Syn.subst σ (data x A B C) = data (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) := by simp [data]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x A B C : PTm n) :
    Syn.subst σ (sample f p x A B C) = sample f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) := by simp [sample]

theorem raw_distance (f : PR 2) (p x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx]
    distanceBounded (rawValue f p x A B C) (ap2 f p x) (C+one) (unit p) :=
  shrink_distance _ A B C p hB (raw_envelope_at f x A B C p he)

theorem raw_regularity (f : PR 2) (s t x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx]
    distanceBounded (rawValue f s x A B C) (rawValue f t x A B C)
      ((C+two)*(unit s+unit t)) (unit s*unit t) := by
  have hp := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive t)
  have left := distance_radius_mono _ _ _ _ ((C+one)*unit t) (unit s*unit t) (unit_positive s) hp
    (le_of_eq_add (d := zero) (by ipra_ring)) (raw_distance f s x A B C hB he)
  have right := distance_radius_mono _ _ _ _ ((C+one)*unit s) (unit s*unit t) (unit_positive t) hp
    (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_symmetric _ _ _ _ (unit_positive t) (raw_distance f t x A B C hB he))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp
      (distance_triangle_same _ _ _ _ _ _ hp left (GaussianNameEquivalence.point_at f x s t hc)) right)

theorem value_bound (f : PR 2) (p x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx] bounded (value f p x A B C) A B :=
  shrink_bound _ A B C (clock C p) hB (raw_envelope_at f x A B C (clock C p) he)

theorem value_regularity (f : PR 2) (s t x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx]
    distanceBounded (value f s x A B C) (value f t x A B C) (unit s+unit t) (unit s*unit t) :=
  distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (positive_product _ _ (unit_positive s) (unit_positive t))
    (GaussianFastValueCut.regularity_budget (C+two) s t)
    (raw_regularity f (clock C s) (clock C t) x A B C hB hc he)

/-- Independent precisions: the transformed observation retains the SAME original value. -/
theorem value_cross (f : PR 2) (s t x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx]
    distanceBounded (value f s x A B C) (ap2 f t x) (unit s+unit t) (unit s*unit t) := by
  let r := clock C s
  have hp := positive_product (Γ := Γ) _ _ (unit_positive r) (unit_positive t)
  have left := distance_radius_mono _ _ _ _ ((C+one)*unit t) (unit r*unit t) (unit_positive r) hp
    (le_of_eq_add (d := zero) (by ipra_ring)) (raw_distance f r x A B C hB he)
  have combined := distance_triangle_same _ _ _ _ _ _ hp left (GaussianNameEquivalence.point_at f x r t hc)
  apply distance_radius_mono _ _ _ _ _ _ hp (positive_product _ _ (unit_positive s) (unit_positive t)) _ combined
  have budget := GaussianFastValueCut.query_budget (Γ := Γ) (C+two) s
  dsimp only [r,clock]
  ipra_le 𝔞 (unit t)*𝔞 (unit t)*sl budget

theorem sample_at (f : PR 2) (p x A B C : PTm n) : Γ ⊢[PRAAx]
    sample f p x A B C ≐ value f p x A B C := by
  have e := toPR_eq (Γ := Γ) (body f) ![p,data x A B C]
  have e' : Γ ⊢[PRAAx] sample f p x A B C ≐ value f p (sndT (sndT (sndT (data x A B C))))
      (fstT (data x A B C)) (fstT (sndT (data x A B C))) (fstT (sndT (sndT (data x A B C)))) := by
    simpa [sample,nameF,ap2,body] using e
  have rest := snd_pair (Γ := Γ) A (pairT B (pairT C x))
  have tail := (congrSnd rest).eqTrans (snd_pair B (pairT C x))
  have eq := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (value f (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![p,sndT (sndT (sndT (data x A B C))),fstT (data x A B C),
      fstT (sndT (data x A B C)),fstT (sndT (sndT (data x A B C)))]) (σ' := ![p,x,A,B,C])
    (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact (congrSnd tail).eqTrans (snd_pair C x)
      · exact fst_pair _ _
      · exact (congrFst rest).eqTrans (fst_pair _ _)
      · exact (congrFst tail).eqTrans (fst_pair _ _))
  exact e'.eqTrans (by simpa using eq)

theorem sample_bound (f : PR 2) (p x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx] bounded (sample f p x A B C) A B :=
  GaussianRationalReciprocal.bound_congr (sample_at f p x A B C).eqSymm (.eqRefl _) (.eqRefl _) (value_bound f p x A B C hB he)

theorem sample_canonical (f : PR 2) (p x A B C : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (sample f p x A B C) :=
  GaussianRationalHorner.canonical_congr (sample_at f p x A B C) (GaussianRationalHorner.qmul_canonical _ _)

theorem sample_regularity (f : PR 2) (s t x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx]
    distanceBounded (sample f s x A B C) (sample f t x A B C) (unit s+unit t) (unit s*unit t) :=
  distance_congr (sample_at f s x A B C).eqSymm (sample_at f t x A B C).eqSymm (.eqRefl _) (.eqRefl _)
    (value_regularity f s t x A B C hB hc he)

theorem sample_cross (f : PR 2) (s t x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx]
    distanceBounded (sample f s x A B C) (ap2 f t x) (unit s+unit t) (unit s*unit t) :=
  distance_congr (sample_at f s x A B C).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (value_cross f s t x A B C hB hc he)

theorem name_regular (f : PR 2) (x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x A B C) := by
  refine .allI (.allI ?_)
  have bs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift B)) := by simpa [Fm.shift,Syn.shift] using hB.shift.shift
  have cs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by simpa [Fm.shift,Syn.shift] using hc.shift.shift
  have es : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] rawEnvelope f (Syn.shift (Syn.shift x))
      (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift C)) := by simpa [Fm.shift,Syn.shift] using he.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,sample,subst_data,Syn.shift] using
    sample_regularity f (var 1) (var 0) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift C)) bs cs es

theorem cross_equivalent (f : PR 2) (x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) f (data x A B C) x := by
  refine .allI (.allI ?_)
  have bs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift B)) := by simpa [Fm.shift,Syn.shift] using hB.shift.shift
  have cs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by simpa [Fm.shift,Syn.shift] using hc.shift.shift
  have es : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] rawEnvelope f (Syn.shift (Syn.shift x))
      (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift C)) := by simpa [Fm.shift,Syn.shift] using he.shift.shift
  simpa only [crossEquivalent,GaussianEuclideanPointDistance.unit,unit,sample,subst_data,Syn.shift] using
    sample_cross f (var 1) (var 0) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift C)) bs cs es

theorem exact_disk_samples (f : PR 2) (x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx]
    GaussianExponentialSmallPerturbation.smallSamples (nameF f) (data x A B C) A B := by
  refine .allI ?_
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] rawEnvelope f (Syn.shift x) (Syn.shift A) (Syn.shift B) (Syn.shift C) := by
    simpa [Fm.shift,Syn.shift] using he.shift
  simpa only [GaussianExponentialSmallPerturbation.smallSamples,sample,subst_data,Syn.shift] using
    sample_bound f (var 0) (Syn.shift x) (Syn.shift A) (Syn.shift B) (Syn.shift C) bs es

theorem correct (f : PR 2) (x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx]
    pointCN (nameF f) (data x A B C) ⋏ (crossEquivalent (nameF f) f (data x A B C) x ⋏
      GaussianExponentialSmallPerturbation.smallSamples (nameF f) (data x A B C) A B) :=
  .andI (name_regular f x A B C hB hc he) (.andI (cross_equivalent f x A B C hB hc he) (exact_disk_samples f x A B C hB he))

/-- The observation slack has been removed before applying the exact 3A/B perturbation theorem. -/
theorem exponential_near_one (f : PR 2) (x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (hc : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) :
    Γ ⊢[PRAAx] pointCN (GaussianUnitDiskExponentialName.nameF (nameF f)) (data x A B C) ⋏
      GaussianExponentialSmallPerturbation.nearOneSamples (nameF f) (data x A B C) A B :=
  GaussianExponentialSmallPerturbation.regular_near_one (nameF f) (data x A B C) A B hB hAB
    (name_regular f x A B C hB hc he) (exact_disk_samples f x A B C hB he)

theorem actual_exact_disk_shrinking_estimates_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ bounded (var 0) (var 1*unit (var 4)+var 3*var 2) (var 2*unit (var 4)) ⟶
      bounded (shrink (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1) (var 2) ⋏
        distanceBounded (shrink (var 0) (var 1) (var 2) (var 3) (var 4)) (var 0) (var 3+one) (unit (var 4))) :=
  closeUniv 5 (.impI (.impI (.andI (shrink_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0) (shrink_distance _ _ _ _ _ Prf.hyp1 Prf.hyp0))))

theorem actual_exact_disk_shrinking_program_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sample f (var 0) (var 1) (var 2) (var 3) (var 4) ≐ value f (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (sample_at f _ _ _ _ _)
theorem original_regular_exact_disk_shrinking_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ pointCN f (var 0) ⟶ rawEnvelope f (var 0) (var 1) (var 2) (var 3) ⟶
      pointCN (nameF f) (data (var 0) (var 1) (var 2) (var 3)) ⋏
        (crossEquivalent (nameF f) f (data (var 0) (var 1) (var 2) (var 3)) (var 0) ⋏
          GaussianExponentialSmallPerturbation.smallSamples (nameF f) (data (var 0) (var 1) (var 2) (var 3)) (var 1) (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (correct f _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem original_corrected_small_exponential_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 1) (var 2) ⟶ pointCN f (var 0) ⟶ rawEnvelope f (var 0) (var 1) (var 2) (var 3) ⟶
      pointCN (GaussianUnitDiskExponentialName.nameF (nameF f)) (data (var 0) (var 1) (var 2) (var 3)) ⋏
        GaussianExponentialSmallPerturbation.nearOneSamples (nameF f) (data (var 0) (var 1) (var 2) (var 3)) (var 1) (var 2)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (exponential_near_one f _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianExactDiskShrinking
