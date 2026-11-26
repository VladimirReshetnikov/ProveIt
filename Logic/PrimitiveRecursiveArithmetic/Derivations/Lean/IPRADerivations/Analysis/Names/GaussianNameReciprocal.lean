import IPRADerivations.Analysis.Names.GaussianNameRingLaws
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianGeneralCoefficientNames
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianDominantScalarOrder

/-!
# An actual reciprocal name from a finite fractional apartness certificate

The only source hypotheses are the original point CN and a lower bound
at its actual h+2 observation. The used tail lower bound, decoded norm
positivity, reciprocal disk, regularity modulus and normalized output laws
are derived. All data, apartness indices and precisions are numerical.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNameReciprocal

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qnormSq squaredTolerance bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal
  (reciprocal normNumerator inverseNumerator conjugate qone)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN subst_pointCN)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qsub_congr)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq scale mul)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra (sub)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def anchor (h : PTm n) : PTm n := h+two
def R (h : PTm n) : PTm n := unit (succ h)
def lower (q r : PTm n) : Fm PTm n := RationalArgmin.rationalLE (squaredTolerance one r) (qnormSq q)
def apart (f : PR 2) (h x : PTm n) : Fm PTm n := lower (ap2 f (anchor h) x) (unit h)
def input (f : PR 2) (h x : PTm n) : Fm PTm n := pointCN f x ⋏ apart f h x
def tail (f : PR 2) (h x s : PTm n) : PTm n := ap2 f (s+anchor h) x
def liftF (f : PR 2) : PR 3 := PTm.toPR (ap2 f (var 1) (var 2) : PTm 3)

ipra_subst anchor
ipra_subst R
ipra_subst lower
ipra_subst apart
ipra_subst input
ipra_subst tail

theorem lower_congr {q q' r r' : PTm n} (hq : Γ ⊢[PRAAx] q ≐ q') (hr : Γ ⊢[PRAAx] r ≐ r')
    (h : Γ ⊢[PRAAx] lower q r) : Γ ⊢[PRAAx] lower q' r' := by
  have e := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (lower (var 0) (var 1) : Fm PTm 2)
    ![q,r] ![q',r'] (fun i => by fin_cases i; exact hq; exact hr) (by simpa using h)
  simpa using e

theorem R_positive (h : PTm n) : Γ ⊢[PRAAx] le one (R h) := unit_positive _
theorem lift_at (f : PR 2) (i s x : PTm n) : Γ ⊢[PRAAx] ap3 (liftF f) i s x ≐ ap2 f s x := by
  simpa [liftF,ap3] using toPR_eq (Γ := Γ) (ap2 f (var 1) (var 2) : PTm 3) ![i,s,x]

theorem lift_regular (f : PR 2) (i x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    GaussianCoefficientNameBounds.regularCoefficient (liftF f) i x := by
  refine .allI (.allI ?_)
  have h2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift.shift
  exact distance_congr (lift_at f (Syn.shift (Syn.shift i)) (var 1) (Syn.shift (Syn.shift x))).eqSymm
    (lift_at f (Syn.shift (Syn.shift i)) (var 0) (Syn.shift (Syn.shift x))).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.point_at f _ (var 1) (var 0) h2)

theorem lift_CN (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    GaussianGeneralCoefficientNames.generalCN (liftF f) zero x := by
  refine .allI (.impI ?_)
  have h1 : (lt (var 0) (Syn.shift (succ zero))::Γ.map Fm.shift) ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift.wk
  exact lift_regular f (var 0) (Syn.shift x) h1

/-- The finite original certificate supplies separation on the entire used tail. -/
theorem tail_lower (f : PR 2) (h x s : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] apart f h x) : Γ ⊢[PRAAx]
    lower (tail f h x s) (R h) := by
  have ref : Γ ⊢[PRAAx] GaussianGeneralCoefficientNames.apart (liftF f) zero h x :=
    lower_congr (lift_at f zero (anchor h) x).eqSymm (.eqRefl _) ha
  have separated := GaussianGeneralCoefficientNames.apart_tail (liftF f) zero zero h (s+anchor h) x
    (lift_CN f x hf) (le_refl zero) ref (le_add_left (anchor h) s)
  exact lower_congr (lift_at f zero (s+anchor h) x) (.eqRefl _) separated

theorem lower_cleared (q r : PTm n) (hr : Γ ⊢[PRAAx] le one r)
    (h : Γ ⊢[PRAAx] lower q r) : Γ ⊢[PRAAx]
    le (rawDen q*rawDen q) (r*r*normNumerator q) :=
  le_congr (by ipra_ring) (by unfold normNumerator; ipra_ring)
    (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      (GaussianRationalMetric.squared_tolerance_represents one r hr)
      (GaussianRationalMetric.qnormSq_represents q (rawGaussian q) (rawDen q)
        (raw_den_positive q) (raw_represents q)) h)

theorem lower_norm_positive (q r : PTm n) (hr : Γ ⊢[PRAAx] le one r)
    (h : Γ ⊢[PRAAx] lower q r) : Γ ⊢[PRAAx] le one (normNumerator q) :=
  GaussianDominantScalarOrder.factor_positive_left (normNumerator q) (r*r)
    (le_congr (.eqRefl _) (by ipra_ring)
      (le_trans (positive_product _ _ (raw_den_positive q) (raw_den_positive q)) (lower_cleared q r hr h)))

/-- Fractional separation |q|>=1/r gives the actual reciprocal disk r. -/
theorem inverse_bound (q r : PTm n) (hr : Γ ⊢[PRAAx] le one r)
    (h : Γ ⊢[PRAAx] lower q r) : Γ ⊢[PRAAx] bounded (reciprocal q) r one := by
  have hn := lower_norm_positive q r hr h
  have bound := mul_le_mul_right (normNumerator q) (lower_cleared q r hr h)
  have norm := (ComplexLogarithmRemainder.normSq_scale (Γ := Γ) (rawDen q) (conjugate (rawGaussian q))).eqTrans
    (congrMul (.eqRefl _) (GaussianRationalReciprocal.norm_conjugate _))
  apply (GaussianRationalMetric.bounded_iff _ _ _ _ _ hn (le_refl one)
    (GaussianRationalReciprocal.reciprocal_represents q hn)).iffMpr
  exact le_congr (by
    apply deriveNat
    have e := natEq norm
    unfold inverseNumerator normNumerator
    ipra_simps
    rw [e]
    ring) (by ipra_ring) bound

/-- The conjugate/norm numerator identity uses the actual decoded data. -/
theorem inverse_difference_value (a b : PTm n) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal
      (scale (rawDen a*rawDen b)
        (sub (scale (normNumerator b) (inverseNumerator a)) (scale (normNumerator a) (inverseNumerator b))))
      (mul (mul (inverseNumerator a)
        (sub (scale (rawDen a) (rawGaussian b)) (scale (rawDen b) (rawGaussian a)))) (inverseNumerator b)) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    unfold inverseNumerator normNumerator <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
      GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRationalReciprocal.re_conjugate,GaussianRationalReciprocal.im_conjugate,
      Q.mk_mul,map_mul,ComplexLogarithmRemainder.normSq_eval] <;> ring

theorem inverse_difference (a b : PTm n)
    (ha : Γ ⊢[PRAAx] le one (normNumerator a)) (hb : Γ ⊢[PRAAx] le one (normNumerator b)) : Γ ⊢[PRAAx]
    qsub (reciprocal a) (reciprocal b) ≐ qmul (qmul (reciprocal a) (qsub b a)) (reciprocal b) := by
  let D := rawDen a*rawDen b
  let E := (normNumerator a*normNumerator b)*D
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (raw_den_positive a) (raw_den_positive b)
  have hn := positive_product (Γ := Γ) _ _ ha hb
  have he : Γ ⊢[PRAAx] le one E := positive_product _ _ hn hd
  have ia := GaussianRationalReciprocal.reciprocal_represents a ha
  have ib := GaussianRationalReciprocal.reciprocal_represents b hb
  have iac := represents_rescale (reciprocal a) (inverseNumerator a) (normNumerator a) (normNumerator b) ia
  have ibc := GaussianRationalSyntheticDivision.rescale_to (reciprocal b) (inverseNumerator b)
    (normNumerator b) (normNumerator a) (normNumerator a*normNumerator b) ib (mul_comm _ _)
  have left0 := GaussianRationalMetric.qsub_represents _ _ _ _ _ hn iac ibc
  have left := represents_rescale _ _ _ D left0
  have ac := represents_rescale a (rawGaussian a) (rawDen a) (rawDen b) (raw_represents (Γ := Γ) a)
  have bc := GaussianRationalSyntheticDivision.rescale_to b (rawGaussian b) (rawDen b) (rawDen a) D
    (raw_represents (Γ := Γ) b) (mul_comm _ _)
  have ba := GaussianRationalMetric.qsub_represents _ _ _ _ D hd bc ac
  have middle := qmul_represents _ _ _ _ _ _ ha hd ia ba
  have right0 := qmul_represents _ _ _ _ _ _ (positive_product _ _ ha hd) hb middle ib
  have right := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _)
    (show Γ ⊢[PRAAx] (normNumerator a*D)*normNumerator b ≐ E by unfold E; ipra_ring) right0
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _) (qmul_canonical _ _) he (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  exact inverse_difference_value a b

/-- A fractional separation disk gives a genuine inverse Lipschitz law. -/
theorem inverse_distance (a b r A B : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] lower a r) (hb : Γ ⊢[PRAAx] lower b r)
    (hab : Γ ⊢[PRAAx] distanceBounded a b A B) : Γ ⊢[PRAAx]
    distanceBounded (reciprocal a) (reciprocal b) (r*r*A) B := by
  have ba := distance_symmetric _ _ _ _ hB hab
  have first : Γ ⊢[PRAAx] bounded (qmul (reciprocal a) (qsub b a)) (r*A) B :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) hB (inverse_bound a r hr ha) ba)
  have last := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hB (le_refl one) first (inverse_bound b r hr hb)
  exact GaussianRationalReciprocal.bound_congr
    (inverse_difference a b (lower_norm_positive a r hr ha) (lower_norm_positive b r hr hb)).eqSymm
    (by ipra_ring) (by ipra_ring) last

def modulus (h : PTm n) : PTm n := R h*R h
def raw (f : PR 2) (h x s : PTm n) : PTm n := reciprocal (tail f h x s)
def rawData (h x : PTm n) : PTm n := pairT h x
def rawF (f : PR 2) : PR 2 := PTm.toPR
  (raw f (fstT (var 1)) (sndT (var 1)) (var 0) : PTm 2)
def nameF (f : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawF f)
def nameData (h x : PTm n) : PTm n := GaussianFastValueCut.nameData (modulus h) (rawData h x)

ipra_subst modulus
ipra_subst raw
ipra_subst rawData
ipra_subst nameData

theorem reciprocal_congr {q q' : PTm n} (h : Γ ⊢[PRAAx] q ≐ q') : Γ ⊢[PRAAx] reciprocal q ≐ reciprocal q' := by
  ipra_congr (reciprocal (var 0) : PTm 1) with [h]

theorem raw_at (f : PR 2) (h x s : PTm n) : Γ ⊢[PRAAx]
    ap2 (rawF f) s (rawData h x) ≐ raw f h x s := by
  have e := toPR_eq (Γ := Γ) (raw f (fstT (var 1)) (sndT (var 1)) (var 0) : PTm 2) ![s,rawData h x]
  refine e.eqTrans ?_
  simpa only [raw,tail,anchor,GaussianRationalReciprocal.subst_reciprocal,subst_ap2,PTm.subst_add,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,rawData,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    reciprocal_congr (Γ := Γ) (congrAp2 f (congrAdd (.eqRefl s)
      (congrAdd (fst_pair h x) (.eqRefl two))) (snd_pair h x))

theorem tail_coherence (f : PR 2) (h x s t : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (tail f h x s) (tail f h x t) (unit s+unit t) (unit s*unit t) := by
  have hs : Γ ⊢[PRAAx] le (unit s) (unit (s+anchor h)) :=
    GaussianBalancedRadiusArithmetic.unit_monotone s (s+anchor h) (le_add_right s (anchor h))
  have ht : Γ ⊢[PRAAx] le (unit t) (unit (t+anchor h)) :=
    GaussianBalancedRadiusArithmetic.unit_monotone t (t+anchor h) (le_add_right t (anchor h))
  have comparison : Γ ⊢[PRAAx]
      le ((unit (s+anchor h)+unit (t+anchor h))*(unit s*unit t))
        ((unit s+unit t)*(unit (s+anchor h)*unit (t+anchor h))) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (mul_le_mul_right (unit s*unit (s+anchor h)) ht)
        (mul_le_mul_right (unit t*unit (t+anchor h)) hs))
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _))
    (positive_product _ _ (unit_positive s) (unit_positive t)) comparison
    (GaussianNameEquivalence.point_at f x (s+anchor h) (t+anchor h) hf)

theorem raw_regular_at (f : PR 2) (h x s t : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] apart f h x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (rawF f) s (rawData h x)) (ap2 (rawF f) t (rawData h x))
      (modulus h*(unit s+unit t)) (unit s*unit t) :=
  distance_congr (raw_at f h x s).eqSymm (raw_at f h x t).eqSymm (.eqRefl _) (.eqRefl _)
    (inverse_distance _ _ _ _ _ (R_positive h) (positive_product _ _ (unit_positive s) (unit_positive t))
      (tail_lower f h x s hf ha) (tail_lower f h x t hf ha) (tail_coherence f h x s t hf))

theorem raw_regular (f : PR 2) (h x : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] apart f h x) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular (rawF f) (modulus h) (rawData h x) := by
  refine .allI (.allI ?_)
  have hf2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift.shift
  have ha2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] apart f (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_apart,Syn.shift] using ha.shift.shift
  simpa only [Syn.shift,subst_modulus,subst_rawData] using
    raw_regular_at f (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift x)) (var 1) (var 0) hf2 ha2

theorem name_fast (f : PR 2) (h x : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] apart f h x) : Γ ⊢[PRAAx]
    pointCN (nameF f) (nameData h x) :=
  GaussianFastValueCut.name_fast (rawF f) (modulus h) (rawData h x) (raw_regular f h x hf ha)
theorem name_canonical (f : PR 2) (h x k : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 (nameF f) k (nameData h x)) :=
  GaussianFastValueCut.name_canonical (rawF f) (modulus h) (rawData h x) k
theorem name_at (f : PR 2) (h x k : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF f) k (nameData h x) ≐ GaussianFastValueCut.recode
      (raw f h x (GaussianFastValueCut.exponent (modulus h) k)) :=
  (GaussianFastValueCut.name_at (rawF f) (modulus h) (rawData h x) k).eqTrans
    (GaussianNameArithmetic.recode_congr (raw_at f h x _))

theorem name_sample_error (f : PR 2) (h x k : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] apart f h x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) k (nameData h x)) (raw f h x k) (modulus h+one) (unit k) :=
  distance_congr (.eqRefl _) (raw_at f h x k) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.normalized_to_sample (rawF f) (modulus h) (rawData h x) k (raw_regular f h x hf ha))

theorem tail_sample_distance (f : PR 2) (h x s : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f s x) (tail f h x s) two (unit s) := by
  have monotone : Γ ⊢[PRAAx] le (unit s) (unit (s+anchor h)) :=
    GaussianBalancedRadiusArithmetic.unit_monotone s (s+anchor h) (le_add_right s (anchor h))
  have comparison : Γ ⊢[PRAAx]
      le ((unit s+unit (s+anchor h))*unit s) (two*(unit s*unit (s+anchor h))) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (mul_le_mul_right (unit s) monotone) (le_refl (unit s*unit (s+anchor h))))
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive s) (unit_positive _)) (unit_positive s) comparison
    (GaussianNameEquivalence.point_at f x s (s+anchor h) hf)

theorem raw_bound (f : PR 2) (h x s : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] apart f h x) : Γ ⊢[PRAAx]
    bounded (raw f h x s) (R h) one := inverse_bound _ _ (R_positive h) (tail_lower f h x s hf ha)

theorem tail_inverse_identity (f : PR 2) (h x s : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] apart f h x) : Γ ⊢[PRAAx]
    qmul (tail f h x s) (raw f h x s) ≐ qone :=
  GaussianRationalReciprocal.reciprocal_identity _ (lower_norm_positive _ _ (R_positive h) (tail_lower f h x s hf ha))

def productBudget (f : PR 2) (h x : PTm n) : PTm n :=
  (GaussianNameArithmetic.multiplyModulus f (nameF f) x (nameData h x)+one+
    GaussianNameBounds.U f x*(modulus h+one))+two*R h
ipra_subst productBudget

theorem product_one_at (f : PR 2) (h x k : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] apart f h x) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (GaussianNameArithmetic.multiplyF f (nameF f)) k
        (GaussianNameArithmetic.multiplyData f (nameF f) x (nameData h x)))
      (ap2 GaussianNameRingLaws.oneF k x) (productBudget f h x) (unit k) := by
  have hinv := name_fast f h x hf ha
  have outer := GaussianNameRingLaws.multiply_sample_error f (nameF f) x (nameData h x) k hf hinv
  have inner := GaussianNameRingLaws.product_right_error _ _ _ _ _ _ _ (unit_positive k)
    (name_sample_error f h x k hf ha)
    (GaussianNameBounds.sample_bound (nameF f) (nameData h x) k hinv) (GaussianNameBounds.sample_bound f x k hf)
  have first := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ (unit_positive k) outer inner
  have shifted := GaussianNameRingLaws.product_left_error _ _ _ _ _ _ _ (unit_positive k)
    (tail_sample_distance f h x k hf) (raw_bound f h x k hf ha)
    (GaussianNameBounds.sample_bound f x (k+anchor h) hf)
  have last := distance_congr (.eqRefl _)
    ((tail_inverse_identity f h x k hf ha).eqTrans (GaussianNameRingLaws.one_at k x).eqSymm)
    (.eqRefl _) (.eqRefl _) shifted
  exact GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ (unit_positive k) first last

theorem product_one (f : PR 2) (h x : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] apart f h x) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent (GaussianNameArithmetic.multiplyF f (nameF f)) GaussianNameRingLaws.oneF
      (GaussianNameArithmetic.multiplyData f (nameF f) x (nameData h x)) x := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (productBudget f h x)
    (GaussianNameArithmetic.multiply_fast _ _ _ _ hf (name_fast f h x hf ha)) (GaussianNameRingLaws.one_fast x)
  refine .allI ?_
  have hf1 : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  have ha1 : Γ.map Fm.shift ⊢[PRAAx] apart f (Syn.shift h) (Syn.shift x) := by
    simpa only [Fm.shift,subst_apart,Syn.shift] using ha.shift
  simpa only [Syn.shift,GaussianNameArithmetic.subst_multiplyData,subst_nameData,subst_productBudget] using
    product_one_at f (Syn.shift h) (Syn.shift x) (var 0) hf1 ha1

theorem product_one_left (f : PR 2) (h x : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] apart f h x) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent (GaussianNameArithmetic.multiplyF (nameF f) f) GaussianNameRingLaws.oneF
      (GaussianNameArithmetic.multiplyData (nameF f) f (nameData h x) x) x :=
  GaussianNameEquivalence.cross_trans _ _ _ _ _ _
    (GaussianNameRingLaws.multiply_commutative (nameF f) f (nameData h x) x (name_fast f h x hf ha) hf)
    (product_one f h x hf ha)

theorem inverse_distance_two (a b r s A B : PTm n)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] lower a r) (hb : Γ ⊢[PRAAx] lower b s)
    (hab : Γ ⊢[PRAAx] distanceBounded a b A B) : Γ ⊢[PRAAx]
    distanceBounded (reciprocal a) (reciprocal b) (r*s*A) B := by
  have first : Γ ⊢[PRAAx] bounded (qmul (reciprocal a) (qsub b a)) (r*A) B :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) hB (inverse_bound a r hr ha)
        (distance_symmetric _ _ _ _ hB hab))
  have last := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hB (le_refl one) first (inverse_bound b s hs hb)
  exact GaussianRationalReciprocal.bound_congr
    (inverse_difference a b (lower_norm_positive a r hr ha) (lower_norm_positive b s hs hb)).eqSymm
    (by ipra_ring) (by ipra_ring) last

theorem tails_cross (f g : PR 2) (h h' x y k : PTm n)
    (he : Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (tail f h x k) (tail g h' y k) two (unit k) := by
  have hp : Γ ⊢[PRAAx] le (unit k) (unit (k+anchor h)) :=
    GaussianBalancedRadiusArithmetic.unit_monotone k (k+anchor h) (le_add_right k (anchor h))
  have hq : Γ ⊢[PRAAx] le (unit k) (unit (k+anchor h')) :=
    GaussianBalancedRadiusArithmetic.unit_monotone k (k+anchor h') (le_add_right k (anchor h'))
  have comparison : Γ ⊢[PRAAx]
      le ((unit (k+anchor h)+unit (k+anchor h'))*unit k)
        (two*(unit (k+anchor h)*unit (k+anchor h'))) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (mul_le_mul_right (unit (k+anchor h)) hq)
        (mul_le_mul_right (unit (k+anchor h')) hp))
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive k) comparison
    (GaussianNameEquivalence.cross_at f g x y (k+anchor h) (k+anchor h') he)

theorem raw_equivalent_at (f g : PR 2) (h h' x y k : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (ha : Γ ⊢[PRAAx] apart f h x) (hb : Γ ⊢[PRAAx] apart g h' y)
    (he : Γ ⊢[PRAAx] GaussianNameEquivalence.diagonalEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (rawF f) k (rawData h x)) (ap2 (rawF g) k (rawData h' y))
      (R h*R h'*two) (unit k) :=
  distance_congr (raw_at f h x k).eqSymm (raw_at g h' y k).eqSymm (.eqRefl _) (.eqRefl _)
    (inverse_distance_two _ _ _ _ _ _ (R_positive h) (R_positive h') (unit_positive k)
      (tail_lower f h x k hf ha) (tail_lower g h' y k hg hb)
      (tails_cross f g h h' x y k (GaussianNameEquivalence.diagonal_to_cross f g x y hf hg he)))

/-- Equivalent inputs may use different numerical apartness certificates. -/
theorem names_equivalent (f g : PR 2) (h h' x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (ha : Γ ⊢[PRAAx] apart f h x) (hb : Γ ⊢[PRAAx] apart g h' y)
    (he : Γ ⊢[PRAAx] GaussianNameEquivalence.diagonalEquivalent f g x y) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent (nameF f) (nameF g) (nameData h x) (nameData h' y) := by
  apply GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ (modulus h) (modulus h')
    (rawData h x) (rawData h' y) (R h*R h'*two) (raw_regular f h x hf ha) (raw_regular g h' y hg hb)
  refine .allI ?_
  have hf1 : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  have hg1 : Γ.map Fm.shift ⊢[PRAAx] pointCN g (Syn.shift y) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hg.shift
  have ha1 : Γ.map Fm.shift ⊢[PRAAx] apart f (Syn.shift h) (Syn.shift x) := by
    simpa only [Fm.shift,subst_apart,Syn.shift] using ha.shift
  have hb1 : Γ.map Fm.shift ⊢[PRAAx] apart g (Syn.shift h') (Syn.shift y) := by
    simpa only [Fm.shift,subst_apart,Syn.shift] using hb.shift
  have he1 : Γ.map Fm.shift ⊢[PRAAx] GaussianNameEquivalence.diagonalEquivalent f g (Syn.shift x) (Syn.shift y) := by
    simpa only [Fm.shift,GaussianNameEquivalence.subst_diagonalEquivalent,Syn.shift] using he.shift
  simpa only [Syn.shift,subst_rawData,subst_R,PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    raw_equivalent_at f g (Syn.shift h) (Syn.shift h') (Syn.shift x) (Syn.shift y) (var 0) hf1 hg1 ha1 hb1 he1

def equivalenceInput (f g : PR 2) (h h' x y : PTm n) : Fm PTm n :=
  input f h x ⋏ (input g h' y ⋏ GaussianNameEquivalence.diagonalEquivalent f g x y)
ipra_subst equivalenceInput

theorem fractional_reciprocal_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⋏ lower (var 0) (var 1) ⟶ bounded (reciprocal (var 0)) (var 1) one) :=
  closeUniv 2 (.impI (inverse_bound _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))
theorem original_apartness_tail_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input f (var 0) (var 1) ⟶ lower (tail f (var 0) (var 1) (var 2)) (R (var 0))) :=
  closeUniv 3 (.impI (tail_lower f _ _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))
theorem actual_raw_reciprocal_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (rawF f) (var 2) (rawData (var 0) (var 1)) ≐ reciprocal (tail f (var 0) (var 1) (var 2))) :=
  closeUniv 3 (raw_at f _ _ _)
theorem actual_reciprocal_name_at_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (nameF f) (var 2) (nameData (var 0) (var 1)) ≐ GaussianFastValueCut.recode
      (raw f (var 0) (var 1) (GaussianFastValueCut.exponent (modulus (var 0)) (var 2)))) :=
  closeUniv 3 (name_at f _ _ _)
theorem actual_reciprocal_name_fast_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶ pointCN (nameF f) (nameData (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_fast f _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))
theorem actual_reciprocal_name_canonical_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (canonical (ap2 (nameF f) (var 2) (nameData (var 0) (var 1)))) :=
  closeUniv 3 (name_canonical f _ _ _)
theorem fractional_inverse_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⋏ lower (var 0) (var 1) ⟶ qmul (var 0) (reciprocal (var 0)) ≐ qone) :=
  closeUniv 2 (.impI (GaussianRationalReciprocal.reciprocal_identity _
    (lower_norm_positive _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0))))
theorem actual_name_right_inverse_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶
      GaussianNameEquivalence.crossEquivalent (GaussianNameArithmetic.multiplyF f (nameF f)) GaussianNameRingLaws.oneF
        (GaussianNameArithmetic.multiplyData f (nameF f) (var 1) (nameData (var 0) (var 1))) (var 1)) :=
  closeUniv 2 (.impI (product_one f _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))
theorem actual_name_left_inverse_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶
      GaussianNameEquivalence.crossEquivalent (GaussianNameArithmetic.multiplyF (nameF f) f) GaussianNameRingLaws.oneF
        (GaussianNameArithmetic.multiplyData (nameF f) f (nameData (var 0) (var 1)) (var 1)) (var 1)) :=
  closeUniv 2 (.impI (product_one_left f _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))
theorem independently_certified_reciprocals_equivalent_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (equivalenceInput f g (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianNameEquivalence.crossEquivalent (nameF f) (nameF g)
        (nameData (var 0) (var 2)) (nameData (var 1) (var 3))) :=
  closeUniv 4 (.impI (names_equivalent f g _ _ _ _ (.andE₁ (.andE₁ Prf.hyp0))
    (.andE₁ (.andE₁ (.andE₂ Prf.hyp0))) (.andE₂ (.andE₁ Prf.hyp0))
    (.andE₂ (.andE₁ (.andE₂ Prf.hyp0))) (.andE₂ (.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNameReciprocal
