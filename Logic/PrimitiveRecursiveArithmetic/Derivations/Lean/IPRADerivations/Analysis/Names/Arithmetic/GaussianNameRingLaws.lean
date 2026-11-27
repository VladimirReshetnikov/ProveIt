import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameArithmetic
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalSumAlgebra
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianCoefficientNormOrder

/-!
# Ring laws for the actual normalized Gaussian name programs

Every expression below uses the actual PR2 addition/multiplication producers.
A finite same-precision error between proper names suffices for exact
two-precision equivalence, by the existing finite integer-gap theorem.
Thus nested normalization shifts are compared through derived errors, not
by asserting literal identities between their different sample programs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNameRingLaws

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qadd qmul qzero canonical positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (qone)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN subst_pointCN)
open LeanProofs.IPRA.Analysis.GaussianNameEquivalence (crossEquivalent)
open LeanProofs.IPRA.Analysis.GaussianNameArithmetic
  (addF multiplyF addData multiplyData multiplyModulus addRawF multiplyRawF)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder
  (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def three : PTm n := two+one

theorem point_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular f one x := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using h.shift.shift
  have e : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      distanceBounded (ap2 f (var 1) (Syn.shift (Syn.shift x)))
        (ap2 f (var 0) (Syn.shift (Syn.shift x)))
        (one*(unit (var 1)+unit (var 0))) (unit (var 1)*unit (var 0)) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianNameEquivalence.point_at f _ (var 1) (var 0) hs)
  simpa only [Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using e

/-- An arbitrary derived diagonal constant disappears by a finite gap query. -/
theorem equivalent_of_envelope (f g : PR 2) (x y K : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hEnv : Γ ⊢[PRAAx] GaussianValueNormalizerExtensionality.rawDiagonal f g x y K) : Γ ⊢[PRAAx]
    crossEquivalent f g x y := by
  refine .allI (.allI ?_)
  have hf2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift.shift
  have hg2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN g (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hg.shift.shift
  have he2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianValueNormalizerExtensionality.rawDiagonal f g (Syn.shift (Syn.shift x))
        (Syn.shift (Syn.shift y)) (Syn.shift (Syn.shift K)) := by
    simpa only [Fm.shift,GaussianValueNormalizerExtensionality.subst_rawDiagonal,Syn.shift] using hEnv.shift.shift
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianValueNormalizerExtensionality.raw_cross_bound f g one one _ _ _ (var 1) (var 0)
      (point_regular f _ hf2) (point_regular g _ hg2) he2)

theorem recode_left_distance (a b A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded a b A B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianFastValueCut.recode a) b A B := by
  have z := distance_radius_mono _ _ zero one zero B (le_refl _) hB
    (le_of_eq_add (d := zero) (by ipra_ring)) (GaussianFastValueCut.recode_distance (Γ := Γ) a)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hB z h)

/-- A normalized sample is close to the original observation at its own
requested precision, with a computed constant independent of that precision. -/
theorem normalized_to_sample (f : PR 2) (L x k : PTm n)
    (h : Γ ⊢[PRAAx] GaussianFastValueCut.regular f L x) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (GaussianFastValueCut.nameF f) k (GaussianFastValueCut.nameData L x))
      (ap2 f k x) (L+one) (unit k) := by
  let r := GaussianFastValueCut.exponent L k
  have denominator := positive_product (Γ := Γ) _ _ (unit_positive r) (unit_positive k)
  have raw := GaussianFastValueCut.regular_at f L x r k h
  have recoded := recode_left_distance _ _ _ _ denominator raw
  have query := mul_le_mul_right (unit k) (GaussianFastValueCut.query_budget (Γ := Γ) L k)
  have comparison : Γ ⊢[PRAAx]
      le ((L*(unit r+unit k))*unit k) ((L+one)*(unit r*unit k)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (L*unit r*unit k)) query)
  exact distance_congr (GaussianFastValueCut.name_at f L x k).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ denominator (unit_positive k) comparison recoded)

theorem add_sample_error (f g : PR 2) (x y k : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (addF f g) k (addData x y))
      (qadd (ap2 f k x) (ap2 g k y)) three (unit k) :=
  distance_congr (.eqRefl _) (GaussianNameArithmetic.add_raw_at f g k x y) (.eqRefl _) (.eqRefl _)
    (normalized_to_sample (addRawF f g) two (GaussianNameArithmetic.data x y) k
      (GaussianNameArithmetic.add_regular f g x y hf hg))

theorem multiply_sample_error (f g : PR 2) (x y k : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF f g) k (multiplyData f g x y))
      (qmul (ap2 f k x) (ap2 g k y)) (multiplyModulus f g x y+one) (unit k) :=
  distance_congr (.eqRefl _) (GaussianNameArithmetic.multiply_raw_at f g k x y) (.eqRefl _) (.eqRefl _)
    (normalized_to_sample (multiplyRawF f g) (multiplyModulus f g x y) (GaussianNameArithmetic.data x y) k
      (GaussianNameArithmetic.multiply_regular f g x y hf hg))

theorem through_identity (a b u v A C B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hau : Γ ⊢[PRAAx] distanceBounded a u A B)
    (hbv : Γ ⊢[PRAAx] distanceBounded b v C B) (he : Γ ⊢[PRAAx] u ≐ v) : Γ ⊢[PRAAx]
    distanceBounded a b (A+C) B :=
  distance_triangle_same _ _ _ _ _ _ hB hau
    (distance_congr he.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (distance_symmetric _ _ _ _ hB hbv))

theorem add_commutative_at (f g : PR 2) (x y k : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (addF f g) k (addData x y))
      (ap2 (addF g f) k (addData y x)) (three+three) (unit k) :=
  through_identity _ _ _ _ _ _ _ (unit_positive k) (add_sample_error f g x y k hf hg)
    (add_sample_error g f y x k hg hf) (GaussianReciprocalHorner.qadd_commutative _ _)

theorem multiply_commutative_at (f g : PR 2) (x y k : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF f g) k (multiplyData f g x y))
      (ap2 (multiplyF g f) k (multiplyData g f y x))
      ((multiplyModulus f g x y+one)+(multiplyModulus g f y x+one)) (unit k) :=
  through_identity _ _ _ _ _ _ _ (unit_positive k) (multiply_sample_error f g x y k hf hg)
    (multiply_sample_error g f y x k hg hf) (GaussianRationalPowerAlgebra.qmul_commutative _ _)

theorem add_commutative (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    crossEquivalent (addF f g) (addF g f) (addData x y) (addData y x) := by
  apply equivalent_of_envelope _ _ _ _ (three+three)
    (GaussianNameArithmetic.add_fast f g x y hf hg) (GaussianNameArithmetic.add_fast g f y x hg hf)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] pointCN g (Syn.shift y) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hg.shift
  simpa only [Syn.shift,GaussianNameArithmetic.subst_addData,three,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    add_commutative_at f g (Syn.shift x) (Syn.shift y) (var 0) hs ht

theorem multiply_commutative (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF f g) (multiplyF g f)
      (multiplyData f g x y) (multiplyData g f y x) := by
  apply equivalent_of_envelope _ _ _ _
    ((multiplyModulus f g x y+one)+(multiplyModulus g f y x+one))
    (GaussianNameArithmetic.multiply_fast f g x y hf hg) (GaussianNameArithmetic.multiply_fast g f y x hg hf)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] pointCN g (Syn.shift y) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hg.shift
  simpa only [Syn.shift,GaussianNameArithmetic.subst_multiplyData,GaussianNameArithmetic.subst_multiplyModulus,
    PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    multiply_commutative_at f g (Syn.shift x) (Syn.shift y) (var 0) hs ht

theorem sum_left_error (a b u A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded a b A B) : Γ ⊢[PRAAx]
    distanceBounded (qadd a u) (qadd b u) A B :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance a b u u A zero B hB h
      (GaussianRationalPowerDifference.distance_refl_zero u B hB))

theorem sum_right_error (a u v A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    distanceBounded (qadd a u) (qadd a v) A B :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance a a u v zero A B hB
      (GaussianRationalPowerDifference.distance_refl_zero a B hB) h)

/-- Keep the left sample and pay for approximating the right sample in a normalized sum. -/
theorem add_sample_error_right (f g : PR 2) (x y p b K : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 g p y) b K (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (addF f g) p (addData x y)) (qadd (ap2 f p x) b) (three+K) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p) (add_sample_error f g x y p hf hg)
    (sum_right_error (ap2 f p x) (ap2 g p y) b K (unit p) (unit_positive p) h)

theorem add_associative_at (f g h : PR 2) (x y z k : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h z) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (addF (addF f g) h) k (addData (addData x y) z))
      (ap2 (addF f (addF g h)) k (addData x (addData y z)))
      ((three+three)+(three+three)) (unit k) := by
  have hfg := GaussianNameArithmetic.add_fast f g x y hf hg
  have hgh := GaussianNameArithmetic.add_fast g h y z hg hh
  have lhs := distance_triangle_same _ _ _ _ _ _ (unit_positive k)
    (add_sample_error (addF f g) h (addData x y) z k hfg hh)
    (sum_left_error _ _ _ _ _ (unit_positive k) (add_sample_error f g x y k hf hg))
  have rhs := distance_triangle_same _ _ _ _ _ _ (unit_positive k)
    (add_sample_error f (addF g h) x (addData y z) k hf hgh)
    (sum_right_error _ _ _ _ _ (unit_positive k) (add_sample_error g h y z k hg hh))
  exact through_identity _ _ _ _ _ _ _ (unit_positive k) lhs rhs
    (GaussianRationalSumAlgebra.qadd_associative _ _ _)

theorem add_associative (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h z) : Γ ⊢[PRAAx]
    crossEquivalent (addF (addF f g) h) (addF f (addF g h))
      (addData (addData x y) z) (addData x (addData y z)) := by
  apply equivalent_of_envelope _ _ _ _ ((three+three)+(three+three))
    (GaussianNameArithmetic.add_fast _ _ _ _ (GaussianNameArithmetic.add_fast f g x y hf hg) hh)
    (GaussianNameArithmetic.add_fast _ _ _ _ hf (GaussianNameArithmetic.add_fast g h y z hg hh))
  refine .allI ?_
  have hf1 : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  have hg1 : Γ.map Fm.shift ⊢[PRAAx] pointCN g (Syn.shift y) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hg.shift
  have hh1 : Γ.map Fm.shift ⊢[PRAAx] pointCN h (Syn.shift z) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hh.shift
  simpa only [Syn.shift,GaussianNameArithmetic.subst_addData,three,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    add_associative_at f g h (Syn.shift x) (Syn.shift y) (Syn.shift z) (var 0) hf1 hg1 hh1

theorem product_left_error (a b u A B U V : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded a b A B)
    (hu : Γ ⊢[PRAAx] bounded u U one) (hb : Γ ⊢[PRAAx] bounded b V one) : Γ ⊢[PRAAx]
    distanceBounded (qmul a u) (qmul b u) (A*U) B :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.product_distance a b u u A zero B U V hB h
      (GaussianRationalPowerDifference.distance_refl_zero u B hB) hu hb)

theorem product_right_error (a u v A B U V : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded u v A B)
    (hu : Γ ⊢[PRAAx] bounded u U one) (ha : Γ ⊢[PRAAx] bounded a V one) : Γ ⊢[PRAAx]
    distanceBounded (qmul a u) (qmul a v) (V*A) B :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.product_distance a a u v zero A B U V hB
      (GaussianRationalPowerDifference.distance_refl_zero a B hB) h hu ha)

def multiplyAssociativeBudget (f g h : PR 2) (x y z : PTm n) : PTm n :=
  (multiplyModulus (multiplyF f g) h (multiplyData f g x y) z+one+
    (multiplyModulus f g x y+one)*GaussianNameBounds.U h z)+
  (multiplyModulus f (multiplyF g h) x (multiplyData g h y z)+one+
    GaussianNameBounds.U f x*(multiplyModulus g h y z+one))

ipra_subst multiplyAssociativeBudget

theorem multiply_associative_at (f g h : PR 2) (x y z k : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h z) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (multiplyF (multiplyF f g) h) k (multiplyData (multiplyF f g) h (multiplyData f g x y) z))
      (ap2 (multiplyF f (multiplyF g h)) k (multiplyData f (multiplyF g h) x (multiplyData g h y z)))
      (multiplyAssociativeBudget f g h x y z) (unit k) := by
  have hfg := GaussianNameArithmetic.multiply_fast f g x y hf hg
  have hgh := GaussianNameArithmetic.multiply_fast g h y z hg hh
  have bf := GaussianNameBounds.sample_bound f x k hf
  have bg := GaussianNameBounds.sample_bound g y k hg
  have bh := GaussianNameBounds.sample_bound h z k hh
  have bfg : Γ ⊢[PRAAx] bounded (qmul (ap2 f k x) (ap2 g k y))
      (GaussianNameBounds.U f x*GaussianNameBounds.U g y) one :=
    GaussianRationalReciprocal.bounded_product_one bf bg
  have lhs := distance_triangle_same _ _ _ _ _ _ (unit_positive k)
    (multiply_sample_error (multiplyF f g) h (multiplyData f g x y) z k hfg hh)
    (product_left_error _ _ _ _ _ _ _ (unit_positive k)
      (multiply_sample_error f g x y k hf hg) bh bfg)
  have rhs := distance_triangle_same _ _ _ _ _ _ (unit_positive k)
    (multiply_sample_error f (multiplyF g h) x (multiplyData g h y z) k hf hgh)
    (product_right_error _ _ _ _ _ _ _ (unit_positive k)
      (multiply_sample_error g h y z k hg hh) (GaussianNameBounds.sample_bound (multiplyF g h) (multiplyData g h y z) k hgh) bf)
  exact through_identity _ _ _ _ _ _ _ (unit_positive k) lhs rhs
    (GaussianReciprocalHorner.qmul_associative _ _ _)

theorem multiply_associative (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h z) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (multiplyF f g) h) (multiplyF f (multiplyF g h))
      (multiplyData (multiplyF f g) h (multiplyData f g x y) z)
      (multiplyData f (multiplyF g h) x (multiplyData g h y z)) := by
  apply equivalent_of_envelope _ _ _ _ (multiplyAssociativeBudget f g h x y z)
    (GaussianNameArithmetic.multiply_fast _ _ _ _ (GaussianNameArithmetic.multiply_fast f g x y hf hg) hh)
    (GaussianNameArithmetic.multiply_fast _ _ _ _ hf (GaussianNameArithmetic.multiply_fast g h y z hg hh))
  refine .allI ?_
  have hf1 : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  have hg1 : Γ.map Fm.shift ⊢[PRAAx] pointCN g (Syn.shift y) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hg.shift
  have hh1 : Γ.map Fm.shift ⊢[PRAAx] pointCN h (Syn.shift z) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hh.shift
  simpa only [Syn.shift,GaussianNameArithmetic.subst_multiplyData,subst_multiplyAssociativeBudget] using
    multiply_associative_at f g h (Syn.shift x) (Syn.shift y) (Syn.shift z) (var 0) hf1 hg1 hh1

def distributiveBudget (f g h : PR 2) (x y z : PTm n) : PTm n :=
  (multiplyModulus f (addF g h) x (addData y z)+one+GaussianNameBounds.U f x*three)+
    (three+((multiplyModulus f g x y+one)+(multiplyModulus f h x z+one)))

ipra_subst distributiveBudget [three]

theorem distributive_at (f g h : PR 2) (x y z k : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h z) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (multiplyF f (addF g h)) k (multiplyData f (addF g h) x (addData y z)))
      (ap2 (addF (multiplyF f g) (multiplyF f h)) k
        (addData (multiplyData f g x y) (multiplyData f h x z)))
      (distributiveBudget f g h x y z) (unit k) := by
  have hgh := GaussianNameArithmetic.add_fast g h y z hg hh
  have hfg := GaussianNameArithmetic.multiply_fast f g x y hf hg
  have hfh := GaussianNameArithmetic.multiply_fast f h x z hf hh
  have lhs := distance_triangle_same _ _ _ _ _ _ (unit_positive k)
    (multiply_sample_error f (addF g h) x (addData y z) k hf hgh)
    (product_right_error _ _ _ _ _ _ _ (unit_positive k) (add_sample_error g h y z k hg hh)
      (GaussianNameBounds.sample_bound (addF g h) (addData y z) k hgh)
      (GaussianNameBounds.sample_bound f x k hf))
  have rhs := distance_triangle_same _ _ _ _ _ _ (unit_positive k)
    (add_sample_error (multiplyF f g) (multiplyF f h) (multiplyData f g x y) (multiplyData f h x z) k hfg hfh)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ (unit_positive k)
      (multiply_sample_error f g x y k hf hg) (multiply_sample_error f h x z k hf hh))
  exact through_identity _ _ _ _ _ _ _ (unit_positive k) lhs rhs
    (GaussianRationalCoefficientScaling.qmul_add _ _ _)

theorem distributive (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h z) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF f (addF g h)) (addF (multiplyF f g) (multiplyF f h))
      (multiplyData f (addF g h) x (addData y z))
      (addData (multiplyData f g x y) (multiplyData f h x z)) := by
  apply equivalent_of_envelope _ _ _ _ (distributiveBudget f g h x y z)
    (GaussianNameArithmetic.multiply_fast _ _ _ _ hf (GaussianNameArithmetic.add_fast g h y z hg hh))
    (GaussianNameArithmetic.add_fast _ _ _ _ (GaussianNameArithmetic.multiply_fast f g x y hf hg)
      (GaussianNameArithmetic.multiply_fast f h x z hf hh))
  refine .allI ?_
  have hf1 : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  have hg1 : Γ.map Fm.shift ⊢[PRAAx] pointCN g (Syn.shift y) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hg.shift
  have hh1 : Γ.map Fm.shift ⊢[PRAAx] pointCN h (Syn.shift z) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hh.shift
  simpa only [Syn.shift,GaussianNameArithmetic.subst_multiplyData,GaussianNameArithmetic.subst_addData,
    subst_distributiveBudget] using
    distributive_at f g h (Syn.shift x) (Syn.shift y) (Syn.shift z) (var 0) hf1 hg1 hh1

def zeroF : PR 2 := PTm.toPR (qzero : PTm 2)
def oneF : PR 2 := PTm.toPR (qone : PTm 2)
theorem zero_at (k x : PTm n) : Γ ⊢[PRAAx] ap2 zeroF k x ≐ qzero := by
  simpa [zeroF,ap2] using toPR_eq (Γ := Γ) (qzero : PTm 2) ![k,x]
theorem one_at (k x : PTm n) : Γ ⊢[PRAAx] ap2 oneF k x ≐ qone := by
  simpa [oneF,ap2] using toPR_eq (Γ := Γ) (qone : PTm 2) ![k,x]

private theorem distance_of_common_sample (s t : PTm n) {u v a : PTm n}
    (hu : Γ ⊢[PRAAx] u ≐ a) (hv : Γ ⊢[PRAAx] v ≐ a) :
    Γ ⊢[PRAAx] distanceBounded u v (unit s+unit t) (unit s*unit t) := by
  have hD := positive_product _ _ (unit_positive (Γ := Γ) s) (unit_positive t)
  exact distance_congr hu.eqSymm hv.eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono a a zero _ _ _ hD hD
      (le_congr (by ipra_ring) (.eqRefl _) (zero_le _))
      (GaussianRationalPowerDifference.distance_refl_zero a _ hD))

private theorem cross_of_common_sample (f g : PR 2) (x y : PTm n) {value : PTm (n+2)}
    (hx : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] ap2 f (var 1) (Syn.shift (Syn.shift x)) ≐ value)
    (hy : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] ap2 g (var 0) (Syn.shift (Syn.shift y)) ≐ value) :
    Γ ⊢[PRAAx] crossEquivalent f g x y :=
  .allI (.allI (distance_of_common_sample (var 1) (var 0) hx hy))

/-- The program that returns its parameter samples it exactly. -/
theorem constant_parameter_at (p a : PTm n) :
    Γ ⊢[PRAAx] ap2 (PTm.toPR (var 1 : PTm 2)) p a ≐ a := by
  simpa [ap2] using toPR_eq (Γ := Γ) (var 1 : PTm 2) ![p,a]

theorem constant_parameter_regularity (a s t : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (PTm.toPR (var 1 : PTm 2)) s a)
      (ap2 (PTm.toPR (var 1 : PTm 2)) t a) (unit s+unit t) (unit s*unit t) :=
  distance_of_common_sample s t (constant_parameter_at s a) (constant_parameter_at t a)

theorem constant_parameter_regular (a : PTm n) : Γ ⊢[PRAAx] pointCN (PTm.toPR (var 1 : PTm 2)) a :=
  .allI (.allI (constant_parameter_regularity (Syn.shift (Syn.shift a)) (var 1) (var 0)))

/-- Changing the input datum of the constant zero program preserves its name. -/
theorem zero_name_cross (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x y :=
  cross_of_common_sample zeroF zeroF x y (zero_at _ _) (zero_at _ _)

/-- Changing the input datum of the constant one program preserves its name. -/
theorem one_name_cross (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent oneF oneF x y :=
  cross_of_common_sample oneF oneF x y (one_at _ _) (one_at _ _)

theorem zero_fast (x : PTm n) : Γ ⊢[PRAAx] pointCN zeroF x :=
  zero_name_cross x x

theorem one_fast (x : PTm n) : Γ ⊢[PRAAx] pointCN oneF x :=
  one_name_cross x x

/-- Compare the parameter sampler at zero with the constant zero program. -/
theorem constant_zero_cross (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (PTm.toPR (var 1 : PTm 2)) zeroF qzero x := by
  refine cross_of_common_sample _ _ _ _ ?_ (zero_at _ _)
  simpa only [Syn.shift,GaussianRationalHorner.subst_qzero] using
    constant_parameter_at (var 1) (Syn.shift (Syn.shift (qzero : PTm n)))

/-- Compare the parameter sampler at one with the constant one program. -/
theorem constant_one_cross (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (PTm.toPR (var 1 : PTm 2)) oneF qone x := by
  refine cross_of_common_sample _ _ _ _ ?_ (one_at _ _)
  simpa only [Syn.shift,GaussianRationalReciprocal.subst_qone] using
    constant_parameter_at (var 1) (Syn.shift (Syn.shift (qone : PTm n)))

private theorem multiply_zero_raw_at (f g : PR 2) (x y p : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNameArithmetic.multiplyRaw f g
      (GaussianFastValueCut.exponent (multiplyModulus f g x y) p) x y ≐ qzero) :
    Γ ⊢[PRAAx] ap2 (multiplyF f g) p (multiplyData f g x y) ≐ qzero :=
  (GaussianNameArithmetic.multiply_at f g x y p).eqTrans
    ((GaussianNameArithmetic.recode_congr h).eqTrans
      (GaussianRationalHorner.canonical_unique _ _ _ _
        (GaussianFastValueCut.recode_canonical _) GaussianRationalSyntheticDivision.qzero_canonical
        (GaussianRationalL1.raw_den_positive _) (GaussianFastValueCut.recode_represents _)
        (GaussianRationalL1.raw_represents _)))

/-- An exact zero parameter annihilates every observation of the product. -/
theorem constant_zero_multiply_at (f : PR 2) (p c x : PTm n) (hc : Γ ⊢[PRAAx] c ≐ qzero) :
    Γ ⊢[PRAAx] ap2 (multiplyF (PTm.toPR (var 1 : PTm 2)) f) p
      (multiplyData (PTm.toPR (var 1 : PTm 2)) f c x) ≐ qzero :=
  multiply_zero_raw_at _ _ c x p
    ((GaussianRationalSyntheticDivision.qmul_congr ((constant_parameter_at _ c).eqTrans hc) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_left _))

private theorem multiply_zero_samples_cross (f g : PR 2) (x y anchor : PTm n)
    (h : ∀ k : PTm (n+2), (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianNameArithmetic.multiplyRaw f g k (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) ≐ qzero) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f g) zeroF (multiplyData f g x y) anchor := by
  refine cross_of_common_sample _ _ _ _ ?_ (zero_at _ _)
  simpa only [Syn.shift,GaussianNameArithmetic.subst_multiplyData] using
    multiply_zero_raw_at f g (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (var 1) (h _)

theorem multiply_zero_left (f : PR 2) (x y anchor : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF zeroF f) zeroF (multiplyData zeroF f x y) anchor :=
  multiply_zero_samples_cross zeroF f x y anchor fun k =>
    (GaussianRationalSyntheticDivision.qmul_congr (zero_at k _) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_left _)

theorem multiply_zero_right (f : PR 2) (x y anchor : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f zeroF) zeroF (multiplyData f zeroF x y) anchor :=
  multiply_zero_samples_cross f zeroF x y anchor fun k =>
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (zero_at k _)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_right _)

/-- Multiply a parameter sampler at zero by any sampler and read zero. -/
theorem constant_zero_multiply (f : PR 2) (x anchor : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (PTm.toPR (var 1 : PTm 2)) f) zeroF
      (multiplyData (PTm.toPR (var 1 : PTm 2)) f qzero x) anchor := by
  refine cross_of_common_sample _ _ _ _ ?_ (zero_at _ _)
  simpa only [Syn.shift,GaussianNameArithmetic.subst_multiplyData,GaussianRationalHorner.subst_qzero] using
    constant_zero_multiply_at f (var 1) qzero (Syn.shift (Syn.shift x)) (.eqRefl _)

/-- Multiply any sampler by a parameter sampler at zero and read zero. -/
theorem multiply_constant_zero (f : PR 2) (x anchor : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f (PTm.toPR (var 1 : PTm 2))) zeroF
      (multiplyData f (PTm.toPR (var 1 : PTm 2)) x qzero) anchor := by
  refine multiply_zero_samples_cross _ _ x qzero anchor fun k => ?_
  have hz : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      ap2 (PTm.toPR (var 1 : PTm 2)) k (Syn.shift (Syn.shift (qzero : PTm n))) ≐ qzero := by
    simpa only [Syn.shift,GaussianRationalHorner.subst_qzero] using
      constant_parameter_at (Γ := (Γ.map Fm.shift).map Fm.shift) k (qzero : PTm (n+2))
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) hz).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem add_zero_recode (a : PTm n) : Γ ⊢[PRAAx] qadd a qzero ≐ GaussianFastValueCut.recode a := by
  have d := GaussianRationalL1.raw_den_positive (Γ := Γ) a
  have rep := GaussianRationalHorner.qadd_represents a qzero (GaussianRationalL1.rawGaussian a)
    ComplexLogarithmRemainder.zeroCode (GaussianRationalL1.rawDen a) d
    (GaussianRationalL1.raw_represents a) (GaussianRationalHorner.zero_represents _)
  apply GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianFastValueCut.recode_canonical _) d (hrv := GaussianFastValueCut.recode_represents a)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := rep)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero] <;> ring

theorem multiply_one_recode (a : PTm n) : Γ ⊢[PRAAx] qmul a qone ≐ GaussianFastValueCut.recode a := by
  have d := GaussianRationalL1.raw_den_positive (Γ := Γ) a
  have rep := GaussianRationalHorner.qmul_represents a qone (GaussianRationalL1.rawGaussian a)
    (ComplexLogarithmRemainder.scale (GaussianRationalL1.rawDen a) ComplexLogarithmRemainder.oneCode)
    (GaussianRationalL1.rawDen a) (GaussianRationalL1.rawDen a) d d
    (GaussianRationalL1.raw_represents a) (GaussianRationalReciprocal.qone_represents_scaled _)
  have target := GaussianRationalHorner.represents_rescale (GaussianFastValueCut.recode a)
    (GaussianRationalL1.rawGaussian a) (GaussianRationalL1.rawDen a) (GaussianRationalL1.rawDen a)
    (GaussianFastValueCut.recode_represents (Γ := Γ) a)
  apply GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianFastValueCut.recode_canonical _) (positive_product _ _ d d) (hrv := target)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := rep)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring

theorem add_zero_at (f : PR 2) (x k : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (addF f zeroF) k (addData x x)) (ap2 f k x) three (unit k) := by
  have first := distance_congr (.eqRefl _)
    ((GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (zero_at k x)).eqTrans
      (add_zero_recode (ap2 f k x))) (.eqRefl _) (.eqRefl _)
    (add_sample_error f zeroF x x k hf (zero_fast x))
  have last := distance_radius_mono (Γ := Γ) _ _ zero one zero (unit k) (le_refl _) (unit_positive k)
    (le_of_eq_add (d := zero) (by ipra_ring)) (GaussianFastValueCut.recode_distance (ap2 f k x))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive k) first last)

theorem multiply_one_at (f : PR 2) (x k : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF f oneF) k (multiplyData f oneF x x)) (ap2 f k x)
      (multiplyModulus f oneF x x+one) (unit k) := by
  have first := distance_congr (.eqRefl _)
    ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (one_at k x)).eqTrans
      (multiply_one_recode (ap2 f k x))) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error f oneF x x k hf (one_fast x))
  have last := distance_radius_mono (Γ := Γ) _ _ zero one zero (unit k) (le_refl _) (unit_positive k)
    (le_of_eq_add (d := zero) (by ipra_ring)) (GaussianFastValueCut.recode_distance (ap2 f k x))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive k) first last)

theorem add_zero (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    crossEquivalent (addF f zeroF) f (addData x x) x := by
  apply equivalent_of_envelope _ _ _ _ three (GaussianNameArithmetic.add_fast f zeroF x x hf (zero_fast x)) hf
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  simpa only [Syn.shift,GaussianNameArithmetic.subst_addData,three,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using add_zero_at f (Syn.shift x) (var 0) hs

theorem multiply_one (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF f oneF) f (multiplyData f oneF x x) x := by
  apply equivalent_of_envelope _ _ _ _ (multiplyModulus f oneF x x+one)
    (GaussianNameArithmetic.multiply_fast f oneF x x hf (one_fast x)) hf
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  simpa only [Syn.shift,GaussianNameArithmetic.subst_multiplyData,GaussianNameArithmetic.subst_multiplyModulus,
    PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using multiply_one_at f (Syn.shift x) (var 0) hs

def negativeRawF (f : PR 2) : PR 2 := GaussianFastValueCut.differenceF zeroF f
def negativeF (f : PR 2) : PR 2 := GaussianFastValueCut.nameF (negativeRawF f)
def negativeData (x : PTm n) : PTm n := GaussianFastValueCut.nameData (one+one) x
ipra_subst negativeData

theorem negative_raw_at (f : PR 2) (x k : PTm n) : Γ ⊢[PRAAx]
    ap2 (negativeRawF f) k x ≐ qsub qzero (ap2 f k x) :=
  (GaussianFastValueCut.difference_at zeroF f k x).eqTrans
    (GaussianRationalSyntheticDivision.qsub_congr (zero_at k x) (.eqRefl _))

theorem negative_regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular (negativeRawF f) (one+one) x :=
  GaussianFastValueCut.difference_regular zeroF f one one x
    (point_regular zeroF x (zero_fast x)) (point_regular f x hf)

theorem negative_fast (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    pointCN (negativeF f) (negativeData x) :=
  GaussianFastValueCut.name_fast (negativeRawF f) (one+one) x (negative_regular f x hf)
theorem negative_canonical (f : PR 2) (x k : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 (negativeF f) k (negativeData x)) :=
  GaussianFastValueCut.name_canonical (negativeRawF f) (one+one) x k
theorem negative_at (f : PR 2) (x k : PTm n) : Γ ⊢[PRAAx]
    ap2 (negativeF f) k (negativeData x) ≐ GaussianFastValueCut.recode
      (qsub qzero (ap2 f (GaussianFastValueCut.exponent (one+one) k) x)) :=
  (GaussianFastValueCut.name_at (negativeRawF f) (one+one) x k).eqTrans
    (GaussianNameArithmetic.recode_congr (negative_raw_at f x _))

theorem negative_sample_error (f : PR 2) (x k : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (negativeF f) k (negativeData x)) (qsub qzero (ap2 f k x)) three (unit k) :=
  distance_congr (.eqRefl _) (negative_raw_at f x k) (by unfold three; ipra_ring) (.eqRefl _)
    (normalized_to_sample (negativeRawF f) (one+one) x k (negative_regular f x hf))

theorem additive_inverse_value (a : PTm n) : Γ ⊢[PRAAx] qadd a (qsub qzero a) ≐ qzero := by
  have e : Γ ⊢[PRAAx] qsub qzero a ≐ GaussianRationalMetric.qnegative a :=
    (GaussianReciprocalHorner.qadd_commutative qzero (GaussianRationalMetric.qnegative a)).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalMetric.qnegative_canonical a))
  exact (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) e).eqTrans
    (GaussianCoefficientNormOrder.qsub_self a)

theorem add_negative_at (f : PR 2) (x k : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (addF f (negativeF f)) k (addData x (negativeData x)))
      (ap2 zeroF k x) (three+three) (unit k) := by
  have hneg := negative_fast f x hf
  have second := sum_right_error (ap2 f k x) _ _ _ _ (unit_positive k) (negative_sample_error f x k hf)
  have joined := distance_triangle_same _ _ _ _ _ _ (unit_positive k)
    (add_sample_error f (negativeF f) x (negativeData x) k hf hneg) second
  exact distance_congr (.eqRefl _)
    ((additive_inverse_value (ap2 f k x)).eqTrans (zero_at k x).eqSymm) (.eqRefl _) (.eqRefl _) joined

theorem add_negative (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    crossEquivalent (addF f (negativeF f)) zeroF (addData x (negativeData x)) x := by
  apply equivalent_of_envelope _ _ _ _ (three+three)
    (GaussianNameArithmetic.add_fast _ _ _ _ hf (negative_fast f x hf)) (zero_fast x)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  simpa only [Syn.shift,GaussianNameArithmetic.subst_addData,subst_negativeData,three,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using add_negative_at f (Syn.shift x) (var 0) hs

theorem add_zero_left (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    crossEquivalent (addF zeroF f) f (addData x x) x :=
  GaussianNameEquivalence.cross_trans _ _ _ _ _ _
    (add_commutative zeroF f x x (zero_fast x) hf) (add_zero f x hf)
theorem multiply_one_left (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF oneF f) f (multiplyData oneF f x x) x :=
  GaussianNameEquivalence.cross_trans _ _ _ _ _ _
    (multiply_commutative oneF f x x (one_fast x) hf) (multiply_one f x hf)

/-- A name equivalent to one can be dropped from the left of a product. -/
theorem multiply_unit_left (u f : PR 2) (a x anchor : PTm n)
    (hu : Γ ⊢[PRAAx] pointCN u a) (hf : Γ ⊢[PRAAx] pointCN f x)
    (h : Γ ⊢[PRAAx] crossEquivalent u oneF a anchor) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF u f) f (multiplyData u f a x) x := by
  have unitAt := GaussianNameEquivalence.cross_trans u oneF oneF a anchor x h (one_name_cross anchor x)
  have product := GaussianNameArithmetic.multiply_equivalent u oneF f f a x x x hu (one_fast x) hf hf
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ unitAt) (GaussianNameEquivalence.diagonal_refl f x)
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ product (multiply_one_left f x hf)

/-- A name equivalent to one can be dropped from the right of a product. -/
theorem multiply_unit_right (f u : PR 2) (x a anchor : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hu : Γ ⊢[PRAAx] pointCN u a)
    (h : Γ ⊢[PRAAx] crossEquivalent u oneF a anchor) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f u) f (multiplyData f u x a) x := by
  have unitAt := GaussianNameEquivalence.cross_trans u oneF oneF a anchor x h (one_name_cross anchor x)
  have product := GaussianNameArithmetic.multiply_equivalent f f u oneF x x a x hf hf hu (one_fast x)
    (GaussianNameEquivalence.diagonal_refl f x) (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ unitAt)
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ product (multiply_one f x hf)

theorem right_distributive (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h z) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (addF f g) h) (addF (multiplyF f h) (multiplyF g h))
      (multiplyData (addF f g) h (addData x y) z)
      (addData (multiplyData f h x z) (multiplyData g h y z)) := by
  have first := multiply_commutative (addF f g) h (addData x y) z
    (GaussianNameArithmetic.add_fast f g x y hf hg) hh
  have middle := distributive h f g z x y hh hf hg
  have last := GaussianNameArithmetic.add_equivalent
    (multiplyF h f) (multiplyF f h) (multiplyF h g) (multiplyF g h)
    (multiplyData h f z x) (multiplyData f h x z) (multiplyData h g z y) (multiplyData g h y z)
    (GaussianNameArithmetic.multiply_fast h f z x hh hf) (GaussianNameArithmetic.multiply_fast f h x z hf hh)
    (GaussianNameArithmetic.multiply_fast h g z y hh hg) (GaussianNameArithmetic.multiply_fast g h y z hg hh)
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (multiply_commutative h f z x hh hf))
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (multiply_commutative h g z y hh hg))
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ first
    (GaussianNameEquivalence.cross_trans _ _ _ _ _ _ middle last)

theorem negative_equivalent (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (he : Γ ⊢[PRAAx] GaussianNameEquivalence.diagonalEquivalent f g x y) : Γ ⊢[PRAAx]
    crossEquivalent (negativeF f) (negativeF g) (negativeData x) (negativeData y) := by
  apply GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ (one+one) (one+one) x y two
    (negative_regular f x hf) (negative_regular g y hg)
  refine .allI ?_
  have he1 := GaussianNameEquivalence.shift_diagonalEquivalent he
  have e : Γ.map Fm.shift ⊢[PRAAx]
      distanceBounded (ap2 (negativeRawF f) (var 0) (Syn.shift x))
        (ap2 (negativeRawF g) (var 0) (Syn.shift y)) two (unit (var 0)) :=
    distance_congr (negative_raw_at f (Syn.shift x) (var 0)).eqSymm
      (negative_raw_at g (Syn.shift y) (var 0)).eqSymm (by ipra_ring) (.eqRefl _)
      (GaussianFastValueCut.distance_difference_same _ _ _ _ zero two _ (unit_positive (var 0))
        (GaussianRationalPowerDifference.distance_refl_zero qzero (unit (var 0)) (unit_positive (var 0)))
        (GaussianNameEquivalence.diagonal_at f g _ _ (var 0) he1))
  simpa only [Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using e

def tripleInput (f g h : PR 2) (x y z : PTm n) : Fm PTm n :=
  pointCN f x ⋏ (pointCN g y ⋏ pointCN h z)
ipra_subst tripleInput

theorem normalized_observation_error_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianFastValueCut.regular f (var 0) (var 1) ⟶
      distanceBounded (ap2 (GaussianFastValueCut.nameF f) (var 2)
        (GaussianFastValueCut.nameData (var 0) (var 1))) (ap2 f (var 2) (var 1))
        ((var 0)+one) (unit (var 2))) :=
  closeUniv 3 (.impI (normalized_to_sample f _ _ _ Prf.hyp0))

theorem finite_envelope_equivalence_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianNameArithmetic.input f g (var 0) (var 1) ⋏
      GaussianValueNormalizerExtensionality.rawDiagonal f g (var 0) (var 1) (var 2) ⟶
      crossEquivalent f g (var 0) (var 1)) :=
  closeUniv 3 (.impI (equivalent_of_envelope f g _ _ _
    (.andE₁ (.andE₁ Prf.hyp0)) (.andE₂ (.andE₁ Prf.hyp0)) (.andE₂ Prf.hyp0)))

theorem actual_addition_commutativity_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianNameArithmetic.input f g (var 0) (var 1) ⟶
      crossEquivalent (addF f g) (addF g f) (addData (var 0) (var 1)) (addData (var 1) (var 0))) :=
  closeUniv 2 (.impI (add_commutative f g _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))
theorem actual_multiplication_commutativity_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianNameArithmetic.input f g (var 0) (var 1) ⟶
      crossEquivalent (multiplyF f g) (multiplyF g f)
        (multiplyData f g (var 0) (var 1)) (multiplyData g f (var 1) (var 0))) :=
  closeUniv 2 (.impI (multiply_commutative f g _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))

theorem actual_addition_associativity_closed (f g h : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (tripleInput f g h (var 0) (var 1) (var 2) ⟶
      crossEquivalent (addF (addF f g) h) (addF f (addF g h))
        (addData (addData (var 0) (var 1)) (var 2)) (addData (var 0) (addData (var 1) (var 2)))) :=
  closeUniv 3 (.impI (add_associative f g h _ _ _ (.andE₁ Prf.hyp0)
    (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))))
theorem actual_multiplication_associativity_closed (f g h : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (tripleInput f g h (var 0) (var 1) (var 2) ⟶
      crossEquivalent (multiplyF (multiplyF f g) h) (multiplyF f (multiplyF g h))
        (multiplyData (multiplyF f g) h (multiplyData f g (var 0) (var 1)) (var 2))
        (multiplyData f (multiplyF g h) (var 0) (multiplyData g h (var 1) (var 2)))) :=
  closeUniv 3 (.impI (multiply_associative f g h _ _ _ (.andE₁ Prf.hyp0)
    (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))))

theorem actual_left_distribution_closed (f g h : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (tripleInput f g h (var 0) (var 1) (var 2) ⟶
      crossEquivalent (multiplyF f (addF g h)) (addF (multiplyF f g) (multiplyF f h))
        (multiplyData f (addF g h) (var 0) (addData (var 1) (var 2)))
        (addData (multiplyData f g (var 0) (var 1)) (multiplyData f h (var 0) (var 2)))) :=
  closeUniv 3 (.impI (distributive f g h _ _ _ (.andE₁ Prf.hyp0)
    (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))))
theorem actual_right_distribution_closed (f g h : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (tripleInput f g h (var 0) (var 1) (var 2) ⟶
      crossEquivalent (multiplyF (addF f g) h) (addF (multiplyF f h) (multiplyF g h))
        (multiplyData (addF f g) h (addData (var 0) (var 1)) (var 2))
        (addData (multiplyData f h (var 0) (var 2)) (multiplyData g h (var 1) (var 2)))) :=
  closeUniv 3 (.impI (right_distributive f g h _ _ _ (.andE₁ Prf.hyp0)
    (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))))

theorem actual_zero_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pointCN zeroF (var 0) ⋏ ap2 zeroF (var 1) (var 0) ≐ qzero) :=
  closeUniv 2 (.andI (zero_fast _) (zero_at _ _))
theorem actual_one_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pointCN oneF (var 0) ⋏ ap2 oneF (var 1) (var 0) ≐ qone) :=
  closeUniv 2 (.andI (one_fast _) (one_at _ _))
theorem actual_additive_identity_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ crossEquivalent (addF f zeroF) f (addData (var 0) (var 0)) (var 0)) :=
  closeUniv 1 (.impI (add_zero f _ Prf.hyp0))
theorem actual_multiplicative_identity_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ crossEquivalent (multiplyF f oneF) f
      (multiplyData f oneF (var 0) (var 0)) (var 0)) :=
  closeUniv 1 (.impI (multiply_one f _ Prf.hyp0))
theorem actual_additive_inverse_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ crossEquivalent (addF f (negativeF f)) zeroF
      (addData (var 0) (negativeData (var 0))) (var 0)) :=
  closeUniv 1 (.impI (add_negative f _ Prf.hyp0))

theorem actual_negative_name_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pointCN f (var 0) ⟶ pointCN (negativeF f) (negativeData (var 0)) ⋏
      (canonical (ap2 (negativeF f) (var 1) (negativeData (var 0))) ⋏
        ap2 (negativeF f) (var 1) (negativeData (var 0)) ≐ GaussianFastValueCut.recode
          (qsub qzero (ap2 f (GaussianFastValueCut.exponent (one+one) (var 1)) (var 0))))) :=
  closeUniv 2 (.impI (.andI (negative_fast f _ Prf.hyp0)
    (.andI (negative_canonical f _ _) (negative_at f _ _))))
theorem actual_negative_equivalence_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianNameArithmetic.input f g (var 0) (var 1) ⋏
      GaussianNameEquivalence.diagonalEquivalent f g (var 0) (var 1) ⟶
      crossEquivalent (negativeF f) (negativeF g) (negativeData (var 0)) (negativeData (var 1))) :=
  closeUniv 2 (.impI (negative_equivalent f g _ _
    (.andE₁ (.andE₁ Prf.hyp0)) (.andE₂ (.andE₁ Prf.hyp0)) (.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNameRingLaws
