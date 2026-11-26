import IPRADerivations.Analysis.Names.GaussianNameBounds
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianValueNormalizerExtensionality

/-!
# Actual addition and multiplication of fast Gaussian names

The raw PR2 programs operate on the original samples with separately packed
numerical data. Their regularity moduli are derived from genuine input CN:
two for addition and the sum of the computed input disks for multiplication.
The existing actual normalizer produces canonical fast names. Equivalent
inputs give cross-equivalent outputs even when their computed normalization
shifts differ. No output regularity, global disk, or operation-value law is
assumed. This supplies the arithmetic closure/properness component used in
FTA_iPRA's name interpretation; represented ring laws remain separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNameArithmetic

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN subst_pointCN)
open LeanProofs.IPRA.Analysis.GaussianNameEquivalence (diagonalEquivalent crossEquivalent)
open LeanProofs.IPRA.Analysis.GaussianRationalL1
  (rawGaussian rawDen raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (x y : PTm n) : PTm n := pairT x y
def addRaw (f g : PR 2) (s x y : PTm n) : PTm n := qadd (ap2 f s x) (ap2 g s y)
def multiplyRaw (f g : PR 2) (s x y : PTm n) : PTm n := qmul (ap2 f s x) (ap2 g s y)
def addRawF (f g : PR 2) : PR 2 := PTm.toPR
  (addRaw f g (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)
def multiplyRawF (f g : PR 2) : PR 2 := PTm.toPR
  (multiplyRaw f g (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)
def multiplyModulus (f g : PR 2) (x y : PTm n) : PTm n :=
  GaussianNameBounds.U f x+GaussianNameBounds.U g y
def addF (f g : PR 2) : PR 2 := GaussianFastValueCut.nameF (addRawF f g)
def multiplyF (f g : PR 2) : PR 2 := GaussianFastValueCut.nameF (multiplyRawF f g)
def addData (x y : PTm n) : PTm n := GaussianFastValueCut.nameData two (data x y)
def multiplyData (f g : PR 2) (x y : PTm n) : PTm n :=
  GaussianFastValueCut.nameData (multiplyModulus f g x y) (data x y)
def input (f g : PR 2) (x y : PTm n) : Fm PTm n := pointCN f x ⋏ pointCN g y

ipra_subst data
ipra_subst addRaw
ipra_subst multiplyRaw
ipra_subst multiplyModulus
ipra_subst addData
ipra_subst multiplyData
ipra_subst input

theorem add_data_congr {x x' y y' : PTm n} (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') :
    Γ ⊢[PRAAx] addData x y ≐ addData x' y' :=
  congrPairT (.eqRefl two) (congrPairT hx hy)

theorem add_raw_at (f g : PR 2) (s x y : PTm n) : Γ ⊢[PRAAx]
    ap2 (addRawF f g) s (data x y) ≐ addRaw f g s x y := by
  have e := toPR_eq (Γ := Γ)
    (addRaw f g (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![s,data x y]
  refine e.eqTrans ?_
  simpa only [subst_addRaw,subst_qadd,subst_ap2,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,addRaw,data] using
    qadd_congr (Γ := Γ) (congrAp2 f (.eqRefl s) (fst_pair x y))
      (congrAp2 g (.eqRefl s) (snd_pair x y))

theorem multiply_raw_at (f g : PR 2) (s x y : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyRawF f g) s (data x y) ≐ multiplyRaw f g s x y := by
  have e := toPR_eq (Γ := Γ)
    (multiplyRaw f g (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![s,data x y]
  refine e.eqTrans ?_
  simpa only [subst_multiplyRaw,subst_qmul,subst_ap2,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,multiplyRaw,data] using
    qmul_congr (Γ := Γ) (congrAp2 f (.eqRefl s) (fst_pair x y))
      (congrAp2 g (.eqRefl s) (snd_pair x y))

theorem sum_difference_from_representations (a b u v A B U V E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] represents a A E)
    (hb : Γ ⊢[PRAAx] represents b B E) (hu : Γ ⊢[PRAAx] represents u U E)
    (hv : Γ ⊢[PRAAx] represents v V E) : Γ ⊢[PRAAx]
    qsub (qadd a u) (qadd b v) ≐ qadd (qsub a b) (qsub u v) := by
  have lhs := GaussianRationalMetric.qsub_represents _ _ _ _ _ hE
    (qadd_represents _ _ _ _ _ hE ha hu) (qadd_represents _ _ _ _ _ hE hb hv)
  have rhs := qadd_represents _ _ _ _ _ hE
    (GaussianRationalMetric.qsub_represents _ _ _ _ _ hE ha hb)
    (GaussianRationalMetric.qsub_represents _ _ _ _ _ hE hu hv)
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _) (qadd_canonical _ _) hE (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
      GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add] <;> ring

/-- The denominator is computed from the four original raw operands. -/
theorem sum_difference (a b u v : PTm n) : Γ ⊢[PRAAx]
    qsub (qadd a u) (qadd b v) ≐ qadd (qsub a b) (qsub u v) := by
  let E := GaussianRationalSyntheticDivision.remainingDen a b u v
  have ha := GaussianRationalSyntheticDivision.rescale_to a (rawGaussian a) (rawDen a)
    (rawDen b*rawDen u*rawDen v) E (raw_represents (Γ := Γ) a)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have hb := GaussianRationalSyntheticDivision.rescale_to b (rawGaussian b) (rawDen b)
    (rawDen a*rawDen u*rawDen v) E (raw_represents (Γ := Γ) b)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have hu := GaussianRationalSyntheticDivision.rescale_to u (rawGaussian u) (rawDen u)
    (rawDen a*rawDen b*rawDen v) E (raw_represents (Γ := Γ) u)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have hv := GaussianRationalSyntheticDivision.rescale_to v (rawGaussian v) (rawDen v)
    (rawDen a*rawDen b*rawDen u) E (raw_represents (Γ := Γ) v)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  exact sum_difference_from_representations _ _ _ _ _ _ _ _ E
    (GaussianRationalSyntheticDivision.remaining_den_positive a b u v) ha hb hu hv

theorem sum_distance (a b u v A C B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] distanceBounded a b A B)
    (huv : Γ ⊢[PRAAx] distanceBounded u v C B) : Γ ⊢[PRAAx]
    distanceBounded (qadd a u) (qadd b v) (A+C) B :=
  GaussianRationalReciprocal.bound_congr (sum_difference a b u v).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ hB hab huv)

theorem product_distance (a b u v A C B U V : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] distanceBounded a b A B)
    (huv : Γ ⊢[PRAAx] distanceBounded u v C B)
    (hu : Γ ⊢[PRAAx] bounded u U one) (hb : Γ ⊢[PRAAx] bounded b V one) : Γ ⊢[PRAAx]
    distanceBounded (qmul a u) (qmul b v) (A*U+V*C) B := by
  have first := GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hB (le_refl one) hab hu)
  have last := GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) hB hb huv)
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRationalPowerDifference.product_difference a b u v).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ hB first last)

theorem add_regular_at (f g : PR 2) (x y s t : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (addRawF f g) s (data x y)) (ap2 (addRawF f g) t (data x y))
      (two*(unit s+unit t)) (unit s*unit t) :=
  distance_congr (add_raw_at f g s x y).eqSymm (add_raw_at f g t x y).eqSymm (by ipra_ring) (.eqRefl _)
    (sum_distance _ _ _ _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive t))
      (GaussianNameEquivalence.point_at f x s t hf) (GaussianNameEquivalence.point_at g y s t hg))

theorem multiply_regular_at (f g : PR 2) (x y s t : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyRawF f g) s (data x y)) (ap2 (multiplyRawF f g) t (data x y))
      (multiplyModulus f g x y*(unit s+unit t)) (unit s*unit t) :=
  distance_congr (multiply_raw_at f g s x y).eqSymm (multiply_raw_at f g t x y).eqSymm
    (by unfold multiplyModulus; ipra_ring) (.eqRefl _)
    (product_distance _ _ _ _ _ _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive t))
      (GaussianNameEquivalence.point_at f x s t hf) (GaussianNameEquivalence.point_at g y s t hg)
      (GaussianNameBounds.sample_bound g y s hg) (GaussianNameBounds.sample_bound f x t hf))

theorem add_regular (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular (addRawF f g) two (data x y) := by
  refine .allI (.allI ?_)
  have hf2 := GaussianEuclideanDistanceName.shift_pointCN (GaussianEuclideanDistanceName.shift_pointCN hf)
  have hg2 := GaussianEuclideanDistanceName.shift_pointCN (GaussianEuclideanDistanceName.shift_pointCN hg)
  simpa only [Syn.shift,subst_data,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    add_regular_at f g (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (var 1) (var 0) hf2 hg2

theorem multiply_regular (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular (multiplyRawF f g) (multiplyModulus f g x y) (data x y) := by
  refine .allI (.allI ?_)
  have hf2 := GaussianEuclideanDistanceName.shift_pointCN (GaussianEuclideanDistanceName.shift_pointCN hf)
  have hg2 := GaussianEuclideanDistanceName.shift_pointCN (GaussianEuclideanDistanceName.shift_pointCN hg)
  simpa only [Syn.shift,subst_data,subst_multiplyModulus] using
    multiply_regular_at f g (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (var 1) (var 0) hf2 hg2

theorem recode_congr {z w : PTm n} (h : Γ ⊢[PRAAx] z ≐ w) : Γ ⊢[PRAAx]
    GaussianFastValueCut.recode z ≐ GaussianFastValueCut.recode w := by
  ipra_congr (GaussianFastValueCut.recode (var 0) : PTm 1) with [h]

theorem add_at (f g : PR 2) (x y k : PTm n) : Γ ⊢[PRAAx]
    ap2 (addF f g) k (addData x y) ≐ GaussianFastValueCut.recode
      (addRaw f g (GaussianFastValueCut.exponent two k) x y) :=
  (GaussianFastValueCut.name_at (addRawF f g) two (data x y) k).eqTrans
    (recode_congr (add_raw_at f g _ x y))

theorem multiply_at (f g : PR 2) (x y k : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyF f g) k (multiplyData f g x y) ≐ GaussianFastValueCut.recode
      (multiplyRaw f g (GaussianFastValueCut.exponent (multiplyModulus f g x y) k) x y) :=
  (GaussianFastValueCut.name_at (multiplyRawF f g) (multiplyModulus f g x y) (data x y) k).eqTrans
    (recode_congr (multiply_raw_at f g _ x y))

theorem add_canonical (f g : PR 2) (x y k : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (addF f g) k (addData x y)) :=
  GaussianFastValueCut.name_canonical (addRawF f g) two (data x y) k
theorem multiply_canonical (f g : PR 2) (x y k : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (multiplyF f g) k (multiplyData f g x y)) :=
  GaussianFastValueCut.name_canonical (multiplyRawF f g) (multiplyModulus f g x y) (data x y) k
theorem add_fast (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    pointCN (addF f g) (addData x y) :=
  GaussianFastValueCut.name_fast (addRawF f g) two (data x y) (add_regular f g x y hf hg)
theorem multiply_fast (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    pointCN (multiplyF f g) (multiplyData f g x y) :=
  GaussianFastValueCut.name_fast (multiplyRawF f g) (multiplyModulus f g x y) (data x y)
    (multiply_regular f g x y hf hg)

theorem add_raw_diagonal (f f' g g' : PR 2) (x x' y y' : PTm n)
    (hf : Γ ⊢[PRAAx] diagonalEquivalent f f' x x')
    (hg : Γ ⊢[PRAAx] diagonalEquivalent g g' y y') : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal (addRawF f g) (addRawF f' g')
      (data x y) (data x' y') (two+two) := by
  refine .allI ?_
  have hf1 := GaussianNameEquivalence.shift_diagonalEquivalent hf
  have hg1 := GaussianNameEquivalence.shift_diagonalEquivalent hg
  have e : Γ.map Fm.shift ⊢[PRAAx]
      distanceBounded
        (ap2 (addRawF f g) (var 0) (data (Syn.shift x) (Syn.shift y)))
        (ap2 (addRawF f' g') (var 0) (data (Syn.shift x') (Syn.shift y')))
        (two+two)
        (unit (var 0)) := distance_congr
    (add_raw_at f g (var 0) (Syn.shift x) (Syn.shift y)).eqSymm
    (add_raw_at f' g' (var 0) (Syn.shift x') (Syn.shift y')).eqSymm (.eqRefl _) (.eqRefl _)
    (sum_distance _ _ _ _ _ _ _ (unit_positive (var 0))
      (GaussianNameEquivalence.diagonal_at f f' _ _ (var 0) hf1)
      (GaussianNameEquivalence.diagonal_at g g' _ _ (var 0) hg1))
  simpa only [Syn.shift,subst_data,PTm.subst_add,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using e

theorem multiply_raw_diagonal (f f' g g' : PR 2) (x x' y y' : PTm n)
    (hfp : Γ ⊢[PRAAx] pointCN f' x') (hg : Γ ⊢[PRAAx] pointCN g y)
    (hfe : Γ ⊢[PRAAx] diagonalEquivalent f f' x x')
    (hge : Γ ⊢[PRAAx] diagonalEquivalent g g' y y') : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal (multiplyRawF f g) (multiplyRawF f' g')
      (data x y) (data x' y') (two*(GaussianNameBounds.U f' x'+GaussianNameBounds.U g y)) := by
  refine .allI ?_
  have hfp1 := GaussianEuclideanDistanceName.shift_pointCN hfp
  have hg1 := GaussianEuclideanDistanceName.shift_pointCN hg
  have hfe1 := GaussianNameEquivalence.shift_diagonalEquivalent hfe
  have hge1 := GaussianNameEquivalence.shift_diagonalEquivalent hge
  have e : Γ.map Fm.shift ⊢[PRAAx]
      distanceBounded
        (ap2 (multiplyRawF f g) (var 0) (data (Syn.shift x) (Syn.shift y)))
        (ap2 (multiplyRawF f' g') (var 0) (data (Syn.shift x') (Syn.shift y')))
        (two*(GaussianNameBounds.U f' (Syn.shift x')+GaussianNameBounds.U g (Syn.shift y)))
        (unit (var 0)) := distance_congr
    (multiply_raw_at f g (var 0) (Syn.shift x) (Syn.shift y)).eqSymm
    (multiply_raw_at f' g' (var 0) (Syn.shift x') (Syn.shift y')).eqSymm
    (by ipra_ring) (.eqRefl _)
    (product_distance _ _ _ _ _ _ _ _ _ (unit_positive (var 0))
      (GaussianNameEquivalence.diagonal_at f f' _ _ (var 0) hfe1)
      (GaussianNameEquivalence.diagonal_at g g' _ _ (var 0) hge1)
      (GaussianNameBounds.sample_bound g (Syn.shift y) (var 0) hg1)
      (GaussianNameBounds.sample_bound f' (Syn.shift x') (var 0) hfp1))
  simpa only [Syn.shift,subst_data,PTm.subst_add,PTm.subst_mul,GaussianNameBounds.subst_U,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using e

/-- Different input data may produce different disks and precision shifts. -/
theorem add_equivalent (f f' g g' : PR 2) (x x' y y' : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hfp : Γ ⊢[PRAAx] pointCN f' x')
    (hg : Γ ⊢[PRAAx] pointCN g y) (hgp : Γ ⊢[PRAAx] pointCN g' y')
    (hfe : Γ ⊢[PRAAx] diagonalEquivalent f f' x x')
    (hge : Γ ⊢[PRAAx] diagonalEquivalent g g' y y') : Γ ⊢[PRAAx]
    crossEquivalent (addF f g) (addF f' g') (addData x y) (addData x' y') :=
  GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ two two _ _ (two+two)
    (add_regular f g x y hf hg) (add_regular f' g' x' y' hfp hgp)
    (add_raw_diagonal f f' g g' x x' y y' hfe hge)

theorem multiply_equivalent (f f' g g' : PR 2) (x x' y y' : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hfp : Γ ⊢[PRAAx] pointCN f' x')
    (hg : Γ ⊢[PRAAx] pointCN g y) (hgp : Γ ⊢[PRAAx] pointCN g' y')
    (hfe : Γ ⊢[PRAAx] diagonalEquivalent f f' x x')
    (hge : Γ ⊢[PRAAx] diagonalEquivalent g g' y y') : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF f g) (multiplyF f' g')
      (multiplyData f g x y) (multiplyData f' g' x' y') :=
  GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ _ _ _ _
    (two*(GaussianNameBounds.U f' x'+GaussianNameBounds.U g y))
    (multiply_regular f g x y hf hg) (multiply_regular f' g' x' y' hfp hgp)
    (multiply_raw_diagonal f f' g g' x x' y y' hfp hg hfe hge)

def equivalenceInput (f f' g g' : PR 2) (x x' y y' : PTm n) : Fm PTm n :=
  input f g x y ⋏ (input f' g' x' y' ⋏
    (diagonalEquivalent f f' x x' ⋏ diagonalEquivalent g g' y y'))

ipra_subst equivalenceInput

theorem actual_addition_name_at_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (addF f g) (var 2) (addData (var 0) (var 1)) ≐ GaussianFastValueCut.recode
      (addRaw f g (GaussianFastValueCut.exponent two (var 2)) (var 0) (var 1))) :=
  closeUniv 3 (add_at f g _ _ _)
theorem actual_multiplication_name_at_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (multiplyF f g) (var 2) (multiplyData f g (var 0) (var 1)) ≐ GaussianFastValueCut.recode
      (multiplyRaw f g (GaussianFastValueCut.exponent (multiplyModulus f g (var 0) (var 1)) (var 2))
        (var 0) (var 1))) :=
  closeUniv 3 (multiply_at f g _ _ _)
theorem actual_addition_name_fast_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f g (var 0) (var 1) ⟶ pointCN (addF f g) (addData (var 0) (var 1))) :=
  closeUniv 2 (.impI (add_fast f g _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))
theorem actual_multiplication_name_fast_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f g (var 0) (var 1) ⟶ pointCN (multiplyF f g) (multiplyData f g (var 0) (var 1))) :=
  closeUniv 2 (.impI (multiply_fast f g _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))
theorem actual_addition_name_canonical_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (canonical (ap2 (addF f g) (var 2) (addData (var 0) (var 1)))) :=
  closeUniv 3 (add_canonical f g _ _ _)
theorem actual_multiplication_name_canonical_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (canonical (ap2 (multiplyF f g) (var 2) (multiplyData f g (var 0) (var 1)))) :=
  closeUniv 3 (multiply_canonical f g _ _ _)
theorem actual_addition_equivalence_closed (f f' g g' : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (equivalenceInput f f' g g' (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent (addF f g) (addF f' g') (addData (var 0) (var 2)) (addData (var 1) (var 3))) := by
  refine closeUniv 4 (.impI ?_)
  have h := Prf.hyp0 (Ax := PRAAx) (Γ := [])
    (φ := equivalenceInput f f' g g' (var 0 : PTm 4) (var 1) (var 2) (var 3))
  exact add_equivalent f f' g g' _ _ _ _ (.andE₁ (.andE₁ h)) (.andE₁ (.andE₁ (.andE₂ h)))
    (.andE₂ (.andE₁ h)) (.andE₂ (.andE₁ (.andE₂ h)))
    (.andE₁ (.andE₂ (.andE₂ h))) (.andE₂ (.andE₂ (.andE₂ h)))
theorem actual_multiplication_equivalence_closed (f f' g g' : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (equivalenceInput f f' g g' (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent (multiplyF f g) (multiplyF f' g')
        (multiplyData f g (var 0) (var 2)) (multiplyData f' g' (var 1) (var 3))) := by
  refine closeUniv 4 (.impI ?_)
  have h := Prf.hyp0 (Ax := PRAAx) (Γ := [])
    (φ := equivalenceInput f f' g g' (var 0 : PTm 4) (var 1) (var 2) (var 3))
  exact multiply_equivalent f f' g g' _ _ _ _ (.andE₁ (.andE₁ h)) (.andE₁ (.andE₁ (.andE₂ h)))
    (.andE₂ (.andE₁ h)) (.andE₂ (.andE₁ (.andE₂ h)))
    (.andE₁ (.andE₂ (.andE₂ h))) (.andE₂ (.andE₂ (.andE₂ h)))

end LeanProofs.IPRA.Analysis.GaussianNameArithmetic
