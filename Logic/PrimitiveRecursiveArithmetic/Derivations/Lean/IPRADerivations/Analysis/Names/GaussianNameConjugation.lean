import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalConjugation
import IPRADerivations.Analysis.Names.GaussianNameRingLaws
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference
import IPRADerivations.Analysis.Names.RationalGaussianNameEmbedding

/-!
# Actual conjugation of Gaussian names and their precision normalizers

The actual sampler conjugates each original observation. Its isometry
preserves independent-precision comparisons. Normalizer transport uses
both actual moduli; no identification of distinct clocks is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNameConjugation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalConjugation (point point_congr point_canonical point_distance point_add point_mul)
open GaussianRationalHorner (canonical_unique represents_congr positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def body (f : PR 2) : PTm 2 := point (PTm.app f ![var 0,var 1])
def nameF (f : PR 2) : PR 2 := PTm.toPR (body f)
theorem sample_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] ap2 (nameF f) p x ≐ point (ap2 f p x) := by
  have args : (fun i : Fin 2 => Syn.subst (![p,x] : Fin 2 → PTm n) ((![var 0,var 1] : Fin 2 → PTm 2) i)) = ![p,x] := by
    funext i
    fin_cases i <;> rfl
  simpa only [nameF,body,GaussianRationalConjugation.subst_point,ap2,ConciseIPRA.PTm.subst_app,args] using
    toPR_eq (Γ := Γ) (body f) ![p,x]

theorem conjugate_cross_at (f g : PR 2) (x y p q : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p x) (ap2 (nameF g) q y) (unit p+unit q) (unit p*unit q) :=
  distance_congr (sample_at f p x).eqSymm (sample_at g q y).eqSymm (.eqRefl _) (.eqRefl _)
    (point_distance _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
      (GaussianNameEquivalence.cross_at f g x y p q h))

theorem conjugate_cross (f g : PR 2) (x y : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f) (nameF g) x y := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent f g (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [crossEquivalent,Syn.shift,unit,GaussianEuclideanPointDistance.unit] using
    conjugate_cross_at f g (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (var 1) (var 0) hs

theorem regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx] pointCN (nameF f) x :=
  conjugate_cross f f x x (GaussianNameEquivalence.cross_refl f x h)

theorem raw_regular_at (f : PR 2) (L x p q : PTm n) (h : Γ ⊢[PRAAx] GaussianFastValueCut.regular f L x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p x) (ap2 (nameF f) q x) (L*(unit p+unit q)) (unit p*unit q) :=
  distance_congr (sample_at f p x).eqSymm (sample_at f q x).eqSymm (.eqRefl _) (.eqRefl _)
    (point_distance _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
      (GaussianFastValueCut.regular_at f L x p q h))

theorem raw_regular (f : PR 2) (L x : PTm n) (h : Γ ⊢[PRAAx] GaussianFastValueCut.regular f L x) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular (nameF f) L x := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianFastValueCut.regular f (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [GaussianFastValueCut.regular,Syn.shift,PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit] using
    raw_regular_at f (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift x)) (var 1) (var 0) hs

theorem point_recode (q : PTm n) : Γ ⊢[PRAAx] point (GaussianFastValueCut.recode q) ≐ point q :=
  canonical_unique _ _ _ _ (point_canonical _) (point_canonical _) (raw_den_positive q)
    (GaussianRationalConjugation.point_represents _ _ _ (raw_den_positive q) (GaussianFastValueCut.recode_represents q))
    (GaussianRationalConjugation.point_represents q _ _ (raw_den_positive q) (raw_represents q))

theorem normalized_at (f : PR 2) (L x p : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF (GaussianFastValueCut.nameF f)) p (GaussianFastValueCut.nameData L x) ≐
      ap2 (GaussianFastValueCut.nameF (nameF f)) p (GaussianFastValueCut.nameData L x) := by
  have left := (sample_at (Γ := Γ) (GaussianFastValueCut.nameF f) p (GaussianFastValueCut.nameData L x)).eqTrans
    ((point_congr (GaussianFastValueCut.name_at f L x p)).eqTrans (point_recode _))
  have right := (GaussianFastValueCut.name_at (Γ := Γ) (nameF f) L x p).eqTrans
    ((GaussianNameArithmetic.recode_congr (sample_at f (GaussianFastValueCut.exponent L p) x)).eqTrans
      (GaussianExponentialReference.recode_fixed _ (point_canonical _)))
  exact left.eqTrans right.eqSymm

def pointwiseEqual (f g : PR 2) (x y : PTm n) : Fm PTm n := .all
  (ap2 f (var 0) (Syn.shift x) ≐ ap2 g (var 0) (Syn.shift y))
@[simp] theorem subst_pointwiseEqual {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (x y : PTm n) :
    (pointwiseEqual f g x y).subst σ = pointwiseEqual f g (Syn.subst σ x) (Syn.subst σ y) := by
  simp [pointwiseEqual,Syn.subst_shift,Syn.shift_subst]

theorem equal_distance (q r D : PTm n) (hD : Γ ⊢[PRAAx] le one D) (e : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx]
    distanceBounded q r zero D :=
  distance_congr e.eqSymm (.eqRefl r) (.eqRefl zero) (.eqRefl D)
    (GaussianRationalPowerDifference.distance_refl_zero r D hD)

theorem equal_samples_cross (f g : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (he : Γ ⊢[PRAAx] pointwiseEqual f g x y) : Γ ⊢[PRAAx] crossEquivalent f g x y := by
  apply GaussianNameRingLaws.equivalent_of_envelope f g x y zero hf hg
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointwiseEqual f g (Syn.shift x) (Syn.shift y) := by simpa [Fm.shift,Syn.shift] using he.shift
  have eq : Γ.map Fm.shift ⊢[PRAAx] ap2 f (var 0) (Syn.shift x) ≐ ap2 g (var 0) (Syn.shift y) := by
    simpa only [pointwiseEqual,Fm.subst_eq,subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hs.allE (var 0)
  have d : Γ.map Fm.shift ⊢[PRAAx] distanceBounded
      (ap2 f (var 0) (Syn.shift x)) (ap2 g (var 0) (Syn.shift y)) zero (unit (var 0)) :=
    equal_distance _ _ _ (unit_positive _) eq
  simpa only [Syn.shift,ConciseIPRA.PTm.subst_zero] using d

theorem normalized_cross (f : PR 2) (L x : PTm n) (h : Γ ⊢[PRAAx] GaussianFastValueCut.regular f L x) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (GaussianFastValueCut.nameF f)) (GaussianFastValueCut.nameF (nameF f))
      (GaussianFastValueCut.nameData L x) (GaussianFastValueCut.nameData L x) := by
  apply equal_samples_cross _ _ _ _ (regular _ _ (GaussianFastValueCut.name_fast f L x h))
    (GaussianFastValueCut.name_fast _ _ _ (raw_regular f L x h))
  refine .allI ?_
  simpa only [pointwiseEqual,Syn.shift,GaussianFastValueCut.subst_nameData] using
    normalized_at (Γ := Γ.map Fm.shift) f (Syn.shift L) (Syn.shift x) (var 0)

def covariance (f g : PR 2) (x y : PTm n) : Fm PTm n := .all
  (point (ap2 f (var 0) (Syn.shift x)) ≐ ap2 g (var 0) (Syn.shift y))
@[simp] theorem subst_covariance {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (x y : PTm n) :
    (covariance f g x y).subst σ = covariance f g (Syn.subst σ x) (Syn.subst σ y) := by simp [covariance,Syn.subst_shift,Syn.shift_subst]

/-- Both actual normalization moduli are retained. The only covariance
premise concerns the underlying raw programs and is discharged by each
concrete finite producer before this transport theorem is used. -/
theorem normalized_transport (f g : PR 2) (L M x y : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianFastValueCut.regular f L x) (hg : Γ ⊢[PRAAx] GaussianFastValueCut.regular g M y)
    (he : Γ ⊢[PRAAx] covariance f g x y) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (GaussianFastValueCut.nameF f)) (GaussianFastValueCut.nameF g)
      (GaussianFastValueCut.nameData L x) (GaussianFastValueCut.nameData M y) := by
  have diag : Γ ⊢[PRAAx] GaussianValueNormalizerExtensionality.rawDiagonal (nameF f) g x y zero := by
    refine .allI ?_
    have hs : Γ.map Fm.shift ⊢[PRAAx] covariance f g (Syn.shift x) (Syn.shift y) := by simpa [Fm.shift,Syn.shift] using he.shift
    have eq : Γ.map Fm.shift ⊢[PRAAx] point (ap2 f (var 0) (Syn.shift x)) ≐ ap2 g (var 0) (Syn.shift y) := by
      simpa only [covariance,Fm.subst_eq,GaussianRationalConjugation.subst_point,subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hs.allE (var 0)
    have e : Γ.map Fm.shift ⊢[PRAAx] ap2 (nameF f) (var 0) (Syn.shift x) ≐ ap2 g (var 0) (Syn.shift y) :=
      (sample_at f (var 0) (Syn.shift x)).eqTrans eq
    have d : Γ.map Fm.shift ⊢[PRAAx] distanceBounded
        (ap2 (nameF f) (var 0) (Syn.shift x)) (ap2 g (var 0) (Syn.shift y)) zero (unit (var 0)) :=
      equal_distance _ _ _ (unit_positive _) e
    simpa only [Syn.shift,ConciseIPRA.PTm.subst_zero] using d
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ (normalized_cross f L x hf)
    (GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ _ _ _ _ zero (raw_regular f L x hf) hg diag)


theorem add_raw_covariance_at (f g : PR 2) (p x y : PTm n) : Γ ⊢[PRAAx]
    point (ap2 (GaussianNameArithmetic.addRawF f g) p (GaussianNameArithmetic.data x y)) ≐
      ap2 (GaussianNameArithmetic.addRawF (nameF f) (nameF g)) p (GaussianNameArithmetic.data x y) :=
  (point_congr (GaussianNameArithmetic.add_raw_at f g p x y)).eqTrans
    ((point_add _ _).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (sample_at f p x).eqSymm (sample_at g p y).eqSymm).eqTrans
        (GaussianNameArithmetic.add_raw_at (nameF f) (nameF g) p x y).eqSymm))

theorem multiply_raw_covariance_at (f g : PR 2) (p x y : PTm n) : Γ ⊢[PRAAx]
    point (ap2 (GaussianNameArithmetic.multiplyRawF f g) p (GaussianNameArithmetic.data x y)) ≐
      ap2 (GaussianNameArithmetic.multiplyRawF (nameF f) (nameF g)) p (GaussianNameArithmetic.data x y) :=
  (point_congr (GaussianNameArithmetic.multiply_raw_at f g p x y)).eqTrans
    ((point_mul _ _).eqTrans
      ((GaussianRationalSyntheticDivision.qmul_congr (sample_at f p x).eqSymm (sample_at g p y).eqSymm).eqTrans
        (GaussianNameArithmetic.multiply_raw_at (nameF f) (nameF g) p x y).eqSymm))

theorem add_raw_covariance (f g : PR 2) (x y : PTm n) : Γ ⊢[PRAAx]
    covariance (GaussianNameArithmetic.addRawF f g) (GaussianNameArithmetic.addRawF (nameF f) (nameF g))
      (GaussianNameArithmetic.data x y) (GaussianNameArithmetic.data x y) := by
  refine .allI ?_
  simpa only [covariance,Syn.shift,GaussianNameArithmetic.subst_data] using
    add_raw_covariance_at (Γ := Γ.map Fm.shift) f g (var 0) (Syn.shift x) (Syn.shift y)

theorem multiply_raw_covariance (f g : PR 2) (x y : PTm n) : Γ ⊢[PRAAx]
    covariance (GaussianNameArithmetic.multiplyRawF f g) (GaussianNameArithmetic.multiplyRawF (nameF f) (nameF g))
      (GaussianNameArithmetic.data x y) (GaussianNameArithmetic.data x y) := by
  refine .allI ?_
  simpa only [covariance,Syn.shift,GaussianNameArithmetic.subst_data] using
    multiply_raw_covariance_at (Γ := Γ.map Fm.shift) f g (var 0) (Syn.shift x) (Syn.shift y)

theorem add_cross (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (GaussianNameArithmetic.addF f g)) (GaussianNameArithmetic.addF (nameF f) (nameF g))
      (GaussianNameArithmetic.addData x y) (GaussianNameArithmetic.addData x y) :=
  normalized_transport _ _ two two _ _ (GaussianNameArithmetic.add_regular f g x y hf hg)
    (GaussianNameArithmetic.add_regular (nameF f) (nameF g) x y (regular f x hf) (regular g y hg))
    (add_raw_covariance f g x y)

theorem multiply_cross (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (GaussianNameArithmetic.multiplyF f g)) (GaussianNameArithmetic.multiplyF (nameF f) (nameF g))
      (GaussianNameArithmetic.multiplyData f g x y) (GaussianNameArithmetic.multiplyData (nameF f) (nameF g) x y) :=
  normalized_transport _ _ (GaussianNameArithmetic.multiplyModulus f g x y)
    (GaussianNameArithmetic.multiplyModulus (nameF f) (nameF g) x y) _ _
    (GaussianNameArithmetic.multiply_regular f g x y hf hg)
    (GaussianNameArithmetic.multiply_regular (nameF f) (nameF g) x y (regular f x hf) (regular g y hg))
    (multiply_raw_covariance f g x y)

theorem embedded_sample_fixed (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF (RationalGaussianNameEmbedding.nameF f)) p x ≐ ap2 (RationalGaussianNameEmbedding.nameF f) p x :=
  (sample_at _ p x).eqTrans
    ((point_congr (RationalGaussianNameEmbedding.sample_at f p x)).eqTrans
      ((GaussianRationalConjugation.point_embed _).eqTrans (RationalGaussianNameEmbedding.sample_at f p x).eqSymm))

theorem embedded_cross_fixed (f : PR 2) (x : PTm n)
    (h : Γ ⊢[PRAAx] pointCN (RationalGaussianNameEmbedding.nameF f) x) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (RationalGaussianNameEmbedding.nameF f)) (RationalGaussianNameEmbedding.nameF f) x x := by
  apply equal_samples_cross _ _ _ _ (regular _ _ h) h
  refine .allI ?_
  simpa only [pointwiseEqual,Syn.shift] using embedded_sample_fixed (Γ := Γ.map Fm.shift) f (var 0) (Syn.shift x)

theorem exponential_input (f : PR 2) (R x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input (nameF f) R x := by
  refine .andI (regular f x h.andE₁) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianRadiusExponentialName.boundedSamples f (Syn.shift R) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRadiusExponentialName.subst_boundedSamples,Syn.shift] using h.andE₂.shift
  have bound := GaussianRadiusExponentialName.bounded_samples_at f (Syn.shift R) (Syn.shift x) (var 0) hs
  have d := GaussianRationalConjugation.point_bound _ _ one (le_refl _) bound
  have e := GaussianRationalReciprocal.bound_congr (sample_at f (var 0) (Syn.shift x)).eqSymm (.eqRefl (Syn.shift R)) (.eqRefl one) d
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using e

theorem scalar_sum_congr {q r : PTm n} (k : PTm n) (e : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx]
    GaussianRationalPolynomialExponential.scalarSum q k ≐ GaussianRationalPolynomialExponential.scalarSum r k :=
  GaussianRationalFiniteSum.sum_index_congr _ (.eqRefl _) e

theorem exponential_sample (f : PR 2) (R p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF (GaussianRadiusExponentialName.nameF f)) p (GaussianRadiusExponentialName.data R x) ≐
      ap2 (GaussianRadiusExponentialName.nameF (nameF f)) p (GaussianRadiusExponentialName.data R x) :=
  (sample_at _ p _).eqTrans
    ((point_congr (GaussianRadiusExponentialName.sample_at f R p x)).eqTrans
      ((GaussianRationalConjugation.point_scalar_sum _ _).eqTrans
        ((scalar_sum_congr _ (sample_at f (GaussianRadiusExponentialName.inputPrecision R p) x).eqSymm).eqTrans
          (GaussianRadiusExponentialName.sample_at (nameF f) R p x).eqSymm)))

theorem exponential_cross (f : PR 2) (R x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (GaussianRadiusExponentialName.nameF f)) (GaussianRadiusExponentialName.nameF (nameF f))
      (GaussianRadiusExponentialName.data R x) (GaussianRadiusExponentialName.data R x) := by
  apply equal_samples_cross _ _ _ _ (regular _ _ (GaussianRadiusExponentialName.name_regular f R x h))
    (GaussianRadiusExponentialName.name_regular (nameF f) R x (exponential_input f R x h))
  refine .allI ?_
  simpa only [pointwiseEqual,Syn.shift,GaussianRadiusExponentialName.subst_data] using
    exponential_sample (Γ := Γ.map Fm.shift) f (Syn.shift R) (var 0) (Syn.shift x)


theorem sample_canonical (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (nameF f) p x) :=
  GaussianRationalHorner.canonical_congr (sample_at f p x) (point_canonical _)

theorem actual_conjugation_sampler_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (nameF f) (var 0) (var 1) ≐ point (ap2 f (var 0) (var 1))) := closeUniv 2 (sample_at f _ _)

theorem actual_conjugate_name_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ pointCN (nameF f) (var 0)) := closeUniv 1 (.impI (regular f _ Prf.hyp0))

theorem actual_independent_conjugation_proper_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent f g (var 0) (var 1) ⟶ crossEquivalent (nameF f) (nameF g) (var 0) (var 1)) :=
  closeUniv 2 (.impI (conjugate_cross f g _ _ Prf.hyp0))

theorem actual_raw_conjugate_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianFastValueCut.regular f (var 0) (var 1) ⟶ GaussianFastValueCut.regular (nameF f) (var 0) (var 1)) :=
  closeUniv 2 (.impI (raw_regular f _ _ Prf.hyp0))

theorem actual_independent_normalizers_conjugation_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianFastValueCut.regular f (var 0) (var 2) ⋏
      (GaussianFastValueCut.regular g (var 1) (var 3) ⋏ covariance f g (var 2) (var 3)) ⟶
      crossEquivalent (nameF (GaussianFastValueCut.nameF f)) (GaussianFastValueCut.nameF g)
        (GaussianFastValueCut.nameData (var 0) (var 2)) (GaussianFastValueCut.nameData (var 1) (var 3))) :=
  closeUniv 4 (.impI (normalized_transport f g _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_addition_conjugation_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianNameArithmetic.input f g (var 0) (var 1) ⟶
      crossEquivalent (nameF (GaussianNameArithmetic.addF f g)) (GaussianNameArithmetic.addF (nameF f) (nameF g))
        (GaussianNameArithmetic.addData (var 0) (var 1)) (GaussianNameArithmetic.addData (var 0) (var 1))) :=
  closeUniv 2 (.impI (add_cross f g _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_multiplication_conjugation_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianNameArithmetic.input f g (var 0) (var 1) ⟶
      crossEquivalent (nameF (GaussianNameArithmetic.multiplyF f g)) (GaussianNameArithmetic.multiplyF (nameF f) (nameF g))
        (GaussianNameArithmetic.multiplyData f g (var 0) (var 1))
        (GaussianNameArithmetic.multiplyData (nameF f) (nameF g) (var 0) (var 1))) :=
  closeUniv 2 (.impI (multiply_cross f g _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_embedded_rational_name_fixed_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN (RationalGaussianNameEmbedding.nameF f) (var 0) ⟶
      crossEquivalent (nameF (RationalGaussianNameEmbedding.nameF f)) (RationalGaussianNameEmbedding.nameF f) (var 0) (var 0)) :=
  closeUniv 1 (.impI (embedded_cross_fixed f _ Prf.hyp0))

theorem actual_radius_exponential_conjugation_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRadiusExponentialName.input f (var 0) (var 1) ⟶
      crossEquivalent (nameF (GaussianRadiusExponentialName.nameF f)) (GaussianRadiusExponentialName.nameF (nameF f))
        (GaussianRadiusExponentialName.data (var 0) (var 1)) (GaussianRadiusExponentialName.data (var 0) (var 1))) :=
  closeUniv 2 (.impI (exponential_cross f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNameConjugation
