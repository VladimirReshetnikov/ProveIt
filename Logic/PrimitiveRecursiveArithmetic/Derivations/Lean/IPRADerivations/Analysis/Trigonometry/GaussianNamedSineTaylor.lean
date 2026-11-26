import IPRADerivations.Analysis.Trigonometry.GaussianScalarSineTaylor
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference

/-!
# Original named sine and its literal factorial Taylor observations

The negative exponential's original observation clock determines the
common base sample of both finite exponentials. Their common even cutoff
gives exactly the signed factorial truncation of the original argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianNamedSineTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentCayleyValues (imaginaryPoint imaginaryCode)
open GaussianNamedSineFromExponential (multiplier sineF sineData sine_regular differenceF differenceData)
open GaussianScalarSineTaylor (signedSum finite_sine_taylor)
open GaussianRationalHorner (qzero qmul canonical canonical_unique represents_congr ofGaussian_canonical
  ofGaussian_represents positive_product)
open GaussianRationalMetric (qsub qnegative qnegative_canonical qnegative_represents bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_negative)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalSyntheticDivision (qzero_add)
open GaussianRadiusExponentialName (input data nameF name_regular index inputPrecision sample bounded_samples_at)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyModulus recode_congr)
open GaussianNameRingLaws (negativeF negativeData negative_at multiply_sample_error)
open GaussianNameEquivalence (point_at crossEquivalent)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (recode_fixed finite_reference)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianRationalFiniteSum (sum_index_congr)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def imaginaryArgument (q : PTm n) : PTm n := qmul imaginaryPoint q
def imaginaryF (f : PR 2) : PR 2 := PTm.toPR (imaginaryArgument (ap2 f (var 0) (var 1)) : PTm 2)

@[simp] theorem subst_imaginaryArgument {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (imaginaryArgument q) = imaginaryArgument (Syn.subst σ q) := by
  simp [imaginaryArgument, imaginaryPoint, imaginaryCode]

theorem imaginary_at (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] ap2 (imaginaryF f) p x ≐ imaginaryArgument (ap2 f p x) := by
  change Γ ⊢[PRAAx] PTm.app (imaginaryF f) ![p,x] ≐ imaginaryArgument (ap2 f p x)
  simpa only [imaginaryF, subst_imaginaryArgument, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one] using toPR_eq (Γ := Γ) (imaginaryArgument (ap2 f (var 0) (var 1)) : PTm 2) ![p,x]

private theorem imaginary_bound : Γ ⊢[PRAAx] bounded (imaginaryPoint : PTm n) one one :=
  bound_congr (GaussianArctangentCayleyValues.right_endpoint one (le_refl one)) (.eqRefl _) (.eqRefl _)
    (GaussianArctangentCayleyValues.unit_bound one one (le_refl one))

private theorem multiplier_bound : Γ ⊢[PRAAx] bounded (multiplier : PTm n) one one := by
  let i := (GaussianArctangentQuarterExponential.halfImaginary : PTm n)
  have hd : Γ ⊢[PRAAx] le one two := le_succ_self one
  have e : Γ ⊢[PRAAx] qnegative i ≐ multiplier :=
    canonical_unique _ _ _ two (qnegative_canonical _) (ofGaussian_canonical _ _ hd) hd
      (qnegative_represents _ _ _ (ofGaussian_represents _ _ hd)) (ofGaussian_represents _ _ hd)
  exact bound_congr e (.eqRefl _) (.eqRefl _)
    (bounded_negative i one one (le_refl one) GaussianArctangentQuarterExponential.half_imaginary_bound)

theorem imaginary_regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (imaginaryF f) x := by
  refine .allI (.allI ?_)
  let C := (Γ.map Fm.shift).map Fm.shift
  let u := Syn.shift (Syn.shift x)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hr : C ⊢[PRAAx] pointCN f u := by simpa only [Fm.shift, Syn.shift, subst_pointCN, C, u] using hf.shift.shift
  have hden := positive_product _ _ (unit_positive (Γ := C) p) (unit_positive q)
  have d := multiply_distance imaginaryPoint _ _ one _ _ hden imaginary_bound (point_at f u p q hr)
  exact distance_congr (imaginary_at f p u).eqSymm (imaginary_at f q u).eqSymm (one_mul _) (.eqRefl _) d

private theorem imaginary_sample_bound (f : PR 2) (R x p : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (ap2 (imaginaryF f) p x) R one :=
  bound_congr (imaginary_at f p x).eqSymm (one_mul R) (one_mul one)
    (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) imaginary_bound (bounded_samples_at f R x p hf.andE₂))

theorem imaginary_input (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] input (imaginaryF f) R x := by
  refine .andI (imaginary_regular f x hf.andE₁) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by
    simpa only [Fm.shift, Syn.shift, GaussianRadiusExponentialName.subst_input] using hf.shift
  exact imaginary_sample_bound f _ _ (var 0) hs

def argumentPrecision (R p : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (one+one) (inputPrecision R p)
def taylorValue (f : PR 2) (R x p : PTm n) : PTm n :=
  signedSum (ap2 f (argumentPrecision R p) x) (index R p)

@[simp] theorem subst_argumentPrecision {m : ℕ} (σ : Fin n → PTm m) (R p : PTm n) :
    Syn.subst σ (argumentPrecision R p) = argumentPrecision (Syn.subst σ R) (Syn.subst σ p) := by simp [argumentPrecision]
@[simp] theorem subst_taylorValue {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (R x p : PTm n) :
    Syn.subst σ (taylorValue f R x p) = taylorValue f (Syn.subst σ R) (Syn.subst σ x) (Syn.subst σ p) := by
  simp [taylorValue]

def budget (f : PR 2) (R x : PTm n) : PTm n :=
  multiplyModulus constantF (differenceF (imaginaryF f)) multiplier (differenceData R x)+num 9

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (R x : PTm n) :
    Syn.subst σ (budget f R x) = budget f (Syn.subst σ R) (Syn.subst σ x) := by simp [budget]

private theorem negative_sample (f : PR 2) (q x : PTm n) :
    Γ ⊢[PRAAx] ap2 (negativeF f) q (negativeData x) ≐
      qnegative (ap2 f (GaussianFastValueCut.exponent (one+one) q) x) :=
  (negative_at f x q).eqTrans
    ((recode_congr (qzero_add _ (qnegative_canonical _))).eqTrans (recode_fixed _ (qnegative_canonical _)))

theorem finite_taylor_error (f : PR 2) (R x p : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (sineF (imaginaryF f)) p (sineData (imaginaryF f) R x))
      (taylorValue f R x p) (budget f R x) (unit p) := by
  let g := imaginaryF f
  let a := ap2 f (argumentPrecision R p) x
  let m := index R p
  let E := nameF g
  let N := nameF (negativeF g)
  let u := data R x
  let v := data R (negativeData x)
  let D := differenceF g
  let d := differenceData R x
  have h := imaginary_input f R x hf
  have hn := GaussianExponentialInverse.negative_input g R x h
  have heReg := name_regular g R x h
  have hnReg := name_regular _ _ _ hn
  have dReg : Γ ⊢[PRAAx] pointCN D d := GaussianNamedDifference.name_regular _ _ _ _ heReg hnReg
  have hm : Γ ⊢[PRAAx] le m (two*m) := by ipra_le 𝔞 m
  have hpos := finite_reference g R x p (argumentPrecision R p) (two*m) h (le_add_right _ _) hm
  have hneg := finite_reference (negativeF g) R (negativeData x) p (inputPrecision R p) (two*m) hn (le_refl _) hm
  have pe := imaginary_at (Γ := Γ) f (argumentPrecision R p) x
  have ne := (negative_sample g (inputPrecision R p) x).eqTrans (GaussianInverseBinomialRows.negative_congr pe)
  have lp : Γ ⊢[PRAAx] distanceBounded (ap2 E p u) (scalarSum (imaginaryArgument a) (two*m)) one (unit p) :=
    distance_symmetric _ _ _ _ (unit_positive p)
      (distance_congr (sum_index_congr scalarBody (.eqRefl _) pe) (.eqRefl _) (.eqRefl _) (.eqRefl _) hpos)
  have ln : Γ ⊢[PRAAx] distanceBounded (ap2 N p v) (scalarSum (qnegative (imaginaryArgument a)) (two*m)) one (unit p) :=
    distance_symmetric _ _ _ _ (unit_positive p)
      (distance_congr (sum_index_congr scalarBody (.eqRefl _) ne) (.eqRefl _) (.eqRefl _) (.eqRefl _) hneg)
  have raw := GaussianNamedDifference.sample_error E N u v p heReg hnReg
  have dError := distance_triangle_same _ _ _ _ _ _ (unit_positive p) raw
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ (unit_positive p) lp ln)
  have prodError := multiply_distance multiplier _ _ one _ _ (unit_positive p) multiplier_bound dError
  have mul := multiply_sample_error constantF D multiplier d p (constant_regular _) dReg
  have step := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at p multiplier) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) mul
  exact distance_congr (.eqRefl _) (finite_sine_taylor a m)
    (by unfold budget; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) step prodError)

def rawData (R x : PTm n) : PTm n := pairT R x
def rawF (f : PR 2) : PR 2 := PTm.toPR
  (taylorValue f (fstT (var 1)) (sndT (var 1)) (var 0) : PTm 2)

@[simp] theorem subst_rawData {m : ℕ} (σ : Fin n → PTm m) (R x : PTm n) :
    Syn.subst σ (rawData R x) = rawData (Syn.subst σ R) (Syn.subst σ x) := by simp [rawData]

theorem raw_at (f : PR 2) (R x p : PTm n) :
    Γ ⊢[PRAAx] ap2 (rawF f) p (rawData R x) ≐ taylorValue f R x p := by
  have e : Γ ⊢[PRAAx] ap2 (rawF f) p (rawData R x) ≐ taylorValue f (fstT (rawData R x)) (sndT (rawData R x)) p := by
    change Γ ⊢[PRAAx] PTm.app (rawF f) ![p,rawData R x] ≐ taylorValue f (fstT (rawData R x)) (sndT (rawData R x)) p
    simpa only [rawF, subst_taylorValue, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero,
      Matrix.cons_val_one] using toPR_eq (Γ := Γ) (taylorValue f (fstT (var 1)) (sndT (var 1)) (var 0) : PTm 2) ![p,rawData R x]
  have r : Γ ⊢[PRAAx] taylorValue f (fstT (rawData R x)) (sndT (rawData R x)) p ≐ taylorValue f R x p := by
    simpa only [subst_taylorValue, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (taylorValue f (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![fstT (rawData R x),sndT (rawData R x),p]) (σ' := ![R,x,p])
        (fun j => by fin_cases j; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl p)
  exact e.eqTrans r

private theorem raw_regular_at (f : PR 2) (R x p q : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (rawF f) p (rawData R x)) (ap2 (rawF f) q (rawData R x))
      ((budget f R x+one)*(unit p+unit q)) (unit p*unit q) := by
  let P := unit p
  let Q := unit q
  let B := budget f R x
  let g := imaginaryF f
  let d := sineData g R x
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have den := positive_product _ _ hP hQ
  have left := distance_radius_mono _ _ B P (B*Q) (P*Q) hP den
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring))
    (distance_symmetric _ _ _ _ hP (finite_taylor_error f R x p hf))
  have right := distance_radius_mono _ _ B Q (B*P) (P*Q) hQ den
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) (finite_taylor_error f R x q hf)
  have mid := point_at (sineF g) d p q (sine_regular g R x (imaginary_input f R x hf))
  have result := distance_triangle_same _ _ _ _ _ _ den
    (distance_triangle_same _ _ _ _ _ _ den left mid) right
  exact distance_congr (raw_at f R x p).eqSymm (raw_at f R x q).eqSymm
    (by dsimp only [B,P,Q]; ipra_ring) (.eqRefl _) result

theorem raw_regular (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular (rawF f) (budget f R x+one) (rawData R x) := by
  refine .allI (.allI ?_)
  let C := (Γ.map Fm.shift).map Fm.shift
  let Rt := Syn.shift (Syn.shift R)
  let xt := Syn.shift (Syn.shift x)
  have h : C ⊢[PRAAx] input f Rt xt := by
    simpa only [Fm.shift, Syn.shift, GaussianRadiusExponentialName.subst_input, C, Rt, xt] using hf.shift.shift
  simpa only [Syn.shift, GaussianFastValueCut.regular, subst_rawData, subst_budget, PTm.subst_add, one,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, unit, GaussianEuclideanPointDistance.unit, C, Rt, xt] using
    raw_regular_at f Rt xt (var 1) (var 0) h

def taylorF (f : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawF f)
def taylorData (f : PR 2) (R x : PTm n) : PTm n :=
  GaussianFastValueCut.nameData (budget f R x+one) (rawData R x)

@[simp] theorem subst_taylorData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (R x : PTm n) :
    Syn.subst σ (taylorData f R x) = taylorData f (Syn.subst σ R) (Syn.subst σ x) := by simp [taylorData]

theorem taylor_regular (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] pointCN (taylorF f) (taylorData f R x) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_regular f R x hf)

theorem taylor_at (f : PR 2) (R x p : PTm n) :
    Γ ⊢[PRAAx] ap2 (taylorF f) p (taylorData f R x) ≐
      taylorValue f R x (GaussianFastValueCut.exponent (budget f R x+one) p) :=
  (GaussianFastValueCut.name_at _ _ _ p).eqTrans
    ((recode_congr (raw_at f R x _)).eqTrans (recode_fixed _ (GaussianScalarSineTaylor.signed_sum_canonical _ _)))

theorem original_sine_taylor_cross (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (imaginaryF f)) (taylorF f) (sineData (imaginaryF f) R x) (taylorData f R x) := by
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (two*budget f R x+two)
    (sine_regular _ _ _ (imaginary_input f R x hf)) (taylor_regular f R x hf)
  refine .allI ?_
  let C := Γ.map Fm.shift
  let Rt := Syn.shift R
  let xt := Syn.shift x
  let p : PTm (n+1) := var 0
  have h : C ⊢[PRAAx] input f Rt xt := by
    simpa only [Fm.shift, Syn.shift, GaussianRadiusExponentialName.subst_input, C, Rt, xt] using hf.shift
  have left := distance_congr (.eqRefl _) (raw_at f Rt xt p).eqSymm (.eqRefl _) (.eqRefl _)
    (finite_taylor_error f Rt xt p h)
  have right := GaussianNameRingLaws.normalized_to_sample (rawF f) (budget f Rt xt+one) (rawData Rt xt) p
    (raw_regular f Rt xt h)
  have result := distance_triangle_same _ _ _ _ _ _ (unit_positive p) left
    (distance_symmetric _ _ _ _ (unit_positive p) right)
  have cost : C ⊢[PRAAx] budget f Rt xt+(budget f Rt xt+one+one) ≐ two*budget f Rt xt+two := by ipra_ring
  simpa only [GaussianNamedDiagonalRate.diagonalRate, Syn.shift, taylorF, taylorData,
    GaussianFastValueCut.subst_nameData, subst_rawData,
    GaussianNamedSineFromExponential.subst_sineData, subst_budget, PTm.subst_add, PTm.subst_mul, two, one,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, C, Rt, xt, p] using
    distance_congr (.eqRefl _) (.eqRefl _) cost (.eqRefl _) result

theorem actual_original_named_sine_taylor_equivalence_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (input f (var 0) (var 1) ⟶
        crossEquivalent (sineF (imaginaryF f)) (taylorF f) (sineData (imaginaryF f) (var 0) (var 1))
          (taylorData f (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_sine_taylor_cross f _ _ Prf.hyp0))

theorem actual_original_named_sine_taylor_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (input f (var 0) (var 1) ⟶ distanceBounded
        (ap2 (sineF (imaginaryF f)) (var 2) (sineData (imaginaryF f) (var 0) (var 1)))
        (taylorValue f (var 0) (var 1) (var 2)) (budget f (var 0) (var 1)) (unit (var 2))) :=
  closeUniv 3 (.impI (finite_taylor_error f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedSineTaylor
