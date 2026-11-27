import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.Coordinates.GaussianArctangentCayleyValues
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianBoundedConstantProductName
import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfPiName
import IPRADerivations.Analysis.Exponential.Names.LocalEstimates.GaussianNamedExponentialLinearRate
import IPRADerivations.Analysis.Trigonometry.Hyperbolic.ProductEstimates.GaussianSineProductImaginaryScaling
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaHalfShift
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff

/-!
# Original π scaled by signed rational arguments

Both signs use the original π sampler with an exact rational constant.
The actual samples have certified Euclidean bounds, and addition of
rational arguments agrees with named addition.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianPiRationalScale

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (eval_im_code eval_re_code normSq normSq_neg)
open GaussianArctangentCayleyValues (imaginaryCode imaginaryPoint)
open GaussianBoundedConstantProductName (constantF constant_regular ordinary_product_identity)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (addData addF add_fast multiplyData multiplyF)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (right_distributive equivalent_of_envelope negativeF negativeData negative_fast negative_sample_error three)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianRationalHorner
  (canonical canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents positive_product qadd qadd_canonical
    qadd_represents qmul qmul_canonical qmul_represents represents_congr)
open GaussianRationalMetric (bounded bounded_iff qnegative qnegative_canonical qnegative_represents qsub)
open GaussianRationalL1 (raw_represents raw_den_positive rawDen)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qzero_add qmul_congr qsub_congr)
open GaussianRootAlgebra (equal_of_values im_add im_mul im_neg re_add re_mul re_neg)
open GaussianSineProductImaginaryLogDerivative (axisNumerator realNumerator)
open GaussianSineProductImaginaryLogDerivativeTail (real_norm)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "piF" => GaussianGammaHalfPiName.nameF
local notation "πbound" => U piF

def native (negative : Bool) (A : PTm n) : PTm n :=
  if negative then ComplexLogarithmRemainder.neg (realNumerator A) else realNumerator A

def point (negative : Bool) (A B : PTm n) : PTm n := ofGaussian (native negative A) B

def nameF : PR 2 := GaussianBoundedConstantProductName.nameF piF
def data (negative : Bool) (A B R x : PTm n) : PTm n :=
  GaussianBoundedConstantProductName.data R (point negative A B) x

@[simp] theorem subst_native {m : ℕ} (σ : Fin n → PTm m) (s : Bool) (A : PTm n) :
    Syn.subst σ (native s A) = native s (Syn.subst σ A) := by
  cases s <;> simp [native]

@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (s : Bool) (A B : PTm n) :
    Syn.subst σ (point s A B) = point s (Syn.subst σ A) (Syn.subst σ B) := by
  simp [point]

ipra_subst data

theorem point_add (s : Bool) (A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd (point s A B) (point s C B) ≐ point s (A+C) B := by
  have a := ofGaussian_represents (Γ := Γ) (native s A) B hB
  have b := ofGaussian_represents (Γ := Γ) (native s C) B hB
  have left := qadd_represents _ _ _ _ _ hB a b
  have right := ofGaussian_represents (Γ := Γ) (native s (A+C)) B hB
  apply canonical_unique _ _ _ B (qadd_canonical _ _) (ofGaussian_canonical _ _ hB) hB (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  cases s <;> apply equal_of_values <;>
    simp [native, re_add, im_add, re_neg, im_neg, realNumerator, eval_re_code, eval_im_code, ZT.toZ_ofNat] <;> ring

theorem point_negate (s : Bool) (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qnegative (point s A B) ≐ point (!s) A B := by
  have left := qnegative_represents _ _ _ (ofGaussian_represents (Γ := Γ) (native s A) B hB)
  have right := ofGaussian_represents (Γ := Γ) (native (!s) A) B hB
  apply canonical_unique _ _ _ B (qnegative_canonical _) (ofGaussian_canonical _ _ hB) hB (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  cases s <;> apply equal_of_values <;> simp [native, re_neg, im_neg]

theorem imaginary_axis_point (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul imaginaryPoint (ofGaussian (axisNumerator A) B) ≐ point true A B := by
  have left := qmul_represents _ _ _ _ _ _ (le_refl one) hB
    (ofGaussian_represents (Γ := Γ) imaginaryCode one (le_refl one))
    (ofGaussian_represents (axisNumerator A) B hB)
  have right := ofGaussian_represents (Γ := Γ) (native true A) B hB
  apply canonical_unique _ _ _ B (qmul_canonical _ _) (ofGaussian_canonical _ _ hB) hB (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := one_mul B) (h := left)
  change Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.mul imaginaryCode (axisNumerator A))
    (ComplexLogarithmRemainder.neg (realNumerator A))
  apply equal_of_values <;>
    simp only [re_mul, im_mul, re_neg, im_neg, imaginaryCode, axisNumerator, realNumerator,
      eval_re_code, eval_im_code, ZT.toZ_ofNat] <;>
    ipra_simps <;> ring

private theorem native_norm (s : Bool) (A : PTm n) : Γ ⊢[PRAAx] normSq (native s A) ≐ A*A := by
  cases s
  · exact real_norm A
  · exact (normSq_neg (realNumerator A)).eqTrans (real_norm A)

theorem point_bound (s : Bool) (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] le (D*A) (C*B)) : Γ ⊢[PRAAx] bounded (point s A B) C D := by
  have sq := le_mul_mono h h
  have e : Γ ⊢[PRAAx] (D*A)*(D*A) ≐ (D*D)*normSq (native s A) :=
    (show Γ ⊢[PRAAx] (D*A)*(D*A) ≐ (D*D)*(A*A) from by ipra_ring).eqTrans
      (congrMul (.eqRefl _) (native_norm s A).eqSymm)
  exact (bounded_iff _ _ _ _ _ hB hD (ofGaussian_represents _ _ hB)).iffMpr
    (le_congr e (by ipra_ring) sq)

private theorem scale_input (s : Bool) (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] GaussianBoundedConstantProductName.input piF R (point s A B) x :=
  .andI (GaussianGammaHalfPiName.name_regular x)
    (point_bound s A B R one hB (le_refl one) (le_congr (one_mul _).eqSymm (.eqRefl _) h))

theorem regular (s : Bool) (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN nameF (data s A B R x) :=
  GaussianBoundedConstantProductName.name_regular piF R _ x (scale_input s A B R x hB h)

theorem ordinary (s : Bool) (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent nameF (multiplyF constantF piF) (data s A B R x)
      (multiplyData constantF piF (point s A B) x) :=
  ordinary_product_identity piF R _ x (scale_input s A B R x hB h)

theorem sample_bound_and_canonical (s : Bool) (A B R p x : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data s A B R x)) (A*πbound x) B ⋏ canonical (ap2 nameF p (data s A B R x)) := by
  let C := point s A B
  let t := GaussianBoundedConstantProductName.clock p R
  have b := sample_bound piF x t (GaussianGammaHalfPiName.name_regular (Γ := Γ) x)
  have hc := point_bound s A B A B hB hB (le_congr (mul_comm _ _) (.eqRefl _) (le_refl _))
  have eq := GaussianBoundedConstantProductName.sample_at (Γ := Γ) piF p R C x
  exact .andI (bound_congr eq.eqSymm (.eqRefl _) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ hB (le_refl one) hc b))
    (GaussianRationalHorner.canonical_congr eq (qmul_canonical _ _))

theorem small_source (s : Bool) (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le A (R*B)) (hsmall : Γ ⊢[PRAAx] le (A*πbound x) B) : Γ ⊢[PRAAx]
    GaussianNamedExponentialLinearRate.source nameF (data s A B R x) (A*πbound x) B := by
  refine .andI hB (.andI hsmall (.andI (regular s A B R x hB h) (.allI ?_)))
  let Δ := Γ.map Fm.shift
  let sh (a : PTm n) := Syn.shift a
  have bs : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hB.shift
  simpa only [GaussianNamedExponentialLinearRate.smallSamples, Syn.shift, sh, Δ, subst_data, PTm.subst_mul,
    GaussianNameBounds.subst_U] using sample_bound_and_canonical s (sh A) (sh B) (sh R) (var 0) (sh x) bs

theorem exponential_input (s : Bool) (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le A (R*B)) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input nameF (R*πbound x) (data s A B R x) := by
  refine .andI (regular s A B R x hB h) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (a : PTm n) := Syn.shift a
  have bs : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hB.shift
  have hs : Δ ⊢[PRAAx] le (sh A) (sh R*sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  have b := (sample_bound_and_canonical s (sh A) (sh B) (sh R) (var 0) (sh x) bs).andE₁
  have target : Δ ⊢[PRAAx] bounded (ap2 nameF (var 0) (data s (sh A) (sh B) (sh R) (sh x))) (sh R*πbound (sh x)) one :=
    bounded_radius_mono _ _ _ _ _ bs (le_refl one)
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (πbound (sh x)) hs)) b
  simpa only [GaussianRadiusExponentialName.boundedSamples, Syn.shift, sh, Δ, subst_data, PTm.subst_mul,
    GaussianNameBounds.subst_U] using target

theorem addition (s : Bool) (A B C R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] le (A+C) (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent nameF (addF nameF nameF) (data s (A+C) B R x)
      (addData (data s A B R x) (data s C B R x)) := by
  let a := point s A B
  let c := point s C B
  let e := point s (A+C) B
  let H := multiplyF constantF piF
  let ha := multiplyData constantF piF a x
  let hc := multiplyData constantF piF c x
  let he := multiplyData constantF piF e x
  let ca := data s A B R x
  let cc := data s C B R x
  have pi := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have sa := scale_input s A B R x hB (le_trans (le_add_right _ _) h)
  have sc := scale_input s C B R x hB (le_trans (le_add_left _ _) h)
  have se := scale_input s (A+C) B R x hB h
  have rawSum := constant_sum a c e (point_add s A B C hB)
  have toSum := multiply_cross constantF (addF constantF constantF) piF piF e (addData a c) x x
    (constant_regular e) (add_fast _ _ _ _ (constant_regular a) (constant_regular c)) pi pi
    (cross_symm _ _ _ _ rawSum) (cross_refl _ _ pi)
  have distributivity := right_distributive constantF constantF piF a c x (constant_regular a) (constant_regular c) pi
  have attach := add_cross H nameF H nameF ha ca hc cc
    (GaussianNameArithmetic.multiply_fast constantF piF a x (constant_regular a) pi)
    (GaussianBoundedConstantProductName.name_regular piF R a x sa)
    (GaussianNameArithmetic.multiply_fast constantF piF c x (constant_regular c) pi)
    (GaussianBoundedConstantProductName.name_regular piF R c x sc)
    (cross_symm _ _ _ _ (ordinary_product_identity piF R a x sa))
    (cross_symm _ _ _ _ (ordinary_product_identity piF R c x sc))
  exact cross_trans _ _ _ _ _ _ (ordinary_product_identity piF R e x se)
    (cross_trans _ _ _ _ _ _ toSum (cross_trans _ _ _ _ _ _ distributivity attach))

private theorem negate_product (a b : PTm n) :
    Γ ⊢[PRAAx] qnegative (qmul a b) ≐ qmul (qnegative a) b := by
  let A := rawDen a
  let B := rawDen b
  have ha := raw_den_positive (Γ := Γ) a
  have hb := raw_den_positive (Γ := Γ) b
  have left := qnegative_represents _ _ _ (qmul_represents _ _ _ _ _ _ ha hb (raw_represents a) (raw_represents b))
  have right := qmul_represents _ _ _ _ _ _ ha hb (qnegative_represents _ _ _ (raw_represents a)) (raw_represents b)
  apply canonical_unique _ _ _ (A*B) (qnegative_canonical _) (qmul_canonical _ _) (positive_product _ _ ha hb)
    (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply equal_of_values <;> simp only [re_mul, im_mul, re_neg, im_neg] <;> ring

private theorem negated_sample (s : Bool) (A B R x p : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qsub GaussianRationalHorner.qzero (ap2 nameF p (data s A B R x)) ≐
      ap2 nameF p (data (!s) A B R x) := by
  let C := point s A B
  let v := ap2 piF (GaussianBoundedConstantProductName.clock p R) x
  have h₁ := GaussianBoundedConstantProductName.sample_at (Γ := Γ) piF p R C x
  have h₂ := GaussianBoundedConstantProductName.sample_at (Γ := Γ) piF p R (point (!s) A B) x
  exact (qsub_congr (.eqRefl _) h₁).eqTrans
    ((qzero_add (qnegative (qmul C v)) (qnegative_canonical _)).eqTrans
      ((negate_product C v).eqTrans ((qmul_congr (point_negate s A B hB) (.eqRefl v)).eqTrans h₂.eqSymm)))

theorem negation (s : Bool) (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF nameF) nameF (negativeData (data s A B R x)) (data (!s) A B R x) := by
  apply equivalent_of_envelope _ _ _ _ three (negative_fast _ _ (regular s A B R x hB h)) (regular (!s) A B R x hB h)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (a : PTm n) := Syn.shift a
  have bs : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hB.shift
  have hs : Δ ⊢[PRAAx] le (sh A) (sh R*sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  have q := negative_sample_error nameF (data s (sh A) (sh B) (sh R) (sh x)) (var 0)
    (regular s (sh A) (sh B) (sh R) (sh x) bs hs)
  simpa only [Δ, sh, Syn.shift, subst_data, GaussianNameRingLaws.subst_negativeData, three, one, two, PTm.subst_add,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _)
      (negated_sample s (sh A) (sh B) (sh R) (sh x) (var 0) bs) (.eqRefl _) (.eqRefl _) q

theorem actual_named_pi_rational_addition_closed (s : Bool) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let A := var 0
       let B := var 1
       let C := var 2
       let R := var 3
       let x := var 4
       (le one B ⋏ le (A+C) (R*B)) ⟶
       crossEquivalent nameF (addF nameF nameF) (data s (A+C) B R x)
         (addData (data s A B R x) (data s C B R x))) :=
  closeUniv 5 (.impI (addition s _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPiRationalScale
