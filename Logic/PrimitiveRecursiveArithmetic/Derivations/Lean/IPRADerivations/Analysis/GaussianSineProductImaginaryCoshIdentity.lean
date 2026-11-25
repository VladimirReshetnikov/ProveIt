import IPRADerivations.Analysis.GaussianSineProductImaginaryHyperbolicDerivative

/-!
# The original hyperbolic derivative as π cosh

This binds the signed first-order exponential combination to the
elementary positive sum of the original two exponential names.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryCoshIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (eval_re_code eval_im_code)
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (through_identity equivalent_of_envelope product_right_error multiply_sample_error add_sample_error three)
open GaussianNamedDifference (difference_distance name_regular sample_error)
open GaussianPiRationalScale (point native)
open GaussianPiRationalScaleFactors (signedF signedData signed_regular)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (qadd qadd_represents qmul qmul_canonical qmul_represents ofGaussian_represents
  positive_product canonical_unique represents_congr)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (distanceBounded qsub qsub_represents)
open GaussianRationalSyntheticDivision (qmul_congr rescale_to)
open GaussianRootAlgebra (equal_of_values re_add im_add re_sub im_sub re_mul im_mul re_neg im_neg)
open GaussianSineProductImaginaryHyperbolic (expF expData)
open GaussianSineProductImaginaryHyperbolicDerivative (branchF branchData derivativeF derivativeData derivative_regular negativeHalf)
open GaussianSineProductImaginaryLogDerivative (realNumerator)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Pi" => GaussianGammaHalfPiName.nameF
local notation "Diff" => GaussianNamedDifference.nameF

def half : PTm n := point false one two
def sumF : PR 2 := addF expF expF
def sumData (A B R x : PTm n) : PTm n := addData (expData true A B R x) (expData false A B R x)
def coshF : PR 2 := multiplyF constantF sumF
def coshData (A B R x : PTm n) : PTm n := multiplyData constantF sumF half (sumData A B R x)
def productF : PR 2 := multiplyF Pi coshF
def productData (A B R x : PTm n) : PTm n := multiplyData Pi coshF x (coshData A B R x)

private theorem ex_regular (s : Bool) (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) : Γ ⊢[PRAAx] pointCN expF (expData s A B R x) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (GaussianPiRationalScale.exponential_input s A B R x hB hA)

theorem cosh_regular (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN coshF (coshData A B R x) :=
  multiply_fast _ _ _ _ (constant_regular _)
    (add_fast _ _ _ _ (ex_regular true A B R x hB hA) (ex_regular false A B R x hB hA))

theorem rational_identity (a b u : PTm n) : Γ ⊢[PRAAx]
    qmul negativeHalf (qsub (qmul a (qmul (point true one one) u)) (qmul b (qmul (point false one one) u))) ≐
      qmul u (qmul half (qadd a b)) := by
  let E := rawDen a*rawDen b*rawDen u
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _
    (positive_product _ _ (raw_den_positive a) (raw_den_positive b)) (raw_den_positive u)
  have h₂ : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hE₂ := positive_product _ _ hE hE
  have ha := rescale_to a (rawGaussian a) (rawDen a) (rawDen b*rawDen u) E (raw_represents (Γ := Γ) a) (by dsimp only [E]; ipra_ring)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen a*rawDen u) E (raw_represents (Γ := Γ) b) (by dsimp only [E]; ipra_ring)
  have hu := rescale_to u (rawGaussian u) (rawDen u) (rawDen a*rawDen b) E (raw_represents (Γ := Γ) u) (by dsimp only [E]; ipra_ring)
  have sign (s : Bool) := ofGaussian_represents (Γ := Γ) (native s (one : PTm n)) one (le_refl one)
  have mulSign (s : Bool) := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (one_mul E)
    (qmul_represents _ _ _ _ _ _ (le_refl one) hE (sign s) hu)
  have l₁ := qmul_represents _ _ _ _ _ _ hE hE ha (mulSign true)
  have l₂ := qmul_represents _ _ _ _ _ _ hE hE hb (mulSign false)
  have l := qmul_represents negativeHalf _ _ _ _ _ h₂ hE₂ (ofGaussian_represents (native true one) _ h₂)
    (qsub_represents _ _ _ _ _ hE₂ l₁ l₂)
  have r₁ := qmul_represents half _ _ _ _ _ h₂ hE (ofGaussian_represents (native false one) _ h₂)
    (qadd_represents _ _ _ _ _ hE ha hb)
  have r := qmul_represents _ _ _ _ _ _ hE (positive_product _ _ h₂ hE) hu r₁
  have r' := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _)
    (show Γ ⊢[PRAAx] E*(two*E) ≐ two*(E*E) by ipra_ring) r
  apply canonical_unique _ _ _ (two*(E*E)) (qmul_canonical _ _) (qmul_canonical _ _)
    (positive_product _ _ h₂ hE₂) (hrv := r')
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := l)
  apply equal_of_values <;>
    simp [re_add,im_add,re_sub,im_sub,re_mul,im_mul,re_neg,im_neg,native,realNumerator,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;>
    ring

private def productCost (f g : PR 2) (x y : PTm n) : PTm n := multiplyModulus f g x y+one
private def scalarCost (g : PR 2) (a x C : PTm n) : PTm n := productCost constantF g a x+U constantF a*C
private def branchCost (s : Bool) (A B R x : PTm n) : PTm n :=
  productCost expF signedF (expData s A B R x) (signedData s x)+
    U expF (expData s A B R x)*productCost constantF Pi (point s one one) x
private def derivCost (A B R x : PTm n) : PTm n := scalarCost (Diff branchF branchF) negativeHalf
  (GaussianNamedDifference.data (branchData true A B R x) (branchData false A B R x))
  (num 6+(branchCost true A B R x+branchCost false A B R x))
private def coshCost (A B R x : PTm n) : PTm n :=
  productCost Pi coshF x (coshData A B R x)+U Pi x*scalarCost sumF half (sumData A B R x) three

private theorem product_error (f g : PR 2) (x y p r C : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 g p y) r C (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF f g) p (multiplyData f g x y)) (qmul (ap2 f p x) r)
      (productCost f g x y+U f x*C) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p) (multiply_sample_error f g x y p hf hg)
    (product_right_error _ _ _ _ _ _ _ (unit_positive p) h (sample_bound g y p hg) (sample_bound f x p hf))

private theorem scalar_error (g : PR 2) (a y p r C : PTm n)
    (hg : Γ ⊢[PRAAx] pointCN g y)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 g p y) r C (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF constantF g) p (multiplyData constantF g a y)) (qmul a r)
      (scalarCost g a y C) (unit p) :=
  distance_congr (.eqRefl _) (qmul_congr (constant_at p a) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (product_error constantF g a y p r C (constant_regular a) hg h)

private theorem branch_at (s : Bool) (A B R x p : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 branchF p (branchData s A B R x))
      (qmul (ap2 expF p (expData s A B R x)) (qmul (point s one one) (ap2 Pi p x))) (branchCost s A B R x) (unit p) := by
  let a : PTm n := point s one one
  have pi := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have sign := distance_congr (.eqRefl _) (qmul_congr (constant_at p a) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error constantF Pi a x p (constant_regular a) pi)
  exact product_error expF signedF _ _ p _ _ (ex_regular s A B R x hB hA) (signed_regular s x) sign

theorem derivative_at (A B R x p : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 derivativeF p (derivativeData A B R x))
      (qmul negativeHalf (qsub (qmul (ap2 expF p (expData true A B R x)) (qmul (point true one one) (ap2 Pi p x)))
        (qmul (ap2 expF p (expData false A B R x)) (qmul (point false one one) (ap2 Pi p x))))) (derivCost A B R x) (unit p) := by
  have regular (s : Bool) := multiply_fast expF signedF (expData s A B R x) (signedData s x)
    (ex_regular s A B R x hB hA) (signed_regular s x)
  have read := sample_error branchF branchF _ _ p (regular true) (regular false)
  have moved := difference_distance _ _ _ _ _ _ _ (unit_positive p) (branch_at true A B R x p hB hA) (branch_at false A B R x p hB hA)
  exact scalar_error (Diff branchF branchF) negativeHalf _ p _ _
    (name_regular _ _ _ _ (regular true) (regular false)) (distance_triangle_same _ _ _ _ _ _ (unit_positive p) read moved)

theorem cosh_product_at (A B R x p : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 productF p (productData A B R x))
      (qmul (ap2 Pi p x) (qmul half (qadd (ap2 expF p (expData true A B R x)) (ap2 expF p (expData false A B R x)))))
      (coshCost A B R x) (unit p) := by
  have neg := ex_regular true A B R x hB hA
  have pos := ex_regular false A B R x hB hA
  have h := scalar_error sumF half (sumData A B R x) p _ three (add_fast _ _ _ _ neg pos)
    (add_sample_error expF expF _ _ p neg pos)
  exact product_error Pi coshF x (coshData A B R x) p _ _ (GaussianGammaHalfPiName.name_regular x)
    (cosh_regular A B R x hB hA) h

theorem derivative_as_pi_cosh (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent derivativeF productF (derivativeData A B R x) (productData A B R x) := by
  apply equivalent_of_envelope _ _ _ _ (derivCost A B R x+coshCost A B R x)
    (derivative_regular A B R x hB hA)
    (multiply_fast _ _ _ _ (GaussianGammaHalfPiName.name_regular x) (cosh_regular A B R x hB hA))
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  let p : PTm (n+1) := var 0
  have bs : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hB.shift
  have hs : Δ ⊢[PRAAx] le (sh A) (sh R*sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hA.shift
  have v := through_identity _ _ _ _ _ _ _ (unit_positive p)
    (derivative_at (sh A) (sh B) (sh R) (sh x) p bs hs)
    (cosh_product_at (sh A) (sh B) (sh R) (sh x) p bs hs)
    (rational_identity (ap2 expF p (expData true (sh A) (sh B) (sh R) (sh x)))
      (ap2 expF p (expData false (sh A) (sh B) (sh R) (sh x))) (ap2 Pi p (sh x)))
  simpa only [Δ,sh,p,Syn.shift,derivCost,coshCost,branchCost,scalarCost,productCost,productF,productData,coshData,sumData,
    derivativeData,branchData,signedData,expData,negativeHalf,half,GaussianNameArithmetic.subst_multiplyData,
    GaussianNamedDifference.subst_data,GaussianNameArithmetic.subst_multiplyModulus,GaussianNameBounds.subst_U,
    GaussianRadiusExponentialName.subst_data,GaussianPiRationalScale.subst_data,GaussianPiRationalScale.subst_point,
    GaussianNameArithmetic.subst_addData,PTm.subst_mul,PTm.subst_add,PTm.subst_num,three,one,two,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using v

theorem actual_hyperbolic_sine_derivative_is_pi_cosh_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ le (var 0) (var 2*var 1)) ⟶ crossEquivalent derivativeF productF
      (derivativeData (var 0) (var 1) (var 2) (var 3)) (productData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (derivative_as_pi_cosh _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryCoshIdentity
