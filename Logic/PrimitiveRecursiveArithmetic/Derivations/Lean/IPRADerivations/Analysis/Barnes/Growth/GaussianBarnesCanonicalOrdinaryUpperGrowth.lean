import IPRADerivations.Analysis.Barnes.Growth.BarnesDyadicRadius
import IPRADerivations.Analysis.Barnes.Growth.BarnesUpperOrderThreshold
import IPRADerivations.Analysis.Barnes.Growth.GaussianBarnesCanonicalDyadicUpperGrowth
import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedIncrementEndpoints

/-!
# Barnes upper growth on ordinary integer disks

Use the computed dyadic bracket of the integer radius. The enclosing
disk also contains the centered argument of (G). Compare the same
named evaluation on the two certified disks, then discharge the
positive rational order gap by clearing the exponent denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalOrdinaryUpperGrowth

open_ipra
open BarnesDyadicRadius (index bracket threshold_le_index)
open ComplexLogarithmRemainder (normSq_neg normSq_one oneCode)
open GaussianBarnesCanonicalDyadicUpperGrowth (exponent growthConstant named_sample_bound transfer_bound)
open GaussianBarnesCanonicalNamedDemand (source data)
open GaussianBarnesCanonicalNamedFrozen (source_widen independent_radii)
open GaussianCoefficientNameBounds (bounded_radius_mono_one unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFactorBudget (power_monotone_length)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameArithmetic (addF addData)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "B" => GaussianBarnesCanonicalNamed.nameF

def shellConstant : PTm n := num 48*growthConstant+two
def shellExponent (j : PTm n) : PTm n := shellConstant*succ j*(unit j*unit j)
def orderThreshold (b : PTm n) : PTm n := unit (BarnesUpperOrderThreshold.threshold shellConstant b)

private theorem next_two (j : PTm n) : Γ ⊢[PRAAx] unit (j+two) ≐ unit j*(two*two) :=
  (pw_add two j two).eqTrans (congrMul (.eqRefl _) ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))))

private theorem shell_allowance (j : PTm n) : Γ ⊢[PRAAx] le (exponent (j+two)+two) (shellExponent j) := by
  let D := unit j*unit j
  let K : PTm n := growthConstant
  let A := num 48*K*succ j*D
  have count : Γ ⊢[PRAAx] le (succ (j+two)) (num 3*succ j) :=
    le_of_eq_add (d := two*j) (by ipra_ring)
  have e : Γ ⊢[PRAAx] exponent (j+two) ≐ succ (j+two)*(num 16*K*D) := by
    unfold exponent
    refine (congrMul (.eqRefl _) (congrMul (next_two j) (next_two j))).eqTrans ?_
    dsimp [K,D]
    ipra_ring
  have hA : Γ ⊢[PRAAx] le (exponent (j+two)) A :=
    le_congr e.eqSymm (by dsimp [A]; ipra_ring) (mul_le_mul_right _ count)
  have hD := positive_product _ _ (zero_lt_succ (Γ := Γ) j)
    (positive_product _ _ (unit_positive j) (unit_positive j))
  have spare := le_congr (one_mul two) (.eqRefl _) (mul_le_mul_right two hD)
  exact le_congr (.eqRefl _) (by dsimp [A,K,D,shellExponent,shellConstant]; ipra_ring)
    (add_le_add₂ hA spare)

theorem named_shell_bound (f : PR 2) (p x R j : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hR : Γ ⊢[PRAAx] le R (unit (j+two))) :
    Γ ⊢[PRAAx] bounded (ap2 (B f) p (data x R)) (unit (shellExponent j)) one := by
  let S := unit (j+two)
  have hS := source_widen f x R S hf hR
  have moved := transfer_bound (B f) (B f) p (data x R) (data x S) (exponent (j+two))
    (independent_radii f x R S hf hS) (named_sample_bound f p x (j+two) hS)
  exact bounded_radius_mono_one (unit_monotone (shell_allowance j)) moved

def minusOne : PTm n := ofGaussian (ComplexLogarithmRemainder.neg oneCode) one

def nameF (f : PR 2) : PR 2 := B (addF f constantF)
def valueData (x r : PTm n) : PTm n := data (addData x minusOne) (r+one)

private theorem minus_source : Γ ⊢[PRAAx] source constantF minusOne one := by
  have radius : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (ComplexLogarithmRemainder.neg oneCode) (one*one) :=
    le_congr ((normSq_neg oneCode).eqTrans normSq_one).eqSymm (by ipra_ring) (le_refl one)
  exact GaussianBarnesCanonicalNamed.constant_source _ _ _ (.andI (le_refl one) radius)

private theorem shifted_source (f : PR 2) (x r : PTm n) (hf : Γ ⊢[PRAAx] source f x r) :
    Γ ⊢[PRAAx] source (addF f constantF) (addData x minusOne) (r+one) :=
  GaussianBarnesCanonicalNamedIncrementEndpoints.shifted_source f constantF x minusOne r hf minus_source

theorem regular (f : PR 2) (x r : PTm n) (hf : Γ ⊢[PRAAx] source f x r) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN (nameF f) (valueData x r) :=
  GaussianBarnesCanonicalNamed.name_regular _ _ _ (shifted_source f x r hf)

private theorem shifted_radius (r : PTm n) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] le (r+one) (unit (index r+two)) := by
  let j := index r
  have tr : Γ ⊢[PRAAx] le r (unit (succ j)) :=
    le_trans (le_succ_self r) (bracket r hr).andE₂
  have e : Γ ⊢[PRAAx] unit (succ j)*two ≐ unit (j+two) :=
    (congrMul (pw_succ two j) (.eqRefl two)).eqTrans
      ((by ipra_ring : Γ ⊢[PRAAx] unit j*two*two ≐ unit j*(two*two)).eqTrans (next_two j).eqSymm)
  exact le_trans (add_le_add₂ (le_refl r) hr)
    (le_congr (by ipra_ring) e (mul_le_mul_right two tr))

theorem sample_bound (f : PR 2) (p x r : PTm n) (hf : Γ ⊢[PRAAx] source f x r) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF f) p (valueData x r)) (unit (shellExponent (index r))) one :=
  named_shell_bound (addF f constantF) p (addData x minusOne) (r+one) (index r)
    (shifted_source f x r hf) (shifted_radius r hr)

theorem logarithmic_exponent_bound (r : PTm n) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] le (shellExponent (index r)) (shellConstant*succ (index r)*(r*r)) :=
  Common.mul_le_mul (le_refl _) (sq_le_sq (bracket r hr).andE₁)

theorem order_gap (r a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (ht : Γ ⊢[PRAAx] le (orderThreshold b) r) :
    Γ ⊢[PRAAx] le (pw (shellExponent (index r)) b) (pw r (two*b+a)) := by
  let j := index r
  have hr : Γ ⊢[PRAAx] le one r := le_trans (unit_positive _) ht
  have hj := threshold_le_index r (BarnesUpperOrderThreshold.threshold shellConstant b) hr ht
  have lower : Γ ⊢[PRAAx] le (unit j) r := (bracket r hr).andE₁
  have base := BarnesUpperOrderThreshold.exponent_bound shellConstant b j hb hj
  exact le_trans base (le_trans (pw_le_pw (two*b+one) lower)
    (power_monotone_length r (two*b+one) (two*b+a) hr (add_le_add₂ (le_refl _) ha)))

theorem order_upper (f : PR 2) (p x r a b : PTm n) (hf : Γ ⊢[PRAAx] source f x r)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (ht : Γ ⊢[PRAAx] le (orderThreshold b) r) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF f) p (valueData x r)) (unit (shellExponent (index r))) one ⋏
      le (pw (shellExponent (index r)) b) (pw r (two*b+a)) :=
  .andI (sample_bound f p x r hf (le_trans (unit_positive _) ht)) (order_gap r a b ha hb ht)

theorem actual_Barnes_ordinary_disk_upper_order_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let p := var 0
     let x := var 1
     let r := var 2
     let a := var 3
     let b := var 4
     ((source f x r ⋏ (le one a ⋏ le one b)) ⋏ le (orderThreshold b) r) ⟶
       bounded (ap2 (nameF f) p (valueData x r)) (unit (shellExponent (index r))) one ⋏
         le (pw (shellExponent (index r)) b) (pw r (two*b+a))) :=
  closeUniv 5 (.impI (order_upper f _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂.andE₁
    Prf.hyp0.andE₁.andE₂.andE₂ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalOrdinaryUpperGrowth
