import IPRADerivations.Analysis.Stirling.AllOrders.Truncation.GaussianStirlingAllOrderCentralTaylor

/-!
# The cleared reciprocal-power second-difference error

Clearing the two adjacent denominators makes the reciprocal-power
central Taylor defect a polynomial. The exact constant and quadratic
terms cancel, leaving an explicit fourth-order polynomial in the step.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderReciprocalTaylor

open Finset
open GaussianStirlingAllOrderCentralTaylor (quadratic evenTailTerm central_monomial)

def innerTerm {R : Type*} [CommRing R] (e k : ℕ) (x h : R) : R :=
  if 2≤k then (e.choose k : R)*(x*x)^(e-k)*(-(h*h))^k else 0

def innerTail {R : Type*} [CommRing R] (e : ℕ) (x h : R) : R :=
  ∑ k ∈ range (e+1), innerTerm e k x h

def outerTail {R : Type*} [CommRing R] (e : ℕ) (x h : R) : R :=
  ∑ k ∈ range (e+1), evenTailTerm e k x h

def secondCoefficient (e : ℕ) : ℕ := e*(e+1)

theorem inner_expansion {R : Type*} [CommRing R] (e : ℕ) (x h : R) :
    (x*x-h*h)^e = (x*x)^e-(e : R)*(x*x)^(e-1)*(h*h)+innerTail e x h := by
  rw [show x*x-h*h = -(h*h)+x*x by ring,add_pow]
  have key (k : ℕ) : (-(h*h))^k*(x*x)^(e-k)*(e.choose k : R) =
      (if k=0 then (x*x)^e else 0) +
      (if k=1 then -(e : R)*(x*x)^(e-1)*(h*h) else 0) + innerTerm e k x h := by
    by_cases h0 : k=0
    · subst k
      simp [innerTerm]
    · by_cases h1 : k=1
      · subst k
        simp [innerTerm]
        ring
      · have h2 : 2≤k := by omega
        simp only [if_neg h0,if_neg h1,innerTerm,if_pos h2,_root_.zero_add]
        ring
  simp_rw [key]
  rw [sum_add_distrib,sum_add_distrib]
  have hzero : ∑ k ∈ range (e+1), (if k=0 then (x*x)^e else 0) = (x*x)^e := by simp
  have hone : (∑ k ∈ range (e+1), if k=1 then -(e:R)*(x*x)^(e-1)*(h*h) else 0) =
      -(e:R)*(x*x)^(e-1)*(h*h) := by
    by_cases he : e=0
    · simp [he]
    · have hm : 1 ∈ range (e+1) := mem_range.mpr (by omega)
      rw [sum_eq_single_of_mem 1 hm]
      · simp
      · intro k _ hk
        simp [hk]
  rw [hzero,hone]
  unfold innerTail
  ring

private theorem power_alignment {R : Type*} [CommRing R] (e : ℕ) (he : 2≤e) (x : R) :
    x*x*x^e*x^(e-2) = (x*x)^e := by
  rw [show x*x = x^2 by ring,←pow_mul,←pow_add,←pow_add]
  congr 1
  omega

private theorem inner_power_alignment {R : Type*} [CommRing R] (e : ℕ) (he : 2≤e) (x : R) :
    x*x*(x*x)^(e-1) = (x*x)^e := by
  calc
    x*x*(x*x)^(e-1) = (x*x)^1*(x*x)^(e-1) := by rw [pow_one]
    _ = (x*x)^e := by rw [←pow_add,show 1+(e-1)=e by omega]

def clearedDefect {R : Type*} [CommRing R] (e : ℕ) (x h : R) : R :=
  x*x*(x^e*((x+h)^e+(x-h)^e)-2*(x*x-h*h)^e) -
    (secondCoefficient e : ℕ)*(h*h)*(x*x-h*h)^e

theorem exact_cleared_error {R : Type*} [CommRing R] (e : ℕ) (he : 2≤e) (x h : R) :
    clearedDefect e x h =
      x*x*(x^e*outerTail e x h-2*innerTail e x h) +
        (secondCoefficient e : ℕ)*(h*h)*((e : R)*(x*x)^(e-1)*(h*h)-innerTail e x h) := by
  have a := central_monomial e x h
  have b := inner_expansion e x h
  have c := power_alignment e he x
  have d := inner_power_alignment e he x
  have e₀ : (x*x)^e=x^e*x^e := by rw [mul_pow]
  have q : (quadratic e : R)+2*(e:R) = (secondCoefficient e : R) := by
    have en : quadratic e+2*e=secondCoefficient e := by
      unfold quadratic secondCoefficient
      have h : e-1+1=e := by omega
      nlinarith [congrArg (e*·) h]
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun z : ℕ => (z : R)) en
  unfold clearedDefect outerTail
  linear_combination x*x*x^e*a - (2*x*x+(secondCoefficient e:R)*(h*h))*b
    +(quadratic e:R)*(h*h)*c+2*(e:R)*(h*h)*d-2*x*x*e₀+
      (x*x)^e*(h*h)*q

def outerFourth {R : Type*} [CommRing R] (e : ℕ) (x h : R) : R :=
  ∑ k ∈ range (e+1), if 4≤k ∧ Even k then (2*e.choose k : ℕ)*x^(e-k)*h^(k-4) else 0

def innerFourth {R : Type*} [CommRing R] (e : ℕ) (x h : R) : R :=
  ∑ k ∈ range (e+1), if 2≤k then (e.choose k : R)*(x*x)^(e-k)*(-1:R)^k*(h*h)^(k-2) else 0

theorem outer_fourth {R : Type*} [CommRing R] (e : ℕ) (x h : R) :
    outerTail e x h = h^4*outerFourth e x h := by
  unfold outerTail outerFourth
  rw [Finset.mul_sum]
  refine sum_congr rfl (fun k _ => ?_)
  unfold evenTailTerm
  split_ifs with h₄
  · have ep : h^k=h^4*h^(k-4) := by
      rw [←pow_add,Nat.add_sub_of_le h₄.1]
    rw [ep]
    ring
  · ring

theorem inner_fourth {R : Type*} [CommRing R] (e : ℕ) (x h : R) :
    innerTail e x h = h^4*innerFourth e x h := by
  unfold innerTail innerFourth
  rw [Finset.mul_sum]
  refine sum_congr rfl (fun k _ => ?_)
  unfold innerTerm
  split_ifs with h₂
  · have ep : (h*h)^k=h^4*(h*h)^(k-2) := by
      rw [show h^4=(h*h)^2 by ring,←pow_add,Nat.add_sub_of_le h₂]
    rw [show -(h*h)=(-1)*(h*h) by ring,mul_pow (-1:R) (h*h),ep]
    ring
  · ring

theorem exact_fourth_order {R : Type*} [CommRing R] (e : ℕ) (he : 2≤e) (x h : R) :
    clearedDefect e x h =
      h^4*(x*x*(x^e*outerFourth e x h-2*innerFourth e x h) +
        (secondCoefficient e : ℕ)*((e : R)*(x*x)^(e-1)-(h*h)*innerFourth e x h)) := by
  rw [exact_cleared_error e he,outer_fourth,inner_fourth]
  ring

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderReciprocalTaylor
