import Trace74PellCoefficientReduction
import DiophantineConsistency.ArithmeticPow

/-! Power residues modulo a square-minus-one modulus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74PowerPeriodResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem same_mul {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x*z)%m=(y*w)%m := by
  rw [mod_mul hm,mod_mul (a:=y) hm,h,h']

/-- If `q²=m+1`, represented powers of `q²` are one modulo m even
at nonstandard internal indices. -/
theorem square_power_one (q m k : V) (hm : 0<m) (hq : q*q=m+1) :
    power (q*q) k%m=(1:V)%m := by
  have hqq : (q*q)%m=(1:V)%m := by
    rw [hq,show m+1=1+m*1 by ring,mod_add_mul' _ _ hm]
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [power_succ]
    simpa only [one_mul] using same_mul hm hqq ih

/-- Reduction of represented powers by an internal multiple of `2e`. -/
theorem power_period (a e q m k j : V) (hm : 0<m)
    (hq : q=power a e) (hqm : q*q=m+1) :
    power a ((2*e)*k+j)%m=power a j%m := by
  have hp2 : power a (2*e)=q*q := by
    rw [show 2*e=e+e by ring,power_add,←hq]
  rw [power_add,←power_iterate,hp2]
  simpa only [one_mul] using
    same_mul hm (square_power_one q m k hm hqm) (show power a j%m=power a j%m from rfl)

/-- The concrete candidate index reduces to 93925 modulo twice 590069;
only the positive modulus and square-minus-one binding remain premises. -/
theorem candidate_power_period (q m : V) (hm : 0<m)
    (hq : q=power 2 590069) (hqm : q*q=m+1) :
    power 2 3056651345%m=power 2 93925%m := by
  have h := power_period (2:V) 590069 q m 2590 93925 hm hq hqm
  norm_num at h ⊢
  exact h

#print axioms Trace74PowerPeriodResidue.square_power_one
#print axioms Trace74PowerPeriodResidue.power_period
#print axioms Trace74PowerPeriodResidue.candidate_power_period
end Trace74PowerPeriodResidue
