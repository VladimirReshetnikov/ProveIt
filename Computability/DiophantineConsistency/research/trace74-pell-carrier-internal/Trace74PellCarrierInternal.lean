import Trace74CarrierPellCongruence
import DiophantineConsistency.ArithmeticPellRecurrence
import DiophantineConsistency.ArithmeticPow

/-! Pell carrier congruence at every internal IΣ₁ index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74PellCarrierInternal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence ArithmeticPow
open Trace74CarrierPellCongruence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A subtraction-free Σ₁ invariant supports induction at nonstandard
indices: the two natural witnesses encode a signed quotient. -/
theorem abscissa_balance (b n : V) :
    ∃ s t : V, xcoord n b+(4*b+3)*s=
      power 2 n+b*ycoord n b+(4*b+3)*t := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0,0,by simp⟩
  case succ n ih =>
    obtain ⟨s,t,ht⟩ := ih
    refine ⟨2*s,2*t+ycoord n b,?_⟩
    rw [x_succ,y_succ,power_succ]
    unfold delta
    calc
      (b+2)*xcoord n b+(b+1)*(b+3)*ycoord n b+(4*b+3)*(2*s) =
          2*(xcoord n b+(4*b+3)*s)+b*xcoord n b+
            (b+1)*(b+3)*ycoord n b := by ring
      _ = 2*(power 2 n+b*ycoord n b+(4*b+3)*t)+b*xcoord n b+
            (b+1)*(b+3)*ycoord n b := by rw [ht]
      _ = 2*power 2 n+b*(xcoord n b+(b+2)*ycoord n b)+
            (4*b+3)*(2*t+ycoord n b) := by ring

/-- The same invariant in the model's difference ring. -/
theorem abscissa_congruence (b n : V) :
    (4*ι b+3 : DiffRing V) ∣
      ι (xcoord n b)-ι (power 2 n)-ι b*ι (ycoord n b) := by
  obtain ⟨s,t,ht⟩ := abscissa_balance b n
  refine ⟨ι t-ι s,?_⟩
  have ht' := congrArg ι ht
  simp only [map_add,map_mul,map_ofNat] at ht'
  linear_combination ht'

/-- At every internal index, the Pell norm and congruence imply the
carrier factor, without assuming the congruence. -/
theorem carrier_factor (b n : V) :
    (4*ι b+3 : DiffRing V) ∣
      ι (power 2 n)*(3*ι (ycoord n b)-2*ι (power 2 n))+2 := by
  have hnorm := congrArg ι (norm n b)
  simp only [map_add,map_mul,map_one] at hnorm
  have hd : (ι (delta b) : DiffRing V)=ι b*ι b+(4*ι b+3) := by
    simp only [delta,map_add,map_mul,map_one,map_ofNat]
    ring
  rw [hd] at hnorm
  exact pell_congruence_carrier (ι b) (4*ι b+3) (ι (power 2 n))
    (ι (ycoord n b)) (ι (xcoord n b)) rfl hnorm (abscissa_congruence b n)

#print axioms Trace74PellCarrierInternal.abscissa_balance
#print axioms Trace74PellCarrierInternal.abscissa_congruence
#print axioms Trace74PellCarrierInternal.carrier_factor
end Trace74PellCarrierInternal
