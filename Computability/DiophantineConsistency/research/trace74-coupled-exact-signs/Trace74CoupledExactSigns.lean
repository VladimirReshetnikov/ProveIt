import Trace74ExactAuxIndexResidue
import Trace74PellOddAntiperiod

/-! Combine exact auxiliary signs with the odd Pell anti-period. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CoupledExactSigns
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellResidueClasses
open Trace74ExactAuxPellResidue Trace74ExactAuxIndexResidue Trace74PellOddAntiperiod
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The same auxiliary quotient has opposite main-ordinate residue modulo
the abscissa and positive main-index residue modulo its divisor. -/
theorem exact_pair (a t j s I c : V) (hI : 2≤I) (hc : 0<c)
    (hnorm : I*I+delta a=delta a*(xcoord (2*t) a)*(xcoord (2*t) a))
    (hcI : c∣I) (hct : c∣t) (hcy : c=ycoord (4*j+1) a) :
    let h := j+t*(2*s+1)
    let f := xcoord (2*t) a
    (oddQuotient (2*h) (I-2)+c)%f=0 ∧
      oddQuotient (2*h) (I-2)%c=(4*j+1)%c := by
  let h := j+t*(2*s+1)
  let f := xcoord (2*t) a
  have hf : 0<f := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x (2*t) a)
  have hqf := even_quotient_mod_norm a I f h hI hf hnorm
  have hanti := odd_blocks_antiperiod a t (4*j+1) s
  have hu : 2*(2*h)+1=(4*j+1)+4*t*(2*s+1) := by dsimp [h]; ring
  rw [hu] at hqf
  have hplus := mod_add_congr _ _ c f hf hqf
  have hfirst : (oddQuotient (2*h) (I-2)+c)%f=0 := by
    rw [hplus]
    simpa only [hcy] using hanti
  have hqc := even_quotient_mod_divisor I c h hI hc hcI
  rw [hu] at hqc
  obtain ⟨u,hu'⟩ := hct
  have hindex : ((4*j+1)+4*t*(2*s+1))%c=(4*j+1)%c := by
    rw [hu']
    have he : (4*j+1)+4*(c*u)*(2*s+1)=(4*j+1)+c*(4*u*(2*s+1)) := by ring
    rw [he,mod_add_mul' _ _ hc]
  exact ⟨hfirst,hqc.trans hindex⟩

#print axioms Trace74CoupledExactSigns.exact_pair
end Trace74CoupledExactSigns
