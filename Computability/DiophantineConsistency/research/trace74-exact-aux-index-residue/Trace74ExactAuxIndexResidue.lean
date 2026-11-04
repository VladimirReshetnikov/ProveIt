import Trace74ExactAuxPellResidue

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74ExactAuxIndexResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] xcoord ycoord oddQuotient

/-- For an even half-index and a divisor of the auxiliary base, the
quotient has the **positive** odd-index residue. -/
theorem even_quotient_mod_divisor (I c t : V) (hI : 2≤I) (hc : 0<c) (hd : c∣I) :
    oddQuotient (2*t) (I-2)%c=(2*(2*t)+1)%c := by
  let b := I-2
  have hb : b+2=I := tsub_add_cancel_of_le hI
  have hd4 : c∣4*I*I := by
    obtain ⟨v,hv⟩ := hd
    exact ⟨4*v*I,by rw [hv]; ring⟩
  have hcoef : (4*(b+2)*(b+2)+4)%c=(4:V)%c := by
    rw [hb]
    exact mod_add_remove_left_of_dvd hd4 hc
  have hfirst : (oddQuotient 1 b+3)%c=0 := by
    rw [ArithmeticPellHalfIndex.odd_one,hb]
    exact mod_eq_zero_iff_dvd.mpr hd4
  have all (j : V) :
      oddQuotient (2*j) b%c=(2*(2*j)+1)%c ∧
      (oddQuotient (2*j+1) b+(2*(2*j+1)+1))%c=0 := by
    induction j using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      refine ⟨by simp [odd_zero],?_⟩
      simpa only [mul_zero,zero_add,show (2:V)*1+1=3 by ring] using hfirst
    case succ j ih =>
      have hrec (t : V) : (2*(t+2)+1)+(2*t+1)+2*(2*(t+1)+1)=4*(2*(t+1)+1) := by ring
      have h2 := transport_equal c (4*(b+2)*(b+2)) 4
        _ _ _ _ _ _ hc hcoef (odd_rec (2*j) b) (hrec (2*j)) ih.1 ih.2
      have h3 := transport_opposite c (4*(b+2)*(b+2)) 4
        _ _ _ _ _ _ hc hcoef (odd_rec (2*j+1) b) (hrec (2*j+1)) ih.2
        (by convert h2 using 1 <;> congr 2 <;> ring)
      constructor
      · convert h2 using 1 <;> congr 2 <;> ring
      · simpa only [show (2:V)*(j+1)+1=(2*j+1)+2 by ring] using h3
  exact (all t).1

#print axioms Trace74ExactAuxIndexResidue.even_quotient_mod_divisor
end Trace74ExactAuxIndexResidue
