import DiophantineConsistency.ArithmeticPellHalfIndex

/-! Exact even-half-index residues for the auxiliary Pell quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74ExactAuxPellResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] xcoord ycoord oddQuotient

/-- For an even half-index, the auxiliary quotient has the **positive**
main-ordinate residue; no signed disjunction is left. -/
theorem even_quotient_mod_norm (a I f t : V) (hI : 2≤I) (hf : 0<f)
    (hn : I*I+delta a=delta a*f*f) :
    oddQuotient (2*t) (I-2)%f=ycoord (2*(2*t)+1) a%f := by
  let b := I-2
  have hb : b+2=I := tsub_add_cancel_of_le hI
  have hcoef : (4*(b+2)*(b+2)+4*(a+2)*(a+2))%f=(4:V)%f := by
    have he : 4*(b+2)*(b+2)+4*(a+2)*(a+2)=4+f*(4*delta a*f) := by
      rw [hb]
      calc
        4*I*I+4*(a+2)*(a+2)=4+4*(I*I+delta a) := by unfold delta; ring
        _=4+f*(4*delta a*f) := by rw [hn]; ring
    rw [he,mod_add_mul' _ _ hf]
  have hfirst : (oddQuotient 1 b+ycoord 3 a)%f=0 := by
    have he : oddQuotient 1 b+ycoord 3 a=f*(4*delta a*f) := by
      apply add_right_cancel (b:=(4:V))
      calc
        (oddQuotient 1 b+ycoord 3 a)+4=(oddQuotient 1 b+3)+(ycoord 3 a+1) := by ring
        _=4*I*I+4*(a+2)*(a+2) := by rw [ArithmeticPellHalfIndex.odd_one,y_three,hb]
        _=f*(4*delta a*f)+4 := by
          calc
            4*I*I+4*(a+2)*(a+2)=4*(I*I+delta a)+4 := by unfold delta; ring
            _=f*(4*delta a*f)+4 := by rw [hn]; ring
    rw [he,mod_mul_self_right]
  have all (j : V) :
      oddQuotient (2*j) b%f=ycoord (2*(2*j)+1) a%f ∧
      (oddQuotient (2*j+1) b+ycoord (2*(2*j+1)+1) a)%f=0 := by
    induction j using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      have hy1 : ycoord 1 a=1 := by simpa using y_succ (0:V) a
      constructor
      · simp only [mul_zero,zero_add,odd_zero,hy1]
      · simpa only [mul_zero,zero_add,show (2:V)*1+1=3 by ring] using hfirst
    case succ j ih =>
      have h2 := transport_equal f (4*(b+2)*(b+2)) (4*(a+2)*(a+2))
        _ _ _ _ _ _ hf hcoef (odd_rec (2*j) b) (odd_y_rec (2*j) a) ih.1 ih.2
      have h3 := transport_opposite f (4*(b+2)*(b+2)) (4*(a+2)*(a+2))
        _ _ _ _ _ _ hf hcoef (odd_rec (2*j+1) b) (odd_y_rec (2*j+1) a) ih.2
        (by convert h2 using 1 <;> congr 2 <;> ring)
      constructor
      · convert h2 using 1 <;> congr 2 <;> ring
      · simpa only [show (2:V)*(j+1)+1=(2*j+1)+2 by ring] using h3
  exact (all t).1

#print axioms Trace74ExactAuxPellResidue.even_quotient_mod_norm
end Trace74ExactAuxPellResidue
