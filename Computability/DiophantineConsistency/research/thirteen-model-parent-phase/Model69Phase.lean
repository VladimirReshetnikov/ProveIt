import Foundation.FirstOrder.Arithmetic.Exponential.Log
import Mathlib.Tactic.Ring

/-! Four-block phase extraction in an arithmetic model, conditional on the
explicit block identity and origin digit. Actual graph data remain separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69Phase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A low digit of one at any modulus divisible by four gives the required
`C-1` residue, with subtraction justified by an explicit quotient. -/
theorem pred_mod_four (C modulus n : V) (hmodulus : modulus=4*n)
    (horigin : C%modulus=1) : (C-1)%4=0 := by
  have hc : C=4*(n*(C/modulus))+1 := by
    calc C=modulus*(C/modulus)+C%modulus := (div_add_mod C modulus).symm
      _=4*(n*(C/modulus))+1 := by rw [horigin,hmodulus]; ring
  rw [hc,add_tsub_cancel_right]
  exact mod_eq_zero_iff_dvd.mpr ⟨_,rfl⟩

/-- If the radix is a multiple of four, the lowest two blocks determine
rank mod four independently of all higher blocks. -/
theorem rank_mod_four (q A M D E H R : V) (hq : q%4=0)
    (hA : A%4=0) (hM : M%4=3)
    (hR : R=A+M+q*D+q*q*E+q*q*q*H) : R%4=3 := by
  have h4 : (0:V)<4 := by norm_num
  rw [hR]
  simp [mod_add h4,mod_mul h4,hq,hA,hM,
    mod_eq_self_of_lt (show (3:V)<4 by exact_mod_cast (show (3:ℕ)<4 by decide))]

/-- Combined phase criterion; all block and digit facts are explicit inputs. -/
theorem rank_from_origin (q C M D E H R modulus n : V)
    (hq : q%4=0) (hmodulus : modulus=4*n) (horigin : C%modulus=1)
    (hM : M%4=3) (hR : R=(C-1)+M+q*D+q*q*E+q*q*q*H) : R%4=3 :=
  rank_mod_four q (C-1) M D E H R hq (pred_mod_four C modulus n hmodulus horigin) hM hR
end Model69Phase
#print axioms Model69Phase.pred_mod_four
#print axioms Model69Phase.rank_mod_four
#print axioms Model69Phase.rank_from_origin
