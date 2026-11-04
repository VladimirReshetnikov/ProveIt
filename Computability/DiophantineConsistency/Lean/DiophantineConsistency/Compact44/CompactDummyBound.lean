import DiophantineConsistency.ArithmeticWindowDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactDummyBound
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticBinaryCarry
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem forbidden_zero (x : V) (hx : x<Exp.exp 67)
    (h : NoCarry x (Exp.exp 67-1)) : x=0 := noCarry_ones 67 x hx h

theorem ordinary_le_one (x : V) (hx : x<Exp.exp 67)
    (h : NoCarry x (Exp.exp 67-2)) : x≤1 := by
  apply noCarry_ones_two 66
  · simpa only [show (66:V)+1=67 by norm_num] using hx
  · simpa only [show (66:V)+1=67 by norm_num] using h

/-- The special compact44 low-mask digit rho-4 permits a digit from 0 to 3.
The local digit bound and the no-carry mask relation are explicit inputs. -/
theorem dummy_le_three (x : V) (hx : x<Exp.exp 67)
    (h : NoCarry x (Exp.exp 67-4)) : x≤3 := by
  have hplus : Exp.exp (65:V)-1+1=Exp.exp 65 := tsub_add_cancel_of_le (one_le_exp _)
  have hE : Exp.exp (67:V)=4*(Exp.exp 65-1)+4 := calc
    _=2*(2*Exp.exp (65:V)) := by
      rw [show (67:V)=(65:V)+1+1 by norm_num,exp_succ,exp_succ]
    _=4*(Exp.exp 65-1)+4 := by
      conv_lhs => rw [←hplus]
      ring
  have hmask : Exp.exp (67:V)-4=2*(2*(Exp.exp 65-1))+0 := by
    rw [hE,add_tsub_cancel_right]
    ring
  have hr : x%2≤1 := lt_two_iff_le_one.mp (mod_lt _ (by norm_num))
  have h1in : NoCarry (2*(x/2)+x%2) (2*(2*(Exp.exp 65-1))+0) := by
    rw [div_add_mod x 2,←hmask]
    exact h
  have h1 := ((noCarry_binary (x/2) (2*(Exp.exp 65-1)) (x%2) 0 hr (by simp)).mp h1in).2
  have hr2 : (x/2)%2≤1 := lt_two_iff_le_one.mp (mod_lt _ (by norm_num))
  have h2in : NoCarry (2*((x/2)/2)+(x/2)%2) (2*(Exp.exp 65-1)+0) := by
    rw [div_add_mod (x/2) 2]
    simpa only [add_zero] using h1
  have h2 := ((noCarry_binary ((x/2)/2) (Exp.exp 65-1) ((x/2)%2) 0 hr2 (by simp)).mp h2in).2
  have he67 : Exp.exp (67:V)=2*Exp.exp 66 := by
    simpa only [show (66:V)+1=67 by norm_num] using (exp_succ (66:V))
  have he66 : Exp.exp (66:V)=2*Exp.exp 65 := by
    simpa only [show (65:V)+1=66 by norm_num] using (exp_succ (65:V))
  have hx66 : x/2<Exp.exp 66 := by
    apply div_lt_of_lt_mul
    rw [mul_comm,←he67]
    exact hx
  have hx65 : (x/2)/2<Exp.exp 65 := by
    apply div_lt_of_lt_mul
    rw [mul_comm,←he66]
    exact hx66
  have hz : (x/2)/2=0 := noCarry_ones 65 ((x/2)/2) hx65 h2
  have hq : x/2<2 := by
    have he := div_add_mod (x/2) 2
    rw [hz] at he
    rw [←he]
    simp
  have hq1 : x/2≤1 := lt_two_iff_le_one.mp hq
  calc
    x=2*(x/2)+x%2 := (div_add_mod x 2).symm
    _≤2*1+1 := add_le_add (mul_le_mul_of_nonneg_left hq1 (by simp)) hr
    _=3 := by ring
end CompactDummyBound
#print axioms CompactDummyBound.forbidden_zero
#print axioms CompactDummyBound.ordinary_le_one
#print axioms CompactDummyBound.dummy_le_three
