import DiophantineConsistency.ArithmeticPellPowerRecovery
import DiophantineConsistency.ArithmeticPow

/-! Elementary exponential bound for the entire projection product. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80ProductPower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem whole_product_lt_power (X b r : V) (hX : 32≤X) (hb : b≤X) (hr : 15≤r) :
    b*(X+Exp.exp (2*r+1))*(Exp.exp (2*r+1)*X+1)<power X (r+1) := by
  let s : V := r-2
  let t : V := Exp.exp (2*r+1)
  have hr2 : 2≤r := le_trans (by norm_num : (2:V)≤15) hr
  have hsplus : s+2=r := tsub_add_cancel_of_le hr2
  have hs13 : 13≤s := by
    apply (add_le_add_iff_right (2:V)).mp
    simpa only [hsplus,show (13:V)+2=15 by ring] using hr
  have hx1 : 1≤X := le_trans (by norm_num : (1:V)≤32) hX
  have hxpos : 0<X := lt_of_lt_of_le (by simp) hx1
  have ht1 : 1≤t := one_le_exp _
  have htt : t+1≤2*t := by
    calc
      t+1≤t+t := by simpa only [add_comm] using add_le_add_left ht1 t
      _=2*t := by ring
  have hexp2 : Exp.exp (2:V)=4 := by
    rw [show (2:V)=(0:V)+1+1 by ring,exp_succ,exp_succ]
    norm_num
  have heq : 4*t*t=Exp.exp (4*r+4) := by
    have hsum : Exp.exp ((2*r+1)+(2*r+1)+2)=Exp.exp (2*r+1)*Exp.exp (2*r+1)*4 := by
      rw [exp_add,exp_add,hexp2]
    calc
      4*t*t=Exp.exp (2*r+1)*Exp.exp (2*r+1)*4 := by dsimp [t]; ring
      _=Exp.exp ((2*r+1)+(2*r+1)+2) := hsum.symm
      _=Exp.exp (4*r+4) := by congr 1; ring
  have hexpLt : 4*r+4<5*s := by
    have hs : 12<s := lt_of_lt_of_le (by norm_num : (12:V)<13) hs13
    have h := add_lt_add_left hs (4*s)
    have he1 : 4*r+4=4*s+12 := by rw [←hsplus]; ring
    have he2 : 5*s=4*s+s := by ring
    rw [he1,he2]
    simpa only [add_comm] using h
  have hexp : Exp.exp (4*r+4)<Exp.exp (5*s) := by
    have hsucc : (4*r+4)+1≤5*s := lt_iff_succ_le.mp hexpLt
    calc
      Exp.exp (4*r+4)<Exp.exp ((4*r+4)+1) := by
        rw [exp_succ]
        have hpos := exp_pos (4*r+4)
        simpa only [two_mul] using lt_add_of_pos_right (Exp.exp (4*r+4)) hpos
      _≤Exp.exp (5*s) := exp_monotone_le.mpr hsucc
  have hpow32 : power (32:V) s=Exp.exp (5*s) := by
    have h32 : power (2:V) 5=32 := by
      rw [power_two,show (5:V)=(0:V)+1+1+1+1+1 by ring,
        exp_succ,exp_succ,exp_succ,exp_succ,exp_succ]
      norm_num
    rw [←h32,power_iterate,power_two]
  have hsmall : (t+1)*(t+1)<power X s := calc
    (t+1)*(t+1)≤(2*t)*(2*t) := mul_le_mul htt htt (by simp) (by simp)
    _=4*t*t := by ring
    _=Exp.exp (4*r+4) := heq
    _<Exp.exp (5*s) := hexp
    _=power (32:V) s := hpow32.symm
    _≤power X s := power_mono_base 32 X s hX
  have hfirst : X+t≤X*(t+1) := calc
    X+t≤X+X*t := _root_.add_le_add (le_refl _) (le_mul_of_one_le_left (by simp) hx1)
    _=X*(t+1) := by ring
  have hsecond : t*X+1≤X*(t+1) := calc
    t*X+1≤t*X+X := _root_.add_le_add (le_refl _) hx1
    _=X*(t+1) := by ring
  have htotal : b*(X+t)*(t*X+1)≤X*X*X*((t+1)*(t+1)) := calc
    b*(X+t)*(t*X+1)≤X*(X*(t+1))*(X*(t+1)) :=
      mul_le_mul (mul_le_mul hb hfirst (by simp) (by simp)) hsecond (by simp) (by simp)
    _=X*X*X*((t+1)*(t+1)) := by ring
  have hpow3 : power X 3=X*X*X := by
    rw [show (3:V)=2+1 by ring,power_succ,show (2:V)=1+1 by ring,power_succ,power_one]
    ring
  have hpow : X*X*X*power X s=power X (r+1) := by
    rw [show r+1=s+3 by rw [←hsplus]; ring,power_add,hpow3]
    ring
  calc
    b*(X+t)*(t*X+1)≤X*X*X*((t+1)*(t+1)) := htotal
    _<X*X*X*power X s := mul_lt_mul_of_pos_left hsmall (mul_pos (mul_pos hxpos hxpos) hxpos)
    _=power X (r+1) := hpow

#print axioms Direct80ProductPower.whole_product_lt_power
end Direct80ProductPower
