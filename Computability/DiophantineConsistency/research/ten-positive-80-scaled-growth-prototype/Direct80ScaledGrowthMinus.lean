import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! Power-growth bound with distinct Pell scale and remainder scale. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80ScaledGrowthMinus
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellFirstIndex ArithmeticPellHalfIndex ArithmeticPellPowerRecovery
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coefficient_gap_minus (X S : V) (hX : 16≤X) (hS : 1≤S) :
    16*(2*(2*X*S*S+1)) < (2*(S*(X+1)-1)+3)*(2*(S*(X+1)-1)+3) := by
  have hsq : 16*X≤(X+1)*(X+1) := calc
    16*X≤X*X := mul_le_mul_of_nonneg_right hX (by simp)
    _≤(X+1)*(X+1) := mul_le_mul (by simp) (by simp) (by simp) (by simp)
  have h17 : (17:V)≤S*(X+1) := calc
    17=1*(16+1) := by ring
    _≤S*(X+1) := mul_le_mul hS (add_le_add_left hX 1) (by simp) (by simp)
  have hA1 : S*(X+1)-1+1=S*(X+1) := tsub_add_cancel_of_le (le_trans (by norm_num : (1:V)≤17) h17)
  have heq : 2*(S*(X+1)-1)+3=2*(S*(X+1))+1 := by
    calc
      _=2*(S*(X+1)-1+1)+1 := by ring
      _=2*(S*(X+1))+1 := by rw [hA1]
  rw [heq]
  have h68 : (68:V)≤4*S*(X+1) := calc
    68=4*17 := by ring
    _≤4*(S*(X+1)) := mul_le_mul_of_nonneg_left h17 (by simp)
    _=4*S*(X+1) := by ring
  have hlarge : 64*X*S*S+68+1≤(2*(S*(X+1))+1)*(2*(S*(X+1))+1) := calc
    64*X*S*S+68+1=4*S*S*(16*X)+68+1 := by ring
    _≤4*S*S*((X+1)*(X+1))+4*S*(X+1)+1 :=
      add_le_add_left (add_le_add (mul_le_mul_of_nonneg_left hsq (by simp)) h68) 1
    _=(2*(S*(X+1))+1)*(2*(S*(X+1))+1) := by ring
  apply lt_of_lt_of_le _ hlarge
  have hnum : (32:V)<68+1 := by norm_num
  have h := add_lt_add_of_le_of_lt (le_refl (64*X*S*S)) hnum
  simpa only [show 16*(2*(2*X*S*S+1))=64*X*S*S+32 by ring,add_assoc] using h

theorem power_bound_scaled_minus (X Y S r k c eta zeta : V) (hX : 16≤X) (hS : 1≤S) (hr : 2≤r)
    (hck : c=k*Y+eta) (hkez : k=eta+zeta) (hz : 0<zeta)
    (hc : c=ycoord (2*r+1) (S*(X+1)-1))
    (hk : k=2*ycoord (r+1) (2*(X*S*S-1)+1)) : Exp.exp (2*r+1)<Y := by
  let B:=2*(X*S*S-1)+1
  have hX1 : 1≤X := le_trans (by simp : (1:V)≤16) hX
  have hQ : 1≤X*S*S := one_le_mul (one_le_mul hX1 hS) hS
  have hQe : X*S*S-1+1=X*S*S := tsub_add_cancel_of_le hQ
  have hB : B+2=2*X*S*S+1 := calc
    B+2=2*(X*S*S-1+1)+1 := by dsimp [B]; ring
    _=2*X*S*S+1 := by rw [hQe]; ring
  have hsep : 16*(2*(B+2))<(2*(S*(X+1)-1)+3)*(2*(S*(X+1)-1)+3) := by
    rw [hB]; exact coefficient_gap_minus X S hX hS
  have hrp : 0<r := lt_of_lt_of_le (by simp : (0:V)<2) hr
  have hlow := paired_comparison_strict (S*(X+1)-1) B hsep r hrp
  have hkpos : 0<k := by rw [hkez]; exact add_pos_of_nonneg_of_pos (by simp) hz
  have hinterval : c<k*(Y+1) := by
    rw [hck]
    have he : eta<k := by rw [hkez]; exact lt_add_of_pos_right eta hz
    have h := add_lt_add_of_le_of_lt (le_refl (k*Y)) he
    simpa only [mul_add,mul_one] using h
  have he : Exp.exp (4*r)*k<k*(2*(Y+1)) := calc
    Exp.exp (4*r)*k=2*(Exp.exp (4*r)*ycoord (r+1) B) := by rw [hk]; dsimp [B]; ring
    _<2*ycoord (2*r+1) (S*(X+1)-1) := mul_lt_mul_of_pos_left hlow (by simp)
    _=2*c := by rw [hc]
    _<2*(k*(Y+1)) := mul_lt_mul_of_pos_left hinterval (by simp)
    _=k*(2*(Y+1)) := by ring
  have hupper : Exp.exp (4*r)<2*(Y+1) :=
    (mul_lt_mul_iff_of_pos_left hkpos).mp (by simpa only [mul_comm] using he)
  have hindex : 2*r+3≤4*r := by
    have h4 : (4:V)≤2*r := by simpa only [show (2:V)*2=4 by ring] using
      mul_le_mul_of_nonneg_left hr (by simp : (0:V)≤2)
    have h3 : (3:V)≤2*r := le_trans (by norm_num) h4
    have h := add_le_add (le_refl (2*r)) h3
    simpa only [show 2*r+2*r=4*r by ring] using h
  have hfloor : 2*Exp.exp (2*r+1)+2≤Exp.exp (4*r) := calc
    2*Exp.exp (2*r+1)+2≤2*Exp.exp (2*r+1)+2*Exp.exp (2*r+1) :=
      add_le_add (le_refl _) (le_mul_of_one_le_right (by simp) (one_le_exp _))
    _=Exp.exp (2*r+3) := by
      rw [show 2*r+3=(2*r+1+1)+1 by ring,exp_succ (2*r+1+1),exp_succ (2*r+1)]; ring
    _≤Exp.exp (4*r) := exp_monotone_le.mpr hindex
  have hfinal : 2*Exp.exp (2*r+1)+2<2*Y+2 := by
    simpa only [mul_add,mul_one] using lt_of_le_of_lt hfloor hupper
  exact (mul_lt_mul_iff_of_pos_left (by simp : (0:V)<2)).mp
    ((add_lt_add_iff_right (2:V)).mp hfinal)

#print axioms Direct80ScaledGrowthMinus.power_bound_scaled_minus
end Direct80ScaledGrowthMinus
