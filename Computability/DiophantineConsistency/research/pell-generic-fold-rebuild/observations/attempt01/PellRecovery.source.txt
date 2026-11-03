import PellOddFold

/-! Noncircular recovery of an odd Pell ordinate under explicit size bounds. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositivePellRecovery
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellHalfIndex
open TenPositivePellOddFold
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem recover_odd_ordinate (n s b c : V) (hn : 0<n) (hs : s%2=1)
    (hc : 0<c) (hci : c<ycoord n b) (hsize : 2*ycoord n b<xcoord n b)
    (hcong : SignMod (xcoord n b) c (ycoord s b)) :
    ∃ p : V, 0<p ∧ p<n ∧ p%2=1 ∧ c=ycoord p b := by
  obtain ⟨p,hpn,hpodd,hfold⟩ := fold_odd_index n s b hn hs
  have hp : 0<p := pos_iff_ne_zero.mpr (by intro hp0; simp [hp0] at hpodd)
  have hyp : 0<ycoord p b := lt_of_lt_of_le hp (time_le_y p b)
  have hybound : ycoord p b≤ycoord n b := (y_strictMono b).monotone hpn
  have hcsize : 2*c<xcoord n b := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (le_of_lt hci) (by simp)) hsize
  have hysize : 2*ycoord p b<xcoord n b := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hybound (by simp)) hsize
  have hF : 0<xcoord n b := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x n b)
  have heq : c=ycoord p b := sign_eq_of_half hc hyp hcsize hysize
    (sign_trans hF hcong hfold)
  have hpnlt : p<n := lt_of_le_of_ne hpn (by intro he; subst p; exact (ne_of_lt hci) heq)
  exact ⟨p,hp,hpnlt,hpodd,heq⟩

#print axioms TenPositivePellRecovery.recover_odd_ordinate
end TenPositivePellRecovery
