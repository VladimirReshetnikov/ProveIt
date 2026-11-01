import DiophantineConsistency.AdaptiveGap85NegativeSmallCases
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85NegativeMultiplier
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85NegativeModular AdaptiveGap85NegativeSmallCases
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem negative_modulus_multiplier (X Y q L : V) (hY : 8≤Y) (hq : q∣Y)
    (hneg : (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
      24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26)+
      (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) =
      (4*(Y*(X+1))+3)*L) :
    ∃ m : V, 1≤m ∧ m≤6 ∧ 27*(8*X+1)=(4*(Y*(X+1))+3)*m := by
  have hY1 : 1≤Y := le_trans (by simpa only [show (1:V)+7=8 by ring] using (show (1:V)≤1+7 by simp)) hY
  have hmod := negative_root_cubic_congruence X Y q L hY1 hq hneg
  obtain ⟨m,hm⟩ := mod_eq_zero_iff_dvd.mp hmod
  have hp : 0<27*(8*X+1) := mul_pos (by simp) (by simp)
  have hmpos : 0<m := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have : 27*(8*X+1)=0 := by rw [hm,hz]; simp
    exact (ne_of_gt hp) this
  have hm1 : 1≤m := by simpa using lt_iff_succ_le.mp hmpos
  have hm6 : m≤6 := by
    by_contra hn
    have hm7 : 7≤m := by simpa only [show (6:V)+1=7 by ring] using lt_iff_succ_le.mp (lt_of_not_ge hn)
    have hp' : 8*(X+1)≤Y*(X+1) := mul_le_mul hY (le_refl _) (by simp) (by simp)
    have hH : 32*(X+1)+3≤4*(Y*(X+1))+3 := by
      have hh := add_le_add (Arithmetic.mul_le_mul_left (a:=(4:V)) hp') (le_refl (3:V))
      calc
        _ = 4*(8*(X+1))+3 := by ring
        _ ≤ _ := hh
    have hlarge : 27*(8*X+1)<(32*(X+1)+3)*7 := by
      have hh := lt_add_of_pos_right (27*(8*X+1)) (show (0:V)<8*X+218 by simp)
      calc
        _ < 27*(8*X+1)+(8*X+218) := hh
        _ = _ := by ring
    have hle : (32*(X+1)+3)*7≤(4*(Y*(X+1))+3)*m := mul_le_mul hH hm7 (by simp) (by simp)
    have hh := lt_of_lt_of_le hlarge hle
    rw [←hm] at hh
    exact (_root_.lt_irrefl _) hh
  exact ⟨m,hm1,hm6,hm⟩
end DiophantineConsistency.AdaptiveGap85NegativeMultiplier
