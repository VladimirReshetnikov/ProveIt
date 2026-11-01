import DiophantineConsistency.AdaptiveGap85FourthRootCongruence
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FourthX16Bounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85FourthRootCongruence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_index_two_impossible (Y eta zeta : V) (hY : 8≤Y) (hzeta : 0<zeta)
    (hk : 128*Y*Y+4=eta+zeta)
    (hc : eta+Y*(128*Y*Y+4)=fourthC (17*Y)) : False := by
  let t := Y-8
  have ht : t+8=Y := tsub_add_cancel_of_le hY
  let gap := 20950260+7743256*t+953968*t*t+39176*t*t*t
  have hgap : 0<gap := by dsimp [gap]; simp
  have hcert : (Y+1)*(128*Y*Y+4)+gap=fourthC (17*Y) := by
    calc
      _ = ((t+8)+1)*(128*(t+8)*(t+8)+4)+gap := by rw [ht]
      _ = fourthC (17*(t+8)) := by dsimp [gap,fourthC]; ring
      _ = _ := by rw [ht]
  have hcgt : (Y+1)*(128*Y*Y+4)<fourthC (17*Y) := by
    have hh := lt_add_of_pos_right ((Y+1)*(128*Y*Y+4)) hgap
    rwa [hcert] at hh
  have hetalt : eta<128*Y*Y+4 := by rw [hk]; exact lt_add_of_pos_right eta hzeta
  have hclt : fourthC (17*Y)<(Y+1)*(128*Y*Y+4) := by
    rw [←hc]
    have hh := _root_.add_lt_add_right hetalt (Y*(128*Y*Y+4))
    calc
      _ < (128*Y*Y+4)+Y*(128*Y*Y+4) := by simpa only [add_comm] using hh
      _ = _ := by ring
  exact (lt_asymm hcgt hclt).elim

theorem first_index_three_impossible (Y eta : V) (hY : 8≤Y) (heta : 0<eta)
    (hc : eta+Y*(8192*Y*Y*Y*Y+512*Y*Y+6)=fourthC (17*Y)) : False := by
  let t := Y-8
  have ht : t+8=Y := tsub_add_cancel_of_le hY
  let gap := 247673624+160100586*t+40998160*t*t+5204088*t*t*t+327680*t*t*t*t+8192*t*t*t*t*t
  have hgap : 0<gap := by dsimp [gap]; simp
  have hcert : fourthC (17*Y)+gap=Y*(8192*Y*Y*Y*Y+512*Y*Y+6) := by
    calc
      _ = fourthC (17*(t+8))+gap := by rw [ht]
      _ = (t+8)*(8192*(t+8)*(t+8)*(t+8)*(t+8)+512*(t+8)*(t+8)+6) := by dsimp [gap,fourthC]; ring
      _ = _ := by rw [ht]
  have hclt : fourthC (17*Y)<Y*(8192*Y*Y*Y*Y+512*Y*Y+6) := by
    have hh := lt_add_of_pos_right (fourthC (17*Y)) hgap
    rwa [hcert] at hh
  have hcgt : Y*(8192*Y*Y*Y*Y+512*Y*Y+6)<fourthC (17*Y) := by
    rw [←hc]
    simpa only [add_comm] using lt_add_of_pos_right (Y*(8192*Y*Y*Y*Y+512*Y*Y+6)) heta
  exact (lt_asymm hclt hcgt).elim
end DiophantineConsistency.AdaptiveGap85FourthX16Bounds
