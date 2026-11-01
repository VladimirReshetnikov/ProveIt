import DiophantineConsistency.ArithmeticPellResidueClasses
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85TemplateResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellResidueClasses
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem mod_difference_zero (A D H : V) (hH : 0<H)
    (hmod : (A+27*D)%H=A%H) (hsmall : 27*D<H) : D=0 := by
  have he : (27*D+A)%H=(0+A)%H := by simpa only [add_comm,zero_add,add_zero] using hmod
  have hz : (27*D)%H=0 := by simpa only [zero_mod] using mod_add_cancel (27*D) 0 A H hH he
  rw [mod_eq_self_of_lt hsmall] at hz
  by_contra hn
  have hp : 0<D := pos_iff_ne_zero.mpr hn
  have hp' : 0<27*D := mul_pos (by simp) hp
  exact (ne_of_gt hp') hz

theorem residue_forces_eight (X Y : V) (hX : 4≤X) (hY : 8≤Y)
    (hmod : (27*X)%(4*(Y*(X+1))+3)=(27*8)%(4*(Y*(X+1))+3)) : X=8 := by
  let H := 4*(Y*(X+1))+3
  have hH : 0<H := by dsimp [H]; simp
  have hp : 8*(X+1)≤Y*(X+1) := mul_le_mul hY (le_refl _) (by simp) (by simp)
  have hHlower : 32*(X+1)+3≤H := by
    dsimp [H]
    have hh := add_le_add (Arithmetic.mul_le_mul_left (a:=(4:V)) hp) (le_refl (3:V))
    calc
      _ = 4*(8*(X+1))+3 := by ring
      _ ≤ _ := hh
  by_cases h8 : 8≤X
  · let D := X-8
    have hD : D+8=X := tsub_add_cancel_of_le h8
    have hDX : D≤X := tsub_le_self
    have h27 : 27*D≤27*X := Arithmetic.mul_le_mul_left hDX
    have hlt : 27*X<32*(X+1)+3 := by
      have hh := lt_add_of_pos_right (27*X) (show (0:V)<5*X+35 by simp)
      calc
        _ < 27*X+(5*X+35) := hh
        _ = _ := by ring
    have hsmall : 27*D<H := lt_of_le_of_lt h27 (lt_of_lt_of_le hlt hHlower)
    have he : 27*X=27*8+27*D := by rw [←hD]; ring
    have hmod' : (27*8+27*D)%H=(27*8)%H := by rw [←he]; exact hmod
    have hz : D=0 := mod_difference_zero (27*8) D H hH hmod' hsmall
    simpa only [hz,zero_add] using hD.symm
  · have h8' : X≤8 := le_of_not_ge h8
    let D := 8-X
    have hD : X+D=8 := add_tsub_cancel_of_le h8'
    have hD4 : D≤4 := by
      apply (add_le_add_iff_right (4:V)).mp
      have hh : 4+D≤X+D := add_le_add hX (le_refl D)
      rw [hD] at hh
      simpa only [add_comm,show (4:V)+4=8 by ring] using hh
    have h27 : 27*D≤108 := by
      have hh := Arithmetic.mul_le_mul_left (a:=(27:V)) hD4
      calc
        _ ≤ 27*4 := hh
        _ = 108 := by ring
    have hX5 : 5≤X+1 := by
      have hh := add_le_add hX (le_refl (1:V))
      simpa only [show (4:V)+1=5 by ring] using hh
    have h163 : 163≤32*(X+1)+3 := by
      have hh := add_le_add (Arithmetic.mul_le_mul_left (a:=(32:V)) hX5) (le_refl (3:V))
      calc
        _ = 32*5+3 := by ring
        _ ≤ _ := hh
    have h108 : (108:V)<163 := by
      have hh : (108:V)<108+55 := lt_add_of_pos_right _ (by simp)
      simpa only [show (108:V)+55=163 by ring] using hh
    have hsmall : 27*D<H := lt_of_le_of_lt h27 (lt_of_lt_of_le h108 (le_trans h163 hHlower))
    have he : 27*8=27*X+27*D := by rw [←hD]; ring
    have hmod' : (27*X+27*D)%H=(27*X)%H := by rw [←he]; exact hmod.symm
    have hz : D=0 := mod_difference_zero (27*X) D H hH hmod' hsmall
    simpa only [hz,add_zero] using hD
end DiophantineConsistency.AdaptiveGap85TemplateResidue
