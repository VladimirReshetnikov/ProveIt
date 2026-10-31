import DiophantineConsistency.ArithmeticPellHalfIndex

/-! Small signed rank residues force the positive orientation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85RankOrientation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem mod_cancel85 {a b c m : V} (hm : 0<m) (h : (a+c)%m=(b+c)%m) : a%m=b%m := by
  have hr := le_of_lt (mod_lt c hm)
  have hc : c+(m-c%m)=m*(c/m+1) := by
    calc
      c+(m-c%m)=(m*(c/m)+c%m)+(m-c%m) := by rw [div_add_mod]
      _=m*(c/m)+(c%m+(m-c%m)) := by ring
      _=m*(c/m)+m := by rw [add_tsub_cancel_of_le hr]
      _=m*(c/m+1) := by ring
  have hh : ((a+c)+(m-c%m))%m=((b+c)+(m-c%m))%m := by
    rw [mod_add (a:=a+c) hm,mod_add (a:=b+c) hm,h]
  simpa only [add_assoc,hc,mod_add_mul' _ _ hm] using hh

/-- If the absolute signed rank plus twice the positive index is below the
modulus, the signed residue fixes the rank orientation and exact value. -/
theorem positive_rank_of_small_residue (modulus rp rn n : V)
    (hmod : 0<modulus) (hn : 0<n)
    (hsmall : absdiff rp rn+2*n<modulus)
    (hres : (rp+1)%modulus=(rn+2*n)%modulus) :
    rn<rp ∧ absdiff rp rn+1=2*n := by
  let R := absdiff rp rn
  have hn1 : (1:V)≤n := pos_iff_one_le.mp hn
  have hn2 : (2:V)≤2*n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn1 (by simp : (0:V)≤2)
  have hone : (1:V)≤2*n := le_trans (by simp : (1:V)≤2) hn2
  have htwo : 2*n<modulus := lt_of_le_of_lt (by simp : 2*n≤R+2*n) hsmall
  have hRle : R+1≤R+2*n := by simpa only [add_comm] using add_le_add_left hone R
  have hR1 : R+1<modulus := lt_of_le_of_lt hRle hsmall
  rcases le_total rn rp with h|h
  · have hRdef : R=rp-rn := by dsimp [R,absdiff]; rw [tsub_eq_zero_of_le h,add_zero]
    have hrp : rp=rn+R := by rw [hRdef,add_comm,tsub_add_cancel_of_le h]
    have he : ((R+1)+rn)%modulus=((2*n)+rn)%modulus := by
      rw [hrp] at hres
      simpa only [add_assoc,add_comm,add_left_comm] using hres
    have he' := mod_cancel85 hmod he
    rw [mod_eq_self_of_lt hR1,mod_eq_self_of_lt htwo] at he'
    have hlt : rn<rp := lt_of_le_of_ne h (by
      intro heq
      have hz : R=0 := by rw [hRdef,heq,tsub_self]
      have htwo1 : 2*n=1 := by simpa only [hz,zero_add] using he'.symm
      have hbad : (2:V)≤1 := by simpa only [htwo1] using hn2
      exact (not_le_of_gt (by norm_num : (1:V)<2)) hbad)
    exact ⟨hlt,he'⟩
  · have hRdef : R=rn-rp := by dsimp [R,absdiff]; rw [tsub_eq_zero_of_le h,zero_add]
    have hrn : rn=rp+R := by rw [hRdef,add_comm,tsub_add_cancel_of_le h]
    have he : (1+rp)%modulus=((R+2*n)+rp)%modulus := by
      rw [hrn] at hres
      simpa only [add_assoc,add_comm,add_left_comm] using hres
    have he' := mod_cancel85 hmod he
    have h1 : (1:V)<modulus := lt_of_lt_of_le (by norm_num : (1:V)<2) (le_trans hn2 (le_of_lt htwo))
    rw [mod_eq_self_of_lt h1,mod_eq_self_of_lt hsmall] at he'
    have hgt : (1:V)<R+2*n := lt_of_lt_of_le (by norm_num : (1:V)<2) (le_trans hn2 (by simp))
    exact False.elim ((ne_of_gt hgt) he'.symm)
end DiophantineConsistency.AdaptiveGap85RankOrientation
