import DiophantineConsistency.ArithmeticPellResidueAux

/-! Residues of a signed rank difference without assuming its sign. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85SignedResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellHalfIndex ArithmeticPellResidueAux
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Both signs of the rank are retained; the square residue is an explicit premise. -/
theorem signed_rank_residue (c f t rp rn : V) (hc : 0<c)
    (hfmod : (f*f)%c=(1:V)%c) :
    SignMod c (absdiff (f*f*(t*c+rn)) (f*f*rp+c)) (absdiff rp rn) := by
  have hmul (r : V) : (f*f*r)%c=r%c := by
    have hh := same_mul hc hfmod (show r%c=r%c from rfl)
    simpa only [one_mul] using hh
  have hd : c∣c*(f*f*t) := dvd_mul_right c _
  rcases le_total rn rp with h|h
  · let r := rp-rn
    have hr : rp=rn+r := by dsimp [r]; rw [add_comm,tsub_add_cancel_of_le h]
    have hmag : absdiff rp rn=r := by
      simp only [absdiff,tsub_eq_zero_of_le h,add_zero,r]
    have he : (f*f*(t*c+rn)+r)%c=(f*f*rp+c)%c := by
      have hleft : f*f*(t*c+rn)+r=c*(f*f*t)+(f*f*rn+r) := by ring
      have hright : f*f*rp+c=(f*f*rn+f*f*r)+c := by rw [hr]; ring
      rw [hleft,hright,mod_add_remove_left_of_dvd hd hc,mod_add_remove_right hc]
      calc
        (f*f*rn+r)%c=((f*f*rn)%c+r%c)%c := mod_add hc
        _=((f*f*rn)%c+(f*f*r)%c)%c := by rw [hmul r]
        _=(f*f*rn+f*f*r)%c := (mod_add hc).symm
    rw [hmag]
    exact absdiff_residue c _ _ r hc he
  · let r := rn-rp
    have hr : rn=rp+r := by dsimp [r]; rw [add_comm,tsub_add_cancel_of_le h]
    have hmag : absdiff rp rn=r := by
      simp only [absdiff,tsub_eq_zero_of_le h,zero_add,r]
    have he : (f*f*rp+c+r)%c=(f*f*(t*c+rn))%c := by
      have hleft : f*f*rp+c+r=c+(f*f*rp+r) := by ring
      have hright : f*f*(t*c+rn)=c*(f*f*t)+(f*f*rp+f*f*r) := by rw [hr]; ring
      rw [hleft,hright,mod_add_remove_left hc,mod_add_remove_left_of_dvd hd hc]
      calc
        (f*f*rp+r)%c=((f*f*rp)%c+r%c)%c := mod_add hc
        _=((f*f*rp)%c+(f*f*r)%c)%c := by rw [hmul r]
        _=(f*f*rp+f*f*r)%c := (mod_add hc).symm
    have hs := absdiff_residue c (f*f*rp+c) (f*f*(t*c+rn)) r hc he
    rw [hmag]
    simpa only [absdiff,add_comm] using hs
end DiophantineConsistency.AdaptiveGap85SignedResidue
