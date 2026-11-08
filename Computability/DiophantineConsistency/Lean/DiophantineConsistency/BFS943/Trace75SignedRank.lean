import DiophantineConsistency.BFS943.AdjacentStep
import DiophantineConsistency.ArithmeticPellHalfIndex
import DiophantineConsistency.ArithmeticPellResidueAux

/-! Residues of a signed rank difference without assuming its sign. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace75SignedRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellHalfIndex ArithmeticPellResidueAux ArithmeticSignedPairs ModelDifferenceRing
open TenPositiveAdjacentStep
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Both signs of the rank are retained; the multiplier residue is an explicit premise. -/
theorem signed_rank_residue (c f t rp rn : V) (hc : 0<c)
    (hfmod : (f)%c=(1:V)%c) :
    SignMod c (absdiff (f*(t*c+rn)) (f*rp+c)) (absdiff rp rn) := by
  have hmul (r : V) : (f*r)%c=r%c := by
    have hh := same_mul hc hfmod (show r%c=r%c from rfl)
    simpa only [one_mul] using hh
  have hd : c∣c*(f*t) := dvd_mul_right c _
  rcases le_total rn rp with h|h
  · let r := rp-rn
    have hr : rp=rn+r := by dsimp [r]; rw [add_comm,tsub_add_cancel_of_le h]
    have hmag : absdiff rp rn=r := by
      simp only [absdiff,tsub_eq_zero_of_le h,add_zero,r]
    have he : (f*(t*c+rn)+r)%c=(f*rp+c)%c := by
      have hleft : f*(t*c+rn)+r=c*(f*t)+(f*rn+r) := by ring
      have hright : f*rp+c=(f*rn+f*r)+c := by rw [hr]; ring
      rw [hleft,hright,mod_add_remove_left_of_dvd hd hc,mod_add_remove_right hc]
      calc
        (f*rn+r)%c=((f*rn)%c+r%c)%c := mod_add hc
        _=((f*rn)%c+(f*r)%c)%c := by rw [hmul r]
        _=(f*rn+f*r)%c := (mod_add hc).symm
    rw [hmag]
    exact absdiff_residue c _ _ r hc he
  · let r := rn-rp
    have hr : rn=rp+r := by dsimp [r]; rw [add_comm,tsub_add_cancel_of_le h]
    have hmag : absdiff rp rn=r := by
      simp only [absdiff,tsub_eq_zero_of_le h,zero_add,r]
    have he : (f*rp+c+r)%c=(f*(t*c+rn))%c := by
      have hleft : f*rp+c+r=c+(f*rp+r) := by ring
      have hright : f*(t*c+rn)=c*(f*t)+(f*rp+f*r) := by rw [hr]; ring
      rw [hleft,hright,mod_add_remove_left hc,mod_add_remove_left_of_dvd hd hc]
      calc
        (f*rp+r)%c=((f*rp)%c+r%c)%c := mod_add hc
        _=((f*rp)%c+(f*r)%c)%c := by rw [hmul r]
        _=(f*rp+f*r)%c := (mod_add hc).symm
    have hs := absdiff_residue c (f*rp+c) (f*(t*c+rn)) r hc he
    rw [hmag]
    simpa only [absdiff,add_comm] using hs


/-- A square representative retains the signed rank residue for a single multiplier. -/
theorem rank_residue_of_square (c f t rp rn u : V) (x : DiffRing V)
    (hc : 0<c) (hfmod : (f)%c=(1:V)%c)
    (hx : x=ι (f)*(ι (t*c)+ι rn-ι rp)-ι c)
    (hs : x*x=ι (u*u)) : SignMod c u (absdiff rp rn) := by
  let L := f*(t*c+rn)
  let N := f*rp+c
  have hrep : x=ι L-ι N := by
    rw [hx]
    dsimp [L,N]
    simp only [map_mul,map_add]
    ring
  have hsq : magnitude (L,N)*magnitude (L,N)=u*u := by
    apply ι_injective
    rw [←magnitude_square_cast,←hrep,hs]
  have heq : magnitude (L,N)=u := by
    apply le_antisymm
    · by_contra hn
      have hu : u<magnitude (L,N) := lt_of_not_ge hn
      have h : u*u < magnitude (L,N)*magnitude (L,N) :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt hu) (by simp))
          (mul_lt_mul_of_pos_right hu (lt_of_le_of_lt (by simp) hu))
      rw [hsq] at h
      exact (_root_.lt_irrefl _ h)
    · by_contra hn
      have hu : magnitude (L,N)<u := lt_of_not_ge hn
      have h : magnitude (L,N)*magnitude (L,N)<u*u :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt hu) (by simp))
          (mul_lt_mul_of_pos_right hu (lt_of_le_of_lt (by simp) hu))
      rw [hsq] at h
      exact (_root_.lt_irrefl _ h)
  have h := signed_rank_residue c f t rp rn hc hfmod
  change SignMod c (magnitude (L,N)) (absdiff rp rn) at h
  rwa [heq] at h

#print axioms Trace75SignedRank.rank_residue_of_square
end Trace75SignedRank
