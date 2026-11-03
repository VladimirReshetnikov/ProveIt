import Direct80Adjacent
import DiophantineConsistency.ArithmeticPellHalfIndex

/-! Signed residue for a square multiple minus a natural term. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80Residue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open ArithmeticPellHalfIndex ArithmeticSignedPairs
open TenPositiveAdjacentStep
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- No sign assumption on the difference-ring factor. -/
theorem square_multiple_residue (F c u : V) (w x : DiffRing V)
    (hF : 0<F) (hx : x=ι (F*F)*w-ι c)
    (hs : x*x=ι (u*u)) : SignMod F u c := by
  obtain ⟨rp,rn,hw⟩ := exists_mk w
  rw [mk_eq_sub] at hw
  let L := F*F*rp
  let N := F*F*rn+c
  have hrep : x=ι L-ι N := by
    rw [hx,hw]
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
  have hres : (L+c)%F=N%F := by
    have hL : F∣L := ⟨F*rp,by dsimp [L]; ring⟩
    have hN : F∣F*F*rn := ⟨F*rn,by ring⟩
    calc
      (L+c)%F=c%F := mod_add_remove_left_of_dvd hL hF
      _=(F*F*rn+c)%F := (mod_add_remove_left_of_dvd hN hF).symm
      _=N%F := rfl
  have h := absdiff_residue F L N c hF hres
  change SignMod F (magnitude (L,N)) c at h
  rwa [heq] at h

#print axioms TenPositive80Residue.square_multiple_residue
end TenPositive80Residue
