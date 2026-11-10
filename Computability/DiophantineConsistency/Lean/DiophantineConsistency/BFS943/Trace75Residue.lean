import DiophantineConsistency.BFS943.Trace75Factors
import DiophantineConsistency.BFS943.AdjacentStep
import DiophantineConsistency.ArithmeticPellHalfIndex

/-! Signed trace75 V residue; no index-folding conclusion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75Residue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellHalfIndex ArithmeticSignedPairs TenPositiveAdjacentStep Trace75Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem multiple_residue (F c u : V) (w x : DiffRing V)
    (hF : 0<F) (hx : x=ι F*w-ι c) (hs : x*x=ι (u*u)) : SignMod F u c := by
  obtain ⟨rp,rn,hw⟩ := exists_mk w
  rw [mk_eq_sub] at hw
  let L := F*rp
  let N := F*rn+c
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
    have hL : F∣L := ⟨rp,rfl⟩
    have hN : F∣F*rn := ⟨rn,rfl⟩
    calc
      (L+c)%F=c%F := mod_add_remove_left_of_dvd hL hF
      _=(F*rn+c)%F := (mod_add_remove_left_of_dvd hN hF).symm
      _=N%F := rfl
  have h := absdiff_residue F L N c hF hres
  change SignMod F (magnitude (L,N)) c at h
  rwa [heq] at h

theorem c_eval (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    (regs (ports p) (fun j => ι (v j))).c = ι (c p v) := by
  simp only [c,k,Y,q,b,ports,regs,map_mul,map_add,map_one,map_natCast]

theorem graph_signed_residue (p : Fin 4 → ℕ) (v : Fin 10 → V) (u : V)
    (hs : (regs (ports p) (fun j => ι (v j))).V *
      (regs (ports p) (fun j => ι (v j))).V = ι (u*u)) :
    SignMod (1+2*(delta p v*U p v*U p v*E p v)) u (c p v) := by
  let a : V := delta p v*U p v*U p v*E p v
  let F : V := 1+2*a
  let w : DiffRing V := (regs (ports p) (fun j => ι (v j))).b
  have hF : 0<F := by dsimp [F]; simp
  have hx : (regs (ports p) (fun j => ι (v j))).V=ι F*w-ι (c p v) := by
    rw [V_def,f_eq,a_eq,delta_eval,U_eval,E_eval,c_eval]
    dsimp [w,F,a]
    simp only [pow_two,map_mul,map_add,map_one,map_ofNat]
    ring
  exact multiple_residue F (c p v) u w _ hF hx hs

#print axioms Trace75Residue.graph_signed_residue
end Trace75Residue
