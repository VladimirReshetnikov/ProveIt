import Trace75OffsetDiv
import Trace75Rank

/-! Natural offset congruence for the q³ chart. Draft until checked. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75OffsetCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace75OffsetDiv Trace75Rank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem mod_eq_of_signed_dvd (m x y : V) (hm : 0<m)
    (hd : (ι m : DiffRing V)∣ι x-ι y) : x%m=y%m := by
  obtain ⟨t,ht⟩ := hd
  rcases nonneg_or_nonpos t with ⟨a,ha⟩|⟨a,ha⟩
  · have he : x=y+m*a := by
      apply ι_injective
      calc
        (ι x:DiffRing V)=((ι x:DiffRing V)-ι y)+ι y := by ring
        _=ι m*ι a+ι y := by rw [ht,ha]
        _=ι (y+m*a) := by rw [map_add,map_mul]; ring
    rw [he,mod_add_mul' _ _ hm]
  · have he : x+m*a=y := by
      apply ι_injective
      calc
        (ι (x+m*a):DiffRing V)=ι x+ι m*ι a := by rw [map_add,map_mul]
        _=((ι x:DiffRing V)-ι y)+ι y+ι m*ι a := by ring
        _=ι m*(-ι a)+ι y+ι m*ι a := by rw [ht,ha]
        _=ι y := by ring
    have h := congrArg (fun z : V => z%m) he
    rwa [mod_add_mul' _ _ hm] at h

theorem graph_offset_congruence (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    k v%(q p v)^4=(rankNat p v+1)%(q p v)^4 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hrank := (graph_rank_window p v hb31 hl hh hv hz).1
  have he : (regs (ports p) (fun j => ι (v j))).e =
      (ι (k v):DiffRing V)-ι (rankNat p v+1) := by
    rw [e_def,k_def,hrank]
    simp only [k,map_add,map_one]
    ring
  have hd := graph_offset_divisible p v hb hv hz
  rw [he,←map_pow] at hd
  exact mod_eq_of_signed_dvd _ _ _ (pow_pos hq 4) hd

#print axioms Trace75OffsetCongruence.graph_offset_congruence
end Trace75OffsetCongruence
