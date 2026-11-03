import Trace75OldTracePartsJoin
import Trace75Rank

/-! Bind the natural trace75 representatives to conditional scalar parts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75NaturalPartsBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace75Rank Trace75OldTraceMap Trace75OldTracePartsJoin
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_of_natural_parts (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (tau f0 y u I : V) (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hmask : v 1+v 2<q p v) (hu : 0<u)
    (hE : E p v=tau*tau)
    (hf0 : f0*f0=1+delta p v*U p v*U p v*(tau*tau))
    (hQ : delta p v*(4*(delta p v*U p v*U p v*(tau*tau))*
      (1+delta p v*U p v*U p v*(tau*tau)))=I*I)
    (hV : oldV (ports p) (fun j => ι (v j))=ι u)
    (hZ : oldZ (ports p) (fun j => ι (v j))=
      (regs (ports p) (fun j => ι (v j))).M*(ι tau*ι f0*ι y))
    (haux : I*I*u*u+y*y=1+I*I*y*y) :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ value75 (ports p) (fun j => ι (w j))=0 := by
  let A0 := delta p v*U p v*U p v*(tau*tau)
  let f := 1+2*A0
  let d := 2*delta p v*(v 3)^2*(c p v)^3*E p v
  let z : Fin 10 → DiffRing V := fun j => ι (v j)
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hc : 0<c p v := add_pos (mul_pos hk hY) (hv 8)
  have hf : 0<f := by dsimp [f]; simp
  have hc' : (ι (c p v):DiffRing V)=(regs (ports p) z).c := by
    simp only [c,k,Y,q,b,ports,z,regs,map_mul,map_add,map_one,map_natCast]
  have hr' : (ι (rankNat p v):DiffRing V)=(regs (ports p) z).rank :=
    (rank_eval_of_mask p v hq hmask).symm
  have he' : (regs (ports p) z).E=ι tau*ι tau := by
    rw [E_eval,hE,map_mul]
  have ha' : (regs (ports p) z).a=ι A0 := by
    rw [a_def,delta_eval,U_eval,he']
    dsimp [A0]
    simp only [map_mul]
    ring
  have hf' : (ι f:DiffRing V)=(regs (ports p) z).f := by
    rw [f_def,F0_def,ha']
    dsimp [f]
    simp only [map_add,map_mul,map_one,map_ofNat]
    ring
  have hd' : (ι d:DiffRing V)=2*(regs (ports p) z).Delta*(ι (v 3))^2*
      (regs (ports p) z).c^3*(regs (ports p) z).E := by
    rw [delta_eval,←hc',E_eval]
    dsimp [d]
    simp only [map_mul,map_pow,map_ofNat]
  have hf0' : (regs (ports p) z).F0=ι f0*ι f0 := by
    rw [F0_def,ha']
    dsimp [A0]
    simp only [map_mul]
    have hh := congrArg (ι : V →+* DiffRing V) hf0
    simp only [map_add,map_one,map_mul] at hh
    linear_combination -hh
  have hQ' : (regs (ports p) z).Q=ι I*ι I := by
    rw [Q_def,delta_eval,ha',F0_def,ha']
    dsimp [A0]
    simp only [map_mul]
    have hh := congrArg (ι : V →+* DiffRing V) hQ
    simp only [map_add,map_one,map_mul,map_ofNat] at hh
    linear_combination hh
  have haux' : (ι I:DiffRing V)*ι I*ι u*ι u+ι y*ι y=1+ι I*ι I*ι y*ι y := by
    have hh := congrArg (ι : V →+* DiffRing V) haux
    simpa only [map_add,map_mul,map_one] using hh
  exact positive_zero_of_parts (ports p) v (c p v) f d (rankNat p v) tau f0 y u I
    hc hf hu hv hc' hf' hr' hd' he' hf0' hQ' hV hZ haux'

#print axioms Trace75NaturalPartsBinding.positive_zero_of_natural_parts
end Trace75NaturalPartsBinding
