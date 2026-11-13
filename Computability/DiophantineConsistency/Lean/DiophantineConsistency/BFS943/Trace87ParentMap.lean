import DiophantineConsistency.BFS943.Trace87Factors
import DiophantineConsistency.BFS943.Trace87NormRank
import DiophantineConsistency.BFS943.Trace75NaturalTraceShift

/-! # Squared-trace parent of the 87/214 circuit and its positive map

`Trace82ParentMap` for the free-inverse registers.
The completeness map `T ↦ f T - d R` (`d = 2 Δ i² c³ E`, so `f = 1 + c d`)
multiplies `b = cT - R` by `f` and turns `V` into the parent value
`oldV = f² b - c`; the `bV` carrier becomes `oldZ87` (weight `(f b) oldV`,
denominator `6 q⁷`, offset `eclear`, which does not involve `T`), and `value87 ∘ shift = oldValue87` is a
ring identity. The model side (`positive_zero_of_natural_parts`) is
`Trace76ParentMap`'s with the 87 register evaluations; only `T` moves. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace87ParentMap
open DiophantineConsistency.TenPositiveTrace87 DiophantineConsistency.TenPositiveTrace76

section Ring
variable {R : Type*} [CommRing R]

def shift (p : Fin 4 → R) (v : Fin 10 → R) : Fin 10 → R :=
  let r := regs p v
  let d := 2*r.Delta*(v 3)^2*r.c^3*r.E
  Function.update v 4 (r.f*v 4-d*r.rank)

def oldV (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  r.f*r.f*r.b-r.c

/-- The parent carrier at the `bV` weight, in parent coordinates. -/
def oldZ87 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  let V := oldV p v
  r.h*r.D*(r.H*(v 7-(r.f*r.b)*V*r.B)+r.K)-
    r.H*(r.D*r.B+r.h*ecl p v)

def oldValue87 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  let V := oldV p v
  let Z := oldZ87 p v
  r.Q*(Z*Z-r.M*r.M*r.Gn*(V*V))+(r.M*r.M*r.Gn-Z*Z)

theorem V_shift (p : Fin 4 → R) (v : Fin 10 → R) :
    (regs p (shift p v)).V = oldV p v := by
  let r := regs p v
  let d := 2*r.Delta*(v 3)^2*r.c^3*r.E
  have hshape : r.f = 1+r.c*d := f_one_mod_c p v
  change r.f*(r.c*(r.f*v 4-d*r.rank)-r.rank)-r.c =
    r.f*r.f*(r.c*v 4-r.rank)-r.c
  rw [hshape]
  ring

theorem b_shift (p : Fin 4 → R) (v : Fin 10 → R) :
    (regs p (shift p v)).b = (regs p v).f*(regs p v).b := by
  let r := regs p v
  let d := 2*r.Delta*(v 3)^2*r.c^3*r.E
  have hshape : r.f = 1+r.c*d := f_one_mod_c p v
  change r.c*(r.f*v 4-d*r.rank)-r.rank = r.f*(r.c*v 4-r.rank)
  rw [hshape]
  ring

theorem Z_shift (p : Fin 4 → R) (v : Fin 10 → R) :
    (regs p (shift p v)).Z = oldZ87 p v := by
  have hV := V_shift p v
  have hb := b_shift p v
  change (regs p v).h*(regs p v).D*((regs p v).H*(v 7-
      (regs p (shift p v)).b*(regs p (shift p v)).V*(regs p v).B)+(regs p v).K)-
      (regs p v).H*((regs p v).D*(regs p v).B+(regs p v).h*ecl p v) = oldZ87 p v
  rw [hV,hb]
  rfl

theorem value87_shift (p : Fin 4 → R) (v : Fin 10 → R) :
    value87 p (shift p v) = oldValue87 p v := by
  have hQ : (regs p (shift p v)).Q = (regs p v).Q := rfl
  have hM : (regs p (shift p v)).M = (regs p v).M := rfl
  have hG : (regs p (shift p v)).Gn = (regs p v).Gn := rfl
  rw [value87_norm]
  simp only [normValue,oldValue87]
  rw [Z_shift,V_shift,hQ,hM,hG]

theorem old_output_zero (p : Fin 4 → R) (v : Fin 10 → R) (tau f y u I : R)
    (hE : (regs p v).E=tau*tau)
    (hf : (regs p v).F0=f*f)
    (hQ : (regs p v).Q=I*I)
    (hV : oldV p v=u)
    (hZ : oldZ87 p v=(regs p v).M*(tau*f*y))
    (haux : I*I*u*u+y*y=1+I*I*y*y) : oldValue87 p v=0 := by
  simp only [oldValue87,Gn_def]
  rw [hE,hf,hQ,hV,hZ]
  linear_combination -((regs p v).M*(regs p v).M)*(tau*tau)*(f*f)*haux

end Ring

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open Trace87Factors Trace87NormRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_parent_zero (p : Fin 4 → DiffRing V) (v : Fin 10 → V)
    (c f d r : V) (hc : 0<c) (hf : 0<f) (hv : ∀ j,0<v j)
    (hc' : (ι c:DiffRing V)=(regs p (fun j => ι (v j))).c)
    (hf' : (ι f:DiffRing V)=(regs p (fun j => ι (v j))).f)
    (hr' : (ι r:DiffRing V)=(regs p (fun j => ι (v j))).rank)
    (hd' : (ι d:DiffRing V)=2*(regs p (fun j => ι (v j))).Delta*(ι (v 3))^2*
      (regs p (fun j => ι (v j))).c^3*(regs p (fun j => ι (v j))).E)
    (hV : 0<oldV p (fun j => ι (v j)))
    (hz : oldValue87 p (fun j => ι (v j))=0) :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ value87 p (fun j => ι (w j))=0 := by
  let z : Fin 10 → DiffRing V := fun j => ι (v j)
  have hshape : f=1+c*d := by
    apply ι_injective
    simp only [map_add,map_one,map_mul]
    rw [hf',hc',hd']
    exact f_one_mod_c p z
  have hV' : (0:DiffRing V)<ι f*ι f*(ι c*ι (v 4)-ι r)-ι c := by
    rw [hf',hc',hr']
    exact hV
  obtain ⟨T,hT,hTcast,_heq⟩ := Trace75NaturalTraceShift.natural_shift c f d (v 4) r hc hf hshape hV'
  let w : Fin 10 → V := Function.update v 4 T
  have hw : ∀ j,0<w j := by
    intro j
    fin_cases j <;> simp [w,hT,hv]
  have hcast : (fun j => ι (w j))=shift p z := by
    funext j
    fin_cases j <;> simp [w,shift,z,hTcast,hf',hr',hd']
  refine ⟨w,hw,?_⟩
  rw [hcast,value87_shift]
  exact hz

theorem positive_zero_of_parts (p : Fin 4 → DiffRing V) (v : Fin 10 → V)
    (c f d r tau f0 y u I : V) (hc : 0<c) (hf : 0<f) (hu : 0<u)
    (hv : ∀ j,0<v j)
    (hc' : (ι c:DiffRing V)=(regs p (fun j => ι (v j))).c)
    (hf' : (ι f:DiffRing V)=(regs p (fun j => ι (v j))).f)
    (hr' : (ι r:DiffRing V)=(regs p (fun j => ι (v j))).rank)
    (hd' : (ι d:DiffRing V)=2*(regs p (fun j => ι (v j))).Delta*(ι (v 3))^2*
      (regs p (fun j => ι (v j))).c^3*(regs p (fun j => ι (v j))).E)
    (hE : (regs p (fun j => ι (v j))).E=ι tau*ι tau)
    (hf0 : (regs p (fun j => ι (v j))).F0=ι f0*ι f0)
    (hQ : (regs p (fun j => ι (v j))).Q=ι I*ι I)
    (hV : oldV p (fun j => ι (v j))=ι u)
    (hZ : oldZ87 p (fun j => ι (v j))=(regs p (fun j => ι (v j))).M*(ι tau*ι f0*ι y))
    (haux : (ι I:DiffRing V)*ι I*ι u*ι u+ι y*ι y=1+ι I*ι I*ι y*ι y) :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ value87 p (fun j => ι (w j))=0 := by
  have hVpos : 0<oldV p (fun j => ι (v j)) := by
    rw [hV]
    simpa only [map_zero] using (ι_lt_ι.mpr hu)
  have hz := old_output_zero p (fun j => ι (v j)) (ι tau) (ι f0) (ι y) (ι u) (ι I)
    hE hf0 hQ hV hZ haux
  exact positive_parent_zero p v c f d r hc hf hv hc' hf' hr' hd' hVpos hz

theorem positive_zero_of_natural_parts (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (tau f0 y u I : V) (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hmask : v 1+v 2<q p v) (hu : 0<u)
    (hE : E p v=tau*tau)
    (hf0 : f0*f0=1+delta p v*U p v*U p v*(tau*tau))
    (hQ : delta p v*(4*(delta p v*U p v*U p v*(tau*tau))*
      (1+delta p v*U p v*U p v*(tau*tau)))=I*I)
    (hV : oldV (ports p) (fun j => ι (v j))=ι u)
    (hZ : oldZ87 (ports p) (fun j => ι (v j))=
      (regs (ports p) (fun j => ι (v j))).M*(ι tau*ι f0*ι y))
    (haux : I*I*u*u+y*y=1+I*I*y*y) :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ value87 (ports p) (fun j => ι (w j))=0 := by
  let A0 := delta p v*U p v*U p v*(tau*tau)
  let f := 1+2*A0
  let d := 2*delta p v*(v 3)^2*(c p v)^3*E p v
  let z : Fin 10 → DiffRing V := fun j => ι (v j)
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hc : 0<c p v := add_pos (mul_pos hk (hv 6)) (hv 8)
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hf : 0<f := by dsimp [f]; simp
  have hc' : (ι (c p v):DiffRing V)=(regs (ports p) z).c := by
    simp only [c,k,ports,z,regs,TenPositiveTrace82.regsAtC,map_mul,map_add,map_one,map_natCast]
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

#print axioms Trace87ParentMap.value87_shift
#print axioms Trace87ParentMap.positive_zero_of_natural_parts
end Trace87ParentMap
