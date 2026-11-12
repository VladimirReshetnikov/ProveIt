import RingParentTo88
import ParentTo88FirstCut
import DiophantineConsistency.Compact44.P72Root

/-! Source-only target first residual from explicitly supplied quotient and
Pell norm. No graph zero, witness map or Lean elaboration is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.ParentTo88FirstDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def b (p : Fin 4 → ℕ) (v : Fin 13 → V) : V := v 0*(p 0:V)
def q (p : Fin 4 → ℕ) (v : Fin 13 → V) : V := 1+b p v
def Q (p : Fin 4 → ℕ) (v : Fin 13 → V) : V := q p v*(q p v*q p v)
def k (v : Fin 13 → V) : V := v 9+v 10
def ell (v : Fin 13 → V) : V := (v 6*v 7)*(v 7*k v)
def D (v : Fin 13 → V) : V := 1+ell v*(ell v+k v)
def sigma (v : Fin 13 → V) (s tau : V) : V := ell v+k v+s+tau

/-- Explicit positive-quotient and norm identities force the target first
residual to vanish with the fresh root, independently of its guard. -/
theorem first_zero (p : Fin 4 → ℕ) (v : Fin 13 → V) (s tau t : V)
    (hY : v 7=Q p v*s) (htau : tau*tau=D v) :
    let pi : Fin 4 → ℤ := fun j => (p j : ℤ)
    let w := RingParentTo88Draft.extend (fun j => ι (v j)) (ι (sigma v s tau)) (ι t)
    (P88QuotientGuarded.graph pi).A0.evalRing w=0 := by
  let pi : Fin 4 → ℤ := fun j => (p j : ℤ)
  let z : Fin 13 → DiffRing V := fun j => ι (v j)
  let w := RingParentTo88Draft.extend z (ι (sigma v s tau)) (ι t)
  have hp0 : ((pi 0 : ℤ) : DiffRing V)=ι (p 0:V) := P72Root.cast_port p 0
  have hb : Ring88ToParentDraft.b pi w=ι (b p v) := by
    simp [Ring88ToParentDraft.b,RingParentTo88Draft.extend,b,w,z,hp0,map_mul]
  have hQ : Ring88ToParentDraft.q3 pi w=ι (Q p v) := by
    simp [Ring88ToParentDraft.q3,Ring88ToParentDraft.q,Ring88ToParentDraft.b,
      RingParentTo88Draft.extend,Q,q,b,w,z,hp0,map_add,map_mul,map_one]
  have hk : Ring88ToParentDraft.k w=ι (k v) := by
    simp [Ring88ToParentDraft.k,RingParentTo88Draft.extend,k,w,z,map_add]
  have hell : Ring88ToParentDraft.ell w=ι (ell v) := by
    simp [Ring88ToParentDraft.ell,Ring88ToParentDraft.k,RingParentTo88Draft.extend,
      ell,k,w,z,map_add,map_mul]
  have hD : Ring88ToParentDraft.delta w=ι (D v) := by
    simp [Ring88ToParentDraft.delta,Ring88ToParentDraft.ell,Ring88ToParentDraft.k,
      RingParentTo88Draft.extend,D,ell,k,w,z,map_add,map_mul,map_one]
  have hYs : w 7=Ring88ToParentDraft.q3 pi w*ι s := by
    rw [hQ,←map_mul,←hY]
    simp [w,z,RingParentTo88Draft.extend]
  have hsigma : ι (sigma v s tau)=Ring88ToParentDraft.ell w+Ring88ToParentDraft.k w+ι s+ι tau := by
    rw [hell,hk]
    simp [sigma,map_add]
  have hcut := ParentTo88FirstCutDraft.fresh_first_cut (Ring88ToParentDraft.q3 pi w)
    (Ring88ToParentDraft.b pi w) (w 7) (Ring88ToParentDraft.ell w)
    (Ring88ToParentDraft.k w) (ι s) (ι tau) hYs
  rw [←hsigma] at hcut
  have ht : ι tau*ι tau=ι (D v) := by
    simpa only [map_mul] using congrArg (ι : V →+* DiffRing V) htau
  have hf := RingParentTo88Draft.first_eval pi z (ι (sigma v s tau)) (ι t)
  change (P88QuotientGuarded.graph pi).A0.evalRing w=0
  rw [Ring88ToParentDraft.scale,hcut,hD,←ht] at hf
  rw [hf]
  ring

end DiophantineConsistency.ParentTo88FirstDraft

#print axioms DiophantineConsistency.ParentTo88FirstDraft.first_zero
