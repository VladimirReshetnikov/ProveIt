import Guard88
import Ring88ToParent
import FirstQuotient88

/-! Source-only first-residual transport for an explicitly supplied fresh
root and norm witnesses. No positive parent witness or Lean result. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.ParentFirst88Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing FirstFields86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- With a same-zero guard and explicit quotient/root balance, the projected
parent first residual vanishes. No parent zero or root sign is assumed. -/
theorem first_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (s tau r : V)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P88QuotientGuarded.graph p).output v)
    (hY : v 7=Q beta v*s) (htau : tau*tau=radicand v)
    (hrel : r+((v 6*v 7*v 7)*k v+k v+s)=
      k v*((v 0*beta)*v 13)+v 13+tau) :
    (P88FourSquare.graph p).A0.evalRing
      (Ring88ToParentDraft.project (fun j => ι (v j)) (ι r))=0 := by
  let z : Fin 14 → DiffRing V := fun j => ι (v j)
  have hb : Ring88ToParentDraft.b p z=ι (v 0*beta) := by
    simp [Ring88ToParentDraft.b,z,hport,map_mul]
  have hq3 : Ring88ToParentDraft.q3 p z=ι (Q beta v) := by
    simp [Ring88ToParentDraft.q3,Ring88ToParentDraft.q,Ring88ToParentDraft.b,
      Q,q,z,hport,map_add,map_mul,map_one]
  have hk : Ring88ToParentDraft.k z=ι (k v) := by
    simp [Ring88ToParentDraft.k,k,z,map_add]
  have hell : Ring88ToParentDraft.ell z=ι (ell v) := by
    simp [Ring88ToParentDraft.ell,Ring88ToParentDraft.k,ell,k,z,map_add,map_mul]
  have hdelta : Ring88ToParentDraft.delta z=ι (radicand v) := by
    simp [Ring88ToParentDraft.delta,Ring88ToParentDraft.ell,Ring88ToParentDraft.k,
      radicand,firstP,ell,k,z,map_add,map_mul,map_one]
  have hellnat : ell v=(v 6*v 7*v 7)*k v := by dsimp [ell]; ring
  have hbt : (P88QuotientGuarded.graph p).Bt.evalRing z=
      Ring88ToParentDraft.b p z*ι (v 13) := by
    have h := Guard88Draft.bt_of_zero p beta v hport hz
    change (P88QuotientGuarded.graph p).Bt.evalRing z=ι ((v 0*beta)*v 13) at h
    rw [hb,map_mul]
    exact h
  have hYring : z 7=Ring88ToParentDraft.q3 p z*ι s := by
    rw [hq3,←map_mul,←hY]
  have hr0 : ι r+(ι (ell v)+ι (k v)+ι s)=
      ι (k v)*(ι (v 0*beta)*ι (v 13))+ι (v 13)+ι tau := by
    rw [hellnat]
    simpa only [map_add,map_mul] using congrArg (ι : V →+* DiffRing V) hrel
  have hrring : ι r+(Ring88ToParentDraft.ell z+Ring88ToParentDraft.k z+ι s)=
      Ring88ToParentDraft.k z*(Ring88ToParentDraft.b p z*ι (v 13))+ι (v 13)+ι tau := by
    rw [hell,hk,hb]
    exact hr0
  have hcut := Ring88ToParentDraft.first_cut (Ring88ToParentDraft.q3 p z)
    (Ring88ToParentDraft.b p z) (z 7) (Ring88ToParentDraft.ell z)
    (Ring88ToParentDraft.k z) (ι (v 13)) (ι s) (ι tau) (ι r) hYring hrring
  have ht : ι tau*ι tau=ι (radicand v) := by
    simpa only [map_mul] using congrArg (ι : V →+* DiffRing V) htau
  have hf := Ring88ToParentDraft.first_eval p z (ι r)
  rw [hbt,Ring88ToParentDraft.scale,hcut,hdelta,←ht] at hf
  change (P88FourSquare.graph p).A0.evalRing (Ring88ToParentDraft.project z (ι r))=0
  rw [hf]
  ring

end DiophantineConsistency.ParentFirst88Draft

#print axioms DiophantineConsistency.ParentFirst88Draft.first_zero
