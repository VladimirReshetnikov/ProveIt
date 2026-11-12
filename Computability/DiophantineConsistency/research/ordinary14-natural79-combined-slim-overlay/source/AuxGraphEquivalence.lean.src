import GraphNormClient
import AuxRootBridge

/-! Source-only proposed literal 78↔79 model client. Imports are separately
uncompiled drafts; no elaboration, provider or endpoint result is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.AuxGraphEquivalenceDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open DirectFirstRootModelDraft AuxRootModelDraft AuxGraphNormClientDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def putAux (v : Fin 14 → V) (u : V) : Fin 14 → V := Function.update v 11 u

theorem putAux_self (v : Fin 14 → V) : putAux v (v 11)=v := by
  funext j
  by_cases hj : j=11
  · subst j
    simp [putAux]
  · simp [putAux,hj]

theorem putAux_positive (v : Fin 14 → V) (u : V)
    (hv : ∀ j, 0<v j) (hu : 0<u) : ∀ j, 0<putAux v u j := by
  intro j
  by_cases hj : j=11
  · subst j
    simpa [putAux] using hu
  · simpa [putAux,hj] using hv j

/-- The four non-auxiliary literal fields are shared between the graphs. -/
theorem common_fields (p : Fin 4 → ℤ) :
    (P78AuxRoot.graph p).A0=(P79DirectPell.graph p).A0 ∧
    (P78AuxRoot.graph p).A1=(P79DirectPell.graph p).A1 ∧
    (P78AuxRoot.graph p).gap=(P79DirectPell.graph p).gap ∧
    (P78AuxRoot.graph p).guardResidual=(P79DirectPell.graph p).guardResidual := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- The four old graph fields ignore the auxiliary-coordinate slot. -/
theorem other_fields_ignore_aux (p : Fin 4 → ℤ) (v : Fin 14 → V) (u : V) :
    eval (P79DirectPell.graph p).A0 (putAux v u)=eval (P79DirectPell.graph p).A0 v ∧
    eval (P79DirectPell.graph p).A1 (putAux v u)=eval (P79DirectPell.graph p).A1 v ∧
    eval (P79DirectPell.graph p).gap (putAux v u)=eval (P79DirectPell.graph p).gap v ∧
    eval (P79DirectPell.graph p).guardResidual (putAux v u)=
      eval (P79DirectPell.graph p).guardResidual v := by
  simp [eval,P79DirectPell.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,putAux,Function.update]

/-- Proposed old literal auxiliary residual evaluation. -/
theorem old_aux_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (u : V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P79DirectPell.graph p).aux (putAux v u)-1 =
      oldAux (zvalue p beta v) (coeff beta v) u := by
  simp [eval,P79DirectPell.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,putAux,Function.update,
    oldAux,zvalue,coeff,rank,q,X,Y,k,a,c,Delta,hport,map_add,map_mul,map_one] <;> ring

/-- Proposed direct auxiliary residual evaluation. -/
theorem new_aux_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (y : V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P78AuxRoot.graph p).aux (putAux v y)-1 =
      directAux (zvalue p beta v) (coeff beta v) (ι y) := by
  simp [eval,P78AuxRoot.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,putAux,Function.update,
    directAux,zvalue,coeff,rank,q,X,Y,k,a,c,Delta,hport,map_add,map_mul,map_one] <;> ring

/-- Proposed old output equality with the other four fields fixed. -/
theorem old_output_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (u : V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P79DirectPell.graph p).output (putAux v u)=
      fiveSquares (eval (P79DirectPell.graph p).A0 v) (eval (P79DirectPell.graph p).A1 v)
        (oldAux (zvalue p beta v) (coeff beta v) u) (eval (P79DirectPell.graph p).gap v)
        (eval (P79DirectPell.graph p).guardResidual v) := by
  rw [P79DirectPell.output_shape]
  simp only [eval,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  change fiveSquares (eval (P79DirectPell.graph p).A0 (putAux v u))
      (eval (P79DirectPell.graph p).A1 (putAux v u))
      (eval (P79DirectPell.graph p).aux (putAux v u)-1)
      (eval (P79DirectPell.graph p).gap (putAux v u))
      (eval (P79DirectPell.graph p).guardResidual (putAux v u)) = _
  rcases other_fields_ignore_aux p v u with ⟨h0,h1,hg,hh⟩
  rw [h0,h1,hg,hh,old_aux_eval p beta v u hport]

/-- Proposed direct output equality with the same fixed four fields. -/
theorem new_output_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (y : V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P78AuxRoot.graph p).output (putAux v y)=
      fiveSquares (eval (P79DirectPell.graph p).A0 v) (eval (P79DirectPell.graph p).A1 v)
        (directAux (zvalue p beta v) (coeff beta v) (ι y)) (eval (P79DirectPell.graph p).gap v)
        (eval (P79DirectPell.graph p).guardResidual v) := by
  rw [P78AuxRoot.output_shape]
  simp only [eval,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  rcases common_fields p with ⟨h0,h1,hg,hh⟩
  rw [h0,h1,hg,hh]
  change fiveSquares (eval (P79DirectPell.graph p).A0 (putAux v y))
      (eval (P79DirectPell.graph p).A1 (putAux v y))
      (eval (P78AuxRoot.graph p).aux (putAux v y)-1)
      (eval (P79DirectPell.graph p).gap (putAux v y))
      (eval (P79DirectPell.graph p).guardResidual (putAux v y)) = _
  rcases other_fields_ignore_aux p v y with ⟨g0,g1,gg,gh⟩
  rw [g0,g1,gg,gh,new_aux_eval p beta v y hport]

/-- Proposed all-positive graph existence comparison. Each direction obtains
its strict Q/z bounds from the graph zero with which that direction starts. -/
theorem positive_zero_iff (p : Fin 4 → ℤ) (beta : V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P79DirectPell.graph p).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P78AuxRoot.graph p).output v) := by
  constructor
  · rintro ⟨v,hv,hzero⟩
    obtain ⟨hQ,hz⟩ := bounds_of_79_positive_zero p beta v hbeta hport hv hzero
    have hold : ∃ u : V, 0<u ∧ fiveSquares (eval (P79DirectPell.graph p).A0 v)
        (eval (P79DirectPell.graph p).A1 v) (oldAux (zvalue p beta v) (coeff beta v) u)
        (eval (P79DirectPell.graph p).gap v) (eval (P79DirectPell.graph p).guardResidual v)=0 := by
      refine ⟨v 11,hv 11,?_⟩
      have he : eval (P79DirectPell.graph p).output (putAux v (v 11))=0 := by
        simpa only [putAux_self] using (internalZero_iff _ _).mp hzero
      rw [old_output_eval p beta v (v 11) hport] at he
      exact he
    obtain ⟨y,hy,hyzero⟩ := (positive_aux_coordinate_iff
      (eval (P79DirectPell.graph p).A0 v) (eval (P79DirectPell.graph p).A1 v)
      (eval (P79DirectPell.graph p).gap v) (eval (P79DirectPell.graph p).guardResidual v)
      (zvalue p beta v) (coeff beta v) hQ hz).mp hold
    refine ⟨putAux v y,putAux_positive v y hv hy,?_⟩
    apply (internalZero_iff _ _).mpr
    change eval (P78AuxRoot.graph p).output (putAux v y)=0
    rw [new_output_eval p beta v y hport]
    exact hyzero
  · rintro ⟨v,hv,hzero⟩
    obtain ⟨hQ,hz⟩ := bounds_of_78_positive_zero p beta v hbeta hport hv hzero
    have hnew : ∃ y : V, 0<y ∧ fiveSquares (eval (P79DirectPell.graph p).A0 v)
        (eval (P79DirectPell.graph p).A1 v) (directAux (zvalue p beta v) (coeff beta v) (ι y))
        (eval (P79DirectPell.graph p).gap v) (eval (P79DirectPell.graph p).guardResidual v)=0 := by
      refine ⟨v 11,hv 11,?_⟩
      have he : eval (P78AuxRoot.graph p).output (putAux v (v 11))=0 := by
        simpa only [putAux_self] using (internalZero_iff _ _).mp hzero
      rw [new_output_eval p beta v (v 11) hport] at he
      exact he
    obtain ⟨u,hu,huzero⟩ := (positive_aux_coordinate_iff
      (eval (P79DirectPell.graph p).A0 v) (eval (P79DirectPell.graph p).A1 v)
      (eval (P79DirectPell.graph p).gap v) (eval (P79DirectPell.graph p).guardResidual v)
      (zvalue p beta v) (coeff beta v) hQ hz).mpr hnew
    refine ⟨putAux v u,putAux_positive v u hv hu,?_⟩
    apply (internalZero_iff _ _).mpr
    change eval (P79DirectPell.graph p).output (putAux v u)=0
    rw [old_output_eval p beta v u hport]
    exact huzero

/-- Proposed natural-port specialization; no external port-byte binding. -/
theorem positive_zero_iff_natural_ports (p : Fin 4 → ℕ)
    (hbeta : 0<(p 0 : V)) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P79DirectPell.graph (fun j => (p j : ℤ))).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P78AuxRoot.graph (fun j => (p j : ℤ))).output v) := by
  apply positive_zero_iff (fun j => (p j : ℤ)) (p 0 : V) hbeta
  simpa only using (P72Root.cast_port p 0)

end DiophantineConsistency.AuxGraphEquivalenceDraft

#print axioms DiophantineConsistency.AuxGraphEquivalenceDraft.positive_zero_iff
#print axioms DiophantineConsistency.AuxGraphEquivalenceDraft.positive_zero_iff_natural_ports
