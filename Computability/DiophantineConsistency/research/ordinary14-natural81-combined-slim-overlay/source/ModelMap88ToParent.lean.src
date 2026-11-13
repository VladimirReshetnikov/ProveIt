import FirstRootGap88
import FreshParentRoot
import ParentFirst88
import ParentFields88

/-! Source-only 88→13-parent positive witness composition. All imports are
unelaborated drafts; no Lean, opposite direction or endpoint claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelMap88ToParentDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing FirstFields86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def parentValuation (v : Fin 14 → V) (r : V) : Fin 13 → V :=
  Function.update (fun j : Fin 13 => v j.castSucc) 8 r

theorem parent_positive (v : Fin 14 → V) (r : V) (hv : ∀ j, 0<v j) (hr : 0<r) :
    ∀ j, 0<parentValuation v r j := by
  intro j
  by_cases hj : j=8
  · subst j
    simpa [parentValuation] using hr
  · simpa [parentValuation,hj] using hv j.castSucc

theorem cast_parent (v : Fin 14 → V) (r : V) :
    (fun j => ι (parentValuation v r j)) =
      Ring88ToParentDraft.project (fun j => ι (v j)) (ι r) := by
  funext j
  by_cases hj : j=8
  · subst j
    simp [parentValuation,Ring88ToParentDraft.project]
  · simp [parentValuation,Ring88ToParentDraft.project,hj]

/-- Proposed positive 88→13-parent map using a fresh root. It assumes no K
bound, natural K/mask casts, Mersenne condition, or parent zero. -/
theorem positive_map (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P88QuotientGuarded.graph p).output v) :
    ∃ w : Fin 13 → V, (∀ j, 0<w j) ∧ InternalZero (P88FourSquare.graph p).output w := by
  let m := (v 6*v 7)*v 7
  obtain ⟨s,tau,hs,hY,ht,hn,hk,hgap⟩ :=
    FirstRootGap88Draft.quotient_and_root_gap p beta v hbeta (hv 0) (hv 6) (hv 7) (hv 9) (hv 10) hport hz
  have hb : 0<v 0*beta := mul_pos (hv 0) hbeta
  obtain ⟨r,hr,hrel⟩ := FreshParentRootDraft.fresh_root m (k v) s tau (v 0*beta) (v 13) hb (hv 13) hgap
  have hf := ParentFirst88Draft.first_zero p beta v s tau r hport hz hY hn hrel
  have ho := ParentFields88Draft.projected_fields p v (ι r) hz
  refine ⟨parentValuation v r,parent_positive v r hv hr,?_⟩
  apply (internalZero_iff _ _).mpr
  rw [P88FourSquare.output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  rw [cast_parent v r]
  rw [hf,ho.1,ho.2.1,ho.2.2]
  ring

end DiophantineConsistency.ModelMap88ToParentDraft

#print axioms DiophantineConsistency.ModelMap88ToParentDraft.positive_map
