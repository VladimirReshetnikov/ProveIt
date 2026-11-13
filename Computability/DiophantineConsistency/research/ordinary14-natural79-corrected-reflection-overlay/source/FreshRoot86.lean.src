import FirstFields86
import DiophantineConsistency.Compact44.P72Root

/-! Source-only 86 fresh first-root replacement. Imported graph/model
sources are unelaborated drafts; no 85 witness map or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FreshRoot86Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DirectFirstRootModelDraft FirstFields86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The new old-graph root is P+tau+s; no claim compares it to the old root. -/
def fresh (v : Fin 14 → V) (s tau : V) : Fin 14 → V :=
  putRoot v (firstP v+tau+s)

/-- With Y=q³s and tau²=D the fresh 86 first field vanishes, regardless
of the sign of the original first root. -/
theorem fresh_first (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (s tau : V)
    (hport : (p 0 : DiffRing V)=ι beta) (hY : v 7=Q beta v*s)
    (htau : tau*tau=radicand v) :
    eval (P86ResidueGraph.graph p).A0 (fresh v s tau)=0 := by
  let rr : V := firstP v+tau+s
  have hM : M beta (putRoot v rr)=M beta v := by simp [M,Q,q,b,putRoot]
  have hP : firstP (putRoot v rr)=firstP v := by simp [firstP,ell,k,putRoot]
  have hb : b beta (putRoot v rr)=b beta v := by simp [b,putRoot]
  have hYslot : (putRoot v rr) 7=v 7 := by simp [putRoot]
  have hrslot : (putRoot v rr) 8=rr := by simp [putRoot]
  have hD : radicand (putRoot v rr)=radicand v := by simp [radicand,firstP,ell,k,putRoot]
  have he := first_eval p beta (putRoot v rr) hport
  rw [hM,hP,hb,hYslot,hrslot,hD] at he
  change eval (P86ResidueGraph.graph p).A0 (putRoot v rr)=0
  rw [he]
  simp only [rr,map_add,map_mul]
  have hYι : ι (v 7)=ι (Q beta v)*ι s := by rw [hY,map_mul]
  have hMι : ι (M beta v)=ι (Q beta v)*ι (b beta v) := by simp only [M,map_mul]
  have htι : ι tau*ι tau=ι (radicand v) := by
    simpa only [map_mul] using congrArg (ι : V →+* DiffRing V) htau
  rw [hYι,hMι,←htι]
  ring

/-- Replacing the old first coordinate by the fresh root preserves a full
86 zero; the four nonfirst fields are unchanged. -/
theorem fresh_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (s tau : V)
    (hport : (p 0 : DiffRing V)=ι beta) (hY : v 7=Q beta v*s)
    (htau : tau*tau=radicand v) (hz : InternalZero (P86ResidueGraph.graph p).output v) :
    InternalZero (P86ResidueGraph.graph p).output (fresh v s tau) := by
  have hf := fields_of_zero p v hz
  have ho := other_fields_ignore_root p v (firstP v+tau+s)
  apply (internalZero_iff _ _).mpr
  rw [P86ResidueGraph.output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  change fiveSquares (eval (P86ResidueGraph.graph p).A0 (fresh v s tau))
      (eval (P86ResidueGraph.graph p).A1 (fresh v s tau))
      (eval (P86ResidueGraph.graph p).aux (fresh v s tau)-1)
      (eval (P86ResidueGraph.graph p).gap (fresh v s tau))
      (eval (P86ResidueGraph.graph p).guardResidual (fresh v s tau))=0
  apply (fiveSquares_eq_zero_iff _ _ _ _ _).mpr
  exact ⟨fresh_first p beta v s tau hport hY htau,
    ho.1.trans hf.2.1, by rw [ho.2.1]; exact hf.2.2.1,
    ho.2.2.1.trans hf.2.2.2.1,ho.2.2.2.trans hf.2.2.2.2⟩

end DiophantineConsistency.FreshRoot86Draft

#print axioms DiophantineConsistency.FreshRoot86Draft.fresh_zero
