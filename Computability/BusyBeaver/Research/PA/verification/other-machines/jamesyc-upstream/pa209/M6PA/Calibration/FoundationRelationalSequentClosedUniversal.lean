module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentAllRule
@[expose] public section

/-! Universal introduction from an actual closed accepted certificate. Any
antecedent must already be part of the source formula, not an ambient context. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem closed_universal_certificate (p f lo z child : V)
    (hp : IsSemiformula language 1 p)
    (hchild : verifyValue child=translate (parameters 0 (lo∷f) (lo+1) z)
      (Bootstrapping.free language p)+1) :
    ∃ code, verifyValue code=translate (parameters 0 f lo z) (qqAll p)+1 := by
  rw [translate_free_advance p f lo z hp] at hchild
  let out := (⟨child,hchild⟩ : Certificate
    (translate (advance (parameters 0 f lo z)) p)).all lo
  refine ⟨out.code,?_⟩
  simpa only [translate_all _ _ hp.isUFormula,parameters_allocator,wal,universalValue]
    using out.accepted

attribute [local irreducible] parametersGraph translateGraph verifyGraph freeGraph
noncomputable def closedUniversalSentence : ArithmeticSentence :=
  “∀ p f lo z child, !((isSemiformula language).sigma) 1 p →
    (∃ opened extended param a, !(freeGraph language) opened p ∧ !adjoinDef extended lo f ∧
      !parametersGraph param 0 extended (lo+1) z ∧ !translateGraph a param opened ∧
      !verifyGraph (a+1) child) →
    ∃ all param a code, !qqAllDef all p ∧ !parametersGraph param 0 f lo z ∧
      !translateGraph a param all ∧ !verifyGraph (a+1) code”

theorem pa_proves_closed_universal : theory ⊢ closedUniversalSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [closedUniversalSentence,models_iff,parameters_graph,translate_graph,
    verify_graph,Matrix.comp_vecCons'',eq_comm]
  intro p f lo z child hp hchild
  exact closed_universal_certificate p f lo z child hp hchild

#print axioms closed_universal_certificate
#print axioms pa_proves_closed_universal
end M6.PA.RelationalSource.Numeric

