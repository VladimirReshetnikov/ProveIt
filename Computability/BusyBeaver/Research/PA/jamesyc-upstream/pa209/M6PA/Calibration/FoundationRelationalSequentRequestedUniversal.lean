module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentClosedUniversal
public import M6PA.Calibration.FoundationRelationalSequentPaddingReadback
@[expose] public section

/-! Universal introduction at requested native parameters. A supplier of closed
certificates for the opened source formula is used at an explicitly padded
child environment. The opened code has its own budget, unrelated to the parent
code bound. No generalization under ambient assumptions occurs. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem requested_universal_certificate (p f lo z : V)
    (hp : IsSemiformula language 1 p)
    (hc : FormulaCovered 0 f lo z (qqAll p))
    (hchild : ∀ g l r : V, FormulaCovered 0 g l r (Bootstrapping.free language p) →
      ∃ code, verifyValue code=translate (parameters 0 g l r) (Bootstrapping.free language p)+1) :
    ∃ code, verifyValue code=translate (parameters 0 f lo z) (qqAll p)+1 := by
  let d := Bootstrapping.free language p+1
  let padded := padEnvironment f d
  let reserve := z+lo+d
  have he : ProofEnvironment d padded lo reserve :=
    padded_proofEnvironment d f lo z hc.1.1
  have childCoverage : FormulaCovered 0 (lo∷padded) (lo+1) reserve
      (Bootstrapping.free language p) :=
    (he.all_child (lt_add_one (Bootstrapping.free language p))).coverage hp.free le_rfl
  obtain ⟨child,haccepted⟩ := hchild (lo∷padded) (lo+1) reserve childCoverage
  obtain ⟨code,hcode⟩ := closed_universal_certificate p padded lo reserve child hp haccepted
  exact padded_proof_certificate_readback (qqAll p) f lo z d code hc hcode

attribute [local irreducible] coverageGraph parametersGraph translateGraph verifyGraph freeGraph
noncomputable def requestedUniversalSentence : ArithmeticSentence :=
  “∀ p f lo z opened all, !((isSemiformula language).sigma) 1 p →
    !(freeGraph language) opened p → !qqAllDef all p → !coverageGraph 0 f lo z all →
    (∀ g l r, !coverageGraph 0 g l r opened →
      ∃ param a code, !parametersGraph param 0 g l r ∧ !translateGraph a param opened ∧
        !verifyGraph (a+1) code) →
    ∃ param a code, !parametersGraph param 0 f lo z ∧ !translateGraph a param all ∧
      !verifyGraph (a+1) code”

theorem pa_proves_requested_universal : theory ⊢ requestedUniversalSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [requestedUniversalSentence,models_iff,coverage_graph,parameters_graph,
    translate_graph,verify_graph,Matrix.comp_vecCons'',eq_comm]
  intro p f lo z opened all hp hopen hall hc hchild
  subst opened
  subst all
  exact requested_universal_certificate p f lo z hp hc hchild

#print axioms requested_universal_certificate
#print axioms pa_proves_requested_universal
end M6.PA.RelationalSource.Numeric

