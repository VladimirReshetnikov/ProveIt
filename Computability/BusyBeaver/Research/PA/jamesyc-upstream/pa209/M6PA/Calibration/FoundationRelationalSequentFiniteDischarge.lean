module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentAssumptionDischarge
@[expose] public section

/-! Re-derived finite HFS premise discharge. The premise set may have arbitrary
model length. Its members are valid source codes with explicit accepted native
certificates; no closed image theory or host-list enumeration is assumed. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem sequent_finite_discharge (param s premises goal main : V)
    (hshape : ∀ r, r∈s → r=goal ∨ ∃ a, a∈premises ∧ r=Bootstrapping.neg language a)
    (hvalid : ∀ a, a∈premises → IsUFormula language a)
    (hsupply : ∀ a, a∈premises → ∃ code, verifyValue code=translate param a+1)
    (hmain : verifyValue main=sequentCode param s+1) :
    ∃ code, verifyValue code=translate param goal+1 := by
  obtain ⟨fold,hfold⟩ := sequent_eliminate_certificate param s (translate param goal) (by
    intro r hr
    rcases hshape r hr with he | ⟨a,ha,he⟩
    · subst r
      exact ⟨(ActualCertificateEquivalence.identity (translate param goal)).code,
        (ActualCertificateEquivalence.identity (translate param goal)).accepted⟩
    · subst r
      obtain ⟨positive,hpositive⟩ := hsupply a ha
      obtain ⟨forward,backward,hforward,hbackward⟩ := nnf_certificates a param (hvalid a ha)
      let negative : Context [wn (translate param a)] (wn (translate param a)) :=
        .assumption (by simp)
      let contradiction : Context [wn (translate param a)] 1 :=
        .mp (.closed (⟨positive,hpositive⟩ : Certificate (translate param a))) negative
      let toGoal : Certificate (wim (wn (translate param a)) (translate param goal)) :=
        (contradiction.explosion (translate param goal)).deduction.empty
      let out := implicationCompose (⟨forward,hforward⟩ : Certificate
        (wim (translate param (Bootstrapping.neg language a)) (wn (translate param a)))) toGoal
      exact ⟨out.code,out.accepted⟩)
  let out := (⟨main,hmain⟩ : Certificate (sequentCode param s)).mp ⟨fold,hfold⟩
  exact ⟨out.code,out.accepted⟩

attribute [local irreducible] translateGraph sequentGraph verifyGraph
noncomputable def finiteDischargeSentence : ArithmeticSentence :=
  “∀ param s premises goal main,
    (∀ r, r∈s → r=goal ∨ ∃ a, a∈premises ∧ !((negGraph language)) r a) →
    (∀ a, a∈premises → !((isUFormula language).sigma) a) →
    (∀ a, a∈premises → ∃ out code, !translateGraph out param a ∧ !verifyGraph (out+1) code) →
    (∃ out, !sequentGraph out param s ∧ !verifyGraph (out+1) main) →
    ∃ out code, !translateGraph out param goal ∧ !verifyGraph (out+1) code”

theorem pa_proves_finite_discharge : theory ⊢ finiteDischargeSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [finiteDischargeSentence,models_iff,translate_graph,sequent_graph,
    verify_graph,Matrix.comp_vecCons'',eq_comm]
  intro param s premises goal main hshape hvalid hsupply hmain
  apply sequent_finite_discharge param s premises goal main ?_ hvalid hsupply hmain
  intro r hr
  exact (hshape r hr).imp Eq.symm id

#print axioms sequent_finite_discharge
#print axioms pa_proves_finite_discharge
end M6.PA.RelationalSource.Numeric

