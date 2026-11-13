module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateNDShape
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateCertificate
public import PA196.Arithmetic.Transport.FoundationRelationalSequentFiniteDischarge
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalPredicateTemplate

/-! Actual finite HFS discharge for a host template ND proof. Each premise
certificate is explicitly supplied at the chosen covered native environment. -/
namespace PA196.Arithmetic.Transport.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
open RelationalSource.Numeric

theorem template_nd_certificate {Γ : List ND.Form} {q : ND.Form} (d : ND.Proof Γ q)
    {P f : V} (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hb : (proofFreeBound d:V)≤len f)
    (hsupply : ∀p∈Γ,∀g lo z : V,FormulaCovered 0 g lo z (formulaValue p P 0 f) →
      ∃code,verifyValue code=translate (parameters 0 g lo z) (formulaValue p P 0 f)+1) :
    ∃g lo z code : V,FormulaCovered 0 g lo z (formulaValue q P 0 f) ∧
      verifyValue code=translate (parameters 0 g lo z) (formulaValue q P 0 f)+1 := by
  let premises : V := sequentValue (Γ:Multiset ND.Form) P f
  let goal : V := formulaValue q P 0 f
  obtain ⟨w,hw⟩ := template_lk_sound_of_bound (T:=(∅:Theory L)) d hP hf hb
  let bound : V := max w (max premises goal)
  obtain ⟨g,lo,z,hg⟩ := proofEnvironment_exists bound
  have he : AxiomCertificateSupplier (V:=V) (∅:Theory L) := by
    intro p g lo z hp
    change False at hp
    exact hp.elim
  obtain ⟨main,hmain⟩ := derivation_certificate_of_axiom_supplier he w g lo z hw.2
    (hg.descend (le_max_left _ _))
  have hvalid : ∀a,a∈premises→IsFormula L a := by
    intro a ha
    rcases (mem_sequentValue _ _ _ _).mp ha with ⟨p,hp,rfl⟩
    exact formulaValue_isSemiformula p hP ⟨by simp,hf⟩ (nd_premise_covered d hb p hp)
  have hgoal : FormulaCovered 0 g lo z goal :=
    hg.coverage (formulaValue_isSemiformula q hP ⟨by simp,hf⟩ (nd_goal_covered d hb))
      ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨code,hcode⟩ := sequent_finite_discharge (parameters 0 g lo z)
    (sequentValue (ND.negatives Γ+⦃q⦄) P f) premises goal main
    (nd_sequent_shape d hP hf hb)
    (fun a ha => (hvalid a ha).isUFormula)
    (by
      intro a ha
      have hcov := hg.coverage (hvalid a ha)
        ((lt_of_mem ha).le.trans ((le_max_left _ _).trans (le_max_right _ _)))
      rcases (mem_sequentValue _ _ _ _).mp ha with ⟨p,hp,rfl⟩
      exact hsupply p hp g lo z hcov)
    (by simpa only [hw.1] using hmain)
  exact ⟨g,lo,z,code,hgoal,hcode⟩
#print axioms template_nd_certificate
end PA196.Arithmetic.Transport.RelationalPredicateTemplate
