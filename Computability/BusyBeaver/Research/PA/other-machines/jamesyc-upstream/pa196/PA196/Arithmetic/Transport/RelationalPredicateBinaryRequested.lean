module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryComposition
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateNDRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalPredicateBinary

namespace PA196.Arithmetic.Transport.RelationalPredicateBinary
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

/-- Compile an actual model-valued derivation and discharge its one explicit
negative premise. Padding/readback preserves the caller's requested labels. -/
theorem singleton_requested_certificate (a q : SF (V:=V) 0)
    (d : ND.Proof (T:=(∅:Theory L).internalize V) (insert (∼a) ∅) q)
    (g lo z : V) (hc : FormulaCovered 0 g lo z q.val)
    (hs : ∀g lo z : V, FormulaCovered 0 g lo z a.val →
      ∃code,verifyValue code=translate (parameters 0 g lo z) a.val+1) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) q.val+1 := by
  let bound : V := max d.val (max a.val q.val)
  have hg := padded_proofEnvironment bound g lo z hc.1.1
  have he : AxiomCertificateSupplier (V:=V) (∅:Theory L) := by
    intro p g lo z hp
    change False at hp
    exact hp.elim
  obtain ⟨main,hm⟩ := derivation_certificate_of_axiom_supplier he d.val
    (padEnvironment g bound) lo (z+lo+bound) d.derivationOf.2 (hg.descend (le_max_left _ _))
  have ha : FormulaCovered 0 (padEnvironment g bound) lo (z+lo+bound) a.val :=
    hg.coverage a.isSemiformula_zero ((le_max_left _ _).trans (le_max_right _ _))
  obtain ⟨code,hcode⟩ := sequent_finite_discharge
    (parameters 0 (padEnvironment g bound) lo (z+lo+bound))
    ((insert q (insert (∼a) (∅ : ND.Seq (V:=V)))).val) ({a.val}:V) q.val main
    (by intro r hr; simpa using hr)
    (by
      intro r hr
      have heq : r=a.val := by simpa using hr
      rw [heq]
      exact a.isUFormula)
    (by
      intro r hr
      have heq : r=a.val := by simpa using hr
      rw [heq]
      exact hs _ _ _ ha)
    (by simpa [d.derivationOf.1] using hm)
  exact padded_proof_certificate_readback q.val g lo z bound code hc hcode

#print axioms singleton_requested_certificate
end PA196.Arithmetic.Transport.RelationalPredicateBinary

