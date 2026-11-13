module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueDiagonalSupply
public import M6PA.Calibration.NumericPAeqValueCoherence
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem diagonal_input_certificate {s b f t:V} (h:ValueEnvironment s b f t) (native lo z:V)
    (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (imp language (inputDomain s b f) (coherenceInput s b b f f))):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (inputDomain s b f) (coherenceInput s b b f f))+1 := by
  have hA := inputDomain_valid h
  have hB := NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.1
  have hF := NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.2.1
  have hIB := NumericPAeqValueIsoGuard.guard_vector_isSemiformula h.1 h.1
  have hIF := NumericPAeqValueIsoGuard.guard_vector_isSemiformula h.2.1 h.2.1
  rw [coherenceInput,min_self] at hc ⊢
  apply source_implication_pair _ _ _ native lo z hA hA (IsSemiformula.and.mpr ⟨hA,IsSemiformula.and.mpr ⟨hIB,hIF⟩⟩) hc
  · intro native lo z _; exact source_identity_certificate (RelationalSource.Numeric.parameters 0 native lo z) _ hA.isUFormula
  · intro native lo z hc
    apply source_implication_pair _ _ _ native lo z hA hA (IsSemiformula.and.mpr ⟨hIB,hIF⟩) hc
    · intro native lo z _; exact source_identity_certificate (RelationalSource.Numeric.parameters 0 native lo z) _ hA.isUFormula
    · intro native lo z hc
      apply source_implication_pair _ _ _ native lo z hA hIB hIF hc
      · intro native lo z hc
        apply source_implication_compose _ (NumericPAeqValueDomainGuard.guard b s) _ native lo z hA hB hIB hc
        · intro native lo z _; exact source_conjunction_projection (RelationalSource.Numeric.parameters 0 native lo z) _ _ hB.isUFormula hF.isUFormula true
        · intro native lo z hc; exact diagonal_guard_certificate b s native lo z (fun i hi => h.1.nth hi) hc
      · intro native lo z hc
        apply source_implication_compose _ (NumericPAeqValueDomainGuard.guard f (len f)) _ native lo z hA hF hIF hc
        · intro native lo z _; exact source_conjunction_projection (RelationalSource.Numeric.parameters 0 native lo z) _ _ hB.isUFormula hF.isUFormula false
        · intro native lo z hc; exact diagonal_guard_certificate f (len f) native lo z (fun i hi => h.2.1.nth hi) hc
#print axioms diagonal_input_certificate
end M6.PA.NumericPAeqValueCoherence
