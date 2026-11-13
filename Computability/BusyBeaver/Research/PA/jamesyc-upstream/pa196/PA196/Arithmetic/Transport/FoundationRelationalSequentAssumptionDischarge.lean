module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentPropositional
public import PA196.Arithmetic.Transport.FoundationRelationalSequentSeparationSupplier
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Discharge uses actual HFS insertion and accepted numerical certificates. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem sequent_discharge_certificate (param s p premise axiomCode : V)
    (hp : IsUFormula language p)
    (hmain : verifyValue premise=sequentCode param (insert (Bootstrapping.neg language p) s)+1)
    (haxiom : verifyValue axiomCode=translate param p+1) :
    ∃ code, verifyValue code=sequentCode param s+1 := by
  obtain ⟨arrow,ha⟩ := member_certificate param (insert p s) p (by simp)
  let positive := (⟨axiomCode,haxiom⟩ : Certificate (translate param p)).mp ⟨arrow,ha⟩
  exact sequent_cut_certificate param s p positive.code premise hp positive.accepted hmain

theorem sequent_discharge_separation (s p f lo z premise : V)
    (hp : IsSemiformula language 1 p)
    (hc : FormulaCovered 0 f lo z (sourceSeparation p))
    (hmain : verifyValue premise=sequentCode (parameters 0 f lo z)
      (insert (Bootstrapping.neg language (sourceSeparation p)) s)+1) :
    ∃ code, verifyValue code=sequentCode (parameters 0 f lo z) s+1 := by
  obtain ⟨axiomCode,ha⟩ := source_separation_certificate p f lo z hp hc
  exact sequent_discharge_certificate (parameters 0 f lo z) s (sourceSeparation p)
    premise axiomCode (sourceSeparation_valid hp).isUFormula hmain ha

#print axioms sequent_discharge_certificate
#print axioms sequent_discharge_separation
end PA196.Arithmetic.Transport.RelationalSource.Numeric

