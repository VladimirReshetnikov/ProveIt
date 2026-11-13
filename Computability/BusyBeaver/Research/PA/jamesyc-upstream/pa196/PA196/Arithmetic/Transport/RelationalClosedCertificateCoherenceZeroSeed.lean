module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalClosedCertificateCoherenceZero
public import M6PA.Calibration.RelationalClosedCertificateReserve
public import PA196.Arithmetic.Certificates.Interface
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceEquality
public import PA196.Logic.Relational.Suppliers.PAInterpretedParameterClosure
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalClosedCertificate

namespace PA196.Arithmetic.Transport.RelationalClosedCertificate
noncomputable section
open FFL FFL.FirstOrder RelationalSource ND PairGraph ForwardRelational
attribute [local irreducible] lkBudget zeroIsoDerivation zeroIsoClosed

def zeroIsoReserve : Nat :=
  certificateReserve (3 + lkBudget zeroIsoDerivation) (1 + Encodable.encode zeroIsoClosed)

theorem zeroIsoReserve_code : 1 + Encodable.encode zeroIsoClosed ≤ zeroIsoReserve :=
  certificateReserve_code (3 + lkBudget zeroIsoDerivation) (1 + Encodable.encode zeroIsoClosed)
theorem zeroIsoReserve_room : 20 ≤ zeroIsoReserve :=
  certificateReserve_room (3 + lkBudget zeroIsoDerivation) (1 + Encodable.encode zeroIsoClosed)
theorem zeroIsoReserve_budget : 3 + lkBudget zeroIsoDerivation ≤ zeroIsoReserve :=
  certificateReserve_budget (3 + lkBudget zeroIsoDerivation) (1 + Encodable.encode zeroIsoClosed)
attribute [local irreducible] zeroIsoReserve

def zeroIsoNativeProof : PA196.Logic.Derivation
    (PA196.Logic.Relational.Source.code zeroIsoClosed (fun _=>0) 1 zeroIsoReserve) := by
  unfold zeroIsoClosed
  apply PA196.Logic.Relational.ForwardRelational.closeParametersSupplier 2 zeroIsoOpen
  apply PA196.Logic.Relational.Source.compileContext zeroIsoAxioms zeroIsoOpen zeroIsoDerivation _ (1+2) zeroIsoReserve (by decide)
    (closureLabels_bound 2 (fun _=>0) 1 (by intro; decide)) zeroIsoReserve_budget
  intro p hp
  classical
  by_cases h0 : p=reflexivityFormula
  · subst p; exact PA196.Logic.Relational.Source.reflexivitySupplier _ _ _
  by_cases h1 : p=symmetryFormula
  · subst p; exact PA196.Logic.Relational.Source.symmetrySupplier _ _ _
  by_cases h2 : p=transitivityFormula
  · subst p; exact PA196.Logic.Relational.Source.transitivitySupplier _ _ _
  have h3 : p=congruenceFormula := by simpa [zeroIsoAxioms,h0,h1,h2] using hp
  subst p
  exact PA196.Logic.Relational.Source.congruenceSupplier _ _ _ (lt_of_lt_of_le (by decide : 1+2+3<20) zeroIsoReserve_room)
#print axioms zeroIsoNativeProof
end
end PA196.Arithmetic.Transport.RelationalClosedCertificate

