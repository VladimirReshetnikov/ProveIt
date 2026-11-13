module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSubstitutionVariableTransport
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
attribute [local irreducible] lkBudget isoRightTransportDerivation isoRightTransportClosed

def isoRightTransportReserve : Nat :=
  certificateReserve (4 + lkBudget isoRightTransportDerivation) (1 + Encodable.encode isoRightTransportClosed)

theorem isoRightTransportReserve_code : 1 + Encodable.encode isoRightTransportClosed ≤ isoRightTransportReserve :=
  certificateReserve_code (4 + lkBudget isoRightTransportDerivation) (1 + Encodable.encode isoRightTransportClosed)
theorem isoRightTransportReserve_room : 20 ≤ isoRightTransportReserve :=
  certificateReserve_room (4 + lkBudget isoRightTransportDerivation) (1 + Encodable.encode isoRightTransportClosed)
theorem isoRightTransportReserve_budget : 4 + lkBudget isoRightTransportDerivation ≤ isoRightTransportReserve :=
  certificateReserve_budget (4 + lkBudget isoRightTransportDerivation) (1 + Encodable.encode isoRightTransportClosed)
attribute [local irreducible] isoRightTransportReserve

def isoRightTransportNativeProof : PA196.Logic.Derivation
    (PA196.Logic.Relational.Source.code isoRightTransportClosed (fun _=>0) 1 isoRightTransportReserve) := by
  unfold isoRightTransportClosed
  apply PA196.Logic.Relational.ForwardRelational.closeParametersSupplier 3 isoRightTransportOpen
  apply PA196.Logic.Relational.Source.compileContext zeroIsoAxioms isoRightTransportOpen isoRightTransportDerivation _ (1+3) isoRightTransportReserve (by decide)
    (closureLabels_bound 3 (fun _=>0) 1 (by intro; decide)) isoRightTransportReserve_budget
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
  exact PA196.Logic.Relational.Source.congruenceSupplier _ _ _ (lt_of_lt_of_le (by decide : 1+3+3<20) isoRightTransportReserve_room)
#print axioms isoRightTransportNativeProof
end
end PA196.Arithmetic.Transport.RelationalClosedCertificate
