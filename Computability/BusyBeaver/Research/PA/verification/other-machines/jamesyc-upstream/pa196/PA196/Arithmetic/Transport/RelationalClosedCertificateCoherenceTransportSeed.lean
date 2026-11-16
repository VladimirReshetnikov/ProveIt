module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalClosedCertificateCoherenceTransport
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
attribute [local irreducible] lkBudget isoTransportDerivation isoTransportClosed

def isoTransportReserve : Nat :=
  certificateReserve (5 + lkBudget isoTransportDerivation) (1 + Encodable.encode isoTransportClosed)

theorem isoTransportReserve_code : 1 + Encodable.encode isoTransportClosed ≤ isoTransportReserve :=
  certificateReserve_code (5 + lkBudget isoTransportDerivation) (1 + Encodable.encode isoTransportClosed)
theorem isoTransportReserve_room : 20 ≤ isoTransportReserve :=
  certificateReserve_room (5 + lkBudget isoTransportDerivation) (1 + Encodable.encode isoTransportClosed)
theorem isoTransportReserve_budget : 5 + lkBudget isoTransportDerivation ≤ isoTransportReserve :=
  certificateReserve_budget (5 + lkBudget isoTransportDerivation) (1 + Encodable.encode isoTransportClosed)
attribute [local irreducible] isoTransportReserve

def isoTransportNativeProof : PA196.Logic.Derivation
    (PA196.Logic.Relational.Source.code isoTransportClosed (fun _=>0) 1 isoTransportReserve) := by
  unfold isoTransportClosed
  apply PA196.Logic.Relational.ForwardRelational.closeParametersSupplier 4 isoTransportOpen
  apply PA196.Logic.Relational.Source.compileContext zeroIsoAxioms isoTransportOpen isoTransportDerivation _ (1+4) isoTransportReserve (by decide)
    (closureLabels_bound 4 (fun _=>0) 1 (by intro; decide)) isoTransportReserve_budget
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
  exact PA196.Logic.Relational.Source.congruenceSupplier _ _ _ (lt_of_lt_of_le (by decide : 1+4+3<20) isoTransportReserve_room)
#print axioms isoTransportNativeProof
end
end PA196.Arithmetic.Transport.RelationalClosedCertificate
