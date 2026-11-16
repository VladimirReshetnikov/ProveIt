module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalClosedCertificateCoherenceSuccessor
public import M6PA.Calibration.RelationalClosedCertificateReserve
public import PA196.Arithmetic.Certificates.Interface
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.Suppliers.PAInterpretedParameterClosure
public import PA196.Logic.Relational.Suppliers.RelationalOrderIsoSuccessorSupplier
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalClosedCertificate

namespace PA196.Arithmetic.Transport.RelationalClosedCertificate
noncomputable section
open FFL FFL.FirstOrder RelationalSource ND PairGraph ForwardRelational
attribute [local irreducible] lkBudget successorIsoClosed

def successorIsoReserve : Nat :=
  certificateReserve
    (max (7 + lkBudget adjunctionDerivation) (5 + lkBudget (orderIsoSuccessorDerivation 3 2 1 0)))
    (1 + Encodable.encode successorIsoClosed)

theorem successorIsoReserve_code : 1 + Encodable.encode successorIsoClosed ≤ successorIsoReserve :=
  certificateReserve_code
    (max (7 + lkBudget adjunctionDerivation) (5 + lkBudget (orderIsoSuccessorDerivation 3 2 1 0)))
    (1 + Encodable.encode successorIsoClosed)
theorem successorIsoReserve_room : 20 ≤ successorIsoReserve :=
  certificateReserve_room
    (max (7 + lkBudget adjunctionDerivation) (5 + lkBudget (orderIsoSuccessorDerivation 3 2 1 0)))
    (1 + Encodable.encode successorIsoClosed)
theorem successorIsoReserve_adj : 7 + lkBudget adjunctionDerivation ≤ successorIsoReserve :=
  certificateReserve_budget_left
    (7 + lkBudget adjunctionDerivation) (5 + lkBudget (orderIsoSuccessorDerivation 3 2 1 0))
    (1 + Encodable.encode successorIsoClosed)
theorem successorIsoReserve_budget :
    5 + lkBudget (orderIsoSuccessorDerivation 3 2 1 0) ≤ successorIsoReserve :=
  certificateReserve_budget_right
    (7 + lkBudget adjunctionDerivation) (5 + lkBudget (orderIsoSuccessorDerivation 3 2 1 0))
    (1 + Encodable.encode successorIsoClosed)
attribute [local irreducible] successorIsoReserve

def successorIsoNativeProof : PA196.Logic.Derivation
    (PA196.Logic.Relational.Source.code successorIsoClosed (fun _=>0) 1 successorIsoReserve) := by
  unfold successorIsoClosed
  apply PA196.Logic.Relational.ForwardRelational.closeParametersSupplier 4 (orderIsoSuccessorStatement 3 2 1 0)
  exact PA196.Logic.Relational.Source.PairGraph.orderIsoSuccessorSupplier 3 2 1 0 _ (1+4) successorIsoReserve (by decide)
    (closureLabels_bound 4 (fun _=>0) 1 (by intro; decide))
    (lt_of_lt_of_le (by decide : 1+4+6<20) successorIsoReserve_room)
    successorIsoReserve_adj successorIsoReserve_budget
#print axioms successorIsoNativeProof
end
end PA196.Arithmetic.Transport.RelationalClosedCertificate

