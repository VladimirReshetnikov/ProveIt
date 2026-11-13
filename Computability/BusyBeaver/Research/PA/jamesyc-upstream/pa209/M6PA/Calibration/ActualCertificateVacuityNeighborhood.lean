module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateVacuityLogic
public import M6PA.Calibration.FoundationRelationalCodeAtoms
@[expose] public section

/-! Numeric vacuity for the exact two-neighborhood equality translation.
This supplies finite certificates over arbitrary PA models, not a source
formula induction or an allocator-relocation theorem. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint ActualHeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def iffVacuity (x a b : V)
    (ha : Certificate (wim a (wal x a))) (hb : Certificate (wim b (wal x b))) :
    Certificate (wim (wa (wim a b) (wim b a))
      (wal x (wa (wim a b) (wim b a)))) :=
  conjunctionVacuity x _ _ (implicationVacuity x a b ha hb)
    (implicationVacuity x b a hb ha)

noncomputable def neighborhoodEqualityVacuity (a b z c : V)
    (ha : c ≠ a) (hb : c ≠ b) (hz : c ≠ z) :
    Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
      (wal c (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0))) := by
  let out := conjunctionVacuity c _ _
    (universalVacuity c z _ (iffVacuity c _ _
      (membershipVacuity a z c ha hz) (membershipVacuity b z c hb hz)))
    (universalVacuity c z _ (iffVacuity c _ _
      (membershipVacuity z a c hz ha) (membershipVacuity z b c hz hb)))
  simpa [RelationalSource.Numeric.neighborhoodExpr,ActualArithmeticGraph.eval,
    wa,wn,wim,wal,wel,conj,neg,im,al,mem,implicationValue,universalValue,
    implicationExpr,universalExpr] using out

/-- Readily consumed existential verifier equation; no proof object is extracted
from a proposition to define its certificate. -/
theorem neighborhood_vacuity_certificate (a b z c : V)
    (ha : c ≠ a) (hb : c ≠ b) (hz : c ≠ z) :
    ∃ code, verifyValue code =
      wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
        (wal c (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0))+1 :=
  ⟨(neighborhoodEqualityVacuity a b z c ha hb hz).code,
    (neighborhoodEqualityVacuity a b z c ha hb hz).accepted⟩

#print axioms iffVacuity
#print axioms neighborhoodEqualityVacuity
#print axioms neighborhood_vacuity_certificate
end M6.PA.ActualCertificateEquivalence

