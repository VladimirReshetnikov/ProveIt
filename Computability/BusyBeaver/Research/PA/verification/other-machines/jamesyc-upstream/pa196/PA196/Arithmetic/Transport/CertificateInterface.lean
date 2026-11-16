module
public import PA196.Arithmetic.Transport.FoundationRelationalCodeAtoms
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section

/-! Exact expression bridges for the new PA196 interpretation. The finite
certificate recipes are the newly proved reverse-membership/neighborhood
recipes, including the mirrored existential witness. -/
open M6.PA PA196.Arithmetic
namespace PA196.Arithmetic.Transport.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Certificates Certificates.Dominated Certificates.Logic HeadGraphs Checker
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem neighborhood_expr_eq (a b z : V) :
    ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0 =
      neighborhoodEquality a b z := by
  simp [RelationalSource.Numeric.neighborhoodExpr,neighborhoodEquality,neighborhood,iffCode,
    ActualArithmeticGraph.eval,wa,wn,wim,wal,wel,conj,neg,im,al,mem,
    implicationValue,universalValue,implicationExpr,universalExpr]

noncomputable def neighborhoodReflexivity (a z : V) :
    Certificate (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a a z 0) := by
  rw [neighborhood_expr_eq]
  exact neighborhoodReflexivityCore a z

noncomputable def neighborhoodSymmetry (a b z : V) :
    Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
      (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr b a z 0)) := by
  rw [neighborhood_expr_eq,neighborhood_expr_eq]
  exact neighborhoodSymmetryCore a b z

noncomputable def neighborhoodTransitivity (a b c z : V) :
    Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
      (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr b c z 0)
        (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a c z 0))) := by
  rw [neighborhood_expr_eq,neighborhood_expr_eq,neighborhood_expr_eq]
  exact neighborhoodTransitivityCore a b c z

noncomputable def neighborhoodEqualityVacuity (a b z c : V)
    (ha : c ≠ a) (hb : c ≠ b) (hz : c ≠ z) :
    Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
      (wal c (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0))) := by
  simp only [neighborhood_expr_eq]
  exact Certificates.Logic.neighborhoodEqualityVacuity a b z c ha hb hz

theorem neighborhood_vacuity_certificate (a b z c : V)
    (ha : c ≠ a) (hb : c ≠ b) (hz : c ≠ z) :
    ∃ code, verifyValue code =
      wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
        (wal c (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0))+1 :=
  ⟨(neighborhoodEqualityVacuity a b z c ha hb hz).code,
    (neighborhoodEqualityVacuity a b z c ha hb hz).accepted⟩

noncomputable def neighborhoodRightCongruence (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
      (wim (wel a c) (wel b c))) := by
  rw [neighborhood_expr_eq]
  exact neighborhoodRightCongruenceCore a b z c hza hzb hzc

noncomputable def neighborhoodLeftCongruence (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
      (wim (wel c a) (wel c b))) := by
  rw [neighborhood_expr_eq]
  exact neighborhoodLeftCongruenceCore a b z c hza hzb hzc

noncomputable def neighborhoodBinderChange (a b z z' : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hna : z' ≠ a) (hnb : z' ≠ b) :
    Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
      (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z' 0)) := by
  rw [neighborhood_expr_eq,neighborhood_expr_eq]
  exact neighborhoodBinderChangeCore a b z z' hza hzb hna hnb

noncomputable def primitiveToNeighborhood (a b z : V) (hza : z ≠ a) (hzb : z ≠ b) :
    Certificate (wim (weq a b)
      (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)) := by
  rw [neighborhood_expr_eq]
  exact Certificates.Logic.primitiveToNeighborhood a b z hza hzb

noncomputable def neighborhoodWitness (x c z : V) (hzx : z ≠ x) (hzc : z ≠ c) :
    Certificate (wex x (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr x c z 0)) := by
  rw [neighborhood_expr_eq]
  exact Certificates.Logic.neighborhoodWitness x c z hzx hzc

noncomputable def universalSpecializeNeighborhood (x y z a b : V)
    (hzx : z ≠ x) (hzy : z ≠ y)
    (hr : Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr x y z 0)
      (wim a b))) (hv : Certificate (wim b (wal x b))) :
    Certificate (wim (wal x a) b) := by
  rw [neighborhood_expr_eq] at hr
  exact universalSpecializeNeighborhoodCore x y z a b hzx hzy hr hv

noncomputable def universalAlphaNeighborhood (x y z a b : V)
    (hzx : z ≠ x) (hzy : z ≠ y)
    (hf : Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr x y z 0)
      (wim a b)))
    (hb : Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr x y z 0)
      (wim b a)))
    (hbx : Certificate (wim b (wal x b))) (hay : Certificate (wim a (wal y a))) :
    Certificate (wim (wal x a) (wal y b)) × Certificate (wim (wal y b) (wal x a)) := by
  rw [neighborhood_expr_eq] at hf hb
  exact universalAlphaNeighborhoodCore x y z a b hzx hzy hf hb hbx hay

#print axioms neighborhood_expr_eq
#print axioms neighborhoodWitness
#print axioms universalAlphaNeighborhood
end PA196.Arithmetic.Transport.ActualCertificateEquivalence
