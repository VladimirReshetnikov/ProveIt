module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateVacuityNeighborhood
@[expose] public section

/-! Finite equivalence recipes for the exact neighborhood equality. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint ActualHeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable abbrev iffCode (a b : V) : V := wa (wim a b) (wim b a)
noncomputable abbrev neighborhoodEquality (a b z : V) : V :=
  wa (wal z (iffCode (wel a z) (wel b z)))
    (wal z (iffCode (wel z a) (wel z b)))

noncomputable def Context.forallMP {Γ : List V} (x : V) {a b : V}
    (p : Context Γ (wal x a)) (q : Context Γ (wal x (wim a b))) : Context Γ (wal x b) :=
  .mp p (.mp q (.closed (r2 x a b)))
noncomputable def Context.arrowCompose {Γ : List V} {a b c : V}
    (p : Context Γ (wim a b)) (q : Context Γ (wim b c)) : Context Γ (wim a c) :=
  .mp q (.mp p (.closed (Dominated.composition a b c)))

noncomputable def iffReflexive (a : V) : Certificate (iffCode a a) :=
  (Context.andIntro (.closed (identity a)) (.closed (identity a))).empty

noncomputable def iffSymmetry (a b : V) : Certificate (wim (iffCode a b) (iffCode b a)) := by
  let h : Context [iffCode a b] (wa (wim a b) (wim b a)) := .assumption (by simp [iffCode])
  exact (Context.andIntro h.andRight h.andLeft).deduction.empty

noncomputable def iffTransitivity (a b c : V) :
    Certificate (wim (iffCode a b) (wim (iffCode b c) (iffCode a c))) := by
  let p : Context [iffCode b c,iffCode a b] (wa (wim a b) (wim b a)) :=
    .assumption (by simp [iffCode])
  let q : Context [iffCode b c,iffCode a b] (wa (wim b c) (wim c b)) :=
    .assumption (by simp [iffCode])
  exact (Context.andIntro (p.andLeft.arrowCompose q.andLeft)
    (q.andRight.arrowCompose p.andRight)).deduction.deduction.empty

noncomputable def neighborhoodReflexivityCore (a z : V) : Certificate (neighborhoodEquality a a z) :=
  (Context.andIntro (.closed (.all z (iffReflexive (wel a z))))
    (.closed (.all z (iffReflexive (wel z a))))).empty

noncomputable def neighborhoodSymmetryCore (a b z : V) :
    Certificate (wim (neighborhoodEquality a b z) (neighborhoodEquality b a z)) := by
  let h : Context [neighborhoodEquality a b z] (neighborhoodEquality a b z) := .assumption (by simp)
  let l := h.andLeft.forallMP z (.closed (.all z (iffSymmetry (wel a z) (wel b z))))
  let r := h.andRight.forallMP z (.closed (.all z (iffSymmetry (wel z a) (wel z b))))
  exact (Context.andIntro l r).deduction.empty

noncomputable def neighborhoodTransitivityCore (a b c z : V) :
    Certificate (wim (neighborhoodEquality a b z)
      (wim (neighborhoodEquality b c z) (neighborhoodEquality a c z))) := by
  let p : Context [neighborhoodEquality b c z,neighborhoodEquality a b z]
      (neighborhoodEquality a b z) := .assumption (by simp)
  let q : Context [neighborhoodEquality b c z,neighborhoodEquality a b z]
      (neighborhoodEquality b c z) := .assumption (by simp)
  let l := q.andLeft.forallMP z (p.andLeft.forallMP z
    (.closed (.all z (iffTransitivity (wel a z) (wel b z) (wel c z)))))
  let r := q.andRight.forallMP z (p.andRight.forallMP z
    (.closed (.all z (iffTransitivity (wel z a) (wel z b) (wel z c)))))
  exact (Context.andIntro l r).deduction.deduction.empty


theorem neighborhood_expr_eq (a b z : V) :
    ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0 =
      neighborhoodEquality a b z := by
  simp [RelationalSource.Numeric.neighborhoodExpr,neighborhoodEquality,iffCode,
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

#print axioms Context.forallMP
#print axioms Context.arrowCompose
#print axioms iffReflexive
#print axioms iffSymmetry
#print axioms iffTransitivity
#print axioms neighborhoodReflexivityCore
#print axioms neighborhoodSymmetryCore
#print axioms neighborhoodTransitivityCore
#print axioms neighborhood_expr_eq
#print axioms neighborhoodReflexivity
#print axioms neighborhoodSymmetry
#print axioms neighborhoodTransitivity
end M6.PA.ActualCertificateEquivalence

