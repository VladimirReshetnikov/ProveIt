module
public import M6PA.Theory
public import M6PA.Calibration.ActualRelationalEquivalence
@[expose] public section

/-! Four closed numeric equality suppliers for the relational replacement of
Compact238.equality_base (pinned upstream 84049b5e, arith/Compact238.v).
Labels 0,1,2,3 represent the displayed de Bruijn indices; label4 is reserved
inside each equality replacement. This does not yet prove a structural
source-syntax translation theorem, pointed suppliers, or PA induction. -/
namespace M6.PA.NativeCalculus.ActualBasis

def neighborhoodBothCongruence (a b c d z : Nat)
    (ha : z ≠ a) (hb : z ≠ b) (hc : z ≠ c) (hd : z ≠ d) :
    Proof (wim (neighborhoodEquality a b z)
      (wim (neighborhoodEquality c d z) (wim (wel c a) (wel d b)))) := by
  let he : Context [wel c a,neighborhoodEquality c d z,neighborhoodEquality a b z]
      (neighborhoodEquality a b z) := .assumption (by simp)
  let hf : Context [wel c a,neighborhoodEquality c d z,neighborhoodEquality a b z]
      (neighborhoodEquality c d z) := .assumption (by simp)
  let hm : Context [wel c a,neighborhoodEquality c d z,neighborhoodEquality a b z]
      (wel c a) := .assumption (by simp)
  let hmid := Context.mp hm (.mp he (.closed (neighborhoodLeftCongruence a b z c ha hb hc)))
  exact (Context.mp hmid (.mp hf (.closed
    (neighborhoodRightCongruence c d z b hc hd hb)))).deduction.deduction.deduction.empty

def compactReflexivityCode := wal 0 (neighborhoodEquality 0 0 4)
def compactSymmetryCode := wal 1 (wal 0
  (wim (neighborhoodEquality 1 0 4) (neighborhoodEquality 0 1 4)))
def compactTransitivityCode := wal 2 (wal 1 (wal 0
  (wim (neighborhoodEquality 2 1 4)
    (wim (neighborhoodEquality 1 0 4) (neighborhoodEquality 2 0 4)))))
def compactCongruenceCode := wal 3 (wal 2 (wal 1 (wal 0
  (wim (neighborhoodEquality 3 1 4)
    (wim (neighborhoodEquality 2 0 4) (wim (wel 2 3) (wel 0 1)))))))

def compactReflexivity : Proof compactReflexivityCode :=
  .all 0 (neighborhoodReflexivity 0 4)
def compactSymmetry : Proof compactSymmetryCode :=
  .all 1 (.all 0 (neighborhoodSymmetry 1 0 4))
def compactTransitivity : Proof compactTransitivityCode :=
  .all 2 (.all 1 (.all 0 (neighborhoodTransitivity 2 1 0 4)))
def compactCongruence : Proof compactCongruenceCode :=
  .all 3 (.all 2 (.all 1 (.all 0
    (neighborhoodBothCongruence 3 1 2 0 4 (by decide) (by decide) (by decide) (by decide)))))

#print axioms compactReflexivity
#print axioms compactSymmetry
#print axioms compactTransitivity
#print axioms compactCongruence
end M6.PA.NativeCalculus.ActualBasis

