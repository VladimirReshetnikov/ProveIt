module
public import M6PA.Theory
public import M6PA.Calibration.ActualRelationalCongruence
@[expose] public section

/-! Finite actual-basis equivalence axioms for the explicit relational
replacement, with the same representative binder on each occurrence.
Global binder changes and transport of PA/set-theory suppliers remain separate. -/
namespace M6.PA.NativeCalculus.ActualBasis

def Context.arrowCompose {Γ : List Nat} {a b c : Nat}
    (p : Context Γ (wim a b)) (q : Context Γ (wim b c)) : Context Γ (wim a c) :=
  .mp q (.mp p (.closed (Dominated.composition a b c)))

def iffReflexive (a : Nat) : Proof (iffCode a a) :=
  (Context.andIntro (.closed (identity a)) (.closed (identity a))).empty

def iffSymmetry (a b : Nat) : Proof (wim (iffCode a b) (iffCode b a)) := by
  let h : Context [iffCode a b] (wa (wim a b) (wim b a)) := .assumption (by simp [iffCode])
  exact (Context.andIntro h.andRight h.andLeft).deduction.empty

def iffTransitivity (a b c : Nat) :
    Proof (wim (iffCode a b) (wim (iffCode b c) (iffCode a c))) := by
  let p : Context [iffCode b c,iffCode a b] (wa (wim a b) (wim b a)) :=
    .assumption (by simp [iffCode])
  let q : Context [iffCode b c,iffCode a b] (wa (wim b c) (wim c b)) :=
    .assumption (by simp [iffCode])
  exact (Context.andIntro (p.andLeft.arrowCompose q.andLeft)
    (q.andRight.arrowCompose p.andRight)).deduction.deduction.empty

def neighborhoodReflexivity (a z : Nat) : Proof (neighborhoodEquality a a z) :=
  (Context.andIntro (.closed (.all z (iffReflexive (wel a z))))
    (.closed (.all z (iffReflexive (wel z a))))).empty

def neighborhoodSymmetry (a b z : Nat) :
    Proof (wim (neighborhoodEquality a b z) (neighborhoodEquality b a z)) := by
  let h : Context [neighborhoodEquality a b z] (neighborhoodEquality a b z) := .assumption (by simp)
  let l := h.andLeft.forallMP z (.closed (.all z (iffSymmetry (wel a z) (wel b z))))
  let r := h.andRight.forallMP z (.closed (.all z (iffSymmetry (wel z a) (wel z b))))
  exact (Context.andIntro l r).deduction.empty

def neighborhoodTransitivity (a b c z : Nat) :
    Proof (wim (neighborhoodEquality a b z)
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

#print axioms neighborhoodReflexivity
#print axioms neighborhoodSymmetry
#print axioms neighborhoodTransitivity
end M6.PA.NativeCalculus.ActualBasis

