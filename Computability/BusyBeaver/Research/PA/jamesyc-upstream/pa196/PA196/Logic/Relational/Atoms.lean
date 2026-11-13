module
public import PA196.Logic.Relational.Encoding
public import M6.Logic.NativeRenaming
@[expose] public section

namespace PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)

def _root_.PA196.Logic.Context.relSymm {Γ : List Nat} {a b z : Nat}
    (p : Context Γ (neighborhoodEquality a b z)) : Context Γ (neighborhoodEquality b a z) :=
  .mp p (.closed (neighborhoodSymmetry a b z))

def _root_.PA196.Logic.Context.relTrans {Γ : List Nat} {a b c z : Nat}
    (p : Context Γ (neighborhoodEquality a b z))
    (q : Context Γ (neighborhoodEquality b c z)) : Context Γ (neighborhoodEquality a c z) :=
  .mp q (.mp p (.closed (neighborhoodTransitivity a b c z)))

def _root_.PA196.Logic.Context.relCongruence {Γ : List Nat} {a b c d z : Nat}
    (p : Context Γ (neighborhoodEquality a c z))
    (q : Context Γ (neighborhoodEquality b d z))
    (h : Context Γ (neighborhoodEquality a b z)) : Context Γ (neighborhoodEquality c d z) :=
  (p.relSymm.relTrans h).relTrans q

def _root_.PA196.Logic.Context.memCongruence {Γ : List Nat} {a b c d z : Nat}
    (ha : z ≠ a) (hb : z ≠ b) (hc : z ≠ c) (hd : z ≠ d)
    (p : Context Γ (neighborhoodEquality a c z))
    (q : Context Γ (neighborhoodEquality b d z))
    (h : Context Γ (wel a b)) : Context Γ (wel c d) :=
  .mp h (.mp p (.mp q (.closed (neighborhoodBothCongruence b d a c z hb hd ha hc))))

def _root_.PA196.Logic.Context.renameRel {Γ : List Nat} (x y a z : Nat)
    (h : Context Γ (neighborhoodEquality x y z)) :
    Context Γ (neighborhoodEquality a (renameLabel x y a) z) := by
  by_cases ha : a = x
  · simpa [renameLabel,ha] using h
  · simpa [renameLabel,ha] using (Context.closed (Γ := Γ) (neighborhoodReflexivity a z))

theorem reserved_rename (z x y a : Nat) (ha : z ≠ a) (hy : z ≠ y) :
    z ≠ renameLabel x y a := by
  unfold renameLabel
  split <;> assumption

def relationalRenameMembership (z x y a b : Nat)
    (hza : z ≠ a) (hzb : z ≠ b) (hzy : z ≠ y) :
    Proof (wim (neighborhoodEquality x y z)
      (wim (wel a b) (wel (renameLabel x y a) (renameLabel x y b)))) ×
    Proof (wim (neighborhoodEquality x y z)
      (wim (wel (renameLabel x y a) (renameLabel x y b)) (wel a b))) := by
  have ha' := reserved_rename z x y a hza hzy
  have hb' := reserved_rename z x y b hzb hzy
  constructor
  · let he : Context [wel a b,neighborhoodEquality x y z] (neighborhoodEquality x y z) := .assumption (by simp)
    let hm : Context [wel a b,neighborhoodEquality x y z] (wel a b) := .assumption (by simp)
    exact (Context.memCongruence hza hzb ha' hb' (he.renameRel x y a z)
      (he.renameRel x y b z) hm).deduction.deduction.empty
  · let m := wel (renameLabel x y a) (renameLabel x y b)
    let he : Context [m,neighborhoodEquality x y z] (neighborhoodEquality x y z) := .assumption (by simp)
    let hm : Context [m,neighborhoodEquality x y z] m := .assumption (by simp)
    exact (Context.memCongruence ha' hb' hza hzb (he.renameRel x y a z).relSymm
      (he.renameRel x y b z).relSymm hm).deduction.deduction.empty

def relationalRenameEquality (z x y a b : Nat) :
    Proof (wim (neighborhoodEquality x y z)
      (wim (neighborhoodEquality a b z)
        (neighborhoodEquality (renameLabel x y a) (renameLabel x y b) z))) ×
    Proof (wim (neighborhoodEquality x y z)
      (wim (neighborhoodEquality (renameLabel x y a) (renameLabel x y b) z)
        (neighborhoodEquality a b z))) := by
  constructor
  · let he : Context [neighborhoodEquality a b z,neighborhoodEquality x y z]
      (neighborhoodEquality x y z) := .assumption (by simp)
    let hm : Context [neighborhoodEquality a b z,neighborhoodEquality x y z]
      (neighborhoodEquality a b z) := .assumption (by simp)
    exact (Context.relCongruence (he.renameRel x y a z)
      (he.renameRel x y b z) hm).deduction.deduction.empty
  · let m := neighborhoodEquality (renameLabel x y a) (renameLabel x y b) z
    let he : Context [m,neighborhoodEquality x y z] (neighborhoodEquality x y z) := .assumption (by simp)
    let hm : Context [m,neighborhoodEquality x y z] m := .assumption (by simp)
    exact (Context.relCongruence (he.renameRel x y a z).relSymm
      (he.renameRel x y b z).relSymm hm).deduction.deduction.empty

#print axioms relationalRenameMembership
#print axioms relationalRenameEquality
end PA196.Logic.Relational
