module
public import M6.Logic.NativeConnectives
public import M6.Logic.NativeRenaming
@[expose] public section

/-! Actual finite equality and atomic renaming proof compilation, following
NumericHilbert238.v and NumericNamed238.v at the pinned PA238 source.
Reflexivity is derived from native R1/R7 and guarded bundle vacuity, not assumed.
This is a bounded slice of readback, not the full arithmetic interpretation. -/
namespace M6.PA.NativeCalculus

def negationVacuity (x a : Nat) (hv : Derivation (wim a (wal x a))) :
    Derivation (wim (wn a) (wal x (wn a))) := by
  let hc := contrapose hv
  let hg := Derivation.all x hc
  let hl := Derivation.mp hg (Derivation.r2 x (wn (wal x a)) (wn a))
  let hr := contrapose (Derivation.r6 x a)
  let hf := implicationCompose hr (doubleNegationElimination (wal x (wn (wal x a))))
  exact implicationCompose hf hl

def Context.existsElim {Γ : List Nat} (x : Nat) {a b : Nat}
    (hv : Derivation (wim b (wal x b)))
    (p : Context Γ (wal x (wim a b))) (q : Context Γ (wex x a)) : Context Γ b := by
  let hn : Context (wn b :: Γ) (wn b) := .assumption (by simp)
  let hnb : Context (wn b :: Γ) (wal x (wn b)) :=
    .mp hn (.closed (negationVacuity x b hv))
  let hc : Context (wn b :: Γ) (wal x (wim (wn b) (wn a))) :=
    (p.up (wn b)).forallMP x (.closed (.all x (contraposition a b)))
  let ha : Context (wn b :: Γ) (wal x (wn a)) := hnb.forallMP x hc
  exact (Context.mp ha (q.up (wn b))).deduction.dne

def equalityReflexive (a : Nat) : Derivation (weq a a) := by
  let x := a + 1
  have hxa : x ≠ a := by dsimp [x]; omega
  let hv := equalityVacuity a a x hxa hxa
  let hp : Context [weq x a] (weq x a) := .assumption (by simp)
  let hd : Derivation (wim (weq x a) (weq a a)) :=
    (Context.mp hp (.mp hp (.closed (.r7 x a a)))).deduction.empty
  exact (Context.existsElim (Γ := []) x hv (.closed (.all x hd)) (.closed (.r1 x a))).empty

def equalitySymmetry (a b : Nat) : Derivation (wim (weq a b) (weq b a)) := by
  let hp : Context [weq a b] (weq a b) := .assumption (by simp)
  exact (Context.mp (.closed (equalityReflexive a)) (.mp hp (.closed (.r7 a b a)))).deduction.empty

def Context.equalitySymm {Γ : List Nat} {a b : Nat} (p : Context Γ (weq a b)) :
    Context Γ (weq b a) := .mp p (.closed (equalitySymmetry a b))

def Context.equalityTrans {Γ : List Nat} {a b c : Nat}
    (p : Context Γ (weq a b)) (q : Context Γ (weq b c)) : Context Γ (weq a c) :=
  .mp q (.mp p.equalitySymm (.closed (.r7 b a c)))

def Context.equalityCongruence {Γ : List Nat} {a b c d : Nat}
    (hac : Context Γ (weq a c)) (hbd : Context Γ (weq b d))
    (hab : Context Γ (weq a b)) : Context Γ (weq c d) :=
  (hac.equalitySymm.equalityTrans hab).equalityTrans hbd

def Context.membershipCongruence {Γ : List Nat} {a b c d : Nat}
    (hac : Context Γ (weq a c)) (hbd : Context Γ (weq b d))
    (hab : Context Γ (wel a b)) : Context Γ (wel c d) :=
  .mp hbd (.mp (.mp hab (.mp hac (.closed (.r5 a c b)))) (.closed (.r3 c b d)))

def Context.renameEquality {Γ : List Nat} (x y a : Nat) (h : Context Γ (weq x y)) :
    Context Γ (weq a (renameLabel x y a)) := by
  by_cases ha : a = x
  · simpa [renameLabel,ha] using h
  · simpa [renameLabel,ha] using (Context.closed (Γ := Γ) (equalityReflexive a))

def renameMembershipForward (x y a b : Nat) :
    Derivation (wim (weq x y) (wim (wel a b)
      (wel (renameLabel x y a) (renameLabel x y b)))) := by
  let he : Context [wel a b, weq x y] (weq x y) := .assumption (by simp)
  let hm : Context [wel a b, weq x y] (wel a b) := .assumption (by simp)
  exact (Context.membershipCongruence (he.renameEquality x y a)
    (he.renameEquality x y b) hm).deduction.deduction.empty

def renameMembershipReverse (x y a b : Nat) :
    Derivation (wim (weq x y) (wim (wel (renameLabel x y a) (renameLabel x y b))
      (wel a b))) := by
  let m := wel (renameLabel x y a) (renameLabel x y b)
  let he : Context [m, weq x y] (weq x y) := .assumption (by simp)
  let hm : Context [m, weq x y] m := .assumption (by simp)
  exact (Context.membershipCongruence (he.renameEquality x y a).equalitySymm
    (he.renameEquality x y b).equalitySymm hm).deduction.deduction.empty

def renameEqualityForward (x y a b : Nat) :
    Derivation (wim (weq x y) (wim (weq a b)
      (weq (renameLabel x y a) (renameLabel x y b)))) := by
  let he : Context [weq a b, weq x y] (weq x y) := .assumption (by simp)
  let hm : Context [weq a b, weq x y] (weq a b) := .assumption (by simp)
  exact (Context.equalityCongruence (he.renameEquality x y a)
    (he.renameEquality x y b) hm).deduction.deduction.empty

def renameEqualityReverse (x y a b : Nat) :
    Derivation (wim (weq x y) (wim (weq (renameLabel x y a) (renameLabel x y b))
      (weq a b))) := by
  let m := weq (renameLabel x y a) (renameLabel x y b)
  let he : Context [m, weq x y] (weq x y) := .assumption (by simp)
  let hm : Context [m, weq x y] m := .assumption (by simp)
  exact (Context.equalityCongruence (he.renameEquality x y a).equalitySymm
    (he.renameEquality x y b).equalitySymm hm).deduction.deduction.empty

#print axioms equalityReflexive
#print axioms Context.existsElim
#print axioms renameMembershipForward
end M6.PA.NativeCalculus

