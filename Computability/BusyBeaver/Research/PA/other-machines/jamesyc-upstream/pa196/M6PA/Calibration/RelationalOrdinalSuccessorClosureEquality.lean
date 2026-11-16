module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalSuccessorClosureLogic
@[expose] public section

/-! Ordinary equality premises and their elementary proof transformations.
Only the literal reflexivity, symmetry and membership-congruence formulas
are used here; this introduces neither extensionality nor global irreflexivity. -/
namespace M6.PA.RelationalSource.Ordinal
open FFL FFL.FirstOrder ND

structure EqualityProofs (Γ : List Form) where
  reflexive : ND.Proof Γ reflexivityFormula
  symmetric : ND.Proof Γ symmetryFormula
  congruent : ND.Proof Γ congruenceFormula

macro "equalitySyntax" : tactic => `(tactic|
  (simp only [reflexivityFormula,symmetryFormula,congruenceFormula,
    eqAtom,notEqAtom,memAtom,notMemAtom]; sourceSyntaxEq))

def EqualityProofs.shift {Γ : List Form} (e : EqualityProofs Γ) : EqualityProofs (shifted Γ) where
  reflexive := by convert shiftProof e.reflexive using 1 ; equalitySyntax
  symmetric := by convert shiftProof e.symmetric using 1 ; equalitySyntax
  congruent := by convert shiftProof e.congruent using 1 ; equalitySyntax

def EqualityProofs.up {Γ : List Form} (e : EqualityProofs Γ) (p : Form) : EqualityProofs (p::Γ) where
  reflexive := ND.up e.reflexive p
  symmetric := ND.up e.symmetric p
  congruent := ND.up e.congruent p

def eqRefl {Γ : List Form} (e : EqualityProofs Γ) (i : Nat) :
    ND.Proof Γ (eq (.fvar i) (.fvar i)) := by
  convert allElim _ (.fvar i) e.reflexive using 1 ; equalitySyntax

def eqSymm {Γ : List Form} (e : EqualityProofs Γ) (i j : Nat)
    (h : ND.Proof Γ (eq (.fvar i) (.fvar j))) : ND.Proof Γ (eq (.fvar j) (.fvar i)) := by
  have d : ND.Proof Γ (eq (.fvar i) (.fvar j) 🡒 eq (.fvar j) (.fvar i)) := by
    convert allElim _ (.fvar j) (allElim _ (.fvar i) e.symmetric) using 1 ; equalitySyntax
  exact mp h d

def memCongr {Γ : List Form} (e : EqualityProofs Γ) (a b x y : Nat)
    (hab : ND.Proof Γ (eq (.fvar a) (.fvar b)))
    (hxy : ND.Proof Γ (eq (.fvar x) (.fvar y)))
    (h : ND.Proof Γ (mem (.fvar a) (.fvar x))) : ND.Proof Γ (mem (.fvar b) (.fvar y)) := by
  have d : ND.Proof Γ (eq (.fvar x) (.fvar y) 🡒 eq (.fvar a) (.fvar b) 🡒
      mem (.fvar a) (.fvar x) 🡒 mem (.fvar b) (.fvar y)) := by
    convert allElim _ (.fvar b) (allElim _ (.fvar y)
      (allElim _ (.fvar a) (allElim _ (.fvar x) e.congruent))) using 1 ; equalitySyntax
  exact mp h (mp hab (mp hxy d))

def memContainer {Γ : List Form} (e : EqualityProofs Γ) (a b x : Nat)
    (hab : ND.Proof Γ (eq (.fvar a) (.fvar b)))
    (h : ND.Proof Γ (mem (.fvar a) (.fvar x))) : ND.Proof Γ (mem (.fvar b) (.fvar x)) :=
  memCongr e a b x x hab (eqRefl e x) h

def memElement {Γ : List Form} (e : EqualityProofs Γ) (a x y : Nat)
    (hxy : ND.Proof Γ (eq (.fvar x) (.fvar y)))
    (h : ND.Proof Γ (mem (.fvar a) (.fvar x))) : ND.Proof Γ (mem (.fvar a) (.fvar y)) :=
  memCongr e a a x y (eqRefl e a) hxy h

#print axioms EqualityProofs.shift
#print axioms eqSymm
#print axioms memCongr
end M6.PA.RelationalSource.Ordinal
