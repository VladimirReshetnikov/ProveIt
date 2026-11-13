module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalSuccessorClosureLinear
@[expose] public section

/-! Capture-aware represented-subset and intersection proof operations. -/
namespace M6.PA.RelationalSource.Ordinal
open FFL FFL.FirstOrder ND

def subsetShift {Γ : List Form} (i j : Nat) (d : ND.Proof Γ (subset (.fvar i) (.fvar j))) :
    ND.Proof (shifted Γ) (subset (.fvar (i+1)) (.fvar (j+1))) := by
  convert shiftProof d using 1 ; ordinalSyntax

def subsetAt {Γ : List Form} (i j x : Nat)
    (d : ND.Proof Γ (subset (.fvar i) (.fvar j)))
    (h : ND.Proof Γ (mem (.fvar i) (.fvar x))) : ND.Proof Γ (mem (.fvar j) (.fvar x)) := by
  have hd : ND.Proof Γ (mem (.fvar i) (.fvar x) 🡒 mem (.fvar j) (.fvar x)) := by
    convert allElim _ (.fvar x) d using 1 ; ordinalSyntax
  exact mp h hd

def intersectionShift {Γ : List Form} (a s c : Nat)
    (d : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c))) :
    ND.Proof (shifted Γ) (intersection (.fvar (a+1)) (.fvar (s+1)) (.fvar (c+1))) := by
  convert shiftProof d using 1 ; intersectionSyntax

def intersectionAt {Γ : List Form} (a s c x : Nat)
    (d : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c))) :
    ND.Proof Γ (sourceIff (mem (.fvar c) (.fvar x))
      (mem (.fvar s) (.fvar x) ⋏ mem (.fvar a) (.fvar x))) := by
  convert allElim _ (.fvar x) d using 1 ; intersectionSyntax

def intersectionSubset {Γ : List Form} (a s c : Nat)
    (d : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c))) :
    ND.Proof Γ (subset (.fvar c) (.fvar a)) := by
  apply allIntro
  have hd := intersectionAt (a+1) (s+1) (c+1) 0 (intersectionShift a s c d)
  have h : ND.Proof (shifted Γ) (mem (.fvar (c+1)) (.fvar 0) 🡒 mem (.fvar (a+1)) (.fvar 0)) :=
    impIntro (andRight (mp (assumption (by simp)) (up (andLeft hd) _)))
  convert h using 1 ; ordinalSyntax

def nonemptyIntro {Γ : List Form} (s x : Nat)
    (d : ND.Proof Γ (mem (.fvar s) (.fvar x))) : ND.Proof Γ (nonempty (.fvar s)) := by
  apply exsIntro _ (.fvar x)
  convert d using 1 ; ordinalSyntax

def notNonemptyAt {Γ : List Form} (s x : Nat)
    (d : ND.Proof Γ (∼nonempty (.fvar s)))
    (h : ND.Proof Γ (mem (.fvar s) (.fvar x))) : ND.Proof Γ ⊥ :=
  contradiction (nonemptyIntro s x h) d

def leastShift {Γ : List Form} (s m : Nat) (d : ND.Proof Γ (least (.fvar s) (.fvar m))) :
    ND.Proof (shifted Γ) (least (.fvar (s+1)) (.fvar (m+1))) := by
  convert shiftProof d using 1 ; ordinalSyntax

def greatestShift {Γ : List Form} (s m : Nat) (d : ND.Proof Γ (greatest (.fvar s) (.fvar m))) :
    ND.Proof (shifted Γ) (greatest (.fvar (s+1)) (.fvar (m+1))) := by
  convert shiftProof d using 1 ; ordinalSyntax

def leastAt {Γ : List Form} (s m x : Nat) (d : ND.Proof Γ (least (.fvar s) (.fvar m)))
    (h : ND.Proof Γ (mem (.fvar s) (.fvar x))) :
    ND.Proof Γ (eq (.fvar m) (.fvar x) ⋎ mem (.fvar x) (.fvar m)) := by
  have hd : ND.Proof Γ (mem (.fvar s) (.fvar x) 🡒
      (eq (.fvar m) (.fvar x) ⋎ mem (.fvar x) (.fvar m))) := by
    convert allElim _ (.fvar x) (andRight d) using 1 ; ordinalSyntax
  exact mp h hd

def greatestAt {Γ : List Form} (s m x : Nat) (d : ND.Proof Γ (greatest (.fvar s) (.fvar m)))
    (h : ND.Proof Γ (mem (.fvar s) (.fvar x))) :
    ND.Proof Γ (eq (.fvar x) (.fvar m) ⋎ mem (.fvar m) (.fvar x)) := by
  have hd : ND.Proof Γ (mem (.fvar s) (.fvar x) 🡒
      (eq (.fvar x) (.fvar m) ⋎ mem (.fvar m) (.fvar x))) := by
    convert allElim _ (.fvar x) (andRight d) using 1 ; ordinalSyntax
  exact mp h hd

#print axioms intersectionSubset
#print axioms notNonemptyAt
#print axioms leastAt
#print axioms greatestAt
end M6.PA.RelationalSource.Ordinal

