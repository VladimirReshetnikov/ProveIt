module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalSuccessorBase
public import M6PA.Calibration.RelationalOrdinalIntersectionAxiom
@[expose] public section

/-! Capture-aware elimination and shift operations used by finite ordinal
successor closure. These are proof transformations, not semantic arguments. -/
namespace M6.PA.RelationalSource.Ordinal
open FFL FFL.FirstOrder ND

macro "successorSyntax" : tactic => `(tactic|
  (simp only [successor,sourceIff,sourceImply]; ordinalSyntax))

def successorShift {Γ : List Form} (i j : Nat)
    (d : ND.Proof Γ (successor (.fvar i) (.fvar j))) :
    ND.Proof (shifted Γ) (successor (.fvar (i+1)) (.fvar (j+1))) := by
  convert shiftProof d using 1 ; successorSyntax

def successorAt {Γ : List Form} (i j k : Nat)
    (d : ND.Proof Γ (successor (.fvar i) (.fvar j))) :
    ND.Proof Γ (sourceIff (mem (.fvar j) (.fvar k))
      (mem (.fvar i) (.fvar k) ⋎ eq (.fvar k) (.fvar i))) := by
  convert allElim _ (.fvar k) d using 1 ; successorSyntax

def successorOld {Γ : List Form} (i j k : Nat)
    (d : ND.Proof Γ (successor (.fvar i) (.fvar j)))
    (h : ND.Proof Γ (mem (.fvar i) (.fvar k))) :
    ND.Proof Γ (mem (.fvar j) (.fvar k)) :=
  mp (ND.orLeft h) (andRight (successorAt i j k d))

def transitiveShift {Γ : List Form} (i : Nat)
    (d : ND.Proof Γ (transitive (.fvar i))) :
    ND.Proof (shifted Γ) (transitive (.fvar (i+1))) := by
  convert shiftProof d using 1 ; ordinalSyntax

def transitiveAt {Γ : List Form} (i j k : Nat)
    (d : ND.Proof Γ (transitive (.fvar i)))
    (hx : ND.Proof Γ (mem (.fvar i) (.fvar j)))
    (hy : ND.Proof Γ (mem (.fvar j) (.fvar k))) :
    ND.Proof Γ (mem (.fvar i) (.fvar k)) := by
  have h : ND.Proof Γ ((mem (.fvar i) (.fvar j) ⋏ mem (.fvar j) (.fvar k)) 🡒
      mem (.fvar i) (.fvar k)) := by
    convert allElim _ (.fvar k) (allElim _ (.fvar j) d) using 1 ; ordinalSyntax
  exact mp (andIntro hx hy) h

def memberTransitiveShift {Γ : List Form} (i : Nat)
    (d : ND.Proof Γ (memberTransitive (.fvar i))) :
    ND.Proof (shifted Γ) (memberTransitive (.fvar (i+1))) := by
  convert shiftProof d using 1 ; ordinalSyntax

def memberTransitiveAt {Γ : List Form} (i j : Nat)
    (d : ND.Proof Γ (memberTransitive (.fvar i)))
    (h : ND.Proof Γ (mem (.fvar i) (.fvar j))) :
    ND.Proof Γ (transitive (.fvar j)) := by
  have ht : ND.Proof Γ (mem (.fvar i) (.fvar j) 🡒 transitive (.fvar j)) := by
    convert allElim _ (.fvar j) d using 1 ; ordinalSyntax
  exact mp h ht

def memberIrShift {Γ : List Form} (i : Nat)
    (d : ND.Proof Γ (memberIr (.fvar i))) :
    ND.Proof (shifted Γ) (memberIr (.fvar (i+1))) := by
  convert shiftProof d using 1 ; ordinalSyntax

def memberIrAt {Γ : List Form} (i j : Nat)
    (d : ND.Proof Γ (memberIr (.fvar i)))
    (h : ND.Proof Γ (mem (.fvar i) (.fvar j))) :
    ND.Proof Γ (∼mem (.fvar j) (.fvar j)) := by
  have ht : ND.Proof Γ (mem (.fvar i) (.fvar j) 🡒 ∼mem (.fvar j) (.fvar j)) := by
    convert allElim _ (.fvar j) d using 1 ; ordinalSyntax
  exact mp h ht

/-- Local member irreflexivity already rules out self-membership of its
container; no global irreflexivity axiom is needed. -/
def containerIr {Γ : List Form} (i : Nat)
    (d : ND.Proof Γ (memberIr (.fvar i))) :
    ND.Proof Γ (∼mem (.fvar i) (.fvar i)) := by
  apply byContradiction
  have hm : ND.Proof (∼∼mem (.fvar i) (.fvar i) :: Γ) (mem (.fvar i) (.fvar i)) := by
    simpa using (assumption (Γ := ∼∼mem (.fvar i) (.fvar i) :: Γ)
      (p := ∼∼mem (.fvar i) (.fvar i)) (by simp))
  exact contradiction hm (memberIrAt i i (up d _) hm)

#print axioms successorAt
#print axioms transitiveAt
#print axioms memberTransitiveAt
#print axioms containerIr
end M6.PA.RelationalSource.Ordinal
