module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalSuccessorBase
@[expose] public section

/-! Finite nonextensional graph-entry formulas. Objects are witnesses, never
canonical pairs. Mathematical definitions follow the retained PairGraph238
specification; all Lean proof terms below are independently constructed. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def adjunction (a x b : Term n) : Formula n :=
  ∀¹ sourceIff (mem (Rew.bShift b) (.bvar 0))
    (mem (Rew.bShift a) (.bvar 0) ⋎ eq (.bvar 0) (Rew.bShift x))
def singleton (a s : Term n) : Formula n :=
  ∀¹ sourceIff (mem (Rew.bShift s) (.bvar 0)) (eq (.bvar 0) (Rew.bShift a))
def pair (a b p : Term n) : Formula n :=
  ∀¹ sourceIff (mem (Rew.bShift p) (.bvar 0))
    (eq (.bvar 0) (Rew.bShift a) ⋎ eq (.bvar 0) (Rew.bShift b))
def kuratowski (p a b : Term n) : Formula n :=
  ∃¹ ∃¹ (singleton (Rew.bShift (Rew.bShift a)) (.bvar 1) ⋏
    (pair (Rew.bShift (Rew.bShift a)) (Rew.bShift (Rew.bShift b)) (.bvar 0) ⋏
      pair (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift p))))

def adjunctionExists (a x : Term n) : Formula n :=
  ∃¹ adjunction (Rew.bShift a) (Rew.bShift x) (.bvar 0)
def singletonExists (a : Term n) : Formula n := ∃¹ singleton (Rew.bShift a) (.bvar 0)
def pairExists (a b : Term n) : Formula n := ∃¹ pair (Rew.bShift a) (Rew.bShift b) (.bvar 0)

macro "pairSyntax" : tactic => `(tactic|
  (simp only [adjunction,singleton,pair,kuratowski,adjunctionExists,singletonExists,pairExists,
    Ordinal.zero,mem,eq,sourceIff,sourceImply,Semiformula.shift,Semiformula.free,
    Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
   finishSourceSyntax))

def adjunctionWitness {Γ : List Form} (i j : Nat) (d : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (adjunctionExists (.fvar i) (.fvar j)) := by
  have h := allElim _ (.fvar j) (allElim _ (.fvar i) d)
  convert h using 1 ; pairSyntax

def adjunctionShift {Γ : List Form} (a x b : Nat)
    (d : ND.Proof Γ (adjunction (.fvar a) (.fvar x) (.fvar b))) :
    ND.Proof (shifted Γ) (adjunction (.fvar (a+1)) (.fvar (x+1)) (.fvar (b+1))) := by
  convert shiftProof d using 1 ; pairSyntax

def adjunctionAt {Γ : List Form} (a x b y : Nat)
    (d : ND.Proof Γ (adjunction (.fvar a) (.fvar x) (.fvar b))) :
    ND.Proof Γ (sourceIff (mem (.fvar b) (.fvar y))
      (mem (.fvar a) (.fvar y) ⋎ eq (.fvar y) (.fvar x))) := by
  convert allElim _ (.fvar y) d using 1 ; pairSyntax

def singletonFromAdjunction {Γ : List Form} (e a s : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (ha : ND.Proof Γ (adjunction (.fvar e) (.fvar a) (.fvar s))) :
    ND.Proof Γ (singleton (.fvar a) (.fvar s)) := by
  apply allIntro
  have hi := adjunctionAt (e+1) (a+1) (s+1) 0 (adjunctionShift e a s ha)
  have hn := Ordinal.zeroNotMem (e+1) 0 (Ordinal.zeroShift e hz)
  have result : ND.Proof (shifted Γ) (sourceIff (mem (.fvar (s+1)) (.fvar 0))
      (eq (.fvar 0) (.fvar (a+1)))) := by
    apply andIntro
    · apply impIntro
      have hd := mp (assumption (by simp)) (up (andLeft hi) (mem (.fvar (s+1)) (.fvar 0)))
      apply orElim hd
      · exact botElim (contradiction (assumption (by simp)) (up (up hn _) _))
      · exact assumption (by simp)
    · apply impIntro
      exact mp (ND.orRight (assumption (by simp))) (up (andRight hi) _)
  convert result using 1 ; pairSyntax

def singletonShift {Γ : List Form} (a s : Nat)
    (d : ND.Proof Γ (singleton (.fvar a) (.fvar s))) :
    ND.Proof (shifted Γ) (singleton (.fvar (a+1)) (.fvar (s+1))) := by
  convert shiftProof d using 1 ; pairSyntax

def singletonAt {Γ : List Form} (a s y : Nat)
    (d : ND.Proof Γ (singleton (.fvar a) (.fvar s))) :
    ND.Proof Γ (sourceIff (mem (.fvar s) (.fvar y)) (eq (.fvar y) (.fvar a))) := by
  convert allElim _ (.fvar y) d using 1 ; pairSyntax

def pairFromAdjunction {Γ : List Form} (a b s p : Nat)
    (hs : ND.Proof Γ (singleton (.fvar a) (.fvar s)))
    (ha : ND.Proof Γ (adjunction (.fvar s) (.fvar b) (.fvar p))) :
    ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar p)) := by
  apply allIntro
  have hi := adjunctionAt (s+1) (b+1) (p+1) 0 (adjunctionShift s b p ha)
  have hj := singletonAt (a+1) (s+1) 0 (singletonShift a s hs)
  have result : ND.Proof (shifted Γ) (sourceIff (mem (.fvar (p+1)) (.fvar 0))
      (eq (.fvar 0) (.fvar (a+1)) ⋎ eq (.fvar 0) (.fvar (b+1)))) := by
    apply andIntro
    · apply impIntro
      have hd := mp (assumption (by simp)) (up (andLeft hi) (mem (.fvar (p+1)) (.fvar 0)))
      apply orElim hd
      · exact ND.orLeft (mp (assumption (by simp)) (up (up (andLeft hj) (mem (.fvar (p+1)) (.fvar 0))) (mem (.fvar (s+1)) (.fvar 0))))
      · exact ND.orRight (assumption (by simp))
    · apply impIntro
      have hd : ND.Proof ((eq (.fvar 0) (.fvar (a+1)) ⋎ eq (.fvar 0) (.fvar (b+1))) :: shifted Γ) (mem (.fvar (s+1)) (.fvar 0) ⋎ eq (.fvar 0) (.fvar (b+1))) := by
        apply orElim (assumption (p := eq (.fvar 0) (.fvar (a+1)) ⋎ eq (.fvar 0) (.fvar (b+1))) (by simp))
        · exact ND.orLeft (mp (assumption (by simp)) (up (up (andRight hj) _) _))
        · exact ND.orRight (assumption (by simp))
      exact mp hd (up (andRight hi) _)
  convert result using 1 ; pairSyntax

#print axioms adjunctionWitness
#print axioms singletonFromAdjunction
#print axioms pairFromAdjunction
end M6.PA.RelationalSource.PairGraph
