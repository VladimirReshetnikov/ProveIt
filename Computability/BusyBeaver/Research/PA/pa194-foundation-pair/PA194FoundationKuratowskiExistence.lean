import PA194FoundationPairExistence
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def kuratowskiExists (a b : Term n) : Formula n :=
  ∃⁰ kuratowski (.bvar 0) (Rew.bShift a) (Rew.bShift b)

macro "kuratowskiSyntax" : tactic => `(tactic|
  (simp only [kuratowskiExists,adjunction,singleton,pair,kuratowski,
    Ordinal.zero,mem,eq,sourceIff,sourceImply,Semiformula.shift,Semiformula.free,
    Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def pairShift {Γ : List Form} (a b p : Nat)
    (d : ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar p))) :
    ND.Proof (shifted Γ) (pair (.fvar (a+1)) (.fvar (b+1)) (.fvar (p+1))) := by
  convert shiftProof d using 1 ; pairSyntax

def emptyClosedShift {Γ : List Form} (d : ND.Proof Γ emptyFormula) :
    ND.Proof (shifted Γ) emptyFormula := by
  convert shiftProof d using 1 ; simp only [emptyFormula] ; pairSyntax

def kuratowskiIntro {Γ : List Form} (p a b s t : Nat)
    (hs : ND.Proof Γ (singleton (.fvar a) (.fvar s)))
    (ht : ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar t)))
    (hp : ND.Proof Γ (pair (.fvar s) (.fvar t) (.fvar p))) :
    ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b)) := by
  apply exsIntro _ (.fvar s)
  have h : ND.Proof Γ (∃⁰ (singleton (.fvar a) (.fvar s) ⋏
      (pair (.fvar a) (.fvar b) (.bvar 0) ⋏ pair (.fvar s) (.bvar 0) (.fvar p)))) := by
    apply exsIntro _ (.fvar t)
    convert andIntro hs (andIntro ht hp) using 1 ; pairSyntax
  convert h using 1 ; pairSyntax

def kuratowskiFromComponents {Γ : List Form} (a b s t : Nat)
    (hs : ND.Proof Γ (singleton (.fvar a) (.fvar s)))
    (ht : ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar t)))
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (kuratowskiExists (.fvar a) (.fvar b)) := by
  apply exsElim (pairWitness s t hempty hadj)
  let σ : Formula 1 := pair (.fvar s) (.fvar t) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hp : ND.Proof C (pair (.fvar (s+1)) (.fvar (t+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; pairSyntax
  have hk := kuratowskiIntro 0 (a+1) (b+1) (s+1) (t+1)
    (up (singletonShift a s hs) σ.free) (up (pairShift a b t ht) σ.free) hp
  apply exsIntro _ (.fvar 0)
  convert hk using 1 <;> (dsimp [C,σ] <;> kuratowskiSyntax)

def kuratowskiFromSingleton {Γ : List Form} (a b s : Nat)
    (hs : ND.Proof Γ (singleton (.fvar a) (.fvar s)))
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (kuratowskiExists (.fvar a) (.fvar b)) := by
  apply exsElim (pairWitness a b hempty hadj)
  let σ : Formula 1 := pair (.fvar a) (.fvar b) (.bvar 0)
  let C := σ.free :: shifted Γ
  have ht : ND.Proof C (pair (.fvar (a+1)) (.fvar (b+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; pairSyntax
  have hk := kuratowskiFromComponents (a+1) (b+1) (s+1) 0
    (up (singletonShift a s hs) σ.free) ht
    (up (emptyClosedShift hempty) σ.free) (up (adjunctionClosedShift hadj) σ.free)
  convert hk using 1 <;> (dsimp [C,σ] <;> kuratowskiSyntax)

def kuratowskiWitness {Γ : List Form} (a b : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (kuratowskiExists (.fvar a) (.fvar b)) := by
  apply exsElim (singletonWitness a hempty hadj)
  let σ : Formula 1 := singleton (.fvar a) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hs : ND.Proof C (singleton (.fvar (a+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; pairSyntax
  have hk := kuratowskiFromSingleton (a+1) (b+1) 0 hs
    (up (emptyClosedShift hempty) σ.free) (up (adjunctionClosedShift hadj) σ.free)
  convert hk using 1 <;> (dsimp [C,σ] <;> kuratowskiSyntax)

#print axioms kuratowskiIntro
#print axioms kuratowskiFromComponents
#print axioms kuratowskiFromSingleton
#print axioms kuratowskiWitness
end M6.PA.RelationalSource.PairGraph
