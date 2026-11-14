import PA194FoundationPairGraph
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def singletonFromEmpty {Γ : List Form} (e a : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (singletonExists (.fvar a)) := by
  apply exsElim (adjunctionWitness e a hadj)
  let σ : Formula 1 := adjunction (.fvar e) (.fvar a) (.bvar 0)
  let C := σ.free :: shifted Γ
  have ha : ND.Proof C (adjunction (.fvar (e+1)) (.fvar (a+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; pairSyntax
  have he : ND.Proof C (Ordinal.zero (.fvar (e+1))) :=
    up (Ordinal.zeroShift e hz) _
  have hs := singletonFromAdjunction (e+1) (a+1) 0 he ha
  apply exsIntro _ (.fvar 0)
  convert hs using 1 ; pairSyntax

def singletonWitness {Γ : List Form} (a : Nat)
    (hempty : ND.Proof Γ emptyFormula)
    (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (singletonExists (.fvar a)) := by
  apply exsElim hempty
  let σ : Formula 1 := Ordinal.zero (.bvar 0)
  let C := σ.free :: shifted Γ
  have hz : ND.Proof C (Ordinal.zero (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; pairSyntax
  have hd : ND.Proof C adjunctionFormula := by
    have h := up (shiftProof hadj) σ.free
    convert h using 1 ; simp only [adjunctionFormula] ; pairSyntax
  have hs := singletonFromEmpty 0 (a+1) hz hd
  convert hs using 1 ; pairSyntax

def adjunctionClosedShift {Γ : List Form} (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof (shifted Γ) adjunctionFormula := by
  convert shiftProof hadj using 1 ; simp only [adjunctionFormula] ; pairSyntax

def pairFromSingleton {Γ : List Form} (a b s : Nat)
    (hs : ND.Proof Γ (singleton (.fvar a) (.fvar s)))
    (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (pairExists (.fvar a) (.fvar b)) := by
  apply exsElim (adjunctionWitness s b hadj)
  let σ : Formula 1 := adjunction (.fvar s) (.fvar b) (.bvar 0)
  let C := σ.free :: shifted Γ
  have ha : ND.Proof C (adjunction (.fvar (s+1)) (.fvar (b+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; pairSyntax
  have hh : ND.Proof C (singleton (.fvar (a+1)) (.fvar (s+1))) :=
    up (singletonShift a s hs) _
  have hp := pairFromAdjunction (a+1) (b+1) (s+1) 0 hh ha
  apply exsIntro _ (.fvar 0)
  convert hp using 1 ; pairSyntax

def pairWitness {Γ : List Form} (a b : Nat)
    (hempty : ND.Proof Γ emptyFormula)
    (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (pairExists (.fvar a) (.fvar b)) := by
  apply exsElim (singletonWitness a hempty hadj)
  let σ : Formula 1 := singleton (.fvar a) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hs : ND.Proof C (singleton (.fvar (a+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; pairSyntax
  have hp := pairFromSingleton (a+1) (b+1) 0 hs
    (up (adjunctionClosedShift hadj) σ.free)
  convert hp using 1 ; pairSyntax

#print axioms singletonFromEmpty
#print axioms singletonWitness
#print axioms pairFromSingleton
#print axioms pairWitness
end M6.PA.RelationalSource.PairGraph
