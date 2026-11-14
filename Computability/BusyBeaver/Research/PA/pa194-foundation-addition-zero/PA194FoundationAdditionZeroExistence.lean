import PA194FoundationAdditionZero
set_option maxHeartbeats 800000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def pointExists (a b : Term n) : Formula n :=
  ∃⁰ pointGraph (Rew.bShift a) (Rew.bShift b) (.bvar 0)

def pointGivenEmpty {Γ : List Form} (E : FormulaEquality Γ) (g a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar g)))
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (pointExists (.fvar a) (.fvar b)) := by
  apply exsElim (exactWitness E.core E.transitive g a b hempty hadj)
  let σ : Formula 1 := exactExtension (.fvar g) (.bvar 0) (.fvar a) (.fvar b)
  let C := σ.free :: shifted Γ
  have hx : ND.Proof C (exactExtension (.fvar (g+1)) (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ,exactExtension,classified]; traceSyntax
  have hp := pointFromExact (g+1) 0 (a+1) (b+1) (up (Ordinal.zeroShift g hz) σ.free) hx
  apply exsIntro _ (.fvar 0)
  convert hp using 1 <;> (dsimp [C,σ,pointExists,exactExtension,classified] <;> traceSyntax)

def pointWitness {Γ : List Form} (E : FormulaEquality Γ) (a b : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (pointExists (.fvar a) (.fvar b)) := by
  apply exsElim hempty
  let σ : Formula 1 := Ordinal.zero (.bvar 0)
  let C := σ.free :: shifted Γ
  have hz : ND.Proof C (Ordinal.zero (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ]; traceSyntax
  let EE := E.shifted.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have hp := pointGivenEmpty EE 0 (a+1) (b+1) hz
    (up (emptyClosedShift hempty) σ.free) (up (adjunctionClosedShift hadj) σ.free)
  convert hp using 1 <;> (dsimp [C,σ,pointExists] <;> traceSyntax)

macro "addSyntax" : tactic => `(tactic|
  (dsimp only [addPrefixExists,addPrefix,addRecurrence,addResult,Ordinal.successor]; traceSyntax))

def prefixExistsIntro {Γ : List Form} (a b z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (addPrefix (.fvar a) (.fvar b) (.fvar z) (.fvar g))) :
    ND.Proof Γ (addPrefixExists (.fvar a) (.fvar b)) := by
  apply exsIntro _ (.fvar z)
  have h : ND.Proof Γ (∃⁰ (Ordinal.zero (.fvar z) ⋏
      addPrefix (.fvar a) (.fvar b) (.fvar z) (.bvar 0))) := by
    apply exsIntro _ (.fvar g)
    convert andIntro hz hp using 1 ; addSyntax
  convert h using 1 ; addSyntax

def zeroPrefixWitness {Γ : List Form} (E : FormulaEquality Γ) (a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (addPrefixExists (.fvar a) (.fvar b)) := by
  apply exsElim (pointWitness E a b hempty hadj)
  let σ : Formula 1 := pointGraph (.fvar a) (.fvar b) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hp : ND.Proof C (pointGraph (.fvar (a+1)) (.fvar (b+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ]; traceSyntax
  let EE := E.shifted.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have zz := up (Ordinal.zeroShift a hz) σ.free
  have pp := pointAddPrefix EE (a+1) (b+1) 0 zz (up (domainShift b hb) σ.free) hp
  have out := prefixExistsIntro (a+1) (b+1) (a+1) 0 zz pp
  convert out using 1 <;> (dsimp [C,σ,pointGraph] <;> addSyntax)

#print axioms pointWitness
#print axioms zeroPrefixWitness
end M6.PA.RelationalSource.PairGraph

