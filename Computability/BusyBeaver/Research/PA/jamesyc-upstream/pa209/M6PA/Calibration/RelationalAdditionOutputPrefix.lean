module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionResultWitness
@[expose] public section

/-! Extract an actual ordinal endpoint from an inclusive addition prefix. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

set_option maxHeartbeats 600000 in
def addOutputFromPrefix {Γ : List Form} (E : FormulaEquality Γ) (x y z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (addPrefix (.fvar x) (.fvar y) (.fvar z) (.fvar g))) :
    ND.Proof Γ (addOutput (.fvar x) (.fvar y)) := by
  have he := mp (ND.orRight (E.reflexive (.fvar x))) (andRight (graphDomainAt x g x (andLeft hp)))
  apply exsElim he
  let σ : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hw : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> prefixSyntax)
  have h := addOutputFromEndpoint (x+1) (y+1) 0 (z+1) (g+1)
    (up (Ordinal.zeroShift z hz) σ.free) (up (prefixShift x y z g hp) σ.free) hw
  convert h using 1 <;> (dsimp [C,σ] <;> (try simp only [addOutput]) <;> prefixSyntax)

#print axioms addOutputFromPrefix
end M6.PA.RelationalSource.PairGraph

