module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationResultWitness
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

def mulOutputFromPrefix {Γ : List Form} (E : FormulaEquality Γ) (x y z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar x) (.fvar y) (.fvar z) (.fvar g))) :
    ND.Proof Γ (mulOutput (.fvar x) (.fvar y)) := by
  have parts := hp
  unfold mulPrefix at parts
  have he := mp (ND.orRight (E.reflexive (.fvar x))) (andRight (graphDomainAt x g x (andLeft parts)))
  apply exsElim he
  let σ : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hw : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> mulCompactSyntax)
  have h := mulOutputFromEndpoint (x+1) (y+1) 0 (z+1) (g+1)
    (up (Ordinal.zeroShift z hz) σ.free) (up (mulPrefixShift x y z g hp) σ.free) hw
  convert h using 1 <;> (dsimp [C,σ] <;> (try simp only [mulOutput]) <;> mulCompactSyntax)

#print axioms mulOutputFromPrefix
end M6.PA.RelationalSource.PairGraph

