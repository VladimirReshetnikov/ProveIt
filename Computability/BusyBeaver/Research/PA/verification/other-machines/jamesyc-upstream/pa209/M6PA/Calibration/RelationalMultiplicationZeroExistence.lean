module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationPrefixIntro
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] mulPrefix addPrefix addResult
set_option maxHeartbeats 600000

def mulZeroPrefixWitness {Γ : List Form} (E : FormulaEquality Γ) (a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (mulPrefixExists (.fvar a) (.fvar b)) := by
  apply exsElim (pointWitness E a a hempty hadj)
  let σ : Formula 1 := pointGraph (.fvar a) (.fvar a) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hp : ND.Proof C (pointGraph (.fvar (a+1)) (.fvar (a+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ]; traceSyntax
  let EE := E.shifted.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have zz := up (Ordinal.zeroShift a hz) σ.free
  have pp := pointMulPrefix EE (a+1) (b+1) 0 zz hp
  have out := mulPrefixExistsIntro (a+1) (b+1) (a+1) 0 zz pp
  convert out using 1 <;> (dsimp [C,σ,pointGraph] <;> mulSyntax)


#print axioms mulZeroPrefixWitness
end M6.PA.RelationalSource.PairGraph
