module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationOutputPayload
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

def mulOutputFromExists {Γ : List Form} (E : FormulaEquality Γ) (x y : Nat)
    (hp : ND.Proof Γ (mulPrefixExists (.fvar x) (.fvar y))) :
    ND.Proof Γ (mulOutput (.fvar x) (.fvar y)) := by
  apply exsElim hp
  let σ : Formula 1 := ∃¹ (Ordinal.zero (.bvar 1) ⋏ mulPrefix (.fvar x) (.fvar y) (.bvar 1) (.bvar 0))
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (mulPayload (.fvar (x+1)) (.fvar (y+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ,mulPayload] <;> mulCompactSyntax)
  let EE := E.shifted.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have out := mulOutputFromPayload EE (x+1) (y+1) 0 hh
  convert out using 1 <;> (dsimp [C,σ] <;> (try simp only [mulOutput]) <;> mulCompactSyntax)

#print axioms mulOutputFromExists
end M6.PA.RelationalSource.PairGraph

