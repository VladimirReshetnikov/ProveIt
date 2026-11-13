module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationOutputPrefix
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

def mulOutputFromPayload {Γ : List Form} (E : FormulaEquality Γ) (x y z : Nat)
    (hp : ND.Proof Γ (mulPayload (.fvar x) (.fvar y) (.fvar z))) :
    ND.Proof Γ (mulOutput (.fvar x) (.fvar y)) := by
  apply exsElim hp
  let σ : Formula 1 := Ordinal.zero (.fvar z) ⋏ mulPrefix (.fvar x) (.fvar y) (.fvar z) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (Ordinal.zero (.fvar (z+1)) ⋏ mulPrefix (.fvar (x+1)) (.fvar (y+1)) (.fvar (z+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> mulCompactSyntax)
  let EE := E.shifted.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have out := mulOutputFromPrefix EE (x+1) (y+1) (z+1) 0 (andLeft hh) (andRight hh)
  convert out using 1 <;> (dsimp [C,σ,mulPayload] <;> (try simp only [mulOutput]) <;> mulCompactSyntax)

#print axioms mulOutputFromPayload
end M6.PA.RelationalSource.PairGraph

