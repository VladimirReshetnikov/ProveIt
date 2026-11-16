module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationStepWithZero
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

def mulPayload (top base z : Term n) : Formula n :=
  ∃¹ (Ordinal.zero (Rew.bShift z) ⋏ mulPrefix (Rew.bShift top) (Rew.bShift base) (Rew.bShift z) (.bvar 0))

def mulStepFromPayload {Γ : List Form} (S : SetProofs Γ)
    (top u base z : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (mulPayload (.fvar top) (.fvar base) (.fvar z)))
    (hadd : ND.Proof Γ (addOutputConclusion base)) :
    ND.Proof Γ (mulPrefixExists (.fvar u) (.fvar base)) := by
  apply exsElim hp
  let σ : Formula 1 := Ordinal.zero (.fvar z) ⋏ mulPrefix (.fvar top) (.fvar base) (.fvar z) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (Ordinal.zero (.fvar (z+1)) ⋏
      mulPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> mulCompactSyntax)
  let SS := S.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have out := mulStepWithZero SS (top+1) (u+1) (base+1) (z+1) 0
    (up (domainShift top ht) σ.free) (up (Ordinal.successorShift top u hs) σ.free)
    (andLeft hh) (andRight hh) (up (mulAddOutputConclusionShift base hadd) σ.free)
  convert out using 1 <;> (dsimp [C,σ,mulPayload] <;> mulCompactSyntax)

#print axioms mulStepFromPayload
end M6.PA.RelationalSource.PairGraph
