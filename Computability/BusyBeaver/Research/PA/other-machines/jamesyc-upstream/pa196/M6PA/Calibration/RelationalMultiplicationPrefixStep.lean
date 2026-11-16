module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationPayloadStep
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

/-- Successor prefix existence with the paid fixed-base additive conclusion
explicit. No universal generalization across a parameter-bearing context. -/
def mulPrefixExistsStep {Γ : List Form} (S : SetProofs Γ)
    (top u base : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (mulPrefixExists (.fvar top) (.fvar base)))
    (hadd : ND.Proof Γ (addOutputConclusion base)) :
    ND.Proof Γ (mulPrefixExists (.fvar u) (.fvar base)) := by
  apply exsElim hp
  let σ : Formula 1 := ∃¹ (Ordinal.zero (.bvar 1) ⋏
    mulPrefix (.fvar top) (.fvar base) (.bvar 1) (.bvar 0))
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (mulPayload (.fvar (top+1)) (.fvar (base+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ,mulPayload] <;> mulCompactSyntax)
  let SS := S.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have out := mulStepFromPayload SS (top+1) (u+1) (base+1) 0
    (up (domainShift top ht) σ.free) (up (Ordinal.successorShift top u hs) σ.free)
    hh (up (mulAddOutputConclusionShift base hadd) σ.free)
  convert out using 1 <;> (dsimp [C,σ] <;> mulCompactSyntax)

#print axioms mulPrefixExistsStep
end M6.PA.RelationalSource.PairGraph
