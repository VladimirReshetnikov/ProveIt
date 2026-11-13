module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationAdditiveOutput
public import M6PA.Calibration.RelationalMultiplicationAdditiveShift
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

/-- The finite additive-output conclusion is an explicit premise. The old
multiplication endpoint and the new graph are both actually constructed. -/
def mulGraphFromPrefix {Γ : List Form} (S : SetProofs Γ)
    (top u base z g : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g)))
    (hadd : ND.Proof Γ (addOutputConclusion base)) :
    ND.Proof Γ (mulGraphExists (.fvar u) (.fvar base) (.fvar z)) := by
  have parts := hp
  unfold mulPrefix at parts
  have he := mp (ND.orRight (S.equality.reflexive (.fvar top)))
    (andRight (graphDomainAt top g top (andLeft parts)))
  apply exsElim he
  let σ : Formula 1 := edge (.fvar g) (.fvar top) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (g+1)) (.fvar (top+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> mulCompactSyntax)
  let SS := S.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have pp := up (mulPrefixShift top base z g hp) σ.free
  have ppParts := pp
  unfold mulPrefix at ppParts
  have hc := graphRangeAt (g+1) (top+1) 0 (andLeft (andRight (andRight ppParts))) hh
  have aa := addOutputAt (base+1) 0 (up (mulAddOutputConclusionShift base hadd) σ.free) hc
  have out := mulGraphFromAddOutput SS (top+1) (u+1) (base+1) (z+1) (g+1) 0
    (up (domainShift top ht) σ.free) (up (Ordinal.successorShift top u hs) σ.free) pp hh aa
  convert out using 1 <;> (dsimp [C,σ] <;> mulWitnessSyntax)

#print axioms mulGraphFromPrefix
end M6.PA.RelationalSource.PairGraph
