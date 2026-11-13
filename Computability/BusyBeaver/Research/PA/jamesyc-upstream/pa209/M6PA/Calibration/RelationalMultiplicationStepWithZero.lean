module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationEndpoint
public import M6PA.Calibration.RelationalMultiplicationPrefixIntro
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

def mulStepWithZero {Γ : List Form} (S : SetProofs Γ)
    (top u base z g : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g)))
    (hadd : ND.Proof Γ (addOutputConclusion base)) :
    ND.Proof Γ (mulPrefixExists (.fvar u) (.fvar base)) := by
  apply exsElim (mulGraphFromPrefix S top u base z g ht hs hp hadd)
  let σ : Formula 1 := mulPrefix (.fvar u) (.fvar base) (.fvar z) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (mulPrefix (.fvar (u+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> mulCompactSyntax)
  have out := mulPrefixExistsIntro (u+1) (base+1) (z+1) 0 (up (Ordinal.zeroShift z hz) σ.free) hh
  convert out using 1 <;> (dsimp [C,σ] <;> mulWitnessSyntax)

#print axioms mulStepWithZero
end M6.PA.RelationalSource.PairGraph
