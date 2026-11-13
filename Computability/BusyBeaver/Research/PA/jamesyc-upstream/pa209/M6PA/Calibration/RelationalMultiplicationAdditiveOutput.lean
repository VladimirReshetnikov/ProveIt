module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationGraphExistence
public import M6PA.Calibration.RelationalAdditionApplications
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

/-- Eliminate a real ordinal-valued additive result, rather than postulate a
multiplication value. The additive totality supplier is exposed upstream. -/
def mulGraphFromAddOutput {Γ : List Form} (S : SetProofs Γ)
    (top u base z g c : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c)))
    (ha : ND.Proof Γ (addOutput (.fvar c) (.fvar base))) :
    ND.Proof Γ (mulGraphExists (.fvar u) (.fvar base) (.fvar z)) := by
  apply exsElim ha
  let σ : Formula 1 := Ordinal.domain (.bvar 0) ⋏ addResult (.fvar c) (.fvar base) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hv : ND.Proof C (Ordinal.domain (.fvar 0) ⋏ addResult (.fvar (c+1)) (.fvar (base+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> mulCompactSyntax)
  let SS := S.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have out := mulGraphFromOutputs SS (top+1) (u+1) (base+1) (z+1) (g+1) (c+1) 0
    (up (domainShift top ht) σ.free) (up (Ordinal.successorShift top u hs) σ.free)
    (up (mulPrefixShift top base z g hp) σ.free) (up (edgeShift g top c he) σ.free)
    (andRight hv) (andLeft hv)
  convert out using 1 <;> (dsimp [C,σ] <;> (try simp only [addOutput]) <;> mulWitnessSyntax)

#print axioms mulGraphFromAddOutput
end M6.PA.RelationalSource.PairGraph
