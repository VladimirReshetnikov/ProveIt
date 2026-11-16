module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationFrame
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

/-- Construct the graph rather than assume it: exact adjunction supplies all
new graph and Kuratowski-entry witnesses. The additive output remains explicit. -/
def mulGraphFromOutputs {Γ : List Form} (S : SetProofs Γ)
    (top u base z g c v : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c)))
    (ha : ND.Proof Γ (addResult (.fvar c) (.fvar base) (.fvar v)))
    (hv : ND.Proof Γ (Ordinal.domain (.fvar v))) :
    ND.Proof Γ (mulGraphExists (.fvar u) (.fvar base) (.fvar z)) := by
  apply exsElim (exactWitness S.equality.core S.equality.transitive g u v S.empty S.adjunction)
  let σ : Formula 1 := exactExtension (.fvar g) (.bvar 0) (.fvar u) (.fvar v)
  let C := σ.free :: shifted Γ
  have hx : ND.Proof C (exactExtension (.fvar (g+1)) (.fvar 0) (.fvar (u+1)) (.fvar (v+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> mulWitnessSyntax)
  let SS := S.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have out := mulExtendPrefix SS (top+1) (u+1) (base+1) (z+1) (g+1) (c+1) (v+1) 0
    (up (domainShift top ht) σ.free) (up (Ordinal.successorShift top u hs) σ.free)
    (up (mulPrefixShift top base z g hp) σ.free) (up (edgeShift g top c he) σ.free)
    (up (mulAddShift c base v ha) σ.free) (up (domainShift v hv) σ.free) hx
  apply exsIntro _ (.fvar 0)
  convert out using 1 <;> (dsimp [C,σ] <;> mulWitnessSyntax)

#print axioms mulGraphFromOutputs
end M6.PA.RelationalSource.PairGraph
