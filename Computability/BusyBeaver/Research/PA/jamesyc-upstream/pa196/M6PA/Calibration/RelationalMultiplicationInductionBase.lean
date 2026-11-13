module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationPrefixStep
public import M6PA.Calibration.RelationalMultiplicationZeroExistence
public import M6PA.Calibration.RelationalOrdinalInductionUniform
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix

def mulPrefixProperty (base : Nat) : Formula 1 := mulPrefixExists (.bvar 0) (.fvar base)

set_option maxHeartbeats 600000 in
def mulPrefixInductionBase {Γ : List Form} (S : SetProofs Γ) (base : Nat) :
    ND.Proof Γ (Ordinal.inductionBase (mulPrefixProperty base)) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  let SS := S.shift.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have out := mulZeroPrefixWitness SS.equality 0 (base+1) (andRight hd) SS.empty SS.adjunction
  have h := impIntro out
  convert h using 1 <;> (dsimp [d]; simp only [Ordinal.inductionBase,mulPrefixProperty]; mulCompactSyntax)

#print axioms mulPrefixInductionBase
end M6.PA.RelationalSource.PairGraph

