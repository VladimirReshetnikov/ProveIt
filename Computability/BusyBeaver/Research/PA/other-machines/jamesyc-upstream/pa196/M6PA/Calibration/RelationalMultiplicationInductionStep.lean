module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationInductionBase
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000 in
def mulPrefixInductionStep {Γ : List Form} (S : SetProofs Γ) (base : Nat)
    (hadd : ND.Proof Γ (addOutputConclusion base)) :
    ND.Proof Γ (Ordinal.inductionStep (mulPrefixProperty base)) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏ mulPrefixExists (.fvar 1) (.fvar (base+1+1))))
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  let SS := S.shift.shift.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have ha := up (mulAddOutputConclusionShift (base+1) (mulAddOutputConclusionShift base hadd)) d
  have out := mulPrefixExistsStep SS 1 0 (base+1+1) (andLeft hd)
    (andLeft (andRight (andRight hd))) (andRight (andRight (andRight hd))) ha
  have h := impIntro out
  convert h using 1 <;> (dsimp [d]; simp only [Ordinal.inductionStep,Ordinal.traceProperty,mulPrefixProperty]; mulCompactSyntax)

  all_goals simp only [← Semiformula.neg_eq,Semiformula.rewAux_neg,mulPrefix_rew]
  all_goals finishSourceSyntax

#print axioms mulPrefixInductionStep
end M6.PA.RelationalSource.PairGraph

