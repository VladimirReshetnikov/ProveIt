import PA194FoundationAdditionInductionBase
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix
set_option maxHeartbeats 1200000 in
def prefixInductionStep {Γ : List Form} (S : SetProofs Γ) (base : Nat) :
    ND.Proof Γ (Ordinal.inductionStep (prefixProperty base)) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏ addPrefixExists (.fvar 1) (.fvar (base+1+1))))
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have ss := S.shift.shift.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have out := prefixExistsStep ss 1 0 (base+1+1) (andLeft hd)
    (andLeft (andRight (andRight hd))) (andRight (andRight (andRight hd)))
  have h := impIntro out
  convert h using 1 <;> (dsimp [d]; simp only [Ordinal.inductionStep,Ordinal.traceProperty,prefixProperty]; prefixSyntax)

#print axioms prefixInductionStep
end M6.PA.RelationalSource.PairGraph
