import PA194FoundationAdditionOutputExists
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix

def addOutputConclusion (base : Nat) : Form :=
  ∀⁰ (Ordinal.domain (.bvar 0) 🡒 addOutput (.bvar 0) (.fvar base))

set_option maxHeartbeats 600000 in
def prefixTotalAt {Γ : List Form} (base x : Nat)
    (h : ND.Proof Γ (Ordinal.inductionConclusion (prefixProperty base)))
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x))) :
    ND.Proof Γ (addPrefixExists (.fvar x) (.fvar base)) := by
  have hh : ND.Proof Γ (Ordinal.domain (.fvar x) 🡒 addPrefixExists (.fvar x) (.fvar base)) := by
    convert allElim _ (.fvar x) h using 1 <;>
      (simp only [Ordinal.inductionConclusion,prefixProperty]; prefixSyntax)
  exact mp hx hh

set_option maxHeartbeats 600000 in
def outputConclusionFromPrefix {Γ : List Form} (E : FormulaEquality Γ) (base : Nat)
    (h : ND.Proof Γ (Ordinal.inductionConclusion (prefixProperty base))) :
    ND.Proof Γ (addOutputConclusion base) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have hs : ND.Proof (shifted Γ) (Ordinal.inductionConclusion (prefixProperty (base+1))) := by
    convert shiftProof h using 1 <;>
      (simp only [Ordinal.inductionConclusion,prefixProperty]; prefixSyntax)
  have hp := prefixTotalAt (base+1) 0 (up hs d) hd
  have out := impIntro (addOutputFromExists (E.shifted.weaken (fun p hh => List.mem_cons_of_mem d hh)) 0 (base+1) hp)
  convert out using 1 <;> (dsimp [d] <;> (try simp only [addOutputConclusion,addOutput]) <;> prefixSyntax)

#print axioms prefixTotalAt
#print axioms outputConclusionFromPrefix
end M6.PA.RelationalSource.PairGraph

