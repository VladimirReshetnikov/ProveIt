module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationOutputExists
public import M6PA.Calibration.RelationalMultiplicationTotalSupplier
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

def mulOutputConclusion (base : Nat) : Form :=
  ∀¹ (Ordinal.domain (.bvar 0) 🡒 mulOutput (.bvar 0) (.fvar base))

def mulPrefixTotalAt {Γ : List Form} (base x : Nat)
    (h : ND.Proof Γ (Ordinal.inductionConclusion (mulPrefixProperty base)))
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x))) :
    ND.Proof Γ (mulPrefixExists (.fvar x) (.fvar base)) := by
  have hh : ND.Proof Γ (Ordinal.domain (.fvar x) 🡒 mulPrefixExists (.fvar x) (.fvar base)) := by
    convert allElim _ (.fvar x) h using 1 <;>
      (simp only [Ordinal.inductionConclusion,mulPrefixProperty]; mulCompactSyntax)
  exact mp hx hh

def mulOutputConclusionFromPrefix {Γ : List Form} (E : FormulaEquality Γ) (base : Nat)
    (h : ND.Proof Γ (Ordinal.inductionConclusion (mulPrefixProperty base))) :
    ND.Proof Γ (mulOutputConclusion base) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have hs : ND.Proof (shifted Γ) (Ordinal.inductionConclusion (mulPrefixProperty (base+1))) := by
    convert shiftProof h using 1 <;>
      (simp only [Ordinal.inductionConclusion,mulPrefixProperty]; mulCompactSyntax)
  have hp := mulPrefixTotalAt (base+1) 0 (up hs d) hd
  have out := impIntro (mulOutputFromExists (E.shifted.weaken (fun p hh => List.mem_cons_of_mem d hh)) 0 (base+1) hp)
  convert out using 1 <;> (dsimp [d] <;> (try simp only [mulOutputConclusion,mulOutput]) <;> mulCompactSyntax)

#print axioms mulPrefixTotalAt
#print axioms mulOutputConclusionFromPrefix
end M6.PA.RelationalSource.PairGraph

