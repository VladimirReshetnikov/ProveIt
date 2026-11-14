import PA194FoundationAdditionInduction
import PA194FoundationOrdinalInductionNumeric
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
def totalContext (base : Nat) : List Form := Ordinal.inductionContext (prefixProperty base)
def totalStatement (base : Nat) : Form :=
  sourceImply (Ordinal.domain (.fvar base)) (Ordinal.inductionConclusion (prefixProperty base))
def totalDerivation (base : Nat) : ND.Proof (totalContext base) (totalStatement base) := by
  apply impIntro
  let q : Form := Ordinal.domain (.fvar base)
  let Γ := q :: totalContext base
  let S : SetProofs Γ :=
    ⟨⟨⟨assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext]),
       assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext]),
       assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext])⟩,
       assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext])⟩,
      assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext]),
      assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext]),
      assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext])⟩
  exact prefixTotal S base (assumption (by simp [Γ,q]))
    (assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext]))
end M6.PA.RelationalSource.PairGraph
namespace PA194Logic.Relational.Source.PairGraph
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

def totalFoundationDerivation (base : Nat) : LO.FirstOrder.Derivation
    ((totalContext base).map Semiformula.neg ++ [totalStatement base]) :=
  (totalDerivation base).contra (by simp [ND.Proof])
noncomputable def totalSupplier (base : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+3+depth (∼prefixProperty base) ≤ z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget (totalFoundationDerivation base) ≤ z) :
    Proof (code (totalStatement base) f lo z) := by
  apply compileFoundationContext (totalContext base) (totalStatement base)
    (totalFoundationDerivation base) f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases h : p ∈ exactContext
  · exact graphContextSupplier f lo z hlo hz hadj p h
  by_cases hi : p = M6.PA.RelationalSource.Ordinal.intersectionFormula
  · subst p; exact Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
  have hs : p = separationFormula (∼prefixProperty base) := by
    simpa [totalContext,M6.PA.RelationalSource.Ordinal.inductionContext,h,hi] using hp
  subst p
  exact separationSupplier (∼prefixProperty base) f lo z hlo hf hsep
#print axioms totalFoundationDerivation
#print axioms totalSupplier
end PA194Logic.Relational.Source.PairGraph
