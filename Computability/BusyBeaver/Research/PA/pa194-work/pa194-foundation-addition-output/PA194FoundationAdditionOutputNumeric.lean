import PA194FoundationAdditionOutputTotal
import PA194FoundationAdditionTotalNumeric
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
def outputStatement (base : Nat) : Form :=
  sourceImply (Ordinal.domain (.fvar base)) (addOutputConclusion base)
def outputDerivation (base : Nat) : ND.Proof (totalContext base) (outputStatement base) := by
  apply impIntro
  let q : Form := Ordinal.domain (.fvar base)
  let Γ := q :: totalContext base
  let E : FormulaEquality Γ :=
    ⟨⟨assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext]),
       assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext]),
       assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext])⟩,
       assumption (by simp [Γ, totalContext, Ordinal.inductionContext, exactContext])⟩
  have ht : ND.Proof Γ (Ordinal.inductionConclusion (prefixProperty base)) :=
    mp (assumption (by simp [Γ,q])) (weaken (totalDerivation base) (by intro x hx; simp [Γ,hx]))
  exact outputConclusionFromPrefix E base ht
end M6.PA.RelationalSource.PairGraph
namespace PA194Logic.Relational.Source.PairGraph
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

def outputFoundationDerivation (base : Nat) : LO.FirstOrder.Derivation
    ((totalContext base).map Semiformula.neg ++ [outputStatement base]) :=
  (outputDerivation base).contra (by simp [ND.Proof])
noncomputable def outputSupplier (base : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+3+depth (∼prefixProperty base) ≤ z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget (outputFoundationDerivation base) ≤ z) :
    Proof (code (outputStatement base) f lo z) := by
  apply compileFoundationContext (totalContext base) (outputStatement base)
    (outputFoundationDerivation base) f lo z hlo hf hbudget
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
#print axioms outputFoundationDerivation
#print axioms outputSupplier
end PA194Logic.Relational.Source.PairGraph
