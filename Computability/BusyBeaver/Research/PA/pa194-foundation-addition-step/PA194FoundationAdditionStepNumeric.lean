import PA194FoundationAdditionPrefixStep
import PA194FoundationGraphContext
import PA194SourceIntersection
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
def stepContext : List Form := exactContext ++ [Ordinal.intersectionFormula]
def stepStatement (top u base : Nat) : Form :=
  sourceImply (Ordinal.domain (.fvar top) ⋏
    (Ordinal.successor (.fvar top) (.fvar u) ⋏ addPrefixExists (.fvar top) (.fvar base)))
    (addPrefixExists (.fvar u) (.fvar base))
def stepDerivation (top u base : Nat) : ND.Proof stepContext (stepStatement top u base) := by
  apply impIntro
  let q : Form := Ordinal.domain (.fvar top) ⋏
    (Ordinal.successor (.fvar top) (.fvar u) ⋏ addPrefixExists (.fvar top) (.fvar base))
  have hq : ND.Proof (q :: stepContext) q := assumption (by simp)
  let S : SetProofs (q :: stepContext) :=
    ⟨⟨⟨assumption (by simp [stepContext,exactContext]),
       assumption (by simp [stepContext,exactContext]),
       assumption (by simp [stepContext,exactContext])⟩,
       assumption (by simp [stepContext,exactContext])⟩,
      assumption (by simp [stepContext,exactContext]),
      assumption (by simp [stepContext,exactContext]),
      assumption (by simp [stepContext,exactContext])⟩
  exact prefixExistsStep S top u base (andLeft hq) (andLeft (andRight hq)) (andRight (andRight hq))
end M6.PA.RelationalSource.PairGraph
namespace PA194Logic.Relational.Source.PairGraph
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

def stepFoundationDerivation (top u base : Nat) : LO.FirstOrder.Derivation
    (stepContext.map Semiformula.neg ++ [stepStatement top u base]) :=
  (stepDerivation top u base).contra (by simp [ND.Proof])
noncomputable def stepSupplier (top u base : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget (stepFoundationDerivation top u base) ≤ z) :
    Proof (code (stepStatement top u base) f lo z) := by
  apply compileFoundationContext stepContext (stepStatement top u base)
    (stepFoundationDerivation top u base) f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases h : p ∈ exactContext
  · exact graphContextSupplier f lo z hlo hz hadj p h
  · have he : p = M6.PA.RelationalSource.Ordinal.intersectionFormula := by
      simpa [stepContext,h] using hp
    subst p
    exact Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
#print axioms stepFoundationDerivation
#print axioms stepSupplier
end PA194Logic.Relational.Source.PairGraph
