import PA194FoundationOrdinalInductionUniform
import PA194FoundationGraphContext
import PA194SourceIntersection
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND
open M6.PA.RelationalSource.PairGraph

def inductionContext (p : Formula 1) : List Form :=
  exactContext ++ [intersectionFormula, separationFormula (∼p)]
def inductionStatement (p : Formula 1) : Form :=
  sourceImply (inductionBase p) (sourceImply (inductionStep p) (inductionConclusion p))
def inductionDerivation (p : Formula 1) : ND.Proof (inductionContext p) (inductionStatement p) := by
  apply impIntro
  apply impIntro
  let Γ := inductionStep p :: inductionBase p :: inductionContext p
  let e : EqualityProofs Γ :=
    ⟨assumption (by simp [Γ, inductionContext, exactContext]),
     assumption (by simp [Γ, inductionContext, exactContext]),
     assumption (by simp [Γ, inductionContext, exactContext])⟩
  exact uniformInduction e p
    (assumption (by simp [Γ, inductionContext, exactContext]))
    (assumption (by simp [Γ, inductionContext, exactContext]))
    (assumption (by simp [Γ, inductionContext, exactContext]))
    (assumption (by simp [Γ, inductionContext, exactContext]))
    (assumption (by simp [Γ])) (assumption (by simp [Γ]))
end M6.PA.RelationalSource.Ordinal
namespace PA194Logic.Relational.Source.Ordinal
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal
open M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

def inductionFoundationDerivation (p : Formula 1) : LO.FirstOrder.Derivation
    ((inductionContext p).map Semiformula.neg ++ [inductionStatement p]) :=
  (inductionDerivation p).contra (by simp [ND.Proof])

noncomputable def inductionSupplier (p : Formula 1) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+3+depth (∼p) ≤ z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget (inductionFoundationDerivation p) ≤ z) :
    Proof (code (inductionStatement p) f lo z) := by
  apply compileFoundationContext (inductionContext p) (inductionStatement p)
    (inductionFoundationDerivation p) f lo z hlo hf hbudget
  intro q hq
  classical
  by_cases h : q ∈ exactContext
  · exact PairGraph.graphContextSupplier f lo z hlo hz hadj q h
  by_cases hi : q = intersectionFormula
  · subst q; exact intersectionAxiomSupplier f lo z hlo (by omega)
  have hs : q = separationFormula (∼p) := by
    simpa [inductionContext,h,hi] using hq
  subst q
  exact separationSupplier (∼p) f lo z hlo hf hsep
#print axioms inductionFoundationDerivation
#print axioms inductionSupplier
end PA194Logic.Relational.Source.Ordinal
