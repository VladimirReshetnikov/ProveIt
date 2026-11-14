import PA194FoundationAdditionZeroLaw
import PA194FoundationGraphContext
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
def zeroLawStatement (x base out : Nat) : Form :=
  sourceImply (Ordinal.zero (.fvar x))
    (sourceImply (addResult (.fvar x) (.fvar base) (.fvar out)) (eq (.fvar out) (.fvar base)))
def zeroLawDerivation (x base out : Nat) : ND.Proof exactContext (zeroLawStatement x base out) := by
  apply impIntro
  apply impIntro
  let z : Form := Ordinal.zero (.fvar x)
  let r : Form := addResult (.fvar x) (.fvar base) (.fvar out)
  let Γ := r :: z :: exactContext
  let E : FormulaEquality Γ :=
    ⟨⟨assumption (by simp [Γ, exactContext]),
       assumption (by simp [Γ, exactContext]),
       assumption (by simp [Γ, exactContext])⟩,
       assumption (by simp [Γ, exactContext])⟩
  exact addResultZeroOutput E x base out (assumption (by simp [Γ,z])) (assumption (by simp [Γ,r]))
end M6.PA.RelationalSource.PairGraph
namespace PA194Logic.Relational.Source.PairGraph
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

def zeroLawFoundationDerivation (x base out : Nat) : LO.FirstOrder.Derivation
    (exactContext.map Semiformula.neg ++ [zeroLawStatement x base out]) :=
  (zeroLawDerivation x base out).contra (by simp [ND.Proof])
noncomputable def zeroLawSupplier (x base out : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget (zeroLawFoundationDerivation x base out) ≤ z) :
    Proof (code (zeroLawStatement x base out) f lo z) :=
  compileGraphContext _ (zeroLawFoundationDerivation x base out) f lo z hlo hf hz hadj hbudget
#print axioms zeroLawFoundationDerivation
#print axioms zeroLawSupplier
end PA194Logic.Relational.Source.PairGraph
