module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRestrictionInclusive
public import M6PA.Calibration.RelationalSourceContext
@[expose] public section

/-! Actual-basis discharge of the literal Separation premise. Budgets remain
explicit. Closing a parameter happens only after discharging the ND context. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder NativeCalculus NativeCalculus.ActualBasis

def inclusiveCutDerivation (top g : Nat) :
    ND.Proof [separationFormula (domainEntryProperty (.fvar top))]
      (inclusiveGraphCutExists (.fvar top) (.fvar g)) :=
  inclusiveCutExists top g (ND.assumption (by simp))

def inclusiveCutSupplier (top g : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo)
    (hsep : lo+3+depth (domainEntryProperty (n := 0) (.fvar top)) ≤ z)
    (hbudget : lo+lkBudget (inclusiveCutDerivation top g) ≤ z) :
    Proof (code (inclusiveGraphCutExists (.fvar top) (.fvar g)) f lo z) := by
  apply compileContext _ _ (inclusiveCutDerivation top g) f lo z hlo hf hbudget
  intro p hp
  have he : p = separationFormula (domainEntryProperty (.fvar top)) := by simpa using hp
  subst p
  exact separationSupplier _ f lo z hlo hf hsep

/-- One closed Separation schema can be specialized after new witnesses enter
    the proof context; no context with a free parameter is generalized. -/
def closedInclusiveSeparation : Proposition language :=
  closeParameter (separationFormula (domainEntryProperty (.fvar 0)))

def inclusiveSeparationAt {Γ : List ND.Form} (top : Nat)
    (hs : ND.Proof Γ closedInclusiveSeparation) :
    ND.Proof Γ (separationFormula (domainEntryProperty (.fvar top))) := by
  have hh := specializeParameter (separationFormula (domainEntryProperty (.fvar 0)))
    (.fvar top) hs
  convert hh using 1 <;> inclusiveRestrictionSyntax

def inclusiveCutFromClosedSeparation {Γ : List ND.Form} (top g : Nat)
    (hs : ND.Proof Γ closedInclusiveSeparation) :
    ND.Proof Γ (inclusiveGraphCutExists (.fvar top) (.fvar g)) :=
  inclusiveCutExists top g (inclusiveSeparationAt top hs)

def inclusiveCutClosedDerivation (top g : Nat) :
    ND.Proof [closedInclusiveSeparation] (inclusiveGraphCutExists (.fvar top) (.fvar g)) :=
  inclusiveCutFromClosedSeparation top g (ND.assumption (by simp))

def inclusiveCutClosedSupplier (top g : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo)
    (hsep : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hbudget : lo+lkBudget (inclusiveCutClosedDerivation top g) ≤ z) :
    Proof (code (inclusiveGraphCutExists (.fvar top) (.fvar g)) f lo z) := by
  apply compileContext _ _ (inclusiveCutClosedDerivation top g) f lo z hlo hf hbudget
  intro p hp
  have he : p = closedInclusiveSeparation := by simpa using hp
  subst p
  exact closedSeparationSupplier _ f lo z hlo hf hsep

#print axioms inclusiveCutClosedSupplier
#print axioms inclusiveCutDerivation
#print axioms inclusiveCutSupplier
#print axioms inclusiveSeparationAt
#print axioms inclusiveCutFromClosedSeparation
end M6.PA.RelationalSource.PairGraph
