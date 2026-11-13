module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRestriction
public import M6PA.Calibration.RelationalSourceContext
@[expose] public section

/-! Actual-basis discharge of the literal Separation premise. Budgets remain
explicit. Closing a parameter happens only after discharging the ND context. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder NativeCalculus NativeCalculus.ActualBasis

def strictCutDerivation (top g : Nat) :
    ND.Proof [separationFormula (strictEntryProperty (.fvar top))]
      (strictGraphCutExists (.fvar top) (.fvar g)) :=
  strictCutExists top g (ND.assumption (by simp))

def strictCutSupplier (top g : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo)
    (hsep : lo+3+depth (strictEntryProperty (n := 0) (.fvar top)) ≤ z)
    (hbudget : lo+lkBudget (strictCutDerivation top g) ≤ z) :
    Proof (code (strictGraphCutExists (.fvar top) (.fvar g)) f lo z) := by
  apply compileContext _ _ (strictCutDerivation top g) f lo z hlo hf hbudget
  intro p hp
  have he : p = separationFormula (strictEntryProperty (.fvar top)) := by simpa using hp
  subst p
  exact separationSupplier _ f lo z hlo hf hsep

/-- One closed Separation schema can be specialized after new witnesses enter
    the proof context; no context with a free parameter is generalized. -/
def closedStrictSeparation : Proposition language :=
  closeParameter (separationFormula (strictEntryProperty (.fvar 0)))

def strictSeparationAt {Γ : List ND.Form} (top : Nat)
    (hs : ND.Proof Γ closedStrictSeparation) :
    ND.Proof Γ (separationFormula (strictEntryProperty (.fvar top))) := by
  have hh := specializeParameter (separationFormula (strictEntryProperty (.fvar 0)))
    (.fvar top) hs
  convert hh using 1 <;> restrictionSyntax

def strictCutFromClosedSeparation {Γ : List ND.Form} (top g : Nat)
    (hs : ND.Proof Γ closedStrictSeparation) :
    ND.Proof Γ (strictGraphCutExists (.fvar top) (.fvar g)) :=
  strictCutExists top g (strictSeparationAt top hs)

def strictCutClosedDerivation (top g : Nat) :
    ND.Proof [closedStrictSeparation] (strictGraphCutExists (.fvar top) (.fvar g)) :=
  strictCutFromClosedSeparation top g (ND.assumption (by simp))

def strictCutClosedSupplier (top g : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo)
    (hsep : lo+4+depth (strictEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hbudget : lo+lkBudget (strictCutClosedDerivation top g) ≤ z) :
    Proof (code (strictGraphCutExists (.fvar top) (.fvar g)) f lo z) := by
  apply compileContext _ _ (strictCutClosedDerivation top g) f lo z hlo hf hbudget
  intro p hp
  have he : p = closedStrictSeparation := by simpa using hp
  subst p
  exact closedSeparationSupplier _ f lo z hlo hf hsep

#print axioms strictCutClosedSupplier
#print axioms strictCutDerivation
#print axioms strictCutSupplier
#print axioms strictSeparationAt
#print axioms strictCutFromClosedSeparation
end M6.PA.RelationalSource.PairGraph
