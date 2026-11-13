module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedOrdinaryRefutation
@[expose] public section

/-! Explicit finite numerical bounds exist; no proof premise is hidden here. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def functionBudgetBound (lo : Nat) : Nat :=
  (lo+7) + (lo+4+depth (strictEntryProperty (n := 0) (.fvar 0))) + (lo+4+depth (domainEntryProperty (n := 0) (.fvar 0))) + (lo+3+depth (∼addCoherenceProperty)) + (lo+3+depth (∼mulCoherenceProperty)) + (lo+4+depth (∼prefixProperty 0)) + (lo+4+depth (∼mulPrefixProperty 0)) + (lo+3+lkBudget adjunctionDerivation) + (lo+lkBudget addCoherenceDerivation) + (lo+lkBudget mulCoherenceDerivation) + (lo+lkBudget zeroInhabitedDerivation) + (lo+1+lkBudget (Ordinal.domainSuccessorDerivation (.fvar 0))) + (lo+1+lkBudget (addTotalDerivation 0)) + (lo+1+lkBudget (mulTotalDerivation 0)) + 1

theorem FunctionCongruenceBudgets.of_bound (f : Nat → Nat) (lo z : Nat) (hlo : 0<lo) (hf : ∀i,f i<lo)
    (hz : functionBudgetBound lo ≤ z) : FunctionCongruenceBudgets f lo z := by
  dsimp [functionBudgetBound] at hz
  constructor
  · exact hlo
  · exact hf
  all_goals (try simp only [Nat.reduceAdd] at *) <;> omega

def commutativityBudgetBound (lo : Nat) : Nat :=
  (lo+9) + (lo+4+depth (domainEntryProperty (n := 0) (.fvar 0))) + (lo+3+depth (∼addRightZeroProperty)) + (lo+3+depth (∼addRightSuccessorProperty)) + (lo+3+depth (∼identityProperty)) + (lo+8+depth (∼compositionProperty 1 0 (2+1+1))) + (lo+4+depth (∼prefixProperty 0)) + (lo+3+depth (∼addCommutativityProperty)) + (lo+5+lkBudget adjunctionDerivation) + (lo+lkBudget identityDerivation) + (lo+lkBudget addRightZeroDerivation) + (lo+lkBudget addRightSuccessorDerivation) + (lo+3+lkBudget (compositionTransitivityDerivation 2 1 0)) + (lo+1+lkBudget (addTotalDerivation 0)) + (lo+1+lkBudget (Ordinal.domainSuccessorDerivation (.fvar 0))) + 1

theorem AdditionCommutativityBudget.of_bound (f : Nat → Nat) (lo z : Nat) (hlo : 0<lo) (hf : ∀i,f i<lo)
    (hz : commutativityBudgetBound lo ≤ z) : AdditionCommutativityBudget f lo z := by
  dsimp [commutativityBudgetBound] at hz
  constructor
  · exact hlo
  · exact hf
  all_goals (try simp only [Nat.reduceAdd] at *) <;> omega

end M6.PA.ForwardRelational

