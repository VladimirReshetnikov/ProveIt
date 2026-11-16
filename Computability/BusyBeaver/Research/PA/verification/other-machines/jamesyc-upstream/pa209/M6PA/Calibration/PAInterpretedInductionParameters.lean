module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInduction
@[expose] public section

/-! Finite free-parameter guards for the interpreted schema. Parameter names
are taken from the actual source formula, not a globally covered environment. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

theorem termOccurrence_free {n : Nat} (t : SourceTerm n) (i : Nat)
    (h : TermOccurs (.inr i) t) : i ∈ t.freeVariables := by
  induction t with
  | bvar j => cases h
  | fvar j => cases h; simp [Semiterm.freeVariables]
  | func fn ts ih =>
    cases h with
    | func j hj =>
      simpa only [Semiterm.freeVariables_func,Finset.mem_biUnion,Finset.mem_univ,true_and]
        using (show ∃ j, i ∈ (ts j).freeVariables from ⟨j,ih j hj⟩)

theorem formulaOccurrence_free {n : Nat} (p : SourceFormula n) (i : Nat)
    (h : FormulaOccurs (.inr i) p) : i ∈ p.freeVariables := by
  induction p with
  | verum | falsum => cases h
  | rel r ts =>
    cases h with
    | rel j hj =>
      simp only [Semiformula.freeVariables_rel,Finset.mem_biUnion,Finset.mem_univ,true_and]
      exact ⟨j,termOccurrence_free (ts j) i hj⟩
  | nrel r ts =>
    cases h with
    | nrel j hj =>
      simp only [Semiformula.freeVariables_nrel,Finset.mem_biUnion,Finset.mem_univ,true_and]
      exact ⟨j,termOccurrence_free (ts j) i hj⟩
  | and p q hp hq =>
    cases h with
    | andLeft h => exact Finset.mem_union_left _ (hp h)
    | andRight h => exact Finset.mem_union_right _ (hq h)
  | or p q hp hq =>
    cases h with
    | orLeft h => exact Finset.mem_union_left _ (hp h)
    | orRight h => exact Finset.mem_union_right _ (hq h)
  | all p hp => cases h with | all h => exact hp h
  | exs p hp => cases h with | exs h => exact hp h

def inductionParameterGuard (is : List Nat) (f : Nat → Term 0) : Form :=
  match is with
  | [] => ⊤
  | i::is => Ordinal.domain (f i) ⋏ inductionParameterGuard is f

def inductionParameterGuardAt {Γ : List Form} (is : List Nat) (f : Nat → Term 0)
    (h : ND.Proof Γ (inductionParameterGuard is f)) (i : Nat) (hi : i ∈ is) :
    ND.Proof Γ (Ordinal.domain (f i)) := by
  induction is with
  | nil => simp at hi
  | cons j js ih =>
    by_cases he : i = j
    · subst i; exact andLeft h
    · exact ih (andRight h) ((List.mem_cons.mp hi).resolve_left he)

def inductionGuardCoverage {Γ : List Form} (p : SourceFormula 1) (f : Nat → Term 0)
    (h : ND.Proof Γ (inductionParameterGuard (p.freeVariables.sort (· ≤ ·)) f)) :
    InductionParameterCoverage Γ p f := by
  intro i hi
  exact inductionParameterGuardAt _ f h i ((Finset.mem_sort (· ≤ ·)).mpr (formulaOccurrence_free p i hi))

#print axioms formulaOccurrence_free
#print axioms inductionGuardCoverage
end M6.PA.ForwardRelational
