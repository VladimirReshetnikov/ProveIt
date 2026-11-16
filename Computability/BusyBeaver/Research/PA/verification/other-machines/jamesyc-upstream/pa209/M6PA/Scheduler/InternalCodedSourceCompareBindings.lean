module
public meta import Lean
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCompare
import all M6.Source.MPGuardSteps
public import M6.Source.MPGuardSteps
public import M6.Source.AXGateCompareSteps
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
/- Read-only resolution of the exact already checked private row theorem.
No environment declaration is changed; `exact` supplies an ordinary proof term. -/
meta section
open Lean Elab Tactic in
elab "exact_retained_mp_row " n:num : tactic => do
  let i := n.getNat
  unless 3871 ≤ i && i ≤ 3883 do throwError "Outside retained MP guard row range"
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name,_) =>
    if name.toString.startsWith "_private.M6.Source.MPGuardSteps." &&
      name.toString.endsWith (".row" ++ toString i) then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| exact $(mkIdent name)))
  | _ => throwError "Expected exactly one retained MP row theorem"
end
theorem mp_compare_bound : CompareBound 3874 3884 3910 := by
  intro ⟨j,hj⟩
  have hcases : j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8∨j=9 := by omega
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact_retained_mp_row 3874
  · exact_retained_mp_row 3875
  · exact_retained_mp_row 3876
  · exact_retained_mp_row 3877
  · exact_retained_mp_row 3878
  · exact_retained_mp_row 3879
  · exact_retained_mp_row 3880
  · exact_retained_mp_row 3881
  · exact_retained_mp_row 3882
  · exact_retained_mp_row 3883
lemma compareBound_of_AX (base : Nat) (hb : Source.AXGateCompare.Bound Source.exactSites base) :
    CompareBound base (base+10) (base+12) := by
  intro ⟨j,hj⟩
  have h := hb ⟨j,by omega⟩
  have hcases : j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8∨j=9 := by omega
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact h
#print axioms mp_compare_bound
#print axioms compareBound_of_AX
end M6.Arithmetic.PA.InternalTrace.CodedSource

