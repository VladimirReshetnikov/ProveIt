module
public meta import Lean
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceMPFinishStores
public import M6.Source.MPSuccessPush
import all M6.Source.MPCommand
public import M6.Source.MPCommand
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
meta section
open Lean Elab Tactic in
elab "exact_retained_mp_return" : tactic => do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name,_) =>
    if name.toString.startsWith "_private.M6.Source.MPCommand." &&
      name.toString.endsWith ".return_row" then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| exact $(mkIdent name)))
  | _ => throwError "Expected one retained MP return-row theorem"
end
lemma mp_return_bound : Source.resolveAt Source.exactSites 3910=some (.jump (some 0)) := by exact_retained_mp_return
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma mp_return_step (xs : V) : stepValue (stateCode 3911 xs)=stateCode 1 xs := by
  have h := literal_step 3910 (by decide) _ mp_return_bound xs
  simpa only [instructionValue,destinationCode,Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using h
lemma mp_return_trace (xs : V) : Trace 1 ?[stateCode 3911 xs,stateCode 1 xs] (stateCode 3911 xs) (stateCode 1 xs) := by
  simpa only [mp_return_step] using trace_one (stateCode 3911 xs)
theorem actual_mp_success (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 3885 xs) (stateCode 1 (mpSuccessEnd xs)) := by
  have pushed : ∃n cs,0<n ∧ Trace n cs (stateCode 3885 xs) (stateCode 3904 (pushEnd xs)) :=
    push 3859 (by decide) Source.MPSuccessPush.bound xs hv hx hy
  obtain ⟨np,ps,hp,hP⟩ := pushed
  have pd : registers (pushEnd xs) 4=registers xs 4 := by rw [pushEnd_registers xs hv]; simp [PhysicalRegisters.write]
  have px : registers (pushEnd xs) 6=0 := by rw [pushEnd_registers xs hv]; simp [PhysicalRegisters.write,hx]
  have copied : ∃cs,Trace ((4*registers xs 4+1)+(3*registers xs 4+1)) cs
      (stateCode 3904 (pushEnd xs)) (stateCode 3911 (mpSuccessEnd xs)) := by
    exact copy_loop 3903 4 (by decide) (by decide) (by decide) Source.MPCopy.last_bound
      (registers xs 4) _ (pushEnd_valid xs hv) pd px
  obtain ⟨cs,hC⟩ := copied
  obtain ⟨ds,hd⟩ := trace_compose hP hC
  obtain ⟨es,he⟩ := trace_compose hd (mp_return_trace (mpSuccessEnd xs))
  exact ⟨np+((4*registers xs 4+1)+(3*registers xs 4+1))+1,es,by simp,he⟩
#print axioms mp_return_bound
#print axioms actual_mp_success
end M6.Arithmetic.PA.InternalTrace.CodedSource

