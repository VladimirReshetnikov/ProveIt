module
public import PA196.Program
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Machine.EndpointInternalCodedSourceFrame
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 PA196.Arithmetic.Machine.PA
open PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Symbolic PhysicalRegisters
attribute [local irreducible] PA196.Program.sites program selectValue
section Models
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

lemma lookup_bound {i : Nat} {s : Source.Site} (hs : PA196.Program.sites[i]?=some s) : i<3812 := by
  have hi := Array.getElem?_eq_some_iff.mp hs
  simpa only [PA196.Program.sites_count] using hi.1

lemma refines_valid {c n xs : V} {m : ModelConf V} (h : Refines c n xs m) : ValidState c := by
  obtain ⟨i,s,hs,hpc,hm⟩ := frames_cases h.2.2.2
  refine ⟨h.1,?_⟩
  rw [hpc]
  have hi := lookup_bound hs
  exact_mod_cast (show i+1<3813 by omega)

lemma step_cyclic_calibration (c : V) (i : Nat) (hi : i<3812)
    (hc : PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource.control c=((i+1 : Nat) : V)) (hv : ValidStore (store c)) :
    PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource.control (stepValue c)=
      (controlCode (PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.cycleStep ⟨.at i,registers (store c)⟩).control : V) ∧
    registers (store (stepValue c))=
      (PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.cycleStep ⟨.at i,registers (store c)⟩).registers := by
  obtain ⟨inst,hr⟩ := literal_resolved i hi
  have hz : PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource.control c≠0 := by rw [hc]; exact_mod_cast (show i+1≠0 by omega)
  have hm : PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource.control c≠3813 := by rw [hc]; exact_mod_cast (show i+1≠3813 by omega)
  have he : stepValue c=instructionValue inst (store c) := by
    rw [stepValue,if_neg (not_or_intro hz hm),hc,select_program i hi,hr]
    rfl
  rw [he]
  simpa only [PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.cycleStep,PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.step,hr] using instruction_calibration inst (store c) hv

/-- One actual coded literal step either reaches dense machine halt, or gives
positive physical progress and the full successor refinement. No spare file
cells are projected away; the existential file retains its whole HFS value. -/
theorem physical_step {c n xs : V} {m : ModelConf V} (h : Refines c n xs m) :
    (∃ k qs ls rs lf rf, 0<k ∧ Segment k qs ls rs m.q m.left m.right 215 lf rf) ∨
    ∃ n' xs' m', Refines (stepValue c) n' xs' m' ∧ Progress true m m' := by
  obtain ⟨i,s,hs,hpc,hm⟩ := frames_cases h.2.2.2
  have hi := lookup_bound hs
  obtain ⟨inst,hr,himpl⟩ := PA196.Arithmetic.Machine.OriginalModelCoverage.coverage i hi
  by_cases ht : inst=.halt
  · subst inst
    left
    rw [hm]
    exact himpl n xs h.2.1
  · right
    have hp : ModelPrimitive.Progress PA196.Arithmetic.Machine.OriginalCheck.path 3812 (PA196.Arithmetic.Machine.OriginalCheck.path i) inst n xs := by
      cases inst with
      | halt => exact False.elim (ht rfl)
      | inc r j => exact himpl n xs h.2.1
      | dec r z j => exact himpl n xs h.2.1
      | jump j => exact himpl n xs h.2.1
    obtain ⟨k,n',xs',hk,hsize,hcycle,hprogress⟩ := hp
    have he : PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.cycleStep ⟨.at i,readFile xs⟩ =
        PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.restart (PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.execute inst (readFile xs)) := by
      simp only [PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.cycleStep,PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.step,hr]
    have hc := step_cyclic_calibration c i hi hpc h.1
    rw [h.2.2.1,he,hcycle] at hc
    change PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource.control (stepValue c)=((k+1 : Nat) : V) ∧
      registers (store (stepValue c))=readFile xs' at hc
    have hk' : k<PA196.Program.sites.size := by rw [PA196.Program.sites_count]; exact hk
    let next := PA196.Program.sites[k]
    have hn : PA196.Program.sites[k]?=some next := Array.getElem?_eq_getElem hk'
    refine ⟨n',xs',PhysicalFrame.frame (PA196.Arithmetic.Machine.OriginalCheck.path k) n' xs',?_,?_⟩
    · refine ⟨(step_valid c (refines_valid h)).1,hsize,hc.2,?_⟩
      rw [hc.1]
      exact frames_at k next hn n' xs'
    · simpa only [hm] using hprogress

end Models
#print axioms refines_valid
#print axioms step_cyclic_calibration
#print axioms physical_step
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

