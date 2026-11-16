module
public import M6PA.Model.PATheory
public import M6PA.Model.EndpointInternalCodedSourceFrame
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.Arithmetic.PA
open M6.Arithmetic.PA.InternalTrace.CodedSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Symbolic PhysicalRegisters
attribute [local irreducible] Source.exactSites program selectValue
section Models
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

lemma lookup_bound {i : Nat} {s : Source.Site} (hs : Source.exactSites[i]?=some s) : i<3947 := by
  have hi := Array.getElem?_eq_some_iff.mp hs
  simpa only [Source.exactSites_count] using hi.1

lemma refines_valid {c n xs : V} {m : ModelConf V} (h : Refines c n xs m) : ValidState c := by
  obtain ⟨i,s,hs,hpc,hm⟩ := frames_cases h.2.2.2
  refine ⟨h.1,?_⟩
  rw [hpc]
  have hi := lookup_bound hs
  exact_mod_cast (show i+1<3948 by omega)

lemma step_cyclic_calibration (c : V) (i : Nat) (hi : i<3947)
    (hc : M6.Arithmetic.PA.InternalTrace.CodedSource.control c=((i+1 : Nat) : V)) (hv : ValidStore (store c)) :
    M6.Arithmetic.PA.InternalTrace.CodedSource.control (stepValue c)=
      (controlCode (M6.Arithmetic.PA.InternalTrace.ModelSource.cycleStep ⟨.at i,registers (store c)⟩).control : V) ∧
    registers (store (stepValue c))=
      (M6.Arithmetic.PA.InternalTrace.ModelSource.cycleStep ⟨.at i,registers (store c)⟩).registers := by
  obtain ⟨inst,hr⟩ := literal_resolved i hi
  have hz : M6.Arithmetic.PA.InternalTrace.CodedSource.control c≠0 := by rw [hc]; exact_mod_cast (show i+1≠0 by omega)
  have hm : M6.Arithmetic.PA.InternalTrace.CodedSource.control c≠3948 := by rw [hc]; exact_mod_cast (show i+1≠3948 by omega)
  have he : stepValue c=instructionValue inst (store c) := by
    rw [stepValue,if_neg (not_or_intro hz hm),hc,select_program i hi,hr]
    rfl
  rw [he]
  simpa only [M6.Arithmetic.PA.InternalTrace.ModelSource.cycleStep,M6.Arithmetic.PA.InternalTrace.ModelSource.step,hr] using instruction_calibration inst (store c) hv

/-- One actual coded literal step either reaches dense machine halt, or gives
positive physical progress and the full successor refinement. No spare file
cells are projected away; the existential file retains its whole HFS value. -/
theorem physical_step {c n xs : V} {m : ModelConf V} (h : Refines c n xs m) :
    (∃ k qs ls rs lf rf, 0<k ∧ Segment k qs ls rs m.q m.left m.right 215 lf rf) ∨
    ∃ n' xs' m', Refines (stepValue c) n' xs' m' ∧ Progress true m m' := by
  obtain ⟨i,s,hs,hpc,hm⟩ := frames_cases h.2.2.2
  have hi := lookup_bound hs
  obtain ⟨inst,hr,himpl⟩ := M6.Arithmetic.OriginalModelCoverage.coverage i hi
  by_cases ht : inst=.halt
  · subst inst
    left
    rw [hm]
    exact himpl n xs h.2.1
  · right
    have hp : ModelPrimitive.Progress M6.Arithmetic.OriginalCheck.path 3947 (M6.Arithmetic.OriginalCheck.path i) inst n xs := by
      cases inst with
      | halt => exact False.elim (ht rfl)
      | inc r j => exact himpl n xs h.2.1
      | dec r z j => exact himpl n xs h.2.1
      | jump j => exact himpl n xs h.2.1
    obtain ⟨k,n',xs',hk,hsize,hcycle,hprogress⟩ := hp
    have he : M6.Arithmetic.PA.InternalTrace.ModelSource.cycleStep ⟨.at i,readFile xs⟩ =
        M6.Arithmetic.PA.InternalTrace.ModelSource.restart (M6.Arithmetic.PA.InternalTrace.ModelSource.execute inst (readFile xs)) := by
      simp only [M6.Arithmetic.PA.InternalTrace.ModelSource.cycleStep,M6.Arithmetic.PA.InternalTrace.ModelSource.step,hr]
    have hc := step_cyclic_calibration c i hi hpc h.1
    rw [h.2.2.1,he,hcycle] at hc
    change M6.Arithmetic.PA.InternalTrace.CodedSource.control (stepValue c)=((k+1 : Nat) : V) ∧
      registers (store (stepValue c))=readFile xs' at hc
    have hk' : k<Source.exactSites.size := by rw [Source.exactSites_count]; exact hk
    let next := Source.exactSites[k]
    have hn : Source.exactSites[k]?=some next := Array.getElem?_eq_getElem hk'
    refine ⟨n',xs',PhysicalFrame.frame (M6.Arithmetic.OriginalCheck.path k) n' xs',?_,?_⟩
    · refine ⟨(step_valid c (refines_valid h)).1,hsize,hc.2,?_⟩
      rw [hc.1]
      exact frames_at k next hn n' xs'
    · simpa only [hm] using hprogress

end Models
#print axioms refines_valid
#print axioms step_cyclic_calibration
#print axioms physical_step
end M6.Arithmetic.PA.InternalTrace.CodedSource

