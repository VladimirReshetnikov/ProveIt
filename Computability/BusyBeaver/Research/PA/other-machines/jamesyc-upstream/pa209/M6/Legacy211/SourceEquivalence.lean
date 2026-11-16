module
public import M6.Legacy211.AllSourceChecks
public import M6.Legacy213.SourceEquivalence
@[expose] public section
namespace M6.Legacy211.Source
open M6.Source M6.Source.PathTrie

theorem candidate_resolve (i : Nat) : resolveAt sites i=M6.Legacy213.SourceProgram.codes[i]? := by
  by_cases hi : i<3947
  · rw [resolve_tree]
    rw [nthSite_sites]
    exact checked i hi
  · have hs : sites[i]?=none := Array.getElem?_eq_none_iff.mpr (by rw [sites_count];omega)
    have hc : M6.Legacy213.SourceProgram.codes[i]?=none := Array.getElem?_eq_none_iff.mpr
      (by rw [M6.Legacy213.SourceProgram.codes_count];omega)
    simp [resolveAt,hs,hc]

theorem resolve_eq (i : Nat) : resolveAt sites i=resolveAt exactSites i := by
  rw [candidate_resolve,M6.Legacy213.SourceEquivalence.baseline_resolve]

theorem step_eq (c : Configuration) : step sites c=step exactSites c := by
  rcases c with ⟨q,r⟩
  cases q <;> simp only [step,resolve_eq]

theorem cycleStep_eq (c : Configuration) : cycleStep sites c=cycleStep exactSites c := by
  simp only [cycleStep,step_eq]

theorem cycleRun_eq (n : Nat) (c : Configuration) :
    cycleRun sites n c=cycleRun exactSites n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [cycleRun,cycleStep_eq,ih]

theorem cycleHalts_iff (c : Configuration) : CycleHalts sites c ↔ CycleHalts exactSites c := by
  simp only [CycleHalts,cycleRun_eq]

theorem resolved_program_eq :
    (List.range 3947).map (resolveAt sites)=(List.range 3947).map (resolveAt exactSites) := by
  apply congrArg (fun f => (List.range 3947).map f)
  funext i
  exact resolve_eq i

theorem path_short (i : Nat) : (path i).length≤64 := by
  unfold path
  rw [nthSite_sites]
  cases hs : sites[i]? with
  | none => simp [hs]
  | some s =>
    have hm : s∈sites.toList := by
      exact List.mem_of_getElem? (by simpa using hs)
    have hh := List.all_eq_true.mp all_paths_short s hm
    simpa [hs] using hh

theorem path_eq (i : Nat) : path i=((sites[i]?).map (·.path)).getD [] := by
  rw [path,nthSite_sites]

#print axioms resolve_eq
#print axioms cycleHalts_iff
#print axioms resolved_program_eq
#print axioms path_short
end M6.Legacy211.Source
