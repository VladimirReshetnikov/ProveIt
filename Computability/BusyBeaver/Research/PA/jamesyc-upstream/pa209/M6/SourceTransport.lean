module
public import M6.SourceCrosswalk
@[expose] public section
namespace M6.SourceTransport
open M6.Source M6.SourceCrosswalk

def collapseConfig (c : Configuration) : Configuration :=
  ⟨match c.control with | .at i => .at (collapse i) | q => q, c.registers⟩

def evaluate (code : Option Instruction) (rs : Registers) : Configuration :=
  match code with
  | none => ⟨.malformed, rs⟩
  | some instruction => execute instruction rs

theorem normalize_execute (code : Instruction) (rs : Registers) :
    execute (normalize code) rs = restart (execute code rs) := by
  cases code with
  | inc r n => cases n <;> rfl
  | dec r z p =>
    by_cases h : rs r = 0
    · cases z <;> simp [normalize,execute,h,destination,restart]
    · cases p <;> simp [normalize,execute,h,destination,restart]
  | jump n => cases n <;> rfl
  | halt => rfl

theorem collapse_execute (code : Instruction) (rs : Registers) :
    execute (collapseInstruction code) rs = collapseConfig (restart (execute code rs)) := by
  cases code with
  | inc r n => cases n <;> rfl
  | dec r z p =>
    by_cases h : rs r = 0
    · cases z <;> simp [collapseInstruction,execute,h,destination,restart,collapseConfig]
    · cases p <;> simp [collapseInstruction,execute,h,destination,restart,collapseConfig]
  | jump n => cases n <;> rfl
  | halt => rfl

theorem evaluate_normalize (code : Option Instruction) (rs : Registers) :
    evaluate (code.map normalize) rs = restart (evaluate code rs) := by
  cases code with
  | none => rfl
  | some code => exact normalize_execute code rs

theorem evaluate_collapse (code : Option Instruction) (rs : Registers) :
    evaluate (code.map collapseInstruction) rs = collapseConfig (restart (evaluate code rs)) := by
  cases code with
  | none => rfl
  | some code => exact collapse_execute code rs

theorem cycle_at (sites : Array Site) (i : Nat) (rs : Registers) :
    cycleStep sites ⟨.at i,rs⟩ = restart (evaluate (resolveAt sites i) rs) := by
  cases h : resolveAt sites i <;> simp [cycleStep,step,evaluate,h]

/-- Each inherited instruction commutes with the source-control crosswalk,
including every register test, branch target and normal-root restart. -/
theorem inherited_step (i : Nat) (hi : i < 3947) (rs : Registers) :
    collapseConfig (cycleStep Program.sites ⟨.at i,rs⟩) =
      cycleStep originalSites ⟨.at (collapse i),rs⟩ := by
  rw [cycle_at, cycle_at, Program.resolve_tree, original_resolve]
  change collapseConfig (restart (evaluate (CheckCoverage.codeAt i) rs)) = _
  rw [← evaluate_collapse, code_crosswalk i hi, evaluate_normalize]

/-- The newly inserted final Continue is exactly one stuttering step in
    the old source, with the entire register valuation untouched. -/
theorem inserted_step (rs : Registers) :
    collapseConfig (cycleStep Program.sites ⟨.at 3947,rs⟩) =
      collapseConfig ⟨.at 3947,rs⟩ := by
  rw [cycle_at,Program.resolve_tree]
  change collapseConfig (restart (evaluate (CheckCoverage.codeAt 3947) rs)) = _
  rw [inserted_return]
  rfl

theorem restart_not_exited (c : Configuration) : (restart c).control ≠ .exited := by
  cases c with | mk q r => cases q <;> simp [restart]

theorem collapse_halted (c : Configuration) :
    (collapseConfig c).control = .halted ↔ c.control = .halted := by
  cases c with | mk q r => cases q <;> simp [collapseConfig]

theorem invalid_step (i : Nat) (hi : 3948 ≤ i) (rs : Registers) :
    cycleStep Program.sites ⟨.at i,rs⟩ = ⟨.malformed,rs⟩ := by
  have hn : Program.sites.size ≤ i := by rw [Program.sites_count]; omega
  simp [cycleStep,step,resolveAt,Array.getElem?_eq_none hn,restart]

theorem halted_not_exited {sites : Array Site} {n : Nat} {c : Configuration}
    (h : (cycleRun sites n c).control = .halted) (hc : c.control = .malformed) : False := by
  cases c with | mk q r =>
    simp only at hc
    subst q
    have hs : cycleStep sites ⟨.malformed,r⟩ = ⟨.malformed,r⟩ := rfl
    rw [cycleRun_stable hs n] at h
    cases h

/-- Finite halting reflection, not merely a comparison of sampled traces.
The single inserted Continue may stutter; every other source step is exact.
Malformed and out-of-range controls cannot manufacture a halting execution. -/
theorem halting_reflection (n : Nat) (c : Configuration)
    (hc : c.control ≠ .exited) (h : (cycleRun Program.sites n c).control = .halted) :
    CycleHalts originalSites (collapseConfig c) := by
  induction n generalizing c with
  | zero => exact ⟨0,(collapse_halted c).mpr h⟩
  | succ n ih =>
    have hn := ih (cycleStep Program.sites c) (restart_not_exited _) h
    cases c with | mk q rs =>
      cases q with
      | «at» i =>
        by_cases hi : i < 3947
        · rw [inherited_step i hi rs] at hn
          obtain ⟨k,hk⟩ := hn
          exact ⟨k+1,hk⟩
        · by_cases he : i = 3947
          · subst i
            rwa [inserted_step rs] at hn
          · have hbad := invalid_step i (by omega) rs
            exact False.elim (halted_not_exited (n := n) h (by rw [hbad]))
      | exited => exact False.elim (hc rfl)
      | halted => exact ⟨0,rfl⟩
      | malformed => exact False.elim (halted_not_exited h rfl)

/-- The reordered source is nonhalting from A and any nine-register store
whenever the original source is nonhalting from its A entry at that store.
No consistency assumption or source-invariant premise is hidden here. -/
theorem nonhalting_from_A (rs : Registers)
    (h : ¬ CycleHalts originalSites ⟨.at 0,rs⟩) :
    ¬ CycleHalts Program.sites ⟨.at 25,rs⟩ := by
  rintro ⟨n,hn⟩
  exact h (halting_reflection n ⟨.at 25,rs⟩ (by intro h; cases h) hn)

#print axioms inherited_step
#print axioms inserted_step
#print axioms halting_reflection
#print axioms nonhalting_from_A
end M6.SourceTransport
