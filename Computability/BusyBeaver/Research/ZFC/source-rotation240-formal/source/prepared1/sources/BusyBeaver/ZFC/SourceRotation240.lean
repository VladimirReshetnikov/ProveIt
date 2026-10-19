import BusyBeaver.ZFC.SourceRotation244

/-!
The second transfer-plus-one rotation changes only shared DAG row169. Its
four occurrences account for the exact 6455-leaf source in the incoming240
construction. The old shared rows44/45 remain available elsewhere. Existing
generic loop and context theorems prove arbitrary-register source equivalence;
one finite WF check connects structured runs to RegisterPath halting.

This unit does not identify a binary table, certify runtime or startup, or
establish a complete240-state consistency endpoint or an internal PA theorem.
-/
set_option autoImplicit false

namespace SetTheory.BusyBeaver.ZFC.SourceRotation240
open RMDag

def nodes (n : Nat) : RegisterPath.Edge × RegisterPath.Edge :=
  if n = 169 then (.inc 5, .node 5)
  else ProgramRotation244.program.nodes n

def program : RegisterPath.Program where
  nodes := nodes
  root := ProgramRotation244.program.root
  nnodes := ProgramRotation244.program.nnodes

theorem program_root : program.root = 202 := rfl
theorem program_nnodes : program.nnodes = 203 := rfl
theorem node169 : program.nodes 169 = (.inc 5, .node 5) := rfl

theorem nodes_unmodified (n : Nat) (hn : n ≠ 169) :
    program.nodes n = ProgramRotation244.program.nodes n := by
  simp only [program, nodes, if_neg hn]

abbrev oldDag : RMDag.Prog := SourceRotation244.newDag
def newDag : RMDag.Prog := SourceRotation244.ofProgram program

theorem new_program_eq : RMEquiv.ofDag newDag 203 = program :=
  SourceRotation244.ofDag_ofProgram program

/- All child indices are smaller than their parents. The finite escape sets
   are unchanged from the prior rotated program, including continue bound5=1.
   Only these candidate bounds are input to the kernel-checked WF predicate. -/
private def H (n : Nat) : Nat := n + 1

private def B (n : Nat) : Nat :=
  if n = 0 ∨ n = 9 ∨ n = 173 ∨ n = 174 ∨ n = 175 ∨ n = 184 ∨
      n = 185 ∨ n = 191 ∨ n = 192 ∨ n = 194 ∨ n = 195 then 1 else 0

private def C (n : Nat) : Nat :=
  if n = 1 ∨ n = 13 ∨ n = 32 then 2
  else if n = 2 ∨ n = 4 ∨ n = 5 ∨ n = 10 ∨ n = 14 ∨ n = 16 ∨
      n = 19 ∨ n = 22 ∨ n = 26 ∨ n = 28 ∨ n = 33 ∨ n = 35 ∨
      n = 40 ∨ n = 44 ∨ n = 54 ∨ n = 168 ∨ n = 170 then 1 else 0

private theorem new_wf_check : RMEquiv.wfCheck newDag 203 H B C = true := by
  decide +kernel

theorem new_wf : RMEquiv.WF newDag 203 :=
  RMEquiv.wfCheck_sound new_wf_check

/-- Exact local loop replacement, with all exit/output judgments quantified. -/
theorem local_run_iff (R R' : RMDag.Regs) (x : RMDag.Exit) :
    RMDag.Run oldDag (.node 169) R x R' ↔
      RMDag.Run newDag (.node 169) R x R' :=
  RMDagLoopRotation.run_iff (p := oldDag) (q := newDag)
    (n := 169) (l := 45) (b := 44) (n' := 169) (l' := 5)
    (src := 6) (dst := 5)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by decide) R R' x

/-- No node is excluded: the old transfer children remain shared and unchanged. -/
theorem replacement :
    RMDagContextSubstitution.Replacement oldDag newDag (fun _ => True) 169 := by
  constructor
  · exact local_run_iff
  · intro n _hn_safe hn
    change
      (SourceRotation244.toDagEdge (ProgramRotation244.program.nodes n).1,
       SourceRotation244.toDagEdge (ProgramRotation244.program.nodes n).2) =
      (SourceRotation244.toDagEdge (program.nodes n).1,
       SourceRotation244.toDagEdge (program.nodes n).2)
    rw [nodes_unmodified n hn]
  · intro _n _hn_safe _hn
    exact ⟨True.intro, True.intro⟩

theorem iterHalts_iff (R : RMDag.Regs) :
    RMDag.IterHalts oldDag R ↔ RMDag.IterHalts newDag R :=
  RMDagContextSubstitution.iterHalts_iff replacement rfl True.intro R

/-- New source versus the previously calibrated rotated source, for every R. -/
theorem program_halts_iff (R : RegisterPath.Registers) :
    RegisterPath.Halts program ⟨[], R⟩ ↔
      RegisterPath.Halts ProgramRotation244.program ⟨[], R⟩ := by
  rw [← new_program_eq, ← SourceRotation244.new_program_eq]
  exact (RMEquiv.halts_iff_iterHalts new_wf R).trans
    ((iterHalts_iff R).symm.trans
      (RMEquiv.halts_iff_iterHalts SourceRotation244.new_wf R).symm)

end SetTheory.BusyBeaver.ZFC.SourceRotation240
