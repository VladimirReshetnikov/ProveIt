import BusyBeaver.ZFC.SourceRotation240
open SetTheory.BusyBeaver.ZFC
open SourceRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation240.program_root
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation240.program_nnodes
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation240.node169
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation240.nodes_unmodified
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation240.new_program_eq
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation240.new_wf
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation240.local_run_iff
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation240.replacement
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation240.iterHalts_iff
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation240.program_halts_iff

example : program.root = 202 := program_root
example : program.nnodes = 203 := program_nnodes
example : program.nodes 169 = (.inc 5, .node 5) := node169
example (n : Nat) (hn : n ≠ 169) :
    program.nodes n = ProgramRotation244.program.nodes n := nodes_unmodified n hn
example : RMEquiv.ofDag newDag 203 = program := new_program_eq
example : RMEquiv.WF newDag 203 := new_wf
example (R R' : RMDag.Regs) (x : RMDag.Exit) :
    RMDag.Run oldDag (.node 169) R x R' ↔
      RMDag.Run newDag (.node 169) R x R' := local_run_iff R R' x
example : RMDagContextSubstitution.Replacement oldDag newDag (fun _ => True) 169 :=
  replacement
example (R : RMDag.Regs) :
    RMDag.IterHalts oldDag R ↔ RMDag.IterHalts newDag R := iterHalts_iff R
example (R : RegisterPath.Registers) :
    RegisterPath.Halts program ⟨[], R⟩ ↔
      RegisterPath.Halts ProgramRotation244.program ⟨[], R⟩ := program_halts_iff R
example (R : RegisterPath.Registers) :
    (¬ RegisterPath.Halts program ⟨[], R⟩) ↔
      ¬ RegisterPath.Halts ProgramRotation244.program ⟨[], R⟩ :=
  not_congr (program_halts_iff R)
example (R : RMDag.Regs) :
    RMDag.Run newDag (.node 169) R .normal (RMDagLoopRotation.normalFile R 6 5) :=
  RMDagLoopRotation.new_normal (p := newDag) (n := 169) (l := 5)
    (src := 6) (dst := 5) (by rfl) (by rfl) (by decide) R
example (R : RMDag.Regs) :
    RMDag.Run oldDag (.node 169) R .normal (RMDagLoopRotation.normalFile R 6 5) :=
  RMDagLoopRotation.old_normal (p := oldDag) (n := 169) (l := 45) (b := 44)
    (src := 6) (dst := 5) (by rfl) (by rfl) (by rfl) (by decide) R
