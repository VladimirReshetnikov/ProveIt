import BusyBeaver.ZFC.SourceRotation244
open SetTheory.BusyBeaver.ZFC
open SourceRotation244

#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation244.toPath_toDagEdge
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation244.ofDag_ofProgram
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation244.old_program_eq
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation244.new_program_eq
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation244.old_wf
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation244.new_wf
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation244.replacement
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation244.iterHalts_iff
#print axioms SetTheory.BusyBeaver.ZFC.SourceRotation244.program_halts_iff

example (e : RegisterPath.Edge) : RMEquiv.toPath (toDagEdge e) = e := toPath_toDagEdge e
example (p : RegisterPath.Program) : RMEquiv.ofDag (ofProgram p) p.nnodes = p := ofDag_ofProgram p
example : RMEquiv.ofDag oldDag 203 = ProgramRouting245.program := old_program_eq
example : RMEquiv.ofDag newDag 203 = ProgramRotation244.program := new_program_eq
example : RMEquiv.WF oldDag 203 := old_wf
example : RMEquiv.WF newDag 203 := new_wf
example : RMDagContextSubstitution.Replacement oldDag newDag safe 6 := replacement
example (R : RMDag.Regs) : RMDag.IterHalts oldDag R ↔ RMDag.IterHalts newDag R := iterHalts_iff R
example (R : RegisterPath.Registers) :
    RegisterPath.Halts ProgramRotation244.program ⟨[], R⟩ ↔
      RegisterPath.Halts ProgramRouting245.program ⟨[], R⟩ := program_halts_iff R
example (R : RegisterPath.Registers) :
    (¬ RegisterPath.Halts ProgramRotation244.program ⟨[], R⟩) ↔
      ¬ RegisterPath.Halts ProgramRouting245.program ⟨[], R⟩ := not_congr (program_halts_iff R)
