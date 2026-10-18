import BusyBeaver.ZFC.BisimRouting245
open SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim
#print axioms BisimRouting245.all_ok
#print axioms BisimRouting245.initial_programs
#print axioms BisimRouting245.all_ok_programs
#print axioms BisimRouting245.program_halts_iff
#print axioms BisimRouting245.program_nonhalting_iff

example : allC BisimRouting245Data.test BisimRouting245Data.cert = true := BisimRouting245.all_ok
example : branchOk (ptree Prog254.program) (ptree ProgramRouting245.program)
    BisimRouting245Data.cert [] [] 0 = true := BisimRouting245.initial_programs
example : allC (entryOk (ptree Prog254.program) (ptree ProgramRouting245.program)
    BisimRouting245Data.cert) BisimRouting245Data.cert = true := BisimRouting245.all_ok_programs
example (R : Nat → Nat) : Halts ProgramRouting245.program ⟨[], R⟩ ↔
    Halts Prog254.program ⟨[], R⟩ := BisimRouting245.program_halts_iff R
example (R : Nat → Nat) : (¬Halts ProgramRouting245.program ⟨[], R⟩) ↔
    ¬Halts Prog254.program ⟨[], R⟩ := BisimRouting245.program_nonhalting_iff R
example (R : Nat → Nat) (h : Halts Prog254.program ⟨[], R⟩) :
    Halts ProgramRouting245.program ⟨[], R⟩ := (BisimRouting245.program_halts_iff R).mpr h
