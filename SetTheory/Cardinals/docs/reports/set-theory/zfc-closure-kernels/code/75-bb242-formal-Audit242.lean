import Reduction242
set_option autoImplicit false
open BranchBorrow242 PositiveBlocks

#print axioms BranchBorrow242.old_working_count
#print axioms BranchBorrow242.new_working_count
#print axioms BranchBorrow242.incoming_finite
#print axioms BranchBorrow242.incoming_all
#print axioms BranchBorrow242.patch_finite
#print axioms BranchBorrow242.newRow_patch
#print axioms PositiveBlocks.halting_iff
#print axioms BranchBorrow242.invariant_step
#print axioms BranchBorrow242.invariant_run
#print axioms BranchBorrow242.ordinary_checkpoint
#print axioms BranchBorrow242.exceptional_zero
#print axioms BranchBorrow242.exceptional_one
#print axioms BranchBorrow242.matching_blocks
#print axioms BranchBorrow242.checkpoint_halting_iff
#print axioms BranchBorrow242.start95_halting_iff
#print axioms BranchBorrow242.blank_halting_iff
#print axioms BranchBorrow242.blank_nonhalting_iff
#print axioms BranchBorrow242.calibration_transfer

example : workingCount oldRows = 243 := old_working_count
example : workingCount newRows = 242 := new_working_count
example (q : Nat) (b : Bool) : newRow q b = patched q b := newRow_patch q b
example (q : Nat) (b : Bool) (a : Action) (h : oldRow q b = some a) :
    incoming q b a := incoming_all q b a h
example (c : Config) (h : Inv c) : Inv (step oldRow c) := invariant_step c h
example (n : Nat) (c : Config) (h : Inv c) : Inv (run (step oldRow) n c) :=
  invariant_run n c h
example (c : Config) (hq : c.state = 11) (h0 : c.tape c.head = false)
    (h1 : c.tape (c.head + 1) = false) :
    run (step oldRow) 2 c = {c with state := 21, head := c.head + 2} ∧
    run (step newRow) 4 c = {c with state := 21, head := c.head + 2} :=
  exceptional_zero c hq h0 h1
example (c : Config) (hq : c.state = 11) (h0 : c.tape c.head = false)
    (h1 : c.tape (c.head + 1) = true) :
    run (step oldRow) 2 c = {c with state := 22, head := c.head + 2} ∧
    run (step newRow) 2 c = {c with state := 22, head := c.head + 2} :=
  exceptional_one c hq h0 h1
example (c : Config) (h : Checkpoint c) :
    Halts (step oldRow) terminal c ↔ Halts (step newRow) terminal c :=
  checkpoint_halting_iff c h
example (h : Int) (t : Int → Bool) :
    Halts (step oldRow) terminal ⟨95, h, t⟩ ↔
    Halts (step newRow) terminal ⟨95, h, t⟩ := start95_halting_iff h t
example : Halts (step oldRow) terminal ⟨95, 0, fun _ => false⟩ ↔
    Halts (step newRow) terminal ⟨95, 0, fun _ => false⟩ := blank_halting_iff
example : (¬ Halts (step oldRow) terminal ⟨95, 0, fun _ => false⟩) ↔
    (¬ Halts (step newRow) terminal ⟨95, 0, fun _ => false⟩) := blank_nonhalting_iff
example (C : Prop)
    (old : (¬ Halts (step oldRow) terminal ⟨95, 0, fun _ => false⟩) ↔ C) :
    (¬ Halts (step newRow) terminal ⟨95, 0, fun _ => false⟩) ↔ C :=
  calibration_transfer C old
