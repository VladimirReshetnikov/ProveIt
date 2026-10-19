import BusyBeaver.ZFC.DagControl254

set_option autoImplicit false

/-!
# The dag254 and Rotation240 control interpreters halt together, internally

Two instances of the table interpreter `ArithmeticControlTable`: the dag254
interpreter of `DagControl254` and the Rotation240 interpreter at the packed
6,455-row table `BisimCertRotation240.tableR` (the control catalogue of the
rotated 240-state source; its agreement with the decoder tree executed by the
binary machine is a separate check).

In every model of `IΣ₁`, from every internal register file, the two
represented interpreters halt together (`halts_iff`). The proof instantiates
`ArithmeticControlBisim.halts_iff_of_check` with the generated 3,862-entry
certificate `BisimCertRotation240.certPacked`, checked by the kernel against
both packed row tables in chunks. Its only nonzero offsets (ten entries, each
of size one) absorb the two transfer-plus-one loop rotations of the source; the
routing245 re-association needs none.

For the PA endpoint this replaces the external chain
`SourceRotation240`/`SourceRotation244`/`BisimRouting245`/`Bisim254`.
-/

namespace SetTheory.BusyBeaver.ZFC.ControlBisimRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControlBisim ArithmeticControlTable
open ArithmeticControlFile (regValue fileValue liveValue reg_file live_ne_zero live_defined
  liveDef projectionDef projection_defined)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The row table of the Rotation240 control interpreter. -/
abbrev tableR : List Row := PackedTables.table BisimCertRotation240.tableR BisimCertRotation240.countR

abbrev rowsLitR (c : Nat) : Option Row :=
  PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR c

abbrev cert (i : Nat) : Option Entry :=
  PackedTables.certOf BisimCertRotation240.certPacked BisimCertRotation240.size i

abbrev chunk (start count : Nat) : Bool :=
  checkFrom DagControl254.rowsLit rowsLitR cert BisimCertRotation240.fuel
    BisimCertRotation240.size start count

theorem check0 : chunk 0 1000 = true := by decide +kernel
theorem check1 : chunk 1000 1000 = true := by decide +kernel
theorem check2 : chunk 2000 1000 = true := by decide +kernel
theorem check3 : chunk 3000 862 = true := by decide +kernel

theorem check_all (i : Nat) (hi : i < BisimCertRotation240.size) :
    entryOK DagControl254.rowsLit rowsLitR cert BisimCertRotation240.fuel
      BisimCertRotation240.size i = true := by
  have hs : BisimCertRotation240.size = 3862 := rfl
  rw [hs] at hi
  rcases Nat.lt_or_ge i 1000 with h0 | h0
  · exact checkFrom_entry _ _ _ _ _ 0 1000 check0 i (Nat.zero_le _) (by omega)
  rcases Nat.lt_or_ge i 2000 with h1 | h1
  · exact checkFrom_entry _ _ _ _ _ 1000 1000 check1 i h0 (by omega)
  rcases Nat.lt_or_ge i 3000 with h2 | h2
  · exact checkFrom_entry _ _ _ _ _ 2000 1000 check2 i h1 (by omega)
  · exact checkFrom_entry _ _ _ _ _ 3000 862 check3 i h2 (by omega)

theorem cert_zero : cert 0 = some ⟨1, 1, [0,0,0,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,0], 1, 2⟩ := by
  decide +kernel

section Main

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance proj_defined (p : Fin 9) :
    𝚺₁-Function₁[V] (fun x => regValue x p) via projectionDef 8 p :=
  projection_defined 8 p

theorem specR (c : Nat) (row : Row) (x : V) (h : rowsLitR c = some row) :
    stepValue tableR (liveValue (c : V) x) = sem regValue write liveValue row x := by
  obtain ⟨hc, hg⟩ := PackedTables.rowsOf_some _ _ c row h
  exact spec_get tableR c row x hc hg

/-- **Internal source equivalence.** In every `IΣ₁` model and from every internal
register file, the dag254 and Rotation240 control interpreters halt together. -/
theorem halts_iff (x : V) :
    (∃ t, controlRun DagControl254.table t (liveValue 1 x) = 0) ↔
      (∃ t, controlRun tableR t (liveValue 1 x) = 0) := by
  have h := halts_iff_of_check (reg := regValue) (write := write) (live := liveValue)
    ArithmeticControlFile.fileValue reg_file live_ne_zero liveDef (fun p => projectionDef 8 p)
    (stepValue DagControl254.table) (stepValue tableR)
    (controlRun DagControl254.table) (controlRun tableR)
    DagControl254.rowsLit rowsLitR cert BisimCertRotation240.fuel BisimCertRotation240.size
    (controlRun_zero _) (controlRun_zero _) (controlRun_add _) (controlRun_add _)
    (controlRun_one _) (controlRun_one _) (controlRun_halted _) (controlRun_halted _)
    (fun c row y hr => DagControl254.spec c row y hr) (fun c row y hr => specR c row y hr)
    reg_write_same reg_write_other check_all _ cert_zero (by decide)
    (by decide) (by decide) x
  simpa using h

end Main

end SetTheory.BusyBeaver.ZFC.ControlBisimRotation240
