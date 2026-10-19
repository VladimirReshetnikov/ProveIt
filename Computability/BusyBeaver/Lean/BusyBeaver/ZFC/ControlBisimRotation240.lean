import BusyBeaver.ZFC.ControlBisimRotation240Chunk000
import BusyBeaver.ZFC.ControlBisimRotation240Chunk001
import BusyBeaver.ZFC.ControlBisimRotation240Chunk002
import BusyBeaver.ZFC.ControlBisimRotation240Chunk003
import BusyBeaver.ZFC.ControlBisimRotation240Chunk004
import BusyBeaver.ZFC.ControlBisimRotation240Chunk005
import BusyBeaver.ZFC.ControlBisimRotation240Chunk006
import BusyBeaver.ZFC.ControlBisimRotation240Chunk007
import BusyBeaver.ZFC.ControlBisimRotation240Chunk008
import BusyBeaver.ZFC.ControlBisimRotation240Chunk009
import BusyBeaver.ZFC.ControlBisimRotation240Chunk010
import BusyBeaver.ZFC.ControlBisimRotation240Chunk011
import BusyBeaver.ZFC.ControlBisimRotation240Chunk012
import BusyBeaver.ZFC.ControlBisimRotation240Chunk013
import BusyBeaver.ZFC.ControlBisimRotation240Chunk014
import BusyBeaver.ZFC.ControlBisimRotation240Chunk015
import BusyBeaver.ZFC.ControlBisimRotation240Chunk016
import BusyBeaver.ZFC.ControlBisimRotation240Chunk017
import BusyBeaver.ZFC.ControlBisimRotation240Chunk018
import BusyBeaver.ZFC.ControlBisimRotation240Chunk019
import BusyBeaver.ZFC.ControlBisimRotation240Chunk020
import BusyBeaver.ZFC.ControlBisimRotation240Chunk021
import BusyBeaver.ZFC.ControlBisimRotation240Chunk022
import BusyBeaver.ZFC.ControlBisimRotation240Chunk023
import BusyBeaver.ZFC.ControlBisimRotation240Chunk024
import BusyBeaver.ZFC.ControlBisimRotation240Chunk025
import BusyBeaver.ZFC.ControlBisimRotation240Chunk026
import BusyBeaver.ZFC.ControlBisimRotation240Chunk027
import BusyBeaver.ZFC.ControlBisimRotation240Chunk028
import BusyBeaver.ZFC.ControlBisimRotation240Chunk029
import BusyBeaver.ZFC.ControlBisimRotation240Chunk030

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

theorem check0 : chunk 0 1000 = true := by
  have h_0_256 : chunk 0 256 = true :=
    ControlBisimRotation240Split.chunk_join 0 128 128 ControlBisimRotation240Split.check000 ControlBisimRotation240Split.check001
  have h_256_256 : chunk 256 256 = true :=
    ControlBisimRotation240Split.chunk_join 256 128 128 ControlBisimRotation240Split.check002 ControlBisimRotation240Split.check003
  have h_0_512 : chunk 0 512 = true :=
    ControlBisimRotation240Split.chunk_join 0 256 256 h_0_256 h_256_256
  have h_512_256 : chunk 512 256 = true :=
    ControlBisimRotation240Split.chunk_join 512 128 128 ControlBisimRotation240Split.check004 ControlBisimRotation240Split.check005
  have h_768_232 : chunk 768 232 = true :=
    ControlBisimRotation240Split.chunk_join 768 128 104 ControlBisimRotation240Split.check006 ControlBisimRotation240Split.check007
  have h_512_488 : chunk 512 488 = true :=
    ControlBisimRotation240Split.chunk_join 512 256 232 h_512_256 h_768_232
  have h_0_1000 : chunk 0 1000 = true :=
    ControlBisimRotation240Split.chunk_join 0 512 488 h_0_512 h_512_488
  exact h_0_1000
theorem check1 : chunk 1000 1000 = true := by
  have h_1000_256 : chunk 1000 256 = true :=
    ControlBisimRotation240Split.chunk_join 1000 128 128 ControlBisimRotation240Split.check008 ControlBisimRotation240Split.check009
  have h_1256_256 : chunk 1256 256 = true :=
    ControlBisimRotation240Split.chunk_join 1256 128 128 ControlBisimRotation240Split.check010 ControlBisimRotation240Split.check011
  have h_1000_512 : chunk 1000 512 = true :=
    ControlBisimRotation240Split.chunk_join 1000 256 256 h_1000_256 h_1256_256
  have h_1512_256 : chunk 1512 256 = true :=
    ControlBisimRotation240Split.chunk_join 1512 128 128 ControlBisimRotation240Split.check012 ControlBisimRotation240Split.check013
  have h_1768_232 : chunk 1768 232 = true :=
    ControlBisimRotation240Split.chunk_join 1768 128 104 ControlBisimRotation240Split.check014 ControlBisimRotation240Split.check015
  have h_1512_488 : chunk 1512 488 = true :=
    ControlBisimRotation240Split.chunk_join 1512 256 232 h_1512_256 h_1768_232
  have h_1000_1000 : chunk 1000 1000 = true :=
    ControlBisimRotation240Split.chunk_join 1000 512 488 h_1000_512 h_1512_488
  exact h_1000_1000
theorem check2 : chunk 2000 1000 = true := by
  have h_2000_256 : chunk 2000 256 = true :=
    ControlBisimRotation240Split.chunk_join 2000 128 128 ControlBisimRotation240Split.check016 ControlBisimRotation240Split.check017
  have h_2256_256 : chunk 2256 256 = true :=
    ControlBisimRotation240Split.chunk_join 2256 128 128 ControlBisimRotation240Split.check018 ControlBisimRotation240Split.check019
  have h_2000_512 : chunk 2000 512 = true :=
    ControlBisimRotation240Split.chunk_join 2000 256 256 h_2000_256 h_2256_256
  have h_2512_256 : chunk 2512 256 = true :=
    ControlBisimRotation240Split.chunk_join 2512 128 128 ControlBisimRotation240Split.check020 ControlBisimRotation240Split.check021
  have h_2768_232 : chunk 2768 232 = true :=
    ControlBisimRotation240Split.chunk_join 2768 128 104 ControlBisimRotation240Split.check022 ControlBisimRotation240Split.check023
  have h_2512_488 : chunk 2512 488 = true :=
    ControlBisimRotation240Split.chunk_join 2512 256 232 h_2512_256 h_2768_232
  have h_2000_1000 : chunk 2000 1000 = true :=
    ControlBisimRotation240Split.chunk_join 2000 512 488 h_2000_512 h_2512_488
  exact h_2000_1000
theorem check3 : chunk 3000 862 = true := by
  have h_3128_256 : chunk 3128 256 = true :=
    ControlBisimRotation240Split.chunk_join 3128 128 128 ControlBisimRotation240Split.check025 ControlBisimRotation240Split.check026
  have h_3000_384 : chunk 3000 384 = true :=
    ControlBisimRotation240Split.chunk_join 3000 128 256 ControlBisimRotation240Split.check024 h_3128_256
  have h_3384_256 : chunk 3384 256 = true :=
    ControlBisimRotation240Split.chunk_join 3384 128 128 ControlBisimRotation240Split.check027 ControlBisimRotation240Split.check028
  have h_3640_222 : chunk 3640 222 = true :=
    ControlBisimRotation240Split.chunk_join 3640 128 94 ControlBisimRotation240Split.check029 ControlBisimRotation240Split.check030
  have h_3384_478 : chunk 3384 478 = true :=
    ControlBisimRotation240Split.chunk_join 3384 256 222 h_3384_256 h_3640_222
  have h_3000_862 : chunk 3000 862 = true :=
    ControlBisimRotation240Split.chunk_join 3000 384 478 h_3000_384 h_3384_478
  exact h_3000_862

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
