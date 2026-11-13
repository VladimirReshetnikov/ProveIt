module
public import M6.Startup
public import M6.Source.PhysicalRegisters
@[expose] public section
namespace M6.PaperCorrection
open M6.Zip
/-- The paper's asserted clean file, with twenty-five spare registers. -/
def claimedFile : List Nat := [0,0,0,0,0,0,2,0,0] ++ List.replicate 25 1
/-- The complete claimed zipper, with root at offset0 and header at offset48. -/
def claimedClean : Conf := zc 81 [true]
  ([true] ++ List.replicate 47 false ++ [true] ++ Runtime.sepsR claimedFile)
/-- The actual finite execution has one further one-valued spare. -/
theorem actual_file : Startup.physicalFile = claimedFile ++ [1] := by decide +kernel
/-- All previously claimed cells agree, with the three-cell extension 011. -/
theorem exact_tape_difference : Startup.clean.l = claimedClean.l ∧
    Startup.clean.r = claimedClean.r ++ [false,true,true] := by decide +kernel
/-- This is a genuine discrepancy, not another encoding of the same zero-tailed tape. -/
theorem distinct_clean : Startup.clean ≠ claimedClean := by decide +kernel
/-- The exact kernel-verified trace rules out the claimed endpoint at this time. -/
theorem not_claimed_at_clean_time :
    run Literal.machine 58210 Startup.blank ≠ some claimedClean := by
  rw [Startup.startup_exact]
  exact fun h => distinct_clean (Option.some.inj h)
/-- The corrected file meets the permanent whole-file lower bound. -/
theorem corrected_file_valid : 10 ≤ Startup.physicalFile.length := by decide +kernel
/-- The nine-register source interpretation is unchanged by the extra spare. -/
theorem logical_projection_unchanged :
    Source.readFile Startup.physicalFile = Source.readFile claimedFile := by
  rw [actual_file]
  exact Source.readFile_append claimedFile [1] (by decide +kernel)
/-- The real clean endpoint has N=2 and all other logical registers zero. -/
theorem corrected_logical_seed : ∀ r : Fin 9,
    Source.readFile Startup.physicalFile r = if r.val = 0 then 2 else 0 := by decide +kernel
#print axioms corrected_file_valid
#print axioms logical_projection_unchanged
#print axioms corrected_logical_seed
#print axioms actual_file
#print axioms exact_tape_difference
#print axioms not_claimed_at_clean_time
end M6.PaperCorrection
