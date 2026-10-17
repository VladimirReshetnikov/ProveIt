import BusyBeaver.ZFC.BootPerm252
import BusyBeaver.ZFC.Permutation252Frame

/-!
The exact blank bootstrap of the 252-state permutation candidate, expressed
in the independent whole-tape dispatch frame.

The literal machine derives from Mira-Cult's machine, Jeff's verification,
and Wade's compiler framework at upstream commit
297ab8df7e5de329605c3875b4934643b371a5e3. Its new physical register
permutation is [0,3,4,5,8,1,6,2,7]. The candidate source and canonical tables
are pinned in BootPerm252 and TablePerm252.

This module only combines the checked 82,552-transition blank prefix with
the finite register-layout definition. All nine logical registers are zero;
the physical spare suffix is retained, including its one nonzero block.
No general instruction simulation or consistency equivalence is asserted.
-/

namespace SetTheory.BusyBeaver.ZFC.BootstrapFramePerm252

open FiniteZipper Permutation252Frame

/-- Canonical state 94 is old dispatch state 96 in the frozen candidate. -/
def dispatchPerm252 : Fin 252 := ⟨94, by decide⟩

/-- The complete boot target has ten blank cells on its finite left tail,
one on its finite right tail, gap 40, and all 65 physical spare blocks. -/
theorem boot_target_zip :
    dispatchZip dispatchPerm252 2 10 1 zeroRoot 40 BootPerm252.bootSparesPerm252 =
      BootPerm252.bootTargetPerm252 := by decide +kernel

/-- The actual blank run represents the zero logical root on the whole tape. -/
theorem boot_dispatch_frame :
    DispatchFrame dispatchPerm252 (machinePerm252.run 82552)
      zeroRoot 40 BootPerm252.bootSparesPerm252 := by
  apply frame_of_zeroRoot_zip _ _ _ _ (by decide) 10 1
  rw [BootPerm252.fullBootstrapPerm252_head, boot_target_zip]
  exact BootPerm252.fullBootstrapPerm252

end SetTheory.BusyBeaver.ZFC.BootstrapFramePerm252
