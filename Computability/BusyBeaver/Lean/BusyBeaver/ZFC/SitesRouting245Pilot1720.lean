import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteRouting245

/-!
Source-only coverage measurement for exact routed leaf 1720: changed_break.
The tree-link theorem and accepted-site theorem use the same literal path
and instruction. SiteRouting245 retains fuel 4000 and margin 64. A decrement
acceptance includes both zero and positive guards. No complete coverage or
concrete-time bound is asserted by this single-site unit.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesRouting245Pilot1720
open RegisterPath RMBisim

def path : List Bool := [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, false, true, true, false, false, true]
def instruction : Edge := .brk 1

/-- Exact leaf/depth of the checked actual routed decoder. -/
theorem actual_leaf : twalk TreeRouting245.tree path 0 = some (instruction, 47) := by
  decide +kernel

/-- This one actual leaf is accepted at the unchanged certificate fuel. -/
theorem site_checked : SiteRouting245.checkSite path instruction = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.SitesRouting245Pilot1720
