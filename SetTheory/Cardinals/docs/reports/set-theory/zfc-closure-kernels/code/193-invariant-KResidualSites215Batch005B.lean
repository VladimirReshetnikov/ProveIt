import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.KResidualFast215

/-! Half of the original twelve-block batch, split solely to bound compiler memory.
The maintained subtree equations and all outcomes are unchanged. -/

namespace SetTheory.BusyBeaver.ZFC.KResidualSites215

open RegisterPath RMBisim SiteCoverage KTableCore

/-- 56 leaves. -/
theorem block_66 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, false, false, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, false, false, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_67 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, false, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, false, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_68 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, false, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, false, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_69 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, false, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_70 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, false, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_71 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, false, true, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

end SetTheory.BusyBeaver.ZFC.KResidualSites215
