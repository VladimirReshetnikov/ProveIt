import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.KResidualFast215

/-! Half of the original twelve-block batch, split solely to bound compiler memory.
The maintained subtree equations and all outcomes are unchanged. -/

namespace SetTheory.BusyBeaver.ZFC.KResidualSites215

open RegisterPath RMBisim SiteCoverage KTableCore

/-- 56 leaves. -/
theorem block_90 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 47 leaves. -/
theorem block_91 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_92 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 47 leaves. -/
theorem block_93 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_94 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 78 leaves. -/
theorem block_95 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

end SetTheory.BusyBeaver.ZFC.KResidualSites215
