import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.KResidualFast215

/-! The 215's decoder sites, blocks 96 to 104 (191 leaves).
Reuses the exact maintained partition; checks only the routed residual suffix. -/

namespace SetTheory.BusyBeaver.ZFC.KResidualSites215

open RegisterPath RMBisim SiteCoverage KTableCore

/-- 12 leaves. -/
theorem block_96 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 6 leaves. -/
theorem block_97 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 13 leaves. -/
theorem block_98 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 70 leaves. -/
theorem block_99 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 36 leaves. -/
theorem block_100 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 1 leaves. -/
theorem block_101 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 26 leaves. -/
theorem block_102 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 1 leaves. -/
theorem block_103 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 26 leaves. -/
theorem block_104 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, true]
      (descend KSource215.t215 [true, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

end SetTheory.BusyBeaver.ZFC.KResidualSites215
