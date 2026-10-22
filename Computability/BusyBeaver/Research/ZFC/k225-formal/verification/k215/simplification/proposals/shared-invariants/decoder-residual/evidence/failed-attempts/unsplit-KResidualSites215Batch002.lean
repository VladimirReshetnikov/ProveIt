import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.KResidualFast215

/-! The 215's decoder sites, blocks 24 to 35 (579 leaves).
Reuses the exact maintained partition; checks only the routed residual suffix. -/

namespace SetTheory.BusyBeaver.ZFC.KResidualSites215

open RegisterPath RMBisim SiteCoverage KTableCore

/-- 80 leaves. -/
theorem block_24 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, true, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_25 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, true, true, true, false, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 29 leaves. -/
theorem block_26 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, true, true, true, false, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 20 leaves. -/
theorem block_27 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, true, true, true, true, false, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_28 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, true, true, true, true, false, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 47 leaves. -/
theorem block_29 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, true, true, true, true, false, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 26 leaves. -/
theorem block_30 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, true, true, true, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 27 leaves. -/
theorem block_31 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, false, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, false, false, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_32 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, false, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, false, false, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 2 leaves. -/
theorem block_33 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, true, false, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, false, false, true, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_34 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [true, true, true, false, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, false, false, true, true, true]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_35 :
    allSites (KResidualRouting215.checkLeafSuffix tm215) [false, true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, false, true, false]) = true := by
  exact KResidualFast215.allSites_of_fast (by decide +kernel)

end SetTheory.BusyBeaver.ZFC.KResidualSites215
