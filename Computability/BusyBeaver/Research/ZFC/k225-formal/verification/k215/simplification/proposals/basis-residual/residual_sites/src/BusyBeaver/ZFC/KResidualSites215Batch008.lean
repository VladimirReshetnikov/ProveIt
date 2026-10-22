import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.KResidual215

/-! Residual K215 decoder sites, blocks 96 to 104 (191 leaves).
Partition inherited unchanged from generate_sites215_lean.py; checker changed by adapt_sites.py. -/

namespace SetTheory.BusyBeaver.ZFC.KResidualSites215

open RegisterPath RMBisim SiteCoverage KTableCore

/-- 12 leaves. -/
theorem block_96 :
    allSites (KResidual215.residualTest tm215) [true, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 6 leaves. -/
theorem block_97 :
    allSites (KResidual215.residualTest tm215) [true, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 13 leaves. -/
theorem block_98 :
    allSites (KResidual215.residualTest tm215) [true, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 70 leaves. -/
theorem block_99 :
    allSites (KResidual215.residualTest tm215) [false, true, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 36 leaves. -/
theorem block_100 :
    allSites (KResidual215.residualTest tm215) [true, true, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 1 leaves. -/
theorem block_101 :
    allSites (KResidual215.residualTest tm215) [true, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 26 leaves. -/
theorem block_102 :
    allSites (KResidual215.residualTest tm215) [true, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 1 leaves. -/
theorem block_103 :
    allSites (KResidual215.residualTest tm215) [true, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 26 leaves. -/
theorem block_104 :
    allSites (KResidual215.residualTest tm215) [true, true, true]
      (descend KSource215.t215 [true, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

end SetTheory.BusyBeaver.ZFC.KResidualSites215
