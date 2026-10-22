import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.KResidual215

/-! Residual K215 decoder sites, blocks 12 to 23 (515 leaves).
Partition inherited unchanged from generate_sites215_lean.py; checker changed by adapt_sites.py. -/

namespace SetTheory.BusyBeaver.ZFC.KResidualSites215

open RegisterPath RMBisim SiteCoverage KTableCore

/-- 79 leaves. -/
theorem block_12 :
    allSites (KResidual215.residualTest tm215) [false, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 54 leaves. -/
theorem block_13 :
    allSites (KResidual215.residualTest tm215) [false, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 27 leaves. -/
theorem block_14 :
    allSites (KResidual215.residualTest tm215) [false, false, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_15 :
    allSites (KResidual215.residualTest tm215) [false, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 2 leaves. -/
theorem block_16 :
    allSites (KResidual215.residualTest tm215) [false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_17 :
    allSites (KResidual215.residualTest tm215) [true, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 2 leaves. -/
theorem block_18 :
    allSites (KResidual215.residualTest tm215) [false, false, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_19 :
    allSites (KResidual215.residualTest tm215) [false, true, false, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, false, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_20 :
    allSites (KResidual215.residualTest tm215) [false, false, true, true, false, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, false, true, true, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 29 leaves. -/
theorem block_21 :
    allSites (KResidual215.residualTest tm215) [true, false, true, true, false, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, false, true, true, false, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 1 leaves. -/
theorem block_22 :
    allSites (KResidual215.residualTest tm215) [true, true, true, false, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, false, true, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 29 leaves. -/
theorem block_23 :
    allSites (KResidual215.residualTest tm215) [false, true, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, false, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

end SetTheory.BusyBeaver.ZFC.KResidualSites215
