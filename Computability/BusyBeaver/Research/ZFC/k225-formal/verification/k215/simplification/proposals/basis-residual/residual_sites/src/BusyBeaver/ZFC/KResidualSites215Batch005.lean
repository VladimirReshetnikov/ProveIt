import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.KResidual215

/-! Residual K215 decoder sites, blocks 60 to 71 (681 leaves).
Partition inherited unchanged from generate_sites215_lean.py; checker changed by adapt_sites.py. -/

namespace SetTheory.BusyBeaver.ZFC.KResidualSites215

open RegisterPath RMBisim SiteCoverage KTableCore

/-- 20 leaves. -/
theorem block_60 :
    allSites (KResidual215.residualTest tm215) [false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_61 :
    allSites (KResidual215.residualTest tm215) [false, true, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, true, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 47 leaves. -/
theorem block_62 :
    allSites (KResidual215.residualTest tm215) [true, true, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, true, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_63 :
    allSites (KResidual215.residualTest tm215) [false, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 26 leaves. -/
theorem block_64 :
    allSites (KResidual215.residualTest tm215) [false, false, false, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, false, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_65 :
    allSites (KResidual215.residualTest tm215) [false, true, false, false, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, false, false, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_66 :
    allSites (KResidual215.residualTest tm215) [true, true, false, false, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, false, false, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_67 :
    allSites (KResidual215.residualTest tm215) [false, true, false, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, false, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_68 :
    allSites (KResidual215.residualTest tm215) [true, true, false, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, false, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_69 :
    allSites (KResidual215.residualTest tm215) [false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_70 :
    allSites (KResidual215.residualTest tm215) [false, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, false, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_71 :
    allSites (KResidual215.residualTest tm215) [false, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, false, true, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

end SetTheory.BusyBeaver.ZFC.KResidualSites215
