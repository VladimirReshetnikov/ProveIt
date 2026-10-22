import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.KResidual215

/-! Residual K215 decoder sites, blocks 36 to 47 (515 leaves).
Partition inherited unchanged from generate_sites215_lean.py; checker changed by adapt_sites.py. -/

namespace SetTheory.BusyBeaver.ZFC.KResidualSites215

open RegisterPath RMBisim SiteCoverage KTableCore

/-- 80 leaves. -/
theorem block_36 :
    allSites (KResidual215.residualTest tm215) [false, true, true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, false, true, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_37 :
    allSites (KResidual215.residualTest tm215) [true, true, true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, false, true, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_38 :
    allSites (KResidual215.residualTest tm215) [false, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 2 leaves. -/
theorem block_39 :
    allSites (KResidual215.residualTest tm215) [false, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 26 leaves. -/
theorem block_40 :
    allSites (KResidual215.residualTest tm215) [false, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, true, false, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_41 :
    allSites (KResidual215.residualTest tm215) [false, false, true, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 29 leaves. -/
theorem block_42 :
    allSites (KResidual215.residualTest tm215) [true, false, true, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, true, false, false, true, false, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_43 :
    allSites (KResidual215.residualTest tm215) [false, true, true, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, true, false, false, true, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_44 :
    allSites (KResidual215.residualTest tm215) [false, false, true, true, true, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 29 leaves. -/
theorem block_45 :
    allSites (KResidual215.residualTest tm215) [true, false, true, true, true, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 1 leaves. -/
theorem block_46 :
    allSites (KResidual215.residualTest tm215) [true, true, true, true, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, true, false, false, true, true, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_47 :
    allSites (KResidual215.residualTest tm215) [false, true, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, true, false, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

end SetTheory.BusyBeaver.ZFC.KResidualSites215
