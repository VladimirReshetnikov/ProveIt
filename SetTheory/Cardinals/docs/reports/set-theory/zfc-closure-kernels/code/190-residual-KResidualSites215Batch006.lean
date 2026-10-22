import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.KResidual215

/-! Residual K215 decoder sites, blocks 72 to 83 (685 leaves).
Partition inherited unchanged from generate_sites215_lean.py; checker changed by adapt_sites.py. -/

namespace SetTheory.BusyBeaver.ZFC.KResidualSites215

open RegisterPath RMBisim SiteCoverage KTableCore

/-- 80 leaves. -/
theorem block_72 :
    allSites (KResidual215.residualTest tm215) [true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_73 :
    allSites (KResidual215.residualTest tm215) [false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, true, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_74 :
    allSites (KResidual215.residualTest tm215) [false, false, true, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, true, false, true, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 52 leaves. -/
theorem block_75 :
    allSites (KResidual215.residualTest tm215) [true, false, true, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, true, false, true, false, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 80 leaves. -/
theorem block_76 :
    allSites (KResidual215.residualTest tm215) [true, true, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, true, false, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 47 leaves. -/
theorem block_77 :
    allSites (KResidual215.residualTest tm215) [false, true, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, true, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_78 :
    allSites (KResidual215.residualTest tm215) [false, true, true, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, true, true, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 47 leaves. -/
theorem block_79 :
    allSites (KResidual215.residualTest tm215) [true, true, true, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_80 :
    allSites (KResidual215.residualTest tm215) [false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_81 :
    allSites (KResidual215.residualTest tm215) [false, true, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, true, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 47 leaves. -/
theorem block_82 :
    allSites (KResidual215.residualTest tm215) [false, false, true, true, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, true, true, true, false, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

/-- 56 leaves. -/
theorem block_83 :
    allSites (KResidual215.residualTest tm215) [false, true, false, true, true, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, true, true, true, true, true, false, true, false]) = true := by
  exact KResidual215.allSites_of_fast (by decide +kernel)

end SetTheory.BusyBeaver.ZFC.KResidualSites215
