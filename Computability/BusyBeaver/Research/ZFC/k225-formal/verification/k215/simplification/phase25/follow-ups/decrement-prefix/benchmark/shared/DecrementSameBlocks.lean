import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.KFastSites215

namespace SetTheory.BusyBeaver.ZFC.KSites215

open RegisterPath RMBisim SiteCoverage KTableCore

/-- 9 leaves. -/
theorem block_0 :
    allSites (KSim.checkEdge tm215) [false]
      (descend KSource215.t215 [false]) = true := by
  exact KFastSites215.allSites_of_fast (by decide +kernel)

#print axioms block_0

/-- 52 leaves. -/
theorem block_5 :
    allSites (KSim.checkEdge tm215) [false, false, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, false, false]) = true := by
  exact KFastSites215.allSites_of_fast (by decide +kernel)

#print axioms block_5

/-- 67 leaves. -/
theorem block_10 :
    allSites (KSim.checkEdge tm215) [false, true, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true]
      (descend KSource215.t215 [true, true, false, true, false, false, true, false, false, true, true, true, false, false, true, true, false]) = true := by
  exact KFastSites215.allSites_of_fast (by decide +kernel)

#print axioms block_10

end SetTheory.BusyBeaver.ZFC.KSites215
