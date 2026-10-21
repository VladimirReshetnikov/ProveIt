import BusyBeaver.ZFC.KSites215

namespace K215CompactSiteAudit

open SetTheory.BusyBeaver.ZFC

example : SiteCoverage.allSites (KSim.checkEdge KTableCore.tm215) [] KSource215.t215 = true :=
  KSites215.all_sites

example : KSim.Covered KTableCore.tm215 KSource215.p215 := KSites215.covered

#print axioms KSites215.all_sites
#print axioms KSites215.covered

end K215CompactSiteAudit
