import BusyBeaver.ZFC.SitesRouting245Join009

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_144
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_145
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_146
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_147
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_148
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_149
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_150
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_151
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_152
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_153
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_154
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_155
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_156
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_157
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_158
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_159

example : allSites SiteRouting245.checkSite [true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true]) = true := join_144

example : allSites SiteRouting245.checkSite [false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false]) = true := join_145

example : allSites SiteRouting245.checkSite [false, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, false]) = true := join_146

example : allSites SiteRouting245.checkSite [true, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true]) = true := join_147

example : allSites SiteRouting245.checkSite [false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false]) = true := join_148

example : allSites SiteRouting245.checkSite [false, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true, false]) = true := join_149

example : allSites SiteRouting245.checkSite [true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true]) = true := join_150

example : allSites SiteRouting245.checkSite [true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true]) = true := join_151

example : allSites SiteRouting245.checkSite [false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false]) = true := join_152

example : allSites SiteRouting245.checkSite [true, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, true]) = true := join_153

example : allSites SiteRouting245.checkSite [false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false]) = true := join_154

example : allSites SiteRouting245.checkSite [true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true]) = true := join_155

example : allSites SiteRouting245.checkSite [true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true]) = true := join_156

example : allSites SiteRouting245.checkSite [true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true]) = true := join_157

example : allSites SiteRouting245.checkSite [true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true]) = true := join_158

example : allSites SiteRouting245.checkSite [true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true]) = true := join_159
