import BusyBeaver.ZFC.SitesRouting245Join011

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_176
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_177
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_178
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_179
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_180
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_181
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_182
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_183
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_184
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_185
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_186
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_187
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_188
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_189
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_190
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_191

example : allSites SiteRouting245.checkSite [true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true]) = true := join_176

example : allSites SiteRouting245.checkSite [true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true]) = true := join_177

example : allSites SiteRouting245.checkSite [true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true]) = true := join_178

example : allSites SiteRouting245.checkSite [false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false]) = true := join_179

example : allSites SiteRouting245.checkSite [true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true]) = true := join_180

example : allSites SiteRouting245.checkSite [false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false]) = true := join_181

example : allSites SiteRouting245.checkSite [true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true]) = true := join_182

example : allSites SiteRouting245.checkSite [false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false]) = true := join_183

example : allSites SiteRouting245.checkSite [false, true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true, false]) = true := join_184

example : allSites SiteRouting245.checkSite [true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true]) = true := join_185

example : allSites SiteRouting245.checkSite [true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true]) = true := join_186

example : allSites SiteRouting245.checkSite [true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true]) = true := join_187

example : allSites SiteRouting245.checkSite [true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true]) = true := join_188

example : allSites SiteRouting245.checkSite [true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true]) = true := join_189

example : allSites SiteRouting245.checkSite [false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false]) = true := join_190

example : allSites SiteRouting245.checkSite [false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false]) = true := join_191
