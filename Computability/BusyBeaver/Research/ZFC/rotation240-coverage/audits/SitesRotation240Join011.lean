import BusyBeaver.ZFC.SitesRotation240Join011

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_176
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_177
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_178
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_179
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_180
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_181
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_182
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_183
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_184
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_185
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_186
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_187
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_188
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_189
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_190
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_191

example : allSites SiteRotation240.checkSite [false, false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, false]) = true := join_176

example : allSites SiteRotation240.checkSite [true, false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, true]) = true := join_177

example : allSites SiteRotation240.checkSite [false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false]) = true := join_178

example : allSites SiteRotation240.checkSite [true, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, true]) = true := join_179

example : allSites SiteRotation240.checkSite [true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true]) = true := join_180

example : allSites SiteRotation240.checkSite [true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true]) = true := join_181

example : allSites SiteRotation240.checkSite [false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false]) = true := join_182

example : allSites SiteRotation240.checkSite [true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, true, true]) = true := join_183

example : allSites SiteRotation240.checkSite [true, false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, true]) = true := join_184

example : allSites SiteRotation240.checkSite [false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false]) = true := join_185

example : allSites SiteRotation240.checkSite [false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false]) = true := join_186

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true]) = true := join_187

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false]) = true := join_188

example : allSites SiteRotation240.checkSite [false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false]) = true := join_189

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, false, true]) = true := join_190

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, false]) = true := join_191
