import BusyBeaver.ZFC.SitesRouting245Join010

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_160
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_161
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_162
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_163
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_164
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_165
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_166
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_167
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_168
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_169
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_170
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_171
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_172
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_173
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_174
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_175

example : allSites SiteRouting245.checkSite [true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true]) = true := join_160

example : allSites SiteRouting245.checkSite [false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false]) = true := join_161

example : allSites SiteRouting245.checkSite [true, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, true]) = true := join_162

example : allSites SiteRouting245.checkSite [true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true]) = true := join_163

example : allSites SiteRouting245.checkSite [false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false]) = true := join_164

example : allSites SiteRouting245.checkSite [false, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, false]) = true := join_165

example : allSites SiteRouting245.checkSite [false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false, true, false]) = true := join_166

example : allSites SiteRouting245.checkSite [true, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false, true]) = true := join_167

example : allSites SiteRouting245.checkSite [false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false]) = true := join_168

example : allSites SiteRouting245.checkSite [false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false]) = true := join_169

example : allSites SiteRouting245.checkSite [true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, true]) = true := join_170

example : allSites SiteRouting245.checkSite [true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true]) = true := join_171

example : allSites SiteRouting245.checkSite [true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true]) = true := join_172

example : allSites SiteRouting245.checkSite [false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false]) = true := join_173

example : allSites SiteRouting245.checkSite [false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false]) = true := join_174

example : allSites SiteRouting245.checkSite [true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, true]) = true := join_175
