import BusyBeaver.ZFC.SitesRotation240Join010

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_160
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_161
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_162
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_163
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_164
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_165
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_166
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_167
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_168
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_169
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_170
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_171
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_172
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_173
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_174
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_175

example : allSites SiteRotation240.checkSite [true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true]) = true := join_160

example : allSites SiteRotation240.checkSite [true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true]) = true := join_161

example : allSites SiteRotation240.checkSite [true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true]) = true := join_162

example : allSites SiteRotation240.checkSite [false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false]) = true := join_163

example : allSites SiteRotation240.checkSite [true, true, false, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, false, false, true, true]) = true := join_164

example : allSites SiteRotation240.checkSite [true, false, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, false, false, true]) = true := join_165

example : allSites SiteRotation240.checkSite [false, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, false, false]) = true := join_166

example : allSites SiteRotation240.checkSite [false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, false, true, false]) = true := join_167

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, false, true]) = true := join_168

example : allSites SiteRotation240.checkSite [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, false]) = true := join_169

example : allSites SiteRotation240.checkSite [false, false, false, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, false, false, false]) = true := join_170

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, false, false, true]) = true := join_171

example : allSites SiteRotation240.checkSite [false, false, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, false, false]) = true := join_172

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, false, true, false]) = true := join_173

example : allSites SiteRotation240.checkSite [true, false, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, false, true]) = true := join_174

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, false]) = true := join_175
