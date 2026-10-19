import BusyBeaver.ZFC.SitesRotation240PilotHalt

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240PilotHalt

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240PilotHalt.checked

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true, false]) = true := checked

example (Q : List Bool) (e : Edge)
    (hl : LeafAt (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true, false]) Q e) :
    SiteRotation240.checkSite ([false, true, true, false, true, false, false, true, false, true, true, true].reverse ++ Q) e = true :=
  allSites_sound SiteRotation240.checkSite hl [false, true, true, false, true, false, false, true, false, true, true, true] checked
