import BusyBeaver.ZFC.SitesRotation240PilotLongZero

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240PilotLongZero

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240PilotLongZero.checked

example : allSites SiteRotation240.checkSite [false, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false]) = true := checked

example (Q : List Bool) (e : Edge)
    (hl : LeafAt (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false]) Q e) :
    SiteRotation240.checkSite ([false, false, false, false, true, false, false, true, false, false, true, false, true, true, true].reverse ++ Q) e = true :=
  allSites_sound SiteRotation240.checkSite hl [false, false, false, false, true, false, false, true, false, false, true, false, true, true, true] checked
