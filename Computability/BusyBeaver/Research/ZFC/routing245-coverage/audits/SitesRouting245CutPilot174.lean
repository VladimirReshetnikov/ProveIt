import BusyBeaver.ZFC.SitesRouting245CutPilot174

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245CutPilot174

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245CutPilot174.checked

example : allSites SiteRouting245.checkSite [true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, true]) = true := checked

example (Q : List Bool) (e : Edge)
    (hl : LeafAt (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, true]) Q e) :
    SiteRouting245.checkSite ([true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true].reverse ++ Q) e = true :=
  allSites_sound SiteRouting245.checkSite hl [true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true] checked
