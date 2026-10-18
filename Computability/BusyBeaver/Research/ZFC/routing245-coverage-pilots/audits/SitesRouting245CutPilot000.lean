import BusyBeaver.ZFC.SitesRouting245CutPilot000

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245CutPilot000

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245CutPilot000.checked

example : allSites SiteRouting245.checkSite [false]
      (descend TreeRouting245.tree [false]) = true := checked

example (Q : List Bool) (e : Edge)
    (hl : LeafAt (descend TreeRouting245.tree [false]) Q e) :
    SiteRouting245.checkSite ([false].reverse ++ Q) e = true :=
  allSites_sound SiteRouting245.checkSite hl [false] checked
