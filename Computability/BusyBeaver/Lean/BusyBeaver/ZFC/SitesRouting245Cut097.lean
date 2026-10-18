import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRouting245
import BusyBeaver.ZFC.SitesRouting245Cut097Part000
import BusyBeaver.ZFC.SitesRouting245Cut097Part001
import BusyBeaver.ZFC.SitesRouting245Cut097Part002

/-!
Closed coverage of the exact routed245 instruction tree. Every new cut is a
kernel decision about the imported actual subtree with its complete reverse
prefix; every composition requires both actual children. The three measured
pilot modules and thirteen passed original batches are reused directly. No external coverage premise, native proof
evaluation, or enlarged proof limits. Grouping changes only file boundaries.
Adapted from the maintained permutation252/prefix246 coverage generators,
preserving Mira-Cult, Jeff Ketchersid and Wade's program/simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesRouting245
open RegisterPath RMBisim SiteCoverage

theorem refine_97_0 :
    allSites SiteRouting245.checkSite [false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.part_97_0 SetTheory.BusyBeaver.ZFC.SitesRouting245.part_97_1

theorem block_97 :
    allSites SiteRouting245.checkSite [true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.refine_97_0 SetTheory.BusyBeaver.ZFC.SitesRouting245.part_97_2


end SetTheory.BusyBeaver.ZFC.SitesRouting245
