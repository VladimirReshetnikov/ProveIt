import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Batch000
import BusyBeaver.ZFC.SitesRotation240Join032

/-!
Closed coverage of the exact direct240 instruction tree. Every new cut is a
kernel decision about the imported actual subtree with its complete reverse
prefix; every composition requires both actual children. The four measured
pilot modules are reused directly. No external coverage premise, native proof
evaluation, or enlarged proof limits. Grouping changes only file boundaries.
Adapted from the maintained permutation252/prefix246 coverage generators,
preserving Mira-Cult, Jeff Ketchersid and Wade's program/simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesRotation240
open RegisterPath RMBisim SiteCoverage

theorem join_528 :
    allSites SiteRotation240.checkSite []
      (descend TreeRotation240.tree []) = true :=
  allSites_join SiteRotation240.checkSite []
    (descend TreeRotation240.tree [false])
    (descend TreeRotation240.tree [true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_0 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_527


end SetTheory.BusyBeaver.ZFC.SitesRotation240
