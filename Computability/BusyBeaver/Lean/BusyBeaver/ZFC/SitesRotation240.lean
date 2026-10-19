import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Join033

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

/-- All6455 leaves and8386 guards of the actual rotated decoder. -/
theorem all_sites : allSites SiteRotation240.checkSite [] TreeRotation240.tree = true :=
  SetTheory.BusyBeaver.ZFC.SitesRotation240.join_528

theorem actual_walk_checked (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk SourceRotation240.program (SourceRotation240.program.nnodes + 1) SourceRotation240.program.root P 0 = some (e,d)) :
    SiteRotation240.checkSite (consume P d) e = true :=
  allSites_walk SiteRotation240.checkSite SourceRotation240.program TreeRotation240.tree
    TreeRotation240.tree_eq all_sites P e d hw

theorem actual_walk_exists (P : List Bool) :
    ∃ e d, walk SourceRotation240.program (SourceRotation240.program.nnodes + 1) SourceRotation240.program.root P 0 = some (e,d) :=
  allSites_walk_total SiteRotation240.checkSite SourceRotation240.program TreeRotation240.tree
    TreeRotation240.tree_eq all_sites P

end SetTheory.BusyBeaver.ZFC.SitesRotation240
