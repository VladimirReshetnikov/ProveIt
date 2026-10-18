import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePrefix246
import BusyBeaver.ZFC.SitesPrefix246Join014

/-!
Generated closed actual-tree coverage for the exact246 table and checker.
Every cut is a kernel decision about the imported actual decoder subtree.
Every structural join requires both actual children. No external coverage
premise, native evaluation or enlarged proof limits. Grouping changes only
file boundaries, never the cut propositions or the full coverage statement.
Adapted from the maintained permutation252 and prefix250 generators, preserving
Mira-Cult, Jeff Ketchersid and Wade's program and simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesPrefix246
open RegisterPath RMBisim SiteCoverage

/-- Every leaf of the actual decoder has checked exact246 execution. -/
theorem all_sites : allSites SitePrefix246.checkSite [] ActualTree254.tree = true :=
  join_231

theorem actual_walk_checked (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 = some (e,d)) :
    SitePrefix246.checkSite (consume P d) e = true :=
  allSites_walk SitePrefix246.checkSite Prog254.program ActualTree254.tree
    ActualTree254.tree_eq all_sites P e d hw

theorem actual_walk_exists (P : List Bool) :
    ∃ e d, walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 = some (e,d) :=
  allSites_walk_total SitePrefix246.checkSite Prog254.program ActualTree254.tree
    ActualTree254.tree_eq all_sites P

end SetTheory.BusyBeaver.ZFC.SitesPrefix246
