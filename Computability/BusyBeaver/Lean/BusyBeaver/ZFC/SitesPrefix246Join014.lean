import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePrefix246
import BusyBeaver.ZFC.SitesPrefix246Batch001
import BusyBeaver.ZFC.SitesPrefix246Join013
import BusyBeaver.ZFC.SitesPrefix246Batch085
import BusyBeaver.ZFC.SitesPrefix246Chunk000

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

theorem join_224 :
    allSites SitePrefix246.checkSite [false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true])
    block_3 join_223

theorem join_225 :
    allSites SitePrefix246.checkSite [false, false, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, true, true, true]
    (descend ActualTree254.tree [true, true, true, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, true, false, false, true])
    block_229 block_230

theorem join_226 :
    allSites SitePrefix246.checkSite [false, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, true, true]
    (descend ActualTree254.tree [true, true, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, true, false, true])
    join_225 block_231

theorem join_227 :
    allSites SitePrefix246.checkSite [true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, true]
    (descend ActualTree254.tree [true, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, true, true])
    join_226 block_232

theorem join_228 :
    allSites SitePrefix246.checkSite [true, true, true]
      (descend ActualTree254.tree [true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true]
    (descend ActualTree254.tree [true, true, true, false])
    (descend ActualTree254.tree [true, true, true, true])
    join_224 join_227

theorem join_229 :
    allSites SitePrefix246.checkSite [true, true]
      (descend ActualTree254.tree [true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true]
    (descend ActualTree254.tree [true, true, false])
    (descend ActualTree254.tree [true, true, true])
    block_2 join_228

theorem join_230 :
    allSites SitePrefix246.checkSite [true]
      (descend ActualTree254.tree [true]) = true :=
  allSites_join SitePrefix246.checkSite [true]
    (descend ActualTree254.tree [true, false])
    (descend ActualTree254.tree [true, true])
    block_1 join_229

theorem join_231 :
    allSites SitePrefix246.checkSite []
      (descend ActualTree254.tree []) = true :=
  allSites_join SitePrefix246.checkSite []
    (descend ActualTree254.tree [false])
    (descend ActualTree254.tree [true])
    block_0 join_230


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
