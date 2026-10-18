import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePrefix246
import BusyBeaver.ZFC.SitesPrefix246Batch002
import BusyBeaver.ZFC.SitesPrefix246Batch003
import BusyBeaver.ZFC.SitesPrefix246Batch004
import BusyBeaver.ZFC.SitesPrefix246Batch005
import BusyBeaver.ZFC.SitesPrefix246Batch006
import BusyBeaver.ZFC.SitesPrefix246Batch007
import BusyBeaver.ZFC.SitesPrefix246Batch008

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

theorem join_0 :
    allSites SitePrefix246.checkSite [false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true])
    block_6 block_7

theorem join_1 :
    allSites SitePrefix246.checkSite [false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true])
    join_0 block_8

theorem join_2 :
    allSites SitePrefix246.checkSite [false, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, false, true])
    block_10 block_11

theorem join_3 :
    allSites SitePrefix246.checkSite [true, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, true, true])
    block_12 block_13

theorem join_4 :
    allSites SitePrefix246.checkSite [true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, true])
    join_2 join_3

theorem join_5 :
    allSites SitePrefix246.checkSite [false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true])
    block_9 join_4

theorem join_6 :
    allSites SitePrefix246.checkSite [false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true])
    block_14 block_15

theorem join_7 :
    allSites SitePrefix246.checkSite [false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true])
    join_6 block_16

theorem join_8 :
    allSites SitePrefix246.checkSite [false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true])
    block_17 block_18

theorem join_9 :
    allSites SitePrefix246.checkSite [true, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true])
    block_19 block_20

theorem join_10 :
    allSites SitePrefix246.checkSite [true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true])
    join_8 join_9

theorem join_11 :
    allSites SitePrefix246.checkSite [true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true])
    join_7 join_10

theorem join_12 :
    allSites SitePrefix246.checkSite [false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true])
    join_5 join_11

theorem join_13 :
    allSites SitePrefix246.checkSite [true, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true, true])
    block_23 block_24

theorem join_14 :
    allSites SitePrefix246.checkSite [false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true])
    block_22 join_13

theorem join_15 :
    allSites SitePrefix246.checkSite [false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, false, true])
    block_26 block_27


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
