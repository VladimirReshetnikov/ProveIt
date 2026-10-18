import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePrefix246
import BusyBeaver.ZFC.SitesPrefix246Join000
import BusyBeaver.ZFC.SitesPrefix246Batch009
import BusyBeaver.ZFC.SitesPrefix246Batch008
import BusyBeaver.ZFC.SitesPrefix246Batch007
import BusyBeaver.ZFC.SitesPrefix246Batch010
import BusyBeaver.ZFC.SitesPrefix246Batch011
import BusyBeaver.ZFC.SitesPrefix246Batch012
import BusyBeaver.ZFC.SitesPrefix246Chunk041
import BusyBeaver.ZFC.SitesPrefix246Chunk042
import BusyBeaver.ZFC.SitesPrefix246Batch015

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

theorem join_16 :
    allSites SitePrefix246.checkSite [true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, true])
    join_15 block_28

theorem join_17 :
    allSites SitePrefix246.checkSite [true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true])
    block_25 join_16

theorem join_18 :
    allSites SitePrefix246.checkSite [true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true])
    join_14 join_17

theorem join_19 :
    allSites SitePrefix246.checkSite [false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true])
    block_21 join_18

theorem join_20 :
    allSites SitePrefix246.checkSite [false, false, true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false, false, true])
    block_30 block_31

theorem join_21 :
    allSites SitePrefix246.checkSite [false, true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false, true])
    join_20 block_32

theorem join_22 :
    allSites SitePrefix246.checkSite [true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, true])
    join_21 block_33

theorem join_23 :
    allSites SitePrefix246.checkSite [false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true])
    block_29 join_22

theorem join_24 :
    allSites SitePrefix246.checkSite [false, false, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false, false, true])
    block_34 block_35

theorem join_25 :
    allSites SitePrefix246.checkSite [false, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false, true])
    join_24 block_36

theorem join_26 :
    allSites SitePrefix246.checkSite [false, true, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true, false, true])
    block_37 block_38

theorem join_27 :
    allSites SitePrefix246.checkSite [true, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true, true])
    join_26 block_39

theorem join_28 :
    allSites SitePrefix246.checkSite [false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true])
    join_25 join_27

theorem join_29 :
    allSites SitePrefix246.checkSite [true, false, true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true, false, true, true])
    block_41 block_42

theorem join_30 :
    allSites SitePrefix246.checkSite [false, true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true, false, true])
    block_40 join_29

theorem join_31 :
    allSites SitePrefix246.checkSite [true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true, true])
    join_30 block_43


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
