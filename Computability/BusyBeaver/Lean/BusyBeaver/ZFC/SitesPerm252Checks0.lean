import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePerm252

/-!
Generated persisted batch of the exact permutation252 closed site checks.
All check expressions are unchanged from the original complete cut frontier.
The final SitesPerm252 module imports all batches and composes both children
at every cut against ActualTree254.tree. No external coverage premise is used.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesPerm252
open RegisterPath RMBisim SiteCoverage
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Chunk 0: 10 leaves, 13 guard cases. -/
theorem block_0 :
    allSites SitePerm252.checkSite [false]
      (descend ActualTree254.tree [false]) = true := by decide +kernel

/-- Chunk 1: 14 leaves, 19 guard cases. -/
theorem block_1 :
    allSites SitePerm252.checkSite [false, true]
      (descend ActualTree254.tree [true, false]) = true := by decide +kernel

/-- Chunk 2: 14 leaves, 19 guard cases. -/
theorem block_2 :
    allSites SitePerm252.checkSite [false, true, true]
      (descend ActualTree254.tree [true, true, false]) = true := by decide +kernel

/-- Chunk 3: 1 leaves, 2 guard cases. -/
theorem block_3 :
    allSites SitePerm252.checkSite [false, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, false]) = true := by decide +kernel

/-- Chunk 4: 1 leaves, 2 guard cases. -/
theorem block_4 :
    allSites SitePerm252.checkSite [false, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, false]) = true := by decide +kernel

/-- Chunk 5: 1 leaves, 2 guard cases. -/
theorem block_5 :
    allSites SitePerm252.checkSite [false, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, false]) = true := by decide +kernel

/-- Chunk 6: 26 leaves, 34 guard cases. -/
theorem block_6 :
    allSites SitePerm252.checkSite [false, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false]) = true := by decide +kernel

/-- Chunk 7: 26 leaves, 34 guard cases. -/
theorem block_7 :
    allSites SitePerm252.checkSite [true, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true]) = true := by decide +kernel

/-- Chunk 8: 29 leaves, 37 guard cases. -/
theorem block_8 :
    allSites SitePerm252.checkSite [true, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true]) = true := by decide +kernel

/-- Chunk 9: 14 leaves, 19 guard cases. -/
theorem block_9 :
    allSites SitePerm252.checkSite [false, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, false]) = true := by decide +kernel

/-- Chunk 10: 45 leaves, 59 guard cases. -/
theorem block_10 :
    allSites SitePerm252.checkSite [false, false, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, false, false]) = true := by decide +kernel

/-- Chunk 11: 41 leaves, 54 guard cases. -/
theorem block_11 :
    allSites SitePerm252.checkSite [true, false, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, false, true]) = true := by decide +kernel

/-- Chunk 12: 26 leaves, 34 guard cases. -/
theorem block_12 :
    allSites SitePerm252.checkSite [false, true, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, true, false]) = true := by decide +kernel

/-- Chunk 13: 27 leaves, 35 guard cases. -/
theorem block_13 :
    allSites SitePerm252.checkSite [true, true, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, true, true]) = true := by decide +kernel

/-- Chunk 14: 26 leaves, 34 guard cases. -/
theorem block_14 :
    allSites SitePerm252.checkSite [false, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false]) = true := by decide +kernel

/-- Chunk 15: 26 leaves, 34 guard cases. -/
theorem block_15 :
    allSites SitePerm252.checkSite [true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true]) = true := by decide +kernel

/-- Chunk 16: 27 leaves, 35 guard cases. -/
theorem block_16 :
    allSites SitePerm252.checkSite [true, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true]) = true := by decide +kernel

/-- Chunk 17: 19 leaves, 25 guard cases. -/
theorem block_17 :
    allSites SitePerm252.checkSite [false, false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false]) = true := by decide +kernel

/-- Chunk 18: 33 leaves, 43 guard cases. -/
theorem block_18 :
    allSites SitePerm252.checkSite [true, false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true]) = true := by decide +kernel

/-- Chunk 19: 27 leaves, 35 guard cases. -/
theorem block_19 :
    allSites SitePerm252.checkSite [false, true, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false]) = true := by decide +kernel

/-- Chunk 20: 27 leaves, 35 guard cases. -/
theorem block_20 :
    allSites SitePerm252.checkSite [true, true, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true]) = true := by decide +kernel

/-- Chunk 21: 27 leaves, 35 guard cases. -/
theorem block_21 :
    allSites SitePerm252.checkSite [false, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false]) = true := by decide +kernel

/-- Chunk 22: 26 leaves, 34 guard cases. -/
theorem block_22 :
    allSites SitePerm252.checkSite [false, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, false]) = true := by decide +kernel

/-- Chunk 23: 26 leaves, 34 guard cases. -/
theorem block_23 :
    allSites SitePerm252.checkSite [false, true, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true, false]) = true := by decide +kernel

/-- Chunk 24: 28 leaves, 36 guard cases. -/
theorem block_24 :
    allSites SitePerm252.checkSite [true, true, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true, true]) = true := by decide +kernel

/-- Chunk 25: 2 leaves, 2 guard cases. -/
theorem block_25 :
    allSites SitePerm252.checkSite [false, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, false]) = true := by decide +kernel

/-- Chunk 26: 45 leaves, 59 guard cases. -/
theorem block_26 :
    allSites SitePerm252.checkSite [false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, false, false]) = true := by decide +kernel

/-- Chunk 27: 7 leaves, 9 guard cases. -/
theorem block_27 :
    allSites SitePerm252.checkSite [true, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, false, true]) = true := by decide +kernel

/-- Chunk 28: 28 leaves, 36 guard cases. -/
theorem block_28 :
    allSites SitePerm252.checkSite [true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, true]) = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.SitesPerm252
