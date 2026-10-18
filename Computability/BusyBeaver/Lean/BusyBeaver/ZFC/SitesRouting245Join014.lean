import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRouting245
import BusyBeaver.ZFC.SitesRouting245Batch000
import BusyBeaver.ZFC.SitesRouting245Join013
import BusyBeaver.ZFC.SitesRouting245Cut230
import BusyBeaver.ZFC.SitesRouting245Cut231
import BusyBeaver.ZFC.SitesRouting245Cut232
import BusyBeaver.ZFC.SitesRouting245Cut233
import BusyBeaver.ZFC.SitesRouting245Cut234
import BusyBeaver.ZFC.SitesRouting245Cut235
import BusyBeaver.ZFC.SitesRouting245CutPilot000

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

theorem join_224 :
    allSites SiteRouting245.checkSite [false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_4 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_223

theorem join_225 :
    allSites SiteRouting245.checkSite [false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_224 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_230

theorem join_226 :
    allSites SiteRouting245.checkSite [true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_225 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_231

theorem join_227 :
    allSites SiteRouting245.checkSite [false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_3 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_226

theorem join_228 :
    allSites SiteRouting245.checkSite [false, false, true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, true, true, true]
    (descend TreeRouting245.tree [true, true, true, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_232 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_233

theorem join_229 :
    allSites SiteRouting245.checkSite [false, true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, true]
    (descend TreeRouting245.tree [true, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_228 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_234

theorem join_230 :
    allSites SiteRouting245.checkSite [true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true]
    (descend TreeRouting245.tree [true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_229 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_235

theorem join_231 :
    allSites SiteRouting245.checkSite [true, true, true]
      (descend TreeRouting245.tree [true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true]
    (descend TreeRouting245.tree [true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_227 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_230

theorem join_232 :
    allSites SiteRouting245.checkSite [true, true]
      (descend TreeRouting245.tree [true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true]
    (descend TreeRouting245.tree [true, true, false])
    (descend TreeRouting245.tree [true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_2 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_231

theorem join_233 :
    allSites SiteRouting245.checkSite [true]
      (descend TreeRouting245.tree [true]) = true :=
  allSites_join SiteRouting245.checkSite [true]
    (descend TreeRouting245.tree [true, false])
    (descend TreeRouting245.tree [true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_1 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_232

theorem join_234 :
    allSites SiteRouting245.checkSite []
      (descend TreeRouting245.tree []) = true :=
  allSites_join SiteRouting245.checkSite []
    (descend TreeRouting245.tree [false])
    (descend TreeRouting245.tree [true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245CutPilot000.checked SetTheory.BusyBeaver.ZFC.SitesRouting245.join_233


end SetTheory.BusyBeaver.ZFC.SitesRouting245
