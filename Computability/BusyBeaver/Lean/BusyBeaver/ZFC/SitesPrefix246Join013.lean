import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePrefix246
import BusyBeaver.ZFC.SitesPrefix246Join012
import BusyBeaver.ZFC.SitesPrefix246Batch083
import BusyBeaver.ZFC.SitesPrefix246Join011
import BusyBeaver.ZFC.SitesPrefix246Join010
import BusyBeaver.ZFC.SitesPrefix246Join008
import BusyBeaver.ZFC.SitesPrefix246Join005
import BusyBeaver.ZFC.SitesPrefix246Join000
import BusyBeaver.ZFC.SitesPrefix246Batch002
import BusyBeaver.ZFC.SitesPrefix246Batch084
import BusyBeaver.ZFC.SitesPrefix246Batch001

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

theorem join_208 :
    allSites SitePrefix246.checkSite [false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, true])
    join_207 block_222

theorem join_209 :
    allSites SitePrefix246.checkSite [true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, true])
    join_208 block_223

theorem join_210 :
    allSites SitePrefix246.checkSite [true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true])
    join_205 join_209

theorem join_211 :
    allSites SitePrefix246.checkSite [true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true])
    join_196 join_210

theorem join_212 :
    allSites SitePrefix246.checkSite [true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true])
    join_187 join_211

theorem join_213 :
    allSites SitePrefix246.checkSite [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true])
    join_163 join_212

theorem join_214 :
    allSites SitePrefix246.checkSite [true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true])
    join_133 join_213

theorem join_215 :
    allSites SitePrefix246.checkSite [true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true])
    join_93 join_214

theorem join_216 :
    allSites SitePrefix246.checkSite [false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true])
    join_1 join_215

theorem join_217 :
    allSites SitePrefix246.checkSite [true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, true])
    join_216 block_224

theorem join_218 :
    allSites SitePrefix246.checkSite [false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true])
    block_5 join_217

theorem join_219 :
    allSites SitePrefix246.checkSite [false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, true])
    join_218 block_225

theorem join_220 :
    allSites SitePrefix246.checkSite [true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, true])
    join_219 block_226

theorem join_221 :
    allSites SitePrefix246.checkSite [false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true])
    block_4 join_220

theorem join_222 :
    allSites SitePrefix246.checkSite [false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, true])
    join_221 block_227

theorem join_223 :
    allSites SitePrefix246.checkSite [true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, true])
    join_222 block_228


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
