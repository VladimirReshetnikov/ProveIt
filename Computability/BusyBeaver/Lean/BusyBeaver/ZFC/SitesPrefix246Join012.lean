import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePrefix246
import BusyBeaver.ZFC.SitesPrefix246Batch076
import BusyBeaver.ZFC.SitesPrefix246Batch077
import BusyBeaver.ZFC.SitesPrefix246Join011
import BusyBeaver.ZFC.SitesPrefix246Chunk210
import BusyBeaver.ZFC.SitesPrefix246Batch079
import BusyBeaver.ZFC.SitesPrefix246Batch080
import BusyBeaver.ZFC.SitesPrefix246Batch081
import BusyBeaver.ZFC.SitesPrefix246Batch082
import BusyBeaver.ZFC.SitesPrefix246Batch083

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

theorem join_192 :
    allSites SitePrefix246.checkSite [false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false, false, true])
    block_205 block_206

theorem join_193 :
    allSites SitePrefix246.checkSite [false, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false, true])
    join_192 block_207

theorem join_194 :
    allSites SitePrefix246.checkSite [true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, true])
    join_193 block_208

theorem join_195 :
    allSites SitePrefix246.checkSite [true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true])
    join_191 join_194

theorem join_196 :
    allSites SitePrefix246.checkSite [false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true])
    join_190 join_195

theorem join_197 :
    allSites SitePrefix246.checkSite [false, false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, false, true])
    block_210 block_211

theorem join_198 :
    allSites SitePrefix246.checkSite [false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, true])
    join_197 block_212

theorem join_199 :
    allSites SitePrefix246.checkSite [true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, true])
    join_198 block_213

theorem join_200 :
    allSites SitePrefix246.checkSite [false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true])
    block_209 join_199

theorem join_201 :
    allSites SitePrefix246.checkSite [false, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false, true])
    block_214 block_215

theorem join_202 :
    allSites SitePrefix246.checkSite [true, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true, true])
    block_217 block_218

theorem join_203 :
    allSites SitePrefix246.checkSite [true, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true])
    block_216 join_202

theorem join_204 :
    allSites SitePrefix246.checkSite [true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true])
    join_201 join_203

theorem join_205 :
    allSites SitePrefix246.checkSite [false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true])
    join_200 join_204

theorem join_206 :
    allSites SitePrefix246.checkSite [true, false, false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false, true, true])
    block_220 block_221

theorem join_207 :
    allSites SitePrefix246.checkSite [false, false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false, true])
    block_219 join_206


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
