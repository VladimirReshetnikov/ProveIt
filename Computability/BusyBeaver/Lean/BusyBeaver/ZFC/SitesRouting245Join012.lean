import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRouting245
import BusyBeaver.ZFC.SitesRouting245Join011
import BusyBeaver.ZFC.SitesRouting245Cut205
import BusyBeaver.ZFC.SitesRouting245Cut206
import BusyBeaver.ZFC.SitesRouting245Cut207
import BusyBeaver.ZFC.SitesRouting245Cut208
import BusyBeaver.ZFC.SitesRouting245Cut209
import BusyBeaver.ZFC.SitesRouting245Cut210
import BusyBeaver.ZFC.SitesRouting245Cut211
import BusyBeaver.ZFC.SitesRouting245Cut202
import BusyBeaver.ZFC.SitesRouting245Join000
import BusyBeaver.ZFC.SitesRouting245Cut213
import BusyBeaver.ZFC.SitesRouting245Cut214
import BusyBeaver.ZFC.SitesRouting245Cut215
import BusyBeaver.ZFC.SitesRouting245Cut216
import BusyBeaver.ZFC.SitesRouting245Cut212
import BusyBeaver.ZFC.SitesRouting245Cut217
import BusyBeaver.ZFC.SitesRouting245Cut218
import BusyBeaver.ZFC.SitesRouting245Cut220
import BusyBeaver.ZFC.SitesRouting245Cut221

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

theorem join_192 :
    allSites SiteRouting245.checkSite [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_191 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_205

theorem join_193 :
    allSites SiteRouting245.checkSite [false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_206 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_207

theorem join_194 :
    allSites SiteRouting245.checkSite [false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_208 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_209

theorem join_195 :
    allSites SiteRouting245.checkSite [false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_194 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_210

theorem join_196 :
    allSites SiteRouting245.checkSite [true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_195 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_211

theorem join_197 :
    allSites SiteRouting245.checkSite [true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_193 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_196

theorem join_198 :
    allSites SiteRouting245.checkSite [true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_192 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_197

theorem join_199 :
    allSites SiteRouting245.checkSite [true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_202 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_198

theorem join_200 :
    allSites SiteRouting245.checkSite [true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_190 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_199

theorem join_201 :
    allSites SiteRouting245.checkSite [false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_8 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_200

theorem join_202 :
    allSites SiteRouting245.checkSite [false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_213 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_214

theorem join_203 :
    allSites SiteRouting245.checkSite [false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_202 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_215

theorem join_204 :
    allSites SiteRouting245.checkSite [true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_203 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_216

theorem join_205 :
    allSites SiteRouting245.checkSite [false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_212 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_204

theorem join_206 :
    allSites SiteRouting245.checkSite [false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_217 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_218

theorem join_207 :
    allSites SiteRouting245.checkSite [true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_220 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_221


end SetTheory.BusyBeaver.ZFC.SitesRouting245
