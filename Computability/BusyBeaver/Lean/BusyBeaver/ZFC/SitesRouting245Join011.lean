import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRouting245
import BusyBeaver.ZFC.SitesRouting245Cut190
import BusyBeaver.ZFC.SitesRouting245Join010
import BusyBeaver.ZFC.SitesRouting245Cut194
import BusyBeaver.ZFC.SitesRouting245Cut195
import BusyBeaver.ZFC.SitesRouting245Cut193
import BusyBeaver.ZFC.SitesRouting245Cut197
import BusyBeaver.ZFC.SitesRouting245Cut198
import BusyBeaver.ZFC.SitesRouting245Cut196
import BusyBeaver.ZFC.SitesRouting245Cut199
import BusyBeaver.ZFC.SitesRouting245Cut200
import BusyBeaver.ZFC.SitesRouting245Cut201
import BusyBeaver.ZFC.SitesRouting245Join000
import BusyBeaver.ZFC.SitesRouting245Cut203
import BusyBeaver.ZFC.SitesRouting245Cut204

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

theorem join_176 :
    allSites SiteRouting245.checkSite [true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_190 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_175

theorem join_177 :
    allSites SiteRouting245.checkSite [true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_174 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_176

theorem join_178 :
    allSites SiteRouting245.checkSite [true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_173 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_177

theorem join_179 :
    allSites SiteRouting245.checkSite [false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_165 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_178

theorem join_180 :
    allSites SiteRouting245.checkSite [true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_194 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_195

theorem join_181 :
    allSites SiteRouting245.checkSite [false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_193 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_180

theorem join_182 :
    allSites SiteRouting245.checkSite [true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_197 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_198

theorem join_183 :
    allSites SiteRouting245.checkSite [false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_196 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_182

theorem join_184 :
    allSites SiteRouting245.checkSite [false, true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_199 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_200

theorem join_185 :
    allSites SiteRouting245.checkSite [true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_184 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_201

theorem join_186 :
    allSites SiteRouting245.checkSite [true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_183 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_185

theorem join_187 :
    allSites SiteRouting245.checkSite [true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_181 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_186

theorem join_188 :
    allSites SiteRouting245.checkSite [true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_179 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_187

theorem join_189 :
    allSites SiteRouting245.checkSite [true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_164 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_188

theorem join_190 :
    allSites SiteRouting245.checkSite [false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_9 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_189

theorem join_191 :
    allSites SiteRouting245.checkSite [false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_203 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_204


end SetTheory.BusyBeaver.ZFC.SitesRouting245
