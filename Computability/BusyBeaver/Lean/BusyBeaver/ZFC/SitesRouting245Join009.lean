import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRouting245
import BusyBeaver.ZFC.SitesRouting245Join008
import BusyBeaver.ZFC.SitesRouting245Cut161
import BusyBeaver.ZFC.SitesRouting245Cut158
import BusyBeaver.ZFC.SitesRouting245Cut162
import BusyBeaver.ZFC.SitesRouting245Cut163
import BusyBeaver.ZFC.SitesRouting245Cut164
import BusyBeaver.ZFC.SitesRouting245Cut165
import BusyBeaver.ZFC.SitesRouting245Cut166
import BusyBeaver.ZFC.SitesRouting245Cut167
import BusyBeaver.ZFC.SitesRouting245Cut168
import BusyBeaver.ZFC.SitesRouting245Cut170
import BusyBeaver.ZFC.SitesRouting245Cut171
import BusyBeaver.ZFC.SitesRouting245Cut169
import BusyBeaver.ZFC.SitesRouting245Cut173
import BusyBeaver.ZFC.SitesRouting245CutPilot174
import BusyBeaver.ZFC.SitesRouting245Cut172

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

theorem join_144 :
    allSites SiteRouting245.checkSite [true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_143 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_161

theorem join_145 :
    allSites SiteRouting245.checkSite [false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_158 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_144

theorem join_146 :
    allSites SiteRouting245.checkSite [false, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_162 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_163

theorem join_147 :
    allSites SiteRouting245.checkSite [true, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_164 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_165

theorem join_148 :
    allSites SiteRouting245.checkSite [false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_146 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_147

theorem join_149 :
    allSites SiteRouting245.checkSite [false, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_166 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_167

theorem join_150 :
    allSites SiteRouting245.checkSite [true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_149 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_168

theorem join_151 :
    allSites SiteRouting245.checkSite [true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_148 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_150

theorem join_152 :
    allSites SiteRouting245.checkSite [false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_145 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_151

theorem join_153 :
    allSites SiteRouting245.checkSite [true, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_170 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_171

theorem join_154 :
    allSites SiteRouting245.checkSite [false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_169 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_153

theorem join_155 :
    allSites SiteRouting245.checkSite [true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_173 SetTheory.BusyBeaver.ZFC.SitesRouting245CutPilot174.checked

theorem join_156 :
    allSites SiteRouting245.checkSite [true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_172 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_155

theorem join_157 :
    allSites SiteRouting245.checkSite [true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_154 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_156

theorem join_158 :
    allSites SiteRouting245.checkSite [true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_152 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_157

theorem join_159 :
    allSites SiteRouting245.checkSite [true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_142 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_158


end SetTheory.BusyBeaver.ZFC.SitesRouting245
