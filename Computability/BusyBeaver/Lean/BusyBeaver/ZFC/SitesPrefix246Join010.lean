import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePrefix246
import BusyBeaver.ZFC.SitesPrefix246Batch063
import BusyBeaver.ZFC.SitesPrefix246Join009
import BusyBeaver.ZFC.SitesPrefix246Batch064
import BusyBeaver.ZFC.SitesPrefix246Batch065
import BusyBeaver.ZFC.SitesPrefix246Batch066
import BusyBeaver.ZFC.SitesPrefix246Batch067
import BusyBeaver.ZFC.SitesPrefix246Batch068
import BusyBeaver.ZFC.SitesPrefix246Batch069
import BusyBeaver.ZFC.SitesPrefix246Batch070

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

theorem join_160 :
    allSites SitePrefix246.checkSite [true, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, true, true])
    block_172 block_173

theorem join_161 :
    allSites SitePrefix246.checkSite [true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, true])
    join_159 join_160

theorem join_162 :
    allSites SitePrefix246.checkSite [true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true])
    join_154 join_161

theorem join_163 :
    allSites SitePrefix246.checkSite [false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true])
    join_144 join_162

theorem join_164 :
    allSites SitePrefix246.checkSite [false, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, false, true])
    block_174 block_175

theorem join_165 :
    allSites SitePrefix246.checkSite [false, true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true, false, true])
    block_177 block_178

theorem join_166 :
    allSites SitePrefix246.checkSite [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true, true])
    join_165 block_179

theorem join_167 :
    allSites SitePrefix246.checkSite [false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true])
    block_176 join_166

theorem join_168 :
    allSites SitePrefix246.checkSite [false, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, false, true])
    block_180 block_181

theorem join_169 :
    allSites SitePrefix246.checkSite [true, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true, true, true])
    block_183 block_184

theorem join_170 :
    allSites SitePrefix246.checkSite [true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true, true])
    block_182 join_169

theorem join_171 :
    allSites SitePrefix246.checkSite [true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true])
    join_168 join_170

theorem join_172 :
    allSites SitePrefix246.checkSite [true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true])
    join_167 join_171

theorem join_173 :
    allSites SitePrefix246.checkSite [false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true])
    join_164 join_172

theorem join_174 :
    allSites SitePrefix246.checkSite [false, false, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, false, false, true])
    block_185 block_186

theorem join_175 :
    allSites SitePrefix246.checkSite [true, true, false, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, false, true, true, true])
    block_188 block_189


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
