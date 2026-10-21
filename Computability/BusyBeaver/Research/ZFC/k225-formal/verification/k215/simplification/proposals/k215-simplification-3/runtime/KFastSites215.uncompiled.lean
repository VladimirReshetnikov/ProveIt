import BusyBeaver.ZFC.KFast215
import BusyBeaver.ZFC.KSim

/-!
UNCOMPILED RESEARCH DRAFT. No new evaluator or semantic axiom is introduced.
Install as BusyBeaver/ZFC/KFastSites215.lean before trying the accompanying patch.
The existing fast215 theorem binds the balanced lookup tree to the literal table.
-/

namespace SetTheory.BusyBeaver.ZFC.KFastSites215

open KBoot KBoot215 KTableCore KSim SiteCoverage RMBisim

theorem fast_eq : fastOf tt215 = tm215 :=
  funext fun q => funext fun b => fast215 q b

theorem allSites_of_fast {revPrefix : List Bool} {t : Tree}
    (h : allSites (checkEdge (fastOf tt215)) revPrefix t = true) :
    allSites (checkEdge tm215) revPrefix t = true := by
  rw [← fast_eq]
  exact h

end SetTheory.BusyBeaver.ZFC.KFastSites215
