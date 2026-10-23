import BusyBeaver.ZFC.KFast215
import BusyBeaver.ZFC.KSim

/-!
Transfer site checks through the existing all-state equality of the balanced
transition lookup and the literal table. No evaluator or machine definition changes.
Adapted from Source175 (beaabc8e3b), runtime/KFastSites215.uncompiled.lean.
The two proof bodies are unchanged from that submitted prototype.
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
