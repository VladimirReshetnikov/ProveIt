import BusyBeaver.ZFC.KResidualRouting215

namespace SetTheory.BusyBeaver.ZFC.KResidualFast215
open KBoot KBoot215 KTableCore KResidualRouting215 SiteCoverage RMBisim

theorem fast_eq : fastOf tt215 = tm215 :=
  funext fun q => funext fun b => fast215 q b

theorem allSites_of_fast {revPrefix : List Bool} {t : Tree}
    (h : allSites (checkLeafSuffix (fastOf tt215)) revPrefix t = true) :
    allSites (checkLeafSuffix tm215) revPrefix t = true := by
  rw [← fast_eq]
  exact h
end SetTheory.BusyBeaver.ZFC.KResidualFast215
