import PA194CommonStartupRows
import PA1944LRestrictedComplete

set_option autoImplicit false

namespace PA194CommonStartup
open ConPA.Machine PA194IndexedNumerals PA194IndexedRunRestriction
open PA194BRows (Action)

theorem fromRows (rows : List Action)
    (agree : ∀ (q : Fin 194) (b : Fin 2), ([107, 123] : List Nat).contains q.val = false →
        PA1944LData.rows.getD (2 * q.val + b.val) (0, 0, 194) =
          rows.getD (2 * q.val + b.val) (0, 0, 194)) :
    indexedRun rows 58320 = (24, 1, 152919395647067130113387679226998336721518593) := by
  have equal := transfer PA1944LData.rows rows [107, 123]
    (fun q b hq hb safe => agree ⟨q, hq⟩ ⟨b, hb⟩ safe) (0, 0, 0) 58320
    (congrArg Prod.fst PA1944LRestricted.certificate)
  rw [PA1944LRestricted.certificate] at equal
  exact equal

theorem lca :
    indexedRun PA194LCAData.rows 58320 = (24, 1, 152919395647067130113387679226998336721518593) :=
  fromRows PA194LCAData.rows PA194CommonStartupRows.lca

theorem m4r :
    indexedRun PA194M4RData.rows 58320 = (24, 1, 152919395647067130113387679226998336721518593) :=
  fromRows PA194M4RData.rows PA194CommonStartupRows.m4r

#print axioms lca
#print axioms m4r
end PA194CommonStartup
