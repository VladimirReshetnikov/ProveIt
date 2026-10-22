import BusyBeaver.ZFC.KQHyp
import BusyBeaver.ZFC.QuotientBasic
import BusyBeaver.ZFC.QuotientPower

/- Proposed staging adapter. Not compiler-checked here. No new axioms. -/
namespace SetTheory.BusyBeaver.ZFC.CPGICQHyp
open ProfileModel CompositionModel
universe u
variable {V : Type u}

/-- The old stronger model interface supplies the existing weaker quotient interface. -/
def ofCPGIC (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    KQHyp.QHyp mem where
  gic := h.2
  refl := eqv_refl_of_model mem witness h
  symm := fun hxy => eqv_symm_of_model mem witness h hxy
  trans := fun hxy hyz => eqv_trans_of_model mem witness h hxy hyz
  ext := eqv_extensionality_of_model mem witness h
  pairs := pairs_of_model mem witness h
  union := QuotientBasic.interpreted_union mem witness h
  power := QuotientPower.interpreted_power mem witness h
  singleton := QuotientBasic.interpreted_singleton_closed mem witness h

#print axioms ofCPGIC
end SetTheory.BusyBeaver.ZFC.CPGICQHyp
