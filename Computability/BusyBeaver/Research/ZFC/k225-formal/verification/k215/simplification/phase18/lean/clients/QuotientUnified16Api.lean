import BusyBeaver.ZFC.QuotientCPGIC

open SetTheory SetTheory.BusyBeaver.ZFC
open Form Profile ProfilePairs ProfileCollection ProfileComposition ProfileSyntax
open ProfileModel CompositionModel DeepPositiveClosure

namespace QuotientUnified16Api
universe u
variable {V : Type u}

/-- The exact setoid shape used by the phase15 strong quotient. -/
def legacySetoid (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) : Setoid V where
  r := Eqv mem
  iseqv := ⟨eqv_refl_of_model mem witness h,
    fun hxy => eqv_symm_of_model mem witness h hxy,
    fun hxy hyz => eqv_trans_of_model mem witness h hxy hyz⟩

theorem legacy_carrier (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    QuotientModel.Domain mem witness h = Quotient (legacySetoid mem witness h) := rfl

theorem legacy_constructor (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) (x : V) :
    QuotientModel.mk mem witness h x = Quotient.mk (legacySetoid mem witness h) x := rfl

theorem weak_carrier (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    QuotientModel.Domain mem witness h =
      KQ1Model.Domain mem witness (QuotientModel.ofCPGIC mem witness h) := rfl

theorem weak_constructor (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) (x : V) :
    QuotientModel.mk mem witness h x =
      KQ1Model.mk mem witness (QuotientModel.ofCPGIC mem witness h) x := rfl

theorem weak_membership (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (x y : QuotientModel.Domain mem witness h) :
    QuotientModel.quotientMember mem witness h x y ↔
      KQ1Model.quotientMember mem witness (QuotientModel.ofCPGIC mem witness h) x y := Iff.rfl

theorem cp_gic_supplies_weak (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    KQHyp.QHyp mem := QuotientModel.ofCPGIC mem witness h

/-- Native-equality formulas remain available under only the weak hypotheses. -/
theorem weak_native_gic (mem : V → V → Prop) (witness : V) (h : KQHyp.QHyp mem) :
    ∀ phi env, Sat (KQ1Model.quotientMember mem witness h) env (gicForm phi) :=
  KQ1Collect.quotient_fullGIC mem witness h

/-- The strong public CP/GIC conclusion retains its original stronger premise. -/
theorem strong_cp_gic (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    ModelsCPGIC (QuotientModel.quotientMember mem witness h) :=
  QuotientCPGIC.quotient_modelsCPGIC mem witness h

#print axioms legacy_carrier
#print axioms legacy_constructor
#print axioms weak_carrier
#print axioms weak_constructor
#print axioms weak_membership
#print axioms cp_gic_supplies_weak
#print axioms weak_native_gic
#print axioms strong_cp_gic
end QuotientUnified16Api
