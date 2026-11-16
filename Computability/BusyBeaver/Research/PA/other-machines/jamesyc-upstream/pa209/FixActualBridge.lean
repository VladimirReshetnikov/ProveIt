module
public import FixTemplateBridge
public import OperatorBridge
public import PrimitiveMemberBridge
public import PrimitiveCoreBridge
@[expose] public section
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

theorem core_pi_to : PrimitiveData.core.toFoundation =
 (Nth.blueprint.core.pi : ArithmeticSemisentence 2) := by
 rw [core_to]
 rfl

theorem actualFixSucc_to :
 (fixSuccTemplate PrimitiveData.member PrimitiveData.core PrimitiveData.core).toFoundation =
 (Nth.blueprint.succDef : ArithmeticSemisentence 3) := by
 rw [fixSuccTemplate_to,member_to,core_to]
 unfold standardFixSucc Fixpoint.Blueprint.succDef
 have hpi : (Nth.blueprint.core.pi : ArithmeticSemisentence 2) =
   (Nth.blueprint.core.sigma : ArithmeticSemisentence 2) := rfl
 simp only [Bounding.HierarchySymbol.Semiformula.val_mkSigma,hpi,operator_subst]
 congr! 20
 all_goals first
  | rfl
  | (apply Rew.ext; · intro i; fin_cases i <;> rfl; · intro x; exact Empty.elim x)
  | (funext i; fin_cases i <;> rfl)
  | (rename_i i; fin_cases i <;> rfl)

#print axioms actualFixSucc_to
end PalomarPA
