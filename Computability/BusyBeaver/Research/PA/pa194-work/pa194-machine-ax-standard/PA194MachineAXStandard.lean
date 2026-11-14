import PA194MachineStack
import PA194MachineAXCode
import PA194TargetLeavesStandard
import PA194TargetGate
import PA194CommandTransfer
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194MachineStack PA194TargetCantor PA194TargetLeaves PA194TargetLeavesStandard PA194TargetGate
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
namespace PA194MachineAXStandard

local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA

theorem stack_eq (D H A d h t w : Nat) :
    axStack D H A d h t w =
    ([PA194AXSymbolic.diagonal A] ++ PA196.Commands.Code.heads D H A d h ++ [t]).foldr M6.Source.Cantor.pair w := by
  have hp (x y : Nat) := modelCantorSelected (M := Nat) fixedCantor fixedCantor_certified x y
  have heval (x y : Nat) : Structure.func (L := language) fixedCantor ![x,y] = M6.Source.Cantor.pair x y := by
    change eval fixedCantor (List.Vector.ofFn ![x,y]) = _
    rw [ofFn_two]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using eval_fixedCantor x y
  have hpair := fun x y => (hp x y).symm.trans (heval x y)
  simp only [axStack,PA196.Commands.Code.heads,List.cons_append,List.nil_append,List.foldr_cons,List.foldr_nil,
    head1Value,head2Value,head3Value,head4Value,head5Value,head6Value,rho8Value,diagonalValue,
    (primitive_standard _ _).1,(primitive_standard _ _).2.1,(primitive_standard _ _).2.2.2.1,
    (primitive_standard _ _).2.2.2.2.1,(primitive_standard _ _).2.2.2.2.2,
    PA196.Commands.Code.head1,PA196.Commands.Code.head2,PA196.Commands.Code.head3,
    PA196.Commands.Code.head4,PA196.Commands.Code.head5,PA196.Commands.Code.head6,PA196.Commands.Code.rho8,
    PA194AXSymbolic.diagonal]
  simp only [hpair]

theorem top_eq (H D A : Nat) :
    axTop H D A = PA194AXReadable.guardedOldBundle H D A := by
  have hh := oldBundle_model (M := Nat) H D A
  change eval oldBundle (List.Vector.ofFn ![H,D,A]) = _ at hh
  rw [PA194TargetLeavesStandard.ofFn_three] at hh
  have hv := hh.symm.trans (PA194TargetGate.eval_oldBundle H D A)
  simp only [axTop,PA194AXReadable.guardedOldBundle,hv]
  split <;> rfl

theorem ax_command_eq (c x y : Nat) (s : PA196.Commands.Store) :
    PA194CommandTransfer.step (.ax c x y) s =
      some ⟨axTop (s.h+y) (s.d+x) c,
        axStack (s.d+x) (s.h+y) c s.d s.h s.t s.w,0,0⟩ := by
  simp only [PA194CommandTransfer.step,stack_eq,top_eq]


open PA194MachineAXCode
theorem ax_code_command {n : Nat} (t A d h y x w : Code n) (e : Fin n → Nat) :
    PA194CommandTransfer.step (.ax (Structure.func (L := language) A e) (Structure.func (L := language) x e) (Structure.func (L := language) y e))
      ⟨Structure.func (L := language) t e,Structure.func (L := language) w e,Structure.func (L := language) d e,Structure.func (L := language) h e⟩ =
    some ⟨Structure.func (L := language) (axTopCode A d h y x) e,Structure.func (L := language) (axStackCode t A d h y x w) e,0,0⟩ := by
  rw [ax_command_eq,axTop_model,axStack_model]
  have hadd (a b : Nat) := PA194TargetHead1Standard.localAdd_eq (M := Nat) a b
  have heval (a b : Nat) : Structure.func (L := language) addCode ![a,b] = a+b := by
    change eval addCode (List.Vector.ofFn ![a,b]) = _
    rw [ofFn_two]
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one] using eval_addCode a b
  have hadd' := fun a b => (hadd a b).trans (heval a b)
  simp only [hadd']
#print axioms stack_eq
#print axioms top_eq
#print axioms ax_command_eq
#print axioms ax_code_command

end PA194MachineAXStandard
