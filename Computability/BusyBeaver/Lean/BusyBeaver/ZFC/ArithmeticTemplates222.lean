import BusyBeaver.ZFC.ArithmeticTemplates254
import BusyBeaver.ZFC.KCode222

set_option autoImplicit false
set_option Elab.async false

/-! The single changed equality template of C222, over arbitrary internal
IOpen inputs. This does not define the changed seed bundle or its checker. -/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticTemplates222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCode254 ArithmeticTemplates254

def growGCircuit : Circuit :=
  .im (.eq .input2 .input0)
    (.im (.eq .input2 .input1) (.al (.el .input0 .input1) (.eq .input0 .input1)))

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def growG (a b c : V) : V := growGCircuit.eval a b c 0

theorem growG_eq (a b c : V) : growG a b c =
    wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b))) := rfl

def growGDef : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(growGCircuit.graph) r a b c 0”

instance growG_defined : 𝚺₀-Function₃[V] growG via growGDef :=
  .mk fun v => by simp [growGDef, growG]

@[simp] theorem growG_nat (a b c : Nat) : growG a b c = KCode222.growG a b c := by
  simp only [growG_eq, wim_nat, weq_nat, wal_nat, wel_nat, KCode222.growG]

instance codeGrowG_defined :
    HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ KCode222.growG growGDef := by
  have h : (growG : Nat → Nat → Nat → Nat) = KCode222.growG :=
    funext fun a => funext fun b => funext fun c => growG_nat a b c
  rw [← h]
  exact growG_defined

end SetTheory.BusyBeaver.ZFC.ArithmeticTemplates222
