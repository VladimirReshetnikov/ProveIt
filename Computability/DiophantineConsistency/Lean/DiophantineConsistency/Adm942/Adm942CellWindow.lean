import DiophantineConsistency.ArithmeticWangSoundness
import DiophantineConsistency.Adm942.Adm942WindowInterface
import DiophantineConsistency.Adm942.Adm942Occupation

/-! # Window ⇒ marked word ⇒ halt at admissible942

The counterpart of `ArithmeticCellWindow`, in every model of IΣ1 (soundness spec
§4–§6). The admissible942 window `Adm942WindowInterface.Window` is the cell input
`Adm942CellTransfer.CellInput` with the explicit end-around carry
`carryDigit N W C`; the standard high-mask digits are
`Adm942MaskConstants.highPort_digit`. `Adm942Occupation` then gives the marked
word over the same 942-row `WangTiles942` table, and
`ArithmeticWangSoundness.marked_halts` the halt. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Adm942CellWindow
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open Adm942WindowInterface Adm942CellTransfer Adm942Occupation
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
attribute [local irreducible] Adm942Kernel.K Adm942MaskData.beta
  Adm942MaskData.lowPort Adm942MaskData.highPort

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cellInput_of_window {N W C F : V} (h : Window N W C F) :
    CellInput N W C F (carryDigit N W C) where
  N_pos := h.N_pos
  boolean := h.boolean
  origin := h.origin
  support := h.support
  carry_bound := h.carry_bound
  carry_equation := h.carry_equation
  mask_tests := h.mask_tests
  high_digit := fun j _ => Adm942MaskConstants.highPort_digit j

/-- **The marked word of the internal admissible942 window** (B10). -/
theorem window_marked_word {N W C F : V} (h : Window N W C F) :
    ArithmeticWangPlane.MarkedWord (tileAt C) N ((W / 47) / 4027) :=
  marked_word (cellInput_of_window h)

/-- **Every internal admissible942 window halts the decimal215 run before `N`** (C6). -/
theorem window_halts {N W C F : V} (h : Window N W C F) :
    ∃ t < N, first (ArithmeticMachineRun215.run t) = 0 :=
  ArithmeticWangSoundness.marked_halts (window_marked_word h)

end Adm942CellWindow

#print axioms Adm942CellWindow.window_marked_word
#print axioms Adm942CellWindow.window_halts
