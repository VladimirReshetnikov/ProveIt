import DiophantineConsistency.ArithmeticWangSoundness
import DiophantineConsistency.Bm2963.Bm2963WindowInterface
import DiophantineConsistency.Bm2963.Bm2963Occupation

/-! # Window ⇒ marked word ⇒ halt at block-mask2963

The counterpart of `ArithmeticCellWindow`, in every model of IΣ1 (soundness spec
§4–§6). The block-mask2963 window `Bm2963WindowInterface.Window` is the cell input
`Bm2963CellTransfer.CellInput` with the explicit end-around carry
`carryDigit N W C`; the standard high-mask digits are
`Bm2963MaskConstants.highPort_digit`. `Bm2963Occupation` then gives the marked
word over the same 942-row `WangTiles942` table, and
`ArithmeticWangSoundness.marked_halts` the halt. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Bm2963CellWindow
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open Bm2963WindowInterface Bm2963CellTransfer Bm2963Occupation
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
attribute [local irreducible] Bm2963Kernel.K Bm2963MaskData.beta
  Bm2963MaskData.lowPort Bm2963MaskData.highPort

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
  high_digit := fun j _ => Bm2963MaskConstants.highPort_digit j

/-- **The marked word of the internal block-mask2963 window** (B10). -/
theorem window_marked_word {N W C F : V} (h : Window N W C F) :
    ArithmeticWangPlane.MarkedWord (tileAt C) N ((W / 47) / 2963) :=
  marked_word (cellInput_of_window h)

/-- **Every internal block-mask2963 window halts the decimal215 run before `N`** (C6). -/
theorem window_halts {N W C F : V} (h : Window N W C F) :
    ∃ t < N, first (ArithmeticMachineRun215.run t) = 0 :=
  ArithmeticWangSoundness.marked_halts (window_marked_word h)

end Bm2963CellWindow

#print axioms Bm2963CellWindow.window_marked_word
#print axioms Bm2963CellWindow.window_halts
