import DiophantineConsistency.ArithmeticWindowInterface
import DiophantineConsistency.ArithmeticOccupation
import DiophantineConsistency.ArithmeticWangSoundness

/-! **Window ⇒ marked word ⇒ halt**, in every model of IΣ1 (soundness spec §4–§6).

The window interface `ArithmeticWindowInterface.Window` (W1)–(W7) is the cell input
`ArithmeticCellTransfer.CellInput` with the explicit end-around carry
`carryDigit N W C`; the standard high-mask digits are
`ArithmeticMaskConstants.highPort_digit`. Stage B (`ArithmeticOccupation`) then gives
the marked word, and Stage C (`ArithmeticWangSoundness.marked_halts`) the halt. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCellWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWindowInterface ArithmeticCellTransfer ArithmeticOccupation
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor

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
  high_digit := fun j _ => ArithmeticMaskConstants.highPort_digit j

/-- **The marked word of the internal window** (B10). -/
theorem window_marked_word {N W C F : V} (h : Window N W C F) :
    ArithmeticWangPlane.MarkedWord (tileAt C) N ((W / 47) / 2011) :=
  marked_word (cellInput_of_window h)

/-- **Every internal window halts the decimal215 run before `N`** (C6). -/
theorem window_halts {N W C F : V} (h : Window N W C F) :
    ∃ t < N, first (ArithmeticMachineRun215.run t) = 0 :=
  ArithmeticWangSoundness.marked_halts (window_marked_word h)

end DiophantineConsistency.ArithmeticCellWindow
