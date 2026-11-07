import DiophantineConsistency.Adm942.Adm942WindowZero
import DiophantineConsistency.Adm942.Adm942CellWindow

/-! # Soundness at the admissible942 ports

The counterpart of `ArithmeticSoundness2011`, in every model of IΣ1: a positive
zero of the literal Carrier65 expression at the admissible942 ports
(`Adm942Ports.PositiveZero`) makes the represented decimal215 run halt. The chain
is `PositiveZero` ⇒ `Window` (`Adm942WindowZero`) ⇒ marked cyclic Wang word
(`Adm942CellWindow`, the cell decoding `Adm942CellLocal` … `Adm942Occupation`) ⇒
halt (`ArithmeticWangSoundness.marked_halts`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Adm942Soundness
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open Adm942WindowInterface Adm942WindowZero
attribute [local irreducible] Adm942Kernel.K Adm942MaskData.radix Adm942MaskData.beta
  Adm942MaskData.lowPort Adm942MaskData.highPort

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Zero ⇒ halt.** -/
theorem zero_halts (u : Fin 14 → V) (h : Adm942Ports.PositiveZero u) :
    ∃ t : V, first (ArithmeticMachineRun215.run t) = 0 := by
  obtain ⟨N, W, C, F, hw⟩ := window_of_zero u h
  obtain ⟨t, -, ht⟩ := Adm942CellWindow.window_halts hw
  exact ⟨t, ht⟩

/-- **Zero ⇒ halt, with an explicit witness bound.** The halting time is below
`q u = β·u₀ + 1`, so the witness map is a bounded search over an affine function
of one coordinate. -/
theorem zero_halts_below (u : Fin 14 → V) (h : Adm942Ports.PositiveZero u) :
    ∃ t < Adm942CarrierRadix.q u, first (ArithmeticMachineRun215.run t) = 0 := by
  obtain ⟨N, hq, hw⟩ := window_of_positive_zero u h
  obtain ⟨t, htN, ht⟩ := Adm942CellWindow.window_halts hw
  refine ⟨t, ?_, ht⟩
  have hN : N ≤ 189269 * N := le_mul_of_one_le_left (by simp) (by simp)
  calc t < N := htN
    _ < Exp.exp N := lt_exp N
    _ ≤ Exp.exp (189269 * N) := exp_monotone_le.mpr hN
    _ = Adm942CarrierRadix.q u := hq.symm

end Adm942Soundness

#print axioms Adm942Soundness.zero_halts
#print axioms Adm942Soundness.zero_halts_below
