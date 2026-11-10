import DiophantineConsistency.P138.P138Leaf
import DiophantineConsistency.P138.P138Complete

/-! # Package 138's short 840/108 equation: soundness and completeness

The short form `parity_saturated11_short.json` differs from the native one only in the index
modulus of `k`: `k = R + 1 + h·4q⁴` (`P138Value.kS`) instead of `k = R + 1 + hE`
(`P138Value.kN`). Its circuit is `P138Value.regsS`, its value `P138Value.valueS`.

* **Soundness** (`sound`). The soundness chain B1–B13 (`P138Bootstrap` … `P138Leaf`) is generic
  in the `k` slot of `P138Value.regsK`; it uses `k`'s definition only through an index modulus
  (`P138Window.IndexModulus`: `k = R + 1 + hμ`, `μ ∣ E`, `4q⁴ ≤ |μ|`). The short modulus
  `μ = 4q⁴` is one (`P138Window.short_modulus`): it divides `E = 4q⁴(3w+1)(2v+1)`, and the window
  `R + 2 < q⁴` gives `3R + 1 < 4q⁴` (`P138Window.modulus`). So the first-index argument of
  `P138FirstIndex` (the residues of `ψ_bF(n)` modulo `m ∣ E`, the alternating residue for a
  negative first base, no wrap) gives `2n = R + 1` with `m = 4q⁴` exactly as with `m = |E|`, and
  `P138Leaf.sound_k` concludes.
* **Completeness** (`complete`), by substitution. `P138Value.valueS_update`: the short value at
  `x` with `x 3 := h (3w+1)(2v+1)` is the native value at `x`, as a polynomial identity. So the
  native zero of `P138Complete.complete` gives a short zero. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P138Short
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Value P138Ports P138Window
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Soundness.** A zero of the 840/108 equation in any model of `𝗜𝚺₁` gives an internal halt
of machine 215. -/
theorem sound (x : Fin 11 → DiffRing V) (hz : valueS portsR x = 0) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 :=
  P138Leaf.sound_k x _ (short_modulus portsR x) hz

/-- **Completeness.** An internal halt of machine 215 gives an integer zero of the 840/108
polynomial at the six ports: the native zero `x`, with `x 3 = h` replaced by `h (3w+1)(2v+1)`. -/
theorem complete (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V, valueS portsR x = 0 := by
  obtain ⟨x, hx⟩ := P138Complete.complete T hT
  exact ⟨Function.update x 3 (x 3 * ((3 * x 6 + 1) * (2 * x 5 + 1))),
    (valueS_update portsR x).trans hx⟩

#print axioms sound
#print axioms complete

end DiophantineConsistency.P138Short
