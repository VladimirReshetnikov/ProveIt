import DiophantineConsistency.LinCof.LCLeaf
import DiophantineConsistency.LinCof.LCComplete

/-! # The linear-cofactor family at the 300-type slots: zeros and halting

`LCLeaf.sound` and `LCComplete.lc_complete300` are stated for the whole family of circuits
`LCValue.valueK portsR x (k300 …) (kq300 …) (L300 …) ψ wt`. This module joins them into one
equivalence, with the centre and the radical weight as parameters:

* `zero_iff_halts`: for every centre `ψf` that does not read the unknown `n = x 9` and every
  weight `wt = lw²` that is a nonzero even square (`LCNorm.Weight`), the circuit has a zero in
  the ring of differences of a model of `𝗜𝚺₁` iff machine 215 halts internally.

Soundness uses the weight only through `LCNorm.Weight` and does not read the centre at all;
completeness uses the weight only as a square and the centre only through `hψ`.

Instances: package 172's 300/144 (`psi300`, `1024 = 32²`), package 135's 352/125, 340/129 and
328/130 (weight `4 = 2²`), package 144's 316/133 and 308/140 (weight `64 = 8²`). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.LCFamily
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Ports LCValue
open LCNorm (Weight)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Zeros of a 300-type linear-cofactor circuit are internal halts of machine 215**, for every
centre that does not read `x 9` and every nonzero even square weight. -/
theorem zero_iff_halts {wt : DiffRing V} (lw : DiffRing V) (hwt : wt = lw ^ 2) (hw : Weight wt)
    (ψf : (Fin 11 → DiffRing V) → DiffRing V)
    (hψ : ∀ x t, ψf (Function.update x 9 t) = ψf x) :
    (∃ x : Fin 11 → DiffRing V,
        valueK (portsR (V := V)) x (k300 (portsR (V := V)) x) (kq300 (portsR (V := V)) x)
          (L300 (portsR (V := V)) x) (ψf x) wt = 0) ↔
      ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  constructor
  · rintro ⟨x, hz⟩
    exact LCLeaf.sound (ψf x) wt (slotLaw300 portsR x)
      (LCWindow.modulus300 portsR x (ψf x) wt) hw hz
  · rintro ⟨T, hT⟩
    subst hwt
    exact LCComplete.lc_complete300 lw ψf hψ T hT

#print axioms zero_iff_halts

end DiophantineConsistency.LCFamily
