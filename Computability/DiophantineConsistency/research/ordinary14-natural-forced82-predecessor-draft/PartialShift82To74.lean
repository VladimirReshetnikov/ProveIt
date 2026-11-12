import RingNatural82To86
import RingNatural86To74
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only composition proposal. No elaboration or iPRA claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.PartialShift82To74Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing

def partial {R : Type*} [Add R] [One R] (v : Fin 14 → R) : Fin 14 → R :=
  fun j => if j = 3 ∨ j = 8 ∨ j = 11 then v j else v j + 1

theorem compose_shift {R : Type*} [CommRing R] (v : Fin 14 → R) :
    RingNatural86To74Draft.shift (RingNatural82To86Draft.down v) = partial v := by
  funext j
  fin_cases j <;> simp [RingNatural86To74Draft.shift, RingNatural82To86Draft.down, partial]

theorem output_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P82NaturalForced.graph p).output.evalRing v =
      (P74PositiveGuard.graph p).output.evalRing (partial v) := by
  rw [RingNatural82To86Draft.output_eval, RingNatural86To74Draft.output_eval, compose_shift]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The partial shift takes place in the model, not merely in its ring. -/
theorem partial_embedding (w : Fin 14 → V) :
    partial (fun j => ι (w j)) = fun j => ι (partial w j) := by
  funext j
  fin_cases j <;> simp [partial, map_add, map_one]

theorem internalZero_iff_partial (p : Fin 4 → ℤ) (w : Fin 14 → V) :
    InternalZero (P82NaturalForced.graph p).output w ↔
      InternalZero (P74PositiveGuard.graph p).output (partial w) := by
  rw [ModelDifferenceRing.internalZero_iff, ModelDifferenceRing.internalZero_iff,
    output_eval, partial_embedding]

end DiophantineConsistency.PartialShift82To74Draft
