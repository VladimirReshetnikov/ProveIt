import P80NaturalForcedGamma
import RingNatural82To86
import RingNatural86To74
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only natural-80 to positive-74 partial-coordinate bridge.
All graphs, ring rewrites and model steps are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Natural80Partial74Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing

/-- In the ring, the 82 inputs for J and gamma are one below the 80 inputs. -/
def down82 {R : Type*} [Sub R] [One R] (v : Fin 14 → R) : Fin 14 → R :=
  fun j => if j = 0 ∨ j = 12 then v j - 1 else v j

theorem output_eval82 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P80NaturalForcedGamma.graph p).output.evalRing v =
      (P82NaturalForced.graph p).output.evalRing (down82 v) := by
  simp [P80NaturalForcedGamma.graph, P82NaturalForced.graph, Expr.evalRing_add,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, down82]

/-- Natural-model form of the partial 74 valuation: keep J, f, r, y and
gamma; increment F, alpha, i, T, w, s, eta, zeta and h. -/
def partial74 {R : Type*} [Add R] [One R] (v : Fin 14 → R) : Fin 14 → R :=
  fun j => if j = 0 ∨ j = 3 ∨ j = 8 ∨ j = 11 ∨ j = 12 then v j else v j + 1

theorem composed_coordinates {R : Type*} [CommRing R] (v : Fin 14 → R) :
    RingNatural86To74Draft.shift (RingNatural82To86Draft.down (down82 v)) = partial74 v := by
  funext j
  fin_cases j <;> simp [RingNatural86To74Draft.shift, RingNatural82To86Draft.down,
    down82, partial74]

theorem output_eval74 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P80NaturalForcedGamma.graph p).output.evalRing v =
      (P74PositiveGuard.graph p).output.evalRing (partial74 v) := by
  rw [output_eval82, RingNatural82To86Draft.output_eval,
    RingNatural86To74Draft.output_eval, composed_coordinates]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem partial_embedding (v : Fin 14 → V) :
    partial74 (fun j => ι (v j)) = (fun j => ι (partial74 v j)) := by
  funext j
  fin_cases j <;> simp [partial74, map_add, map_one]

/-- Exact 80-to-74 zero comparison at the related partial valuation; no
positivity premise is needed merely for this polynomial identity. -/
theorem internalZero_iff_partial (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    InternalZero (P80NaturalForcedGamma.graph p).output v ↔
      InternalZero (P74PositiveGuard.graph p).output (partial74 v) := by
  rw [ModelDifferenceRing.internalZero_iff, ModelDifferenceRing.internalZero_iff,
    output_eval74, partial_embedding]

end DiophantineConsistency.Natural80Partial74Draft

#print axioms DiophantineConsistency.Natural80Partial74Draft.output_eval74
#print axioms DiophantineConsistency.Natural80Partial74Draft.internalZero_iff_partial
