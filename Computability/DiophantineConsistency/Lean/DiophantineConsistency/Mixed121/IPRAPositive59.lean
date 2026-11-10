import DiophantineConsistency.Mixed121.IPRAPositive55
import DiophantineConsistency.Mixed121.P55Norm
import DiophantineConsistency.Mixed121.P59Graph

/-! # iPRA endpoints for package 59's 14-positive, degree-52 equation

The equation is `59-degree-separated/short/circuits/p79_d52_14positive.json`:
14 positive unknowns, 79 operations and exact degree 52, at the same
wang943-mixed-121x8801 ports as package 55 (`Mixed121Ports.ports`). Its output is
`M² + (Na − 1)² + (N0·Nt − 1)² + W²`, where every residual evaluates as package
55's (`P59Graph`). In every model of `𝗜𝚺₁` its positive zeros are exactly package
55's:

* a 59-zero has `M = W = 0`, `Na = 1` and `N0·Nt = 1` (four squares summing to
  zero), so package 55's four squares sum to one;
* conversely, at a positive 55-zero `P55Norm.residuals` gives `M = W = 0` and
  `Na = N0 = Nt = 1`, so the 59 output vanishes.

So package 55's closed bridge (`P55Facts.halts`, `P55Converse.converse`) transfers,
and the generic helpers of `IPRAOrdinary12Chain` give native, standard and
equality-only iPRA equivalences with the selected Foundation ZFC consistency
predicate. The endpoints are about the Lean graph; its correspondence with the
JSON and the port binding is the check
`research/mixed121-calibration/tools/generate_p59.py --check`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAPositive59
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly ModelDifferenceRing
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
attribute [local irreducible] Mixed121Ports.ports

/-- The ports as integers. -/
abbrev intPorts : Fin 4 → ℤ := fun j => (Mixed121Ports.ports j : ℤ)

def expression : Expr (Fin 14) := (P59Graph.graph intPorts).output

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Four squares summing to zero all vanish. -/
private theorem four_sq_zero {m n l w : DiffRing V}
    (h : m * m + n * n + l * l + w * w = 0) : m = 0 ∧ n = 0 ∧ l = 0 ∧ w = 0 := by
  have hm := mul_self_nonneg m
  have hn := mul_self_nonneg n
  have hl := mul_self_nonneg l
  have hw := mul_self_nonneg w
  have hm0 : m * m = 0 := by linarith
  have hn0 : n * n = 0 := by linarith
  have hl0 : l * l = 0 := by linarith
  have hw0 : w * w = 0 := by linarith
  exact ⟨mul_self_eq_zero.mp hm0, mul_self_eq_zero.mp hn0, mul_self_eq_zero.mp hl0,
    mul_self_eq_zero.mp hw0⟩

/-- A zero of package 59's equation is a zero of package 55's. -/
theorem zero55_of_zero59 (v : Fin 14 → V)
    (hz : InternalZero expression v) :
    InternalZero (P55Graph.graph intPorts).output v := by
  have h := (internalZero_iff _ v).mp hz
  rw [expression, P59Graph.output_eval, P59Graph.M_eq, P59Graph.Na_eq, P59Graph.N0_eq,
    P59Graph.Nt_eq, P59Graph.W_eq] at h
  obtain ⟨hM, hNa, hl, hW⟩ := four_sq_zero h
  rw [P55Graph.zero_iff]
  dsimp only
  rw [hM, hW, sub_eq_zero.mp hNa, hl]
  ring

/-- A positive zero of package 55's equation is a zero of package 59's. -/
theorem zero59_of_zero55 (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (P55Graph.graph intPorts).output v) :
    InternalZero expression v := by
  obtain ⟨hb, -, -, -⟩ := Mixed121Ports.leaf_bounds (V := V)
  obtain ⟨hM, hW, hNa, hN0, hNt⟩ := P55Norm.residuals Mixed121Ports.ports v hv hb hz
  rw [internalZero_iff] at hM hW
  rw [internalZero_iff, expression, P59Graph.output_eval, P59Graph.M_eq, P59Graph.Na_eq,
    P59Graph.N0_eq, P59Graph.Nt_eq, P59Graph.W_eq, hM, hW, hNa, hN0, hNt]
  ring

end Model

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨v, hv, hz⟩ => P55Facts.halts v hv (zero55_of_zero59 v hz),
   fun ⟨T, hT⟩ =>
    let ⟨v, hv, hz⟩ := P55Converse.converse T hT
    ⟨v, hv, zero59_of_zero55 v hv hz⟩⟩

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge
theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge
theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge

#print axioms zero55_of_zero59
#print axioms zero59_of_zero55
#print axioms positiveBridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end DiophantineConsistency.IPRAPositive59
