import P88PairGraph
import DiophantineConsistency.Compact44.FreeJ13Halt
import DiophantineConsistency.Compact44.IPRAOrdinary12Chain

/-! Source-only proposal. This file has not been elaborated or checked.
The model equivalence uses arbitrary integer ports; the positive bridge
specializes to the existing compact44 symbolic ports. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P88PairModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open IPRAOrdinary12 (PositiveModelBridge)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed zero equivalence for arbitrary ports and every model valuation. -/
theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (P88Pair.graph p).output v ↔
      InternalZero (FreeJ13.graph p).output v := by
  let w : Fin 13 → DiffRing V := fun j => ι (v j)
  constructor
  · intro hz
    rw [internalZero_iff, P88Pair.output_eval] at hz
    change (FreeJ13.graph p).A0.evalRing w * (FreeJ13.graph p).A0.evalRing w +
      (FreeJ13.graph p).A1.evalRing w * (FreeJ13.graph p).A1.evalRing w +
      ((FreeJ13.graph p).aux.evalRing w * (FreeJ13.graph p).strong.evalRing w - 1) *
        ((FreeJ13.graph p).aux.evalRing w * (FreeJ13.graph p).strong.evalRing w - 1) = 0 at hz
    set x := (FreeJ13.graph p).A0.evalRing w
    set y := (FreeJ13.graph p).A1.evalRing w
    set z := (FreeJ13.graph p).aux.evalRing w * (FreeJ13.graph p).strong.evalRing w - 1
    have hx : x = 0 := mul_self_eq_zero.mp (by
      have hxx := mul_self_nonneg x
      have hyy := mul_self_nonneg y
      have hzz := mul_self_nonneg z
      linarith)
    have hy : y = 0 := mul_self_eq_zero.mp (by
      have hxx := mul_self_nonneg x
      have hyy := mul_self_nonneg y
      have hzz := mul_self_nonneg z
      linarith)
    have hzzero : z = 0 := mul_self_eq_zero.mp (by
      have hxx := mul_self_nonneg x
      have hyy := mul_self_nonneg y
      have hzz := mul_self_nonneg z
      linarith)
    have h0 : (FreeJ13.graph p).A0.evalRing w = 0 := hx
    have h1 : (FreeJ13.graph p).A1.evalRing w = 0 := hy
    have hpair : (FreeJ13.graph p).aux.evalRing w *
        (FreeJ13.graph p).strong.evalRing w = 1 := sub_eq_zero.mp hzzero
    rw [internalZero_iff, FreeJ13.output_eq]
    change ((FreeJ13.graph p).strong * ((FreeJ13.graph p).aux *
      ((1 + (FreeJ13.graph p).A0) * (1 + (FreeJ13.graph p).A1))) - 1).evalRing w = 0
    simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
      Expr.evalRing_ofNat, Nat.cast_one]
    rw [h0, h1]
    linear_combination hpair
  · intro hz
    obtain ⟨h0, h1, ha, hs⟩ := FreeJ13.factor_units p v hz
    rw [FreeJ13.unit_iff_one] at h0 h1 ha hs
    change (1 + (FreeJ13.graph p).A0).evalRing w = 1 at h0
    change (1 + (FreeJ13.graph p).A1).evalRing w = 1 at h1
    change (FreeJ13.graph p).aux.evalRing w = 1 at ha
    change (FreeJ13.graph p).strong.evalRing w = 1 at hs
    simp only [Expr.evalRing_add, Expr.evalRing_ofNat, Nat.cast_one] at h0 h1
    have h0zero : (FreeJ13.graph p).A0.evalRing w = 0 := by linear_combination h0
    have h1zero : (FreeJ13.graph p).A1.evalRing w = 0 := by linear_combination h1
    rw [internalZero_iff, P88Pair.output_eval]
    change (FreeJ13.graph p).A0.evalRing w * (FreeJ13.graph p).A0.evalRing w +
      (FreeJ13.graph p).A1.evalRing w * (FreeJ13.graph p).A1.evalRing w +
      ((FreeJ13.graph p).aux.evalRing w * (FreeJ13.graph p).strong.evalRing w - 1) *
        ((FreeJ13.graph p).aux.evalRing w * (FreeJ13.graph p).strong.evalRing w - 1) = 0
    rw [h0zero, h1zero, ha, hs]
    ring

def expression : Expr (Fin 13) := (P88Pair.graph CompactSymbolicModelIff.p).output

/-- Proposed all-model positive-zero/halting bridge at the existing symbolic ports. -/
theorem positiveBridge : PositiveModelBridge expression := by
  intro V _ _
  constructor
  · rintro ⟨v, hv, hz⟩
    apply (FreeJ13Halt.positive_model_iff (V := V)).mp
    exact ⟨v, hv, (zero_iff _ v).mp hz⟩
  · intro h
    obtain ⟨v, hv, hz⟩ := (FreeJ13Halt.positive_model_iff (V := V)).mpr h
    exact ⟨v, hv, (zero_iff _ v).mpr hz⟩

#print axioms zero_iff
#print axioms positiveBridge
end DiophantineConsistency.P88PairModel
