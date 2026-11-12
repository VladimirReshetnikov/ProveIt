import P88FourSquareGraph
import P88PairModel

/-! Uncompiled proposal: same valuation, same free-J encoding and arbitrary
integer ports. Its model theorem is distinct from the external all-integer
zero-set proof. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P88FourSquareModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open IPRAOrdinary12 (PositiveModelBridge)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed model-wise equivalence to the 88/46 parent, with no witness map. -/
theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (P88FourSquare.graph p).output v ↔
      InternalZero (P88Pair.graph p).output v := by
  let w : Fin 13 → DiffRing V := fun j => ι (v j)
  constructor
  · intro hz
    rw [internalZero_iff, P88FourSquare.output_eval] at hz
    change ((P88Pair.graph p).A0.evalRing w * (P88Pair.graph p).A0.evalRing w +
      (P88Pair.graph p).A1.evalRing w * (P88Pair.graph p).A1.evalRing w) +
      (((P88Pair.graph p).aux.evalRing w - 1) * ((P88Pair.graph p).aux.evalRing w - 1) +
      ((P88Pair.graph p).strong.evalRing w - 1) * ((P88Pair.graph p).strong.evalRing w - 1)) = 0 at hz
    set x := (P88Pair.graph p).A0.evalRing w
    set y := (P88Pair.graph p).A1.evalRing w
    set a := (P88Pair.graph p).aux.evalRing w - 1
    set s := (P88Pair.graph p).strong.evalRing w - 1
    have hx : x = 0 := mul_self_eq_zero.mp (by
      have hxx := mul_self_nonneg x
      have hyy := mul_self_nonneg y
      have haa := mul_self_nonneg a
      have hss := mul_self_nonneg s
      linarith)
    have hy : y = 0 := mul_self_eq_zero.mp (by
      have hxx := mul_self_nonneg x
      have hyy := mul_self_nonneg y
      have haa := mul_self_nonneg a
      have hss := mul_self_nonneg s
      linarith)
    have ha : a = 0 := mul_self_eq_zero.mp (by
      have hxx := mul_self_nonneg x
      have hyy := mul_self_nonneg y
      have haa := mul_self_nonneg a
      have hss := mul_self_nonneg s
      linarith)
    have hs : s = 0 := mul_self_eq_zero.mp (by
      have hxx := mul_self_nonneg x
      have hyy := mul_self_nonneg y
      have haa := mul_self_nonneg a
      have hss := mul_self_nonneg s
      linarith)
    have h0 : (P88Pair.graph p).A0.evalRing w = 0 := hx
    have h1 : (P88Pair.graph p).A1.evalRing w = 0 := hy
    have haux : (P88Pair.graph p).aux.evalRing w = 1 := sub_eq_zero.mp ha
    have hstrong : (P88Pair.graph p).strong.evalRing w = 1 := sub_eq_zero.mp hs
    rw [internalZero_iff, P88Pair.output_shape]
    simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_sub,
      Expr.evalRing_ofNat, Nat.cast_one]
    rw [h0, h1, haux, hstrong]
    ring
  · intro hz
    have hp := (P88PairModel.zero_iff p v).mp hz
    obtain ⟨h0, h1, ha, hs⟩ := FreeJ13.factor_units p v hp
    rw [FreeJ13.unit_iff_one] at h0 h1 ha hs
    change (1 + (FreeJ13.graph p).A0).evalRing w = 1 at h0
    change (1 + (FreeJ13.graph p).A1).evalRing w = 1 at h1
    change (FreeJ13.graph p).aux.evalRing w = 1 at ha
    change (FreeJ13.graph p).strong.evalRing w = 1 at hs
    simp only [Expr.evalRing_add, Expr.evalRing_ofNat, Nat.cast_one] at h0 h1
    have h0zero : (P88Pair.graph p).A0.evalRing w = 0 := by
      rw [P88Pair.A0_eq]
      linear_combination h0
    have h1zero : (P88Pair.graph p).A1.evalRing w = 0 := by
      rw [P88Pair.A1_eq]
      linear_combination h1
    have haux : (P88Pair.graph p).aux.evalRing w = 1 := by
      rw [P88Pair.aux_eval_eq]
      exact ha
    have hstrong : (P88Pair.graph p).strong.evalRing w = 1 := by
      rw [P88Pair.strong_eq]
      exact hs
    rw [internalZero_iff, P88FourSquare.output_eval]
    change ((P88Pair.graph p).A0.evalRing w * (P88Pair.graph p).A0.evalRing w +
      (P88Pair.graph p).A1.evalRing w * (P88Pair.graph p).A1.evalRing w) +
      (((P88Pair.graph p).aux.evalRing w - 1) * ((P88Pair.graph p).aux.evalRing w - 1) +
      ((P88Pair.graph p).strong.evalRing w - 1) * ((P88Pair.graph p).strong.evalRing w - 1)) = 0
    rw [h0zero, h1zero, haux, hstrong]
    ring

def expression : Expr (Fin 13) := (P88FourSquare.graph CompactSymbolicModelIff.p).output

/-- Proposed transfer through the parent's already-stated positive bridge. -/
theorem positiveBridge : PositiveModelBridge expression := by
  intro V _ _
  constructor
  · rintro ⟨v, hv, hz⟩
    apply (P88PairModel.positiveBridge V).mp
    exact ⟨v, hv, (zero_iff _ v).mp hz⟩
  · intro h
    obtain ⟨v, hv, hz⟩ := (P88PairModel.positiveBridge V).mpr h
    exact ⟨v, hv, (zero_iff _ v).mpr hz⟩

#print axioms zero_iff
#print axioms positiveBridge
end DiophantineConsistency.P88FourSquareModel
