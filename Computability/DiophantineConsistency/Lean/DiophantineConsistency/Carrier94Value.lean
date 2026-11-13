import DiophantineConsistency.ModelCarrierScaled
import DiophantineConsistency.Carrier94Syntax
import DiophantineConsistency.WeightedExpressionDegree

/-! # The 67/94 value and its completeness map

`value94` is the ring value of `Carrier94Syntax.expressionAt94`, written over the
maintained registers `Carrier65.core` (`evalRing_expressionAt94`).

Completeness (`native/PROOF.md` §6, last paragraph): at a positive zero of the
maintained Carrier65 value, replacing only the strong multiplier `i` by
`Delta i` gives a zero of the 67/94 value. Indeed the maintained zero has
strong norm `f² − Delta (i c²)² = 1`, so `Delta (f² − 1) = (Delta i c²)²`: the
ordinary strong factor is `1` and the auxiliary factor is the maintained one.
This holds in every discretely ordered commutative ring with a residue
homomorphism to `ZMod 4`, so in the ring of differences of every model of
`𝗜𝚺₁`. This module imports neither Foundation nor Mathlib's matrices. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Carrier94Value
open Carrier65 ModelCarrierScaled DiscreteOrderedRingFacts

section Value
variable {R : Type*} [CommRing R]

/-- The 67/94 value over the maintained registers. -/
def value94 (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  let b := core p v
  b.P*b.Q*(b.delta*(b.f^2-1)*(b.V^2-b.y^2)+b.y^2)*b.W*
    (1+(b.i*b.c^2)^2-b.delta*(b.f^2-1))-1

theorem evalRing_expressionAt94 (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (Carrier94Syntax.expressionAt94 p).evalRing v = value94 (fun j => (p j : R)) v := by
  simp only [Carrier94Syntax.expressionAt94, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    value94, Carrier65.core]

/-- Replacing the strong multiplier changes only the strong factor of `value94`. -/
theorem value94_update (p : Fin 4 → R) (v : Fin 14 → R) (x : R) :
    value94 p (Function.update v 5 x) =
      (core p v).P*(core p v).Q*((core p v).delta*((core p v).f^2-1)*
        ((core p v).V^2-(core p v).y^2)+(core p v).y^2)*(core p v).W*
        (1+(x*(core p v).c^2)^2-(core p v).delta*((core p v).f^2-1))-1 := rfl

end Value

section Ordered
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable (hd : ∀ x : R, 0 < x → 1 ≤ x)
include hd

/-- **Completeness map.** A positive Carrier65 zero gives a 67/94 zero by
`i ↦ Delta i`. -/
theorem zero94_of_maintained (φ : R →+* ZMod 4) (p : Fin 4 → R) (v : Fin 14 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hz : Carrier65.value p v = 0) :
    value94 p (Function.update v 5 ((core p v).delta*(core p v).i)) = 0 := by
  have hdelta := (delta_pos hd p v hb hv).ne'
  have hn : strong (core p v) ≠ -1 := by
    unfold strong
    rw [delta_shape]
    exact strong_ne_neg_one φ _ _ _
  rw [original_scaled_identity] at hz
  simp only [mul_eq_zero, hdelta, false_or] at hz
  have hs := strong_eq_one hd hn hz
  unfold product at hz
  rw [hs] at hz
  have hf2 : (core p v).f^2 = 1+(core p v).delta*((core p v).i*(core p v).c^2)^2 := by
    unfold strong at hs
    linear_combination hs
  rw [value94_update, hf2]
  linear_combination hz

/-- The new strong multiplier is positive. -/
theorem multiplier_pos (p : Fin 4 → R) (v : Fin 14 → R) (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    0 < (core p v).delta*(core p v).i :=
  mul_pos (delta_pos hd p v hb hv) (hv 5)

end Ordered

end DiophantineConsistency.Carrier94Value
