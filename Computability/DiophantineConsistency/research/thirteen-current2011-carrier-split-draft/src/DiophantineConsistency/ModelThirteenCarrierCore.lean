import DiophantineConsistency.ModelThirteenRestoration
import DiophantineConsistency.ArithmeticThirteenSeed
import DiophantineConsistency.ArithmeticThirteenOuter
import DiophantineConsistency.ArithmeticPellFirstIndex
import FrontierBridge
/-! # iPRA endpoint for the thirteen-variable 69/174 carrier form

In every model of `𝗜𝚺₁`, the 13-variable form `ThirteenCarrier.value69` and the
maintained 14-variable Carrier65 polynomial have zeros together:

* restoration (`ModelThirteenRestoration`) maps a positive 69-zero to a
  positive Carrier65 zero;
* completion (`complete`) maps a Carrier65 zero to a 69-zero. The outer data
  come from the internal soundness lemmas (`maintained_first_indices`,
  `ArithmeticThirteenOuter`), the strong seed from the internal pigeonhole
  (`ArithmeticThirteenSeed.strong_index`) and the auxiliary pair from
  `auxiliary_seed_of`; the independent coordinate `m` is solved exactly.

This is the internal counterpart of `CurrentCarrierArithmetic2011.positive_zero_65_iff_69`,
so the maintained all-model bridge transfers to the 69 form, giving native,
standard iPRA proofs of its no-zero sentence iff Foundation's
ZFC consistency predicate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenCarrier
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres

/-! ### Literal thirteen-coordinate syntax -/

/-- The common thirteen-coordinate front, followed by `final P Q S f δ gap y t`. -/
def front13 (p : Fin 4 → ℤ)
    (final : Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) →
      Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13)) :
    Expr (Fin 13) :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let alpha : Expr (Fin 13) := .var 2
  let f : Expr (Fin 13) := .var 3
  let i : Expr (Fin 13) := .var 4
  let T : Expr (Fin 13) := .var 5
  let s : Expr (Fin 13) := .var 6
  let w : Expr (Fin 13) := .var 7
  let n : Expr (Fin 13) := .var 8
  let eta : Expr (Fin 13) := .var 9
  let zeta : Expr (Fin 13) := .var 10
  let m : Expr (Fin 13) := .var 11
  let gamma : Expr (Fin 13) := .var 12
  let b := Expr.constant (p 0) * J
  let q := b + 1
  let C := q - F - alpha
  let X := w * q
  let Y := s * q ^ 3
  let E := X * Y
  let k := eta + zeta
  let ell := E * k * Y
  let c := k * Y + eta
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + gamma * H
  let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) +
    (Expr.constant (p 2) + q * Expr.constant (p 3)) * J
  let tau := E * n + k - rank
  let V := f ^ 2 * (c * T - rank) - c
  let G := (Expr.constant (p 1) + w) * C - F
  let y := 1 + 4 * (b * (m - V ^ 2 * G) - G)
  final (tau ^ 2 - ell * (ell + k)) (D ^ 2 - delta * c ^ 2) (delta * (b * i * c ^ 2))
    f delta (V ^ 2 - y ^ 2) y (b * i * c ^ 2)

/-- The 13/69/174 polynomial. -/
def expressionAt69 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13 p fun P Q S f delta gap y _ =>
    P * Q * (S ^ 2 * gap + y ^ 2) * (delta * f ^ 2 - S ^ 2) - delta

theorem evalRing_expressionAt69 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt69 p).evalRing v = ThirteenCarrier.value69 (fun j => (p j : R)) v := by
  simp only [expressionAt69, front13, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    ThirteenCarrier.value69, ThirteenCarrier.core]

/-! ### The completion map (generic ring definitions, as in `ThirteenCarrierComplete`) -/

section Replace
variable {R : Type*} [CommRing R]

def transport (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  (p 1 + v 8) * (Carrier65.core p v).C - v 1

/-- Preserve J,F,alpha,s,w,n,eta,zeta,gamma and replace only f,i,T,m. -/
def replace (v : Fin 14 → R) (f i T m : R) (j : Fin 13) : R :=
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => f
  | 4 => i
  | 5 => T
  | 6 => v 7
  | 7 => v 8
  | 8 => v 9
  | 9 => v 10
  | 10 => v 11
  | 11 => m
  | _ => v 13

theorem core_replace (p : Fin 4 → R) (v : Fin 14 → R) (f i T m : R) :
    let b := Carrier65.core p v
    let V := f ^ 2 * (b.c * T - b.rank) - b.c
    let y := 1 + 4 * (p 0 * v 0 * (m - V ^ 2 * transport p v) - transport p v)
    ThirteenCarrier.core p (replace v f i T m) =
      ⟨b.a, b.delta, p 0 * v 0 * i * b.c ^ 2, f, V ^ 2 - y ^ 2, y, b.P, b.Q⟩ := rfl

theorem replace_zero69 (p : Fin 4 → R) (v : Fin 14 → R) (f i T m : R)
    (hP : (Carrier65.core p v).P = 1) (hQ : (Carrier65.core p v).Q = 1)
    (hs : f ^ 2 - (Carrier65.core p v).delta *
      (p 0 * v 0 * i * (Carrier65.core p v).c ^ 2) ^ 2 = 1)
    (hu : let b := Carrier65.core p v
      let S := b.delta * (p 0 * v 0 * i * b.c ^ 2)
      let V := f ^ 2 * (b.c * T - b.rank) - b.c
      let y := 1 + 4 * (p 0 * v 0 * (m - V ^ 2 * transport p v) - transport p v)
      S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2 = 1) :
    ThirteenCarrier.value69 p (replace v f i T m) = 0 := by
  have hz : (Carrier65.core p v).delta * f ^ 2 -
      ((Carrier65.core p v).delta * (p 0 * v 0 * i * (Carrier65.core p v).c ^ 2)) ^ 2 =
      (Carrier65.core p v).delta := by
    linear_combination (Carrier65.core p v).delta * hs
  dsimp only [ThirteenCarrier.value69]
  rw [core_replace]
  dsimp only
  rw [hP, hQ, hu, hz]
  ring

theorem replace_pos [PartialOrder R] (v : Fin 14 → R) (hv : ∀ j, 0 < v j)
    (f i T m : R) (hf : 0 < f) (hi : 0 < i) (hT : 0 < T) (hm : 0 < m) :
    ∀ j, 0 < replace v f i T m j := by
  intro j
  fin_cases j
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hf
  · exact hi
  · exact hT
  · exact hv 7
  · exact hv 8
  · exact hv 9
  · exact hv 10
  · exact hv 11
  · exact hm
  · exact hv 13

end Replace

end DiophantineConsistency.ModelThirteenCarrier
