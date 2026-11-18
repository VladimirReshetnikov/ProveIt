import IPRADerivations.Core.IntCancel
import IPRADerivations.Core.LinearAlgebra
import IPRADerivations.Geometry.SphericalCore

/-!
# Girard's theorem, polygonal excess and the solid-angle formulas (`spherical_trigonometry_ipra_2026-11-15`, Section 10)

Packet: `geometry/spherical_trigonometry_ipra_2026-11-15`, `sections/10_area.tex`.

**Girard (`thm:girard`).** "Finite additivity gives `T + X + Y + Z = 2π` (10.6) ... the `B`- and
`C`-lunes have areas `T + Y` and `T + Z`. By (10.4), their total area is
`2A + 2B + 2C = 3T + X + Y + Z` (10.7). Use (10.6) to replace `X + Y + Z` by `2π − T`. Then
`2(A + B + C) = 2T + 2π`, so `T = A + B + C − π`."

* `two_ne`: the numeral `2` is not zero;
* `girard`: for integer terms (the values of the area and angle names at a common scale),
  from (10.6) and the three lune equations `T + X = 2A`, `T + Y = 2B`, `T + Z = 2C`, the
  excess formula `T = A + B + C − π` (10.5). The factor `2` is cancelled in the object theory.

**Polygonal excess (`thm:polygon-excess`).** "A triangulation has `n − 2` triangles. Finite
additivity says the polygonal area is the sum of their areas. The triangle angles partition
the polygon's interior angles ... Applying Girard to each triangle therefore gives
`Area(P) = Σ_j α_j − (n − 2)π` (10.16)."

* `polygon_excess`: for every number `m` of triangles and `k` of polygon angles (parameters of
  the Lean statement): from Girard for each triangle, the partition of the angles and
  additivity of the area, `P = Σ_j α_j − m π`. With `m = n − 2` this is (10.16).

**Solid angle (`thm:solid-angle`).** `cos(E/2) = D/Q` (10.10), `sin(E/2) = τ/Q` (10.11), with
`D = 1 + x + y + z`, `Q² = 2(1 + x)(1 + y)(1 + z)`. Since `E = A + B + C − π`,
`cos E = −cos(A + B + C)` and `sin E = −sin(A + B + C)`, and the doubled forms
`cos E = (D² − τ²)/Q²`, `sin E = 2 D τ/Q²` are polynomial in the finite core (4.16). With the
guard `G = s_a² s_b² s_c²` that clears the denominators of the angle cosines and sines:

* `cos_sum_ring`, `sin_sum_ring`, `lagrange_prod`, `solid_cos_ring`, `solid_sin_ring`: the
  certificates over a commutative ring;
* `solid_cos`: `G · Q² · (−cos(A + B + C)) = G · (D² − τ²)`;
* `solid_sin`: `G · Q² · (−sin(A + B + C)) = G · 2 D τ`;
* `solid_tan`: `G² Q² · sin E · (D² − τ²) = G² Q² · cos E · 2 D τ`, the cross-multiplied
  doubled form of (10.13) `tan(E/2) = τ/D`.

All three are closed over the 26 variables of the core. Not derived: the area names
themselves (the measure of a lune (10.4), finite additivity of the dissection), the half-angle
square roots that turn the doubled forms into (10.10)–(10.12), and the `atan2` chart.
-/

namespace LeanProofs.IPRA.Geometry.SphericalSolidAngle

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.SphericalCore
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

/-! ## Girard and polygons -/

section Area

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The numeral `2` is not zero. -/
theorem two_ne : Γ ⊢[PRAAx] neg (ZT.eq (ZT.natLit 2 : ZT n) (ZT.natLit 0)) := by
  refine .impI (succ_ne_zero' _ (a := num 1) ?_)
  have h : (ZT.eq (ZT.natLit 2 : ZT n) (ZT.natLit 0) :: Γ) ⊢[PRAAx]
      succ (num 1) + zero ≐ zero + zero := Prf.hyp0
  exact (add_zero _).eqSymm.eqTrans (h.eqTrans (zero_add _))

/-- `thm:girard`, (10.5): the dissection identity and the three lunes give
`T = A + B + C − π`. -/
theorem girard {T X Y Z A B C π' : ZT n}
    (h0 : Γ ⊢[PRAAx] ZT.eq (T + X + Y + Z) (ZT.natLit 2 * π'))
    (hA : Γ ⊢[PRAAx] ZT.eq (T + X) (ZT.natLit 2 * A))
    (hB : Γ ⊢[PRAAx] ZT.eq (T + Y) (ZT.natLit 2 * B))
    (hC : Γ ⊢[PRAAx] ZT.eq (T + Z) (ZT.natLit 2 * C)) :
    Γ ⊢[PRAAx] ZT.eq T (A + B + C - π') := by
  have e0 := ZT.toZ_eq h0
  have eA := ZT.toZ_eq hA
  have eB := ZT.toZ_eq hB
  have eC := ZT.toZ_eq hC
  have h2 : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (T - (A + B + C - π'))) (ZT.natLit 0) := by
    refine ZT.derive ?_
    simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat,
      Nat.cast_zero] at e0 eA eB eC ⊢
    linear_combination eA + eB + eC - e0
  have e := ZT.toZ_eq (zt_mul_cancel_left two_ne h2)
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_natLit, Nat.cast_zero] at e ⊢
  linear_combination e

/-- `thm:polygon-excess`, (10.16): a polygon cut into `m` triangles has area
`Σ_j α_j − m π`. -/
theorem polygon_excess {m k : ℕ} {T A B C : Fin m → ZT n} {α : Fin k → ZT n} {P π' : ZT n}
    (hg : ∀ t, Γ ⊢[PRAAx] ZT.eq (T t) (A t + B t + C t - π'))
    (hpart : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun t => A t + B t + C t) (ZT.sumFin α))
    (harea : Γ ⊢[PRAAx] ZT.eq P (ZT.sumFin T)) :
    Γ ⊢[PRAAx] ZT.eq P (ZT.sumFin α - ZT.natLit m * π') := by
  have e1 : ∀ t, ZT.toZ Γ (T t) =
      ZT.toZ Γ (A t) + ZT.toZ Γ (B t) + ZT.toZ Γ (C t) - ZT.toZ Γ π' := fun t => by
    have e := ZT.toZ_eq (hg t)
    simpa only [ZT.toZ_add, ZT.toZ_sub] using e
  have e2 := ZT.toZ_eq hpart
  have e3 := ZT.toZ_eq harea
  simp only [ZT.toZ_sumFin, ZT.toZ_add] at e2 e3
  refine ZT.derive ?_
  rw [e3, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, ZT.toZ_sumFin, ← e2]
  simp only [e1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

end Area

/-! ## The solid-angle certificates -/

section Ring

variable {R : Type*} [CommRing R] {x y z τ sa sb sc cA cB cC sA sB sC : R}

/-- `G cos(A + B + C)` in the core variables. -/
theorem cos_sum_ring (h5 : sb * sc * cA = x - y * z) (h6 : sc * sa * cB = y - z * x)
    (h7 : sa * sb * cC = z - x * y) (h8 : sb * sc * sA = τ) (h9 : sc * sa * sB = τ)
    (h10 : sa * sb * sC = τ) :
    sa ^ 2 * sb ^ 2 * sc ^ 2 * (cA * cB * cC - cA * sB * sC - sA * cB * sC - sA * sB * cC) =
      (x - y * z) * (y - z * x) * (z - x * y) -
        τ ^ 2 * ((x - y * z) + (y - z * x) + (z - x * y)) := by
  have p1 : sa ^ 2 * sb ^ 2 * sc ^ 2 * (cA * cB * cC) =
      (x - y * z) * (y - z * x) * (z - x * y) := by
    rw [← h5, ← h6, ← h7]; ring
  have p2 : sa ^ 2 * sb ^ 2 * sc ^ 2 * (cA * sB * sC) = (x - y * z) * τ ^ 2 := by
    calc sa ^ 2 * sb ^ 2 * sc ^ 2 * (cA * sB * sC)
        = sb * sc * cA * (sc * sa * sB) * (sa * sb * sC) := by ring
      _ = (x - y * z) * τ ^ 2 := by rw [h5, h9, h10]; ring
  have p3 : sa ^ 2 * sb ^ 2 * sc ^ 2 * (sA * cB * sC) = (y - z * x) * τ ^ 2 := by
    calc sa ^ 2 * sb ^ 2 * sc ^ 2 * (sA * cB * sC)
        = sb * sc * sA * (sc * sa * cB) * (sa * sb * sC) := by ring
      _ = (y - z * x) * τ ^ 2 := by rw [h8, h6, h10]; ring
  have p4 : sa ^ 2 * sb ^ 2 * sc ^ 2 * (sA * sB * cC) = (z - x * y) * τ ^ 2 := by
    calc sa ^ 2 * sb ^ 2 * sc ^ 2 * (sA * sB * cC)
        = sb * sc * sA * (sc * sa * sB) * (sa * sb * cC) := by ring
      _ = (z - x * y) * τ ^ 2 := by rw [h8, h9, h7]; ring
  linear_combination p1 - p2 - p3 - p4

/-- `G sin(A + B + C)` in the core variables. -/
theorem sin_sum_ring (h5 : sb * sc * cA = x - y * z) (h6 : sc * sa * cB = y - z * x)
    (h7 : sa * sb * cC = z - x * y) (h8 : sb * sc * sA = τ) (h9 : sc * sa * sB = τ)
    (h10 : sa * sb * sC = τ) :
    sa ^ 2 * sb ^ 2 * sc ^ 2 * (sA * cB * cC + cA * sB * cC + cA * cB * sC - sA * sB * sC) =
      τ * ((y - z * x) * (z - x * y) + (x - y * z) * (z - x * y) + (x - y * z) * (y - z * x) -
        τ ^ 2) := by
  have q1 : sa ^ 2 * sb ^ 2 * sc ^ 2 * (sA * cB * cC) = τ * ((y - z * x) * (z - x * y)) := by
    calc sa ^ 2 * sb ^ 2 * sc ^ 2 * (sA * cB * cC)
        = sb * sc * sA * (sc * sa * cB) * (sa * sb * cC) := by ring
      _ = τ * ((y - z * x) * (z - x * y)) := by rw [h8, h6, h7]; ring
  have q2 : sa ^ 2 * sb ^ 2 * sc ^ 2 * (cA * sB * cC) = τ * ((x - y * z) * (z - x * y)) := by
    calc sa ^ 2 * sb ^ 2 * sc ^ 2 * (cA * sB * cC)
        = sb * sc * cA * (sc * sa * sB) * (sa * sb * cC) := by ring
      _ = τ * ((x - y * z) * (z - x * y)) := by rw [h5, h9, h7]; ring
  have q3 : sa ^ 2 * sb ^ 2 * sc ^ 2 * (cA * cB * sC) = τ * ((x - y * z) * (y - z * x)) := by
    calc sa ^ 2 * sb ^ 2 * sc ^ 2 * (cA * cB * sC)
        = sb * sc * cA * (sc * sa * cB) * (sa * sb * sC) := by ring
      _ = τ * ((x - y * z) * (y - z * x)) := by rw [h5, h6, h10]; ring
  have q4 : sa ^ 2 * sb ^ 2 * sc ^ 2 * (sA * sB * sC) = τ * τ ^ 2 := by
    calc sa ^ 2 * sb ^ 2 * sc ^ 2 * (sA * sB * sC)
        = sb * sc * sA * (sc * sa * sB) * (sa * sb * sC) := by ring
      _ = τ * τ ^ 2 := by rw [h8, h9, h10]; ring
  linear_combination q1 + q2 + q3 - q4

/-- The guard in the side cosines: `s_a² s_b² s_c² = (1 − x²)(1 − y²)(1 − z²)`. -/
theorem lagrange_prod (h1 : sa ^ 2 + x ^ 2 = 1) (h2 : sb ^ 2 + y ^ 2 = 1)
    (h3 : sc ^ 2 + z ^ 2 = 1) :
    sa ^ 2 * sb ^ 2 * sc ^ 2 = (1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2) := by
  linear_combination sb ^ 2 * sc ^ 2 * h1 + (1 - x ^ 2) * sc ^ 2 * h2 +
    (1 - x ^ 2) * (1 - y ^ 2) * h3

/-- The doubled form of (10.10)–(10.11), cosine: `G Q² (−cos(A+B+C)) = G (D² − τ²)`. -/
theorem solid_cos_ring (h1 : sa ^ 2 + x ^ 2 = 1) (h2 : sb ^ 2 + y ^ 2 = 1)
    (h3 : sc ^ 2 + z ^ 2 = 1) (h4 : τ ^ 2 = 1 + 2 * x * y * z - x ^ 2 - y ^ 2 - z ^ 2)
    (h5 : sb * sc * cA = x - y * z) (h6 : sc * sa * cB = y - z * x)
    (h7 : sa * sb * cC = z - x * y) (h8 : sb * sc * sA = τ) (h9 : sc * sa * sB = τ)
    (h10 : sa * sb * sC = τ) :
    sa ^ 2 * sb ^ 2 * sc ^ 2 * (2 * (1 + x) * (1 + y) * (1 + z) *
        (-(cA * cB * cC - cA * sB * sC - sA * cB * sC - sA * sB * cC))) =
      sa ^ 2 * sb ^ 2 * sc ^ 2 * ((1 + x + y + z) ^ 2 - τ ^ 2) := by
  have hK := cos_sum_ring h5 h6 h7 h8 h9 h10
  have hG := lagrange_prod h1 h2 h3
  have hc : -(2 * (1 + x) * (1 + y) * (1 + z)) *
      ((x - y * z) * (y - z * x) * (z - x * y) -
        τ ^ 2 * ((x - y * z) + (y - z * x) + (z - x * y))) =
      (1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2) * ((1 + x + y + z) ^ 2 - τ ^ 2) := by
    linear_combination (2 * (1 + x) * (1 + y) * (1 + z) *
      ((x - y * z) + (y - z * x) + (z - x * y)) + (1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2)) * h4
  linear_combination (-(2 * (1 + x) * (1 + y) * (1 + z))) * hK + hc -
    ((1 + x + y + z) ^ 2 - τ ^ 2) * hG

/-- The doubled form of (10.10)–(10.11), sine: `G Q² (−sin(A+B+C)) = G · 2 D τ`. -/
theorem solid_sin_ring (h1 : sa ^ 2 + x ^ 2 = 1) (h2 : sb ^ 2 + y ^ 2 = 1)
    (h3 : sc ^ 2 + z ^ 2 = 1) (h4 : τ ^ 2 = 1 + 2 * x * y * z - x ^ 2 - y ^ 2 - z ^ 2)
    (h5 : sb * sc * cA = x - y * z) (h6 : sc * sa * cB = y - z * x)
    (h7 : sa * sb * cC = z - x * y) (h8 : sb * sc * sA = τ) (h9 : sc * sa * sB = τ)
    (h10 : sa * sb * sC = τ) :
    sa ^ 2 * sb ^ 2 * sc ^ 2 * (2 * (1 + x) * (1 + y) * (1 + z) *
        (-(sA * cB * cC + cA * sB * cC + cA * cB * sC - sA * sB * sC))) =
      sa ^ 2 * sb ^ 2 * sc ^ 2 * (2 * (1 + x + y + z) * τ) := by
  have hK := sin_sum_ring h5 h6 h7 h8 h9 h10
  have hG := lagrange_prod h1 h2 h3
  have hs : -(2 * (1 + x) * (1 + y) * (1 + z)) *
      (τ * ((y - z * x) * (z - x * y) + (x - y * z) * (z - x * y) +
        (x - y * z) * (y - z * x) - τ ^ 2)) =
      (1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2) * (2 * (1 + x + y + z) * τ) := by
    linear_combination (2 * (1 + x) * (1 + y) * (1 + z) * τ) * h4
  linear_combination (-(2 * (1 + x) * (1 + y) * (1 + z))) * hK + hs -
    (2 * (1 + x + y + z) * τ) * hG

end Ring

/-! ## The closed statements over the core -/

/-- `G = s_a² s_b² s_c²`. -/
abbrev guard : ZT 26 := ZT.sq sa * ZT.sq sb * ZT.sq sc
/-- `Q² = 2(1 + x)(1 + y)(1 + z)`. -/
abbrev Q2 : ZT 26 := ZT.natLit 2 * (ZT.natLit 1 + x) * (ZT.natLit 1 + y) * (ZT.natLit 1 + z)
/-- `D = 1 + x + y + z`. -/
abbrev D : ZT 26 := ZT.natLit 1 + x + y + z
/-- `cos E = −cos(A + B + C)`. -/
abbrev cosE : ZT 26 := -(cA * cB * cC - cA * sB * sC - sA * cB * sC - sA * sB * cC)
/-- `sin E = −sin(A + B + C)`. -/
abbrev sinE : ZT 26 := -(sA * cB * cC + cA * sB * cC + cA * cB * sC - sA * sB * sC)

def solidCosFormula : Fm PTm 26 :=
  core ⟶ ZT.eq (guard * (Q2 * cosE)) (guard * (ZT.sq D - ZT.sq τ))

/-- (10.10)–(10.11), doubled: `Q² cos E = D² − τ²`, times the guard. -/
theorem solid_cos : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 solidCosFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_neg, ZT.toZ_sq, ZT.toZ_natLit,
    Nat.cast_one, Nat.cast_ofNat]
  have h := solid_cos_ring h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  linear_combination h

def solidSinFormula : Fm PTm 26 :=
  core ⟶ ZT.eq (guard * (Q2 * sinE)) (guard * (ZT.natLit 2 * D * τ))

/-- (10.10)–(10.11), doubled: `Q² sin E = 2 D τ`, times the guard. -/
theorem solid_sin : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 solidSinFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_neg, ZT.toZ_sq, ZT.toZ_natLit,
    Nat.cast_one, Nat.cast_ofNat]
  have h := solid_sin_ring h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  linear_combination h

def solidTanFormula : Fm PTm 26 :=
  core ⟶ ZT.eq (guard * guard * Q2 * (sinE * (ZT.sq D - ZT.sq τ)))
    (guard * guard * Q2 * (cosE * (ZT.natLit 2 * D * τ)))

/-- (10.13), doubled and cross-multiplied: `sin E (D² − τ²) = cos E · 2 D τ`, times the
guards. -/
theorem solid_tan : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 solidTanFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_neg, ZT.toZ_sq, ZT.toZ_natLit,
    Nat.cast_one, Nat.cast_ofNat]
  have hc := solid_cos_ring h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hs := solid_sin_ring h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  linear_combination
    (ZT.toZ [core] sa ^ 2 * ZT.toZ [core] sb ^ 2 * ZT.toZ [core] sc ^ 2 *
        ((1 + ZT.toZ [core] x + ZT.toZ [core] y + ZT.toZ [core] z) ^ 2 - ZT.toZ [core] τ ^ 2)) *
      hs -
    (ZT.toZ [core] sa ^ 2 * ZT.toZ [core] sb ^ 2 * ZT.toZ [core] sc ^ 2 *
        (2 * (1 + ZT.toZ [core] x + ZT.toZ [core] y + ZT.toZ [core] z) * ZT.toZ [core] τ)) *
      hc

end LeanProofs.IPRA.Geometry.SphericalSolidAngle
