import Mathlib.Data.Int.Basic

/-!
# The 99-operation universal system (satellite work on Jones 1980)

The satellite article to the 1980 announcement measures the complexity of a
system of Diophantine equations by the number of additions and
multiplications of a straight-line certificate that verifies a proposed
solution (fixed numerals free, intermediates reused, every power by repeated
multiplication).  The final system reached by the successive reductions —
`Papers/1980/COMPOSED_99_PROOF.md`, receipt
`Papers/verification/round26_1980_composed_certificate.json` — has 99
operations: 22 equations in 34 positive unknowns with the four supplied
parameters `x, V, H, Tindex`.  The three parameters `V, H, Tindex` form the
*admissible index* of the represented set; they do not depend on the input.

This module transcribes that system.  Every equation is the source residual
of the receipt (the receipt writes the defining expression of `σ` in place
of `σ` inside the packing equation `E7`; the two forms are equivalent by
`ES`).  Subtraction is interpreted over the integers, as in the 1982 article.

Abbreviations of the notes, written out here: `B = H b²`, `C = x + g`,
`U = w n²`, `Y = s n²`, `Q = U Y²`, `A = a + 4`, `A² − 1 = a² + 8a + 15`,
`J = 2r + 1`, `v = o f − d²`, `K_aux = (A² − 1)(f² − 1)`,
`S = g + q²(l + e q + q² σ)`, `T⁺ = q²(1 + θλ) − (b − 1) l + θ l q⁴`.
-/

namespace Jones1980

/-- The 22 equations of the 99-operation system. -/
structure Sys99 (x V H Tindex : ℕ)
    (a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω : ℕ) : Prop where
  /-- `E1a`: the packed code with positive slack, `l + e q + α = q²`. -/
  E1a : l + e * q + α = q ^ 2
  /-- `E1b`: `b = x + β`, so `b > x`. -/
  E1b : b = x + β
  /-- `E2`: the geometric equation `λ(B − 1) = q² − 1` with `B = H b²`. -/
  E2 : lam + q ^ 2 = 1 + lam * (H * b ^ 2)
  /-- `E3`: `θ + 4 = B`. -/
  E3 : θ + 4 = H * b ^ 2
  /-- `E4/E5` packed: the base-four congruence `l + e q = V + t θ`. -/
  E45 : l + e * q = V + t * θ
  /-- `E6`: `n = q⁸`. -/
  E6 : n = q ^ 8
  /-- `E7`: the central code `r = S(n² − n) + T⁺(n² − 1)`. -/
  E7 : (r : ℤ) = ((g : ℤ) + q ^ 2 * (l + e * q + q ^ 2 * σ)) * ((n : ℤ) ^ 2 - n) +
    ((q : ℤ) ^ 2 * (1 + θ * lam) - ((b : ℤ) - 1) * l + θ * l * q ^ 4) * ((n : ℤ) ^ 2 - 1)
  /-- `E9`: the first Pell norm `τ(τ + 1) = Q(Q + 1) k²`, `Q = U Y²`. -/
  E9 : τ * (τ + 1) = (w * n ^ 2 * (s * n ^ 2) ^ 2) * (w * n ^ 2 * (s * n ^ 2) ^ 2 + 1) * k ^ 2
  /-- `E10a`: the positive interval `c = k Y + η`. -/
  E10a : c = k * (s * n ^ 2) + η
  /-- `E10b`: `k = η + ζ`, so `η < k`. -/
  E10b : k = η + ζ
  /-- `E11`: the first index congruence `k = r + 1 + h U Y`. -/
  E11 : k = r + 1 + h * (w * n ^ 2) * (s * n ^ 2)
  /-- `E12`: the main Pell parameter shift `a = Y(U + 1)`; the parameter is `A = a + 4`. -/
  E12 : a = s * n ^ 2 * (w * n ^ 2 + 1)
  /-- `E13`: the gap `c = κ + φ`. -/
  E13 : c = κ + φ
  /-- `E14`: the base-four exponent congruence `d = U + a c + γ(8a + 15)`. -/
  E14 : d = w * n ^ 2 + a * c + γ * (8 * a + 15)
  /-- `E15`: the main Pell norm `d² = 1 + (A² − 1) c²`. -/
  E15 : d ^ 2 = 1 + (a ^ 2 + 8 * a + 15) * c ^ 2
  /-- `E16`: the auxiliary Pell norm `f² = 1 + (A² − 1)(i c²)²`. -/
  E16 : f ^ 2 = 1 + (a ^ 2 + 8 * a + 15) * i ^ 2 * c ^ 4
  /-- `E17`: the doubled-index signed norm `v(v + 1) = K_aux(K_aux − 1)(2r + 1 + j c)²`. -/
  E17 : ((o : ℤ) * f - d ^ 2) * ((o : ℤ) * f - d ^ 2 + 1) =
    (((a : ℤ) ^ 2 + 8 * a + 15) * (f ^ 2 - 1)) * (((a : ℤ) ^ 2 + 8 * a + 15) * (f ^ 2 - 1) - 1) *
      (2 * r + 1 + j * c) ^ 2
  /-- `E18`: the second exponent congruence `μ = q + κ(A − B) + ρ(2AB − B² − 1)`. -/
  E18 : (μ : ℤ) = q + κ * ((a : ℤ) + 4 - H * b ^ 2) +
    ρ * (2 * ((a : ℤ) + 4) * (H * b ^ 2) - (H * b ^ 2) ^ 2 - 1)
  /-- `E19`: the second main Pell norm `μ² = 1 + (A² − 1) κ²`. -/
  E19 : μ ^ 2 = 1 + (a ^ 2 + 8 * a + 15) * κ ^ 2
  /-- `E20`: the fixed index `κ = Tindex + Δ a`. -/
  E20 : κ = Tindex + Δ * a
  /-- `S3_positive`: `σ = θ λ q − (2λ − e) C²`, `C = x + g`. -/
  ES : (σ : ℤ) = θ * lam * q - (2 * lam - e) * (x + g) ^ 2
  /-- `coefficient_positive`: `Ω = 2λ − e`. -/
  EΩ : (Ω : ℤ) = 2 * lam - e

/-- Solvability of the system in positive integers, for the input `x` and the
index `(V, H, Tindex)`. -/
def Solvable99 (x V H Tindex : ℕ) : Prop :=
  ∃ a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω : ℕ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧ 0 < i ∧ 0 < j ∧
    0 < k ∧ 0 < l ∧ 0 < n ∧ 0 < o ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧ 0 < t ∧ 0 < w ∧ 0 < α ∧
    0 < γ ∧ 0 < η ∧ 0 < θ ∧ 0 < lam ∧ 0 < τ ∧ 0 < φ ∧ 0 < κ ∧ 0 < μ ∧ 0 < ρ ∧ 0 < Δ ∧
    0 < β ∧ 0 < ζ ∧ 0 < σ ∧ 0 < Ω ∧
    Sys99 x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω

end Jones1980
