import IPRADerivations.DiophantineNumberTheory.ThueGrid
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Four squares: Euler's identity and the algebra of one descent step

Packet: `diophantine-number-theory/lagrange_four_squares_ipra_2026-11-22`, `sections/01_foundations.tex`
(`lem:euler`, "Euler's four-square identity") and `sections/03_descent.tex` ("The new multiplier", "The new
representing tuple").

Signed quantities never appear as terms. A signed form `P − Q` (with `P`, `Q` natural-number polynomials)
enters only through the square of `|P − Q| = ad P Q`, and `ad_sq` turns that square into
`P² + Q² − 2PQ`, so every statement is a polynomial identity between natural-number terms and every proof is
a certificate in the ring of differences.

* `N4`: `a² + b² + c² + d²`;
* `ad_sq`: `|P − Q|² + 2PQ = P² + Q²`;
* `euler4` (`lem:euler`): `N(x) N(y) = N(z)` with `z = x ȳ` written with absolute differences;
* `le_sq_part`, `le_N4_1`, …, `le_N4_4`: each entry of a tuple is at most its norm;
* the descent step. For a tuple `x` with `N(x) = m p` let `x_i ≡ y_i (mod m)` with the signed residue
  `y_i = a_i (1 − 2 s_i)`, `s_i ∈ {0, 1}`, written as `x_i + 2 s_i a_i = a_i + m U_i`, and `N(a) = m m'`. Then
  - `star`: `m' + 2 ⟨U, a⟩ + m N(U) = p + 4 ∑ U_i s_i a_i` (the relation `N(x) = N(y) + 2m⟨U, y⟩ + m² N(U)`
    divided by `m`);
  - `descent_alg`: the tuple `w` with `w₁ = m' + ⟨U, y⟩` and `w_j` the three antisymmetric forms of `U`,
    `y` satisfies `N(w) = m' p`. No division is performed: `x ȳ = m w` holds identically, so the quotient
    tuple of the paper is written down directly.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresAlgebra

open_ipra
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.ThueGrid (ad)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `a² + b² + c² + d²`. -/
abbrev N4 (a b c d : PTm k) : PTm k := a * a + b * b + (c * c + d * d)

/-! ## Squares of absolute differences -/

theorem ad_alg {m1 m2 P Q : PTm k} (z : Γ ⊢[PRAAx] m1 ≐ zero) (e : Γ ⊢[PRAAx] Q ≐ P + m2) :
    Γ ⊢[PRAAx] (m1 + m2) * (m1 + m2) + two * (P * Q) ≐ P * P + Q * Q := by
  ipra_lc (𝔞 m1 + 𝔞 m2 + 𝔞 Q - 𝔞 P) * (natEq z - natEq e)

theorem ad_alg' {m1 m2 P Q : PTm k} (z : Γ ⊢[PRAAx] m2 ≐ zero) (e : Γ ⊢[PRAAx] P ≐ Q + m1) :
    Γ ⊢[PRAAx] (m1 + m2) * (m1 + m2) + two * (P * Q) ≐ P * P + Q * Q := by
  ipra_lc (𝔞 m1 + 𝔞 m2 + 𝔞 P - 𝔞 Q) * (natEq z - natEq e)

/-- `|P − Q|² + 2PQ = P² + Q²`. -/
theorem ad_sq (P Q : PTm k) : Γ ⊢[PRAAx] ad P Q * ad P Q + two * (P * Q) ≐ P * P + Q * Q := by
  refine .orE (le_total P Q) ?_ ?_
  · have hz : (le P Q :: Γ) ⊢[PRAAx] monus P Q ≐ zero := Prf.hyp0
    exact ad_alg hz (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le P Q)))
  · have hz : (le Q P :: Γ) ⊢[PRAAx] monus Q P ≐ zero := Prf.hyp0
    exact ad_alg' hz (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le Q P)))

/-! ## Euler's identity -/

/-- `lem:euler`: `N(x ȳ) = N(x) N(y)`, the three antisymmetric coordinates as absolute differences. -/
theorem euler4 (a b c d e f g h : PTm k) : Γ ⊢[PRAAx]
    N4 (a * e + b * f + (c * g + d * h)) (ad (b * e + d * g) (a * f + c * h))
      (ad (b * h + c * e) (a * g + d * f)) (ad (c * f + d * e) (a * h + b * g)) ≐
    N4 a b c d * N4 e f g h := by
  ipra_lc natEq (ad_sq (Γ := Γ) (b * e + d * g) (a * f + c * h)) +
    natEq (ad_sq (Γ := Γ) (b * h + c * e) (a * g + d * f)) + natEq (ad_sq (Γ := Γ) (c * f + d * e) (a * h + b * g))

/-! ## Entries are bounded by the norm -/

theorem le_sq_part {a R n : PTm k} (e : Γ ⊢[PRAAx] a * a + R ≐ n) : Γ ⊢[PRAAx] le a n := by
  refine .orE (zero_or_succ a) ?_ ?_
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le n)
  · have ea := natEq (Prf.hyp0 (Γ := Γ) (φ := a ≐ succ (pred a)))
    have en := natEq (e.wk (ψ := a ≐ succ (pred a)))
    ipra_le 𝔞 (pred a) * 𝔞 (pred a) + 𝔞 (pred a) + 𝔞 R with (𝔞 a + 𝔞 (pred a)) * ea - en

theorem le_N4_1 {a b c d n : PTm k} (e : Γ ⊢[PRAAx] N4 a b c d ≐ n) : Γ ⊢[PRAAx] le a n := by
  have en := natEq e
  exact le_sq_part (R := b * b + (c * c + d * d)) (by apply deriveNat; ipra_simps; linear_combination en)

theorem le_N4_2 {a b c d n : PTm k} (e : Γ ⊢[PRAAx] N4 a b c d ≐ n) : Γ ⊢[PRAAx] le b n := by
  have en := natEq e
  exact le_sq_part (R := a * a + (c * c + d * d)) (by apply deriveNat; ipra_simps; linear_combination en)

theorem le_N4_3 {a b c d n : PTm k} (e : Γ ⊢[PRAAx] N4 a b c d ≐ n) : Γ ⊢[PRAAx] le c n := by
  have en := natEq e
  exact le_sq_part (R := a * a + b * b + d * d) (by apply deriveNat; ipra_simps; linear_combination en)

theorem le_N4_4 {a b c d n : PTm k} (e : Γ ⊢[PRAAx] N4 a b c d ≐ n) : Γ ⊢[PRAAx] le d n := by
  have en := natEq e
  exact le_sq_part (R := a * a + b * b + c * c) (by apply deriveNat; ipra_simps; linear_combination en)

/-! ## The descent step -/

section Descent

variable (x A s U : Fin 4 → PTm k) (m mp p : PTm k)

/-- `⟨U, a⟩`. -/
abbrev dotUA : PTm k := U 0 * A 0 + U 1 * A 1 + (U 2 * A 2 + U 3 * A 3)

/-- `∑ U_i s_i a_i`. -/
abbrev dotUSA : PTm k := U 0 * (s 0 * A 0) + U 1 * (s 1 * A 1) + (U 2 * (s 2 * A 2) + U 3 * (s 3 * A 3))

/-- The residue equations `x_i + 2 s_i a_i = a_i + m U_i`. -/
abbrev resEq (i : Fin 4) : Fm PTm k := x i + two * (s i * A i) ≐ A i + m * U i

theorem prestar (he : ∀ i, Γ ⊢[PRAAx] resEq x A s U m i) (ht : ∀ i, Γ ⊢[PRAAx] s i * s i ≐ s i)
    (n1 : Γ ⊢[PRAAx] N4 (x 0) (x 1) (x 2) (x 3) ≐ m * p)
    (n2 : Γ ⊢[PRAAx] N4 (A 0) (A 1) (A 2) (A 3) ≐ m * mp) :
    Γ ⊢[PRAAx] m * (mp + two * dotUA A U + m * N4 (U 0) (U 1) (U 2) (U 3)) ≐
      m * (p + (two * two) * dotUSA A s U) := by
  ipra_lc natEq n1 - natEq n2 - (𝔞 (x 0) + 𝔞 (A 0) * (1 - 2 * 𝔞 (s 0)) + 𝔞 m * 𝔞 (U 0)) * natEq (he 0) -
    (𝔞 (x 1) + 𝔞 (A 1) * (1 - 2 * 𝔞 (s 1)) + 𝔞 m * 𝔞 (U 1)) * natEq (he 1) -
    (𝔞 (x 2) + 𝔞 (A 2) * (1 - 2 * 𝔞 (s 2)) + 𝔞 m * 𝔞 (U 2)) * natEq (he 2) -
    (𝔞 (x 3) + 𝔞 (A 3) * (1 - 2 * 𝔞 (s 3)) + 𝔞 m * 𝔞 (U 3)) * natEq (he 3) -
    4 * (𝔞 (A 0) * 𝔞 (A 0) * natEq (ht 0) + 𝔞 (A 1) * 𝔞 (A 1) * natEq (ht 1) + 𝔞 (A 2) * 𝔞 (A 2) * natEq (ht 2) + 𝔞 (A 3) * 𝔞 (A 3) * natEq (ht 3))

/-- `m' + 2 ⟨U, a⟩ + m N(U) = p + 4 ∑ U_i s_i a_i`. -/
theorem star (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (he : ∀ i, Γ ⊢[PRAAx] resEq x A s U m i)
    (ht : ∀ i, Γ ⊢[PRAAx] s i * s i ≐ s i)
    (n1 : Γ ⊢[PRAAx] N4 (x 0) (x 1) (x 2) (x 3) ≐ m * p)
    (n2 : Γ ⊢[PRAAx] N4 (A 0) (A 1) (A 2) (A 3) ≐ m * mp) :
    Γ ⊢[PRAAx] mp + two * dotUA A U + m * N4 (U 0) (U 1) (U 2) (U 3) ≐ p + (two * two) * dotUSA A s U :=
  mul_cancel hm (prestar x A s U m mp p he ht n1 n2)

/-- The first coordinate of the new tuple: `|m' + ⟨U, y⟩|`. -/
abbrev w1 : PTm k := ad (mp + dotUA A U) (two * dotUSA A s U)

/-- The three antisymmetric coordinates of the new tuple. -/
abbrev w2 : PTm k :=
  ad (A 0 * U 1 + two * (A 1 * U 0 * s 1) + (A 2 * U 3 + two * (A 3 * U 2 * s 3)))
    (two * (A 0 * U 1 * s 0) + A 1 * U 0 + (two * (A 2 * U 3 * s 2) + A 3 * U 2))

abbrev w3 : PTm k :=
  ad (A 0 * U 2 + two * (A 1 * U 3 * s 1) + (two * (A 2 * U 0 * s 2) + A 3 * U 1))
    (two * (A 0 * U 2 * s 0) + A 1 * U 3 + (A 2 * U 0 + two * (A 3 * U 1 * s 3)))

abbrev w4 : PTm k :=
  ad (A 0 * U 3 + A 1 * U 2 + (two * (A 2 * U 1 * s 2) + two * (A 3 * U 0 * s 3)))
    (two * (A 0 * U 3 * s 0) + two * (A 1 * U 2 * s 1) + (A 2 * U 1 + A 3 * U 0))

/-- "The new representing tuple": `N(w) = m' p`. -/
theorem descent_alg (ht : ∀ i, Γ ⊢[PRAAx] s i * s i ≐ s i)
    (n2 : Γ ⊢[PRAAx] N4 (A 0) (A 1) (A 2) (A 3) ≐ m * mp)
    (hs : Γ ⊢[PRAAx] mp + two * dotUA A U + m * N4 (U 0) (U 1) (U 2) (U 3) ≐
      p + (two * two) * dotUSA A s U) :
    Γ ⊢[PRAAx] N4 (w1 A s U mp) (w2 A s U) (w3 A s U) (w4 A s U) ≐ mp * p := by
  ipra_lc natEq (ad_sq (Γ := Γ) (mp + dotUA A U) (two * dotUSA A s U)) +
    natEq (ad_sq (Γ := Γ) (A 0 * U 1 + two * (A 1 * U 0 * s 1) + (A 2 * U 3 + two * (A 3 * U 2 * s 3))) (two * (A 0 * U 1 * s 0) + A 1 * U 0 + (two * (A 2 * U 3 * s 2) + A 3 * U 2))) +
    natEq (ad_sq (Γ := Γ) (A 0 * U 2 + two * (A 1 * U 3 * s 1) + (two * (A 2 * U 0 * s 2) + A 3 * U 1)) (two * (A 0 * U 2 * s 0) + A 1 * U 3 + (A 2 * U 0 + two * (A 3 * U 1 * s 3)))) +
    natEq (ad_sq (Γ := Γ) (A 0 * U 3 + A 1 * U 2 + (two * (A 2 * U 1 * s 2) + two * (A 3 * U 0 * s 3))) (two * (A 0 * U 3 * s 0) + two * (A 1 * U 2 * s 1) + (A 2 * U 1 + A 3 * U 0))) +
    𝔞 mp * natEq hs +
    (𝔞 (U 0) * 𝔞 (U 0) + 𝔞 (U 1) * 𝔞 (U 1) + (𝔞 (U 2) * 𝔞 (U 2) + 𝔞 (U 3) * 𝔞 (U 3))) * (natEq n2 + 4 * (𝔞 (A 0) * 𝔞 (A 0) * natEq (ht 0) + 𝔞 (A 1) * 𝔞 (A 1) * natEq (ht 1) + 𝔞 (A 2) * 𝔞 (A 2) * natEq (ht 2) + 𝔞 (A 3) * 𝔞 (A 3) * natEq (ht 3)))

end Descent

end LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresAlgebra
