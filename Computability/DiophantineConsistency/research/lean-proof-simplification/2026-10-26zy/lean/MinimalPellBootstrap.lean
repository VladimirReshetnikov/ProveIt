import Mathlib.Tactic.Linarith
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum.Ineq

/-!
A source-level arithmetic prototype for a smaller Pell bootstrap dependency.
It imports no ProveIt module and does not claim a production integration.
The maintained source_Y_ge_two statement is stronger than needed: the
linear lifting row and nonnegative beta suffice. The quadratic row is unused.
-/
namespace MinimalPellBootstrap

/-- Counterfactual client after the earlier source-register decoding proposal:
with N = q*(1+L), positivity of L already supplies the needed factor two.
No identity L=q^2-1 or N=q^3 is needed. -/
theorem semantic_lower {q L N s : ℕ}
    (hq : 1 ≤ q) (hL : 0 < L) (hs : 0 < s)
    (hN : N = q * (1 + L)) : 2 ≤ N * s := by
  have hN2 : 2 ≤ N := by rw [hN]; nlinarith
  exact hN2.trans (Nat.le_mul_of_pos_right N hs)

/-- The actual signed source row, without the unused quadratic row,
without positivity of J, and with beta merely nonnegative. -/
theorem raw_lower {β : ℤ} {J L N s : ℕ}
    (hβ : 0 ≤ β) (hL : 0 < L) (hs : 0 < s)
    (hrow : (-1 : ℤ) + (-1) * L + N + (-β) * J +
      (-β) * ((J : ℤ) * L) = 0) : 2 ≤ N * s := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ (Nat.cast_nonneg J)
  have hLZ : (1 : ℤ) ≤ L := by exact_mod_cast hL
  have hNz : (2 : ℤ) ≤ N := by
    nlinarith [mul_nonneg hβJ (show (0 : ℤ) ≤ L by positivity)]
  have hN : 2 ≤ N := by exact_mod_cast hNz
  exact hN.trans (Nat.le_mul_of_pos_right N hs)

/-- Beta zero shows the strict-beta premise cannot be essential. -/
example : 2 ≤ (2 : ℕ) * 1 :=
  raw_lower (β := 0) (J := 0) (L := 1) (N := 2) (s := 1)
    (by decide) (by decide) (by decide) (by norm_num)

#print axioms semantic_lower
#print axioms raw_lower
end MinimalPellBootstrap

namespace MinimalPellBootstrap
/-- Sharper: positivity of the lifted register forces positivity of its
integer quotient, so no beta sign restriction is required at all. -/
theorem raw_lower_no_beta {β : ℤ} {J L N s : ℕ}
    (hL : 0 < L) (hN : 0 < N) (hs : 0 < s)
    (hrow : (-1 : ℤ) + (-1) * L + N + (-β) * J +
      (-β) * ((J : ℤ) * L) = 0) : 2 ≤ N * s := by
  have hfactor : (N : ℤ) = (1 + β * J) * (1 + L) := by
    linear_combination hrow
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  have hLZ : (1 : ℤ) ≤ L := by exact_mod_cast hL
  have hq : (0 : ℤ) < 1 + β * J := by
    exact (mul_pos_iff_of_pos_right (by positivity : (0 : ℤ) < 1 + L)).mp
      (hfactor ▸ hNz)
  have hN2z : (2 : ℤ) ≤ N := by nlinarith
  have hN2 : 2 ≤ N := by exact_mod_cast hN2z
  exact hN2.trans (Nat.le_mul_of_pos_right N hs)
#print axioms raw_lower_no_beta
end MinimalPellBootstrap

namespace MinimalPellBootstrap
/-- This expression is copied literally from the source's row-1 `change`
statement at the pinned commit. Production row-table binding is separate. -/
def sourceRowOne (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ) : ℤ :=
  (-1 : ℤ) + (-1) * x 24 + x 16 + (-ports 0) * x 0 +
    (-ports 0) * ((x 0 : ℤ) * x 24)

/-- A direct replacement body retaining the old beta premise for compatibility.
The premise is weakened to nonnegativity inside the proof. -/
theorem compatible_source_Y_ge_two (ports : Fin 4 → ℤ) (hβ : 0 < ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hrow : sourceRowOne ports x = 0) : 2 ≤ x 16 * x 9 := by
  have hβJ : 0 ≤ ports 0 * (x 0 : ℤ) := mul_nonneg hβ.le (Nat.cast_nonneg _)
  have hL : (1 : ℤ) ≤ x 24 := by exact_mod_cast hx 24
  have hNz : (2 : ℤ) ≤ x 16 := by
    dsimp only [sourceRowOne] at hrow
    nlinarith [mul_nonneg hβJ (Nat.cast_nonneg (x 24))]
  have hN : 2 ≤ x 16 := by exact_mod_cast hNz
  exact hN.trans (Nat.le_mul_of_pos_right _ (hx 9))

/-- Stronger pointwise source theorem: neither a quadratic row nor a port
sign condition is needed. Only three positive registers are consumed. -/
theorem stronger_source_Y_ge_two (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hL : 0 < x 24) (hN : 0 < x 16) (hs : 0 < x 9)
    (hrow : sourceRowOne ports x = 0) : 2 ≤ x 16 * x 9 :=
  raw_lower_no_beta hL hN hs hrow

#print axioms compatible_source_Y_ge_two
#print axioms stronger_source_Y_ge_two
end MinimalPellBootstrap

namespace MinimalPellBootstrap
/-- The other literal equation used to derive positivity of beta itself. -/
def sourceRowZero (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ) : ℤ :=
  (x 24 : ℤ) + ((-2) * ports 0) * x 0 +
    (-(ports 0 ^ 2)) * ((x 0 : ℤ) ^ 2)

/-- On positive source zeros, the sign of beta is an output of the first
two equations. No sign premise on beta or positivity premise on J is used. -/
theorem beta_pos_from_two_rows {β : ℤ} {J L N : ℕ}
    (hL : 0 < L) (hN : 0 < N)
    (hrow0 : (L : ℤ) + ((-2) * β) * J + (-(β ^ 2)) * ((J : ℤ) ^ 2) = 0)
    (hrow1 : (-1 : ℤ) + (-1) * L + N + (-β) * J +
      (-β) * ((J : ℤ) * L) = 0) : 0 < β := by
  let q : ℤ := 1 + β * J
  have hfactor : (N : ℤ) = q * (1 + L) := by
    dsimp [q]
    linear_combination hrow1
  have hLsq : (L : ℤ) = q ^ 2 - 1 := by
    dsimp [q]
    linear_combination hrow0
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have hq : 0 < q :=
    (mul_pos_iff_of_pos_right (by positivity : (0 : ℤ) < 1 + L)).mp
      (hfactor ▸ hNz)
  have hq1 : 1 < q := by
    by_contra h
    have he : q = 1 := by omega
    rw [he] at hLsq
    norm_num at hLsq
    omega
  have hp : 0 < β * J := by dsimp [q] at hq1; omega
  exact pos_of_mul_pos_left hp (Nat.cast_nonneg J)

/-- Pointwise binding to the two literal source rows. The finite tables
remain a production integration boundary. -/
theorem source_beta_pos (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hL : 0 < x 24) (hN : 0 < x 16)
    (hzero : sourceRowZero ports x = 0) (hone : sourceRowOne ports x = 0) :
    0 < ports 0 := beta_pos_from_two_rows hL hN hzero hone

#print axioms beta_pos_from_two_rows
#print axioms source_beta_pos
end MinimalPellBootstrap

/-! The following sourceRows declaration is a byte-exact copy of the maintained
SplitCertificate59 definition at the pinned commit; only its namespace changes.
This verifies literal-table binding without importing cached ProveIt oleans.
It is a focused source extraction, not a complete project build. -/
namespace PinnedSource
variable {R : Type*} [CommRing R]

def sourceRows (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 22 → R :=
  ![(x 24 + ((-2) * ports 0) * (x 0) + ((-(ports 0 ^ 2))) * (x 0 ^ 2)),
    ((-1) + (-1) * (x 24) + x 16 + ((-(ports 0))) * (x 0) + ((-(ports 0))) * (x 0 * x 24)),
    (x 21 + (-1) * (x 10) + ((-(ports 0))) * (x 0 * x 10)),
    (x 20 + (-1) * (x 17) + (-1) * (x 9 * x 16)),
    ((-1) * (x 20 * x 21) + x 17 + x 17 * x 21),
    (x 19 + (-1) * (x 13 * x 20) + x 13 * x 17 + (-1) * (x 12) + (-1) * (x 12 * x 20) + x 12 * x 17),
    (x 18 + (-1) * (x 17 * x 19) + (-1) * (x 13) + (-1) * (x 12) + x 12 * x 17),
    ((-1) + (-1) * (x 18 ^ 2) + x 13 * x 18 + x 12 * x 18 + x 11 ^ 2),
    (x 22 + (-1) * (x 21) + (-1) * (x 19 * x 20) + (-3) * (x 15) + (-4) * (x 15 * x 20)),
    ((-3) + x 30 + (-4) * (x 20) + (-1) * (x 20 ^ 2)),
    (x 23 + (-1) * (x 19 ^ 2)),
    ((-1) + (-1) * (x 23 * x 30) + x 22 ^ 2),
    ((-1) + x 26 + x 13 + x 12 + (-1) * (x 8 * x 19) + (-1) * (x 5 * x 17)),
    ((1) + (-1) * (x 26) + x 24 + (-1) * (x 16) + x 8 * x 19 + (-1) * (x 2 * x 24) + (-1) * (x 1) + (-1) * (x 1 * x 24) + x 1 * x 16 + ((-(ports 3)) + (-(ports 2)) + (2) * ports 0) * (x 0) + (ports 0) * (x 0 * x 24) + ((-(ports 0))) * (x 0 * x 16) + ((-(ports 0))) * (x 0 * x 1) + ((-(ports 0 * ports 3)) + ports 0 ^ 2) * (x 0 ^ 2)),
    ((ports 1) + x 10 + ((-(ports 1))) * (x 2) + (-1) * (x 2 * x 10) + (-1 + (-(ports 1))) * (x 1) + (-1) * (x 1 * x 10) + (ports 0 + ports 0 * ports 1) * (x 0) + (ports 0) * (x 0 * x 10) + ((-(ports 0))) * (x 0 * x 3)),
    (x 25 + (-1) * (x 4 ^ 2)),
    (x 26 + x 19 + (-1) * (x 4 * x 7)),
    (x 27 + x 26 ^ 2 + (-1) * (x 14 ^ 2)),
    (x 28 + (-1) * (x 6 * x 23)),
    (x 29 + (-1) * (x 28 ^ 2)),
    (x 30 + x 29 + (-1) * (x 25 * x 30)),
    ((-1) + (-1) * (x 27 * x 29) + x 14 ^ 2)]

theorem source_Y_ge_two (ports : Fin 4 → ℤ) (hβ : 0 < ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    2 ≤ x 16 * x 9 := by
  have hrow := hs 1
  change (-1 : ℤ) + (-1) * x 24 + x 16 + (-ports 0) * x 0 +
    (-ports 0) * ((x 0 : ℤ) * x 24) = 0 at hrow
  have hβJ : 0 ≤ ports 0 * (x 0 : ℤ) := mul_nonneg hβ.le (Nat.cast_nonneg _)
  have hL : (1 : ℤ) ≤ x 24 := by exact_mod_cast hx 24
  have hNz : (2 : ℤ) ≤ x 16 := by
    nlinarith [mul_nonneg hβJ (Nat.cast_nonneg (x 24))]
  have hN : 2 ≤ x 16 := by exact_mod_cast hNz
  exact hN.trans (Nat.le_mul_of_pos_right _ (hx 9))

theorem source_beta_pos (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hx : ∀ i, 0 < x i)
    (hs : ∀ k, sourceRows ports (fun i => (x i : ℤ)) k = 0) : 0 < ports 0 :=
  MinimalPellBootstrap.beta_pos_from_two_rows (hx 24) (hx 16) (hs 0) (hs 1)

theorem source_Y_ge_two_without_beta (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hx : ∀ i, 0 < x i)
    (hs : ∀ k, sourceRows ports (fun i => (x i : ℤ)) k = 0) : 2 ≤ x 16 * x 9 :=
  MinimalPellBootstrap.raw_lower_no_beta (hx 24) (hx 16) (hx 9) (hs 1)

#print axioms source_Y_ge_two
#print axioms source_beta_pos
#print axioms source_Y_ge_two_without_beta
end PinnedSource
