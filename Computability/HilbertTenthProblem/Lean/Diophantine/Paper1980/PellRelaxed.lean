import Mathlib.NumberTheory.Pell
import Diophantine.Common.PellInt
import Diophantine.Paper1982.Psi
import Diophantine.Paper1980.PellDoubled

/-!
# Tools for the relaxed auxiliary Pell norm (`Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md`)

The 93-operation system replaces the auxiliary norm `f² = 1 + (A² − 1)(i c²)²`
by the relaxed `(i c²)² = (A² − 1)(f² − 1)`.  The relaxed equation has extra
solutions in general; with `c = ψ_A(p)` and the size bound `c > A (A² − 1)²`
it nevertheless forces `f = χ_A(m)`, `i c² = (A² − 1) ψ_A(m)` and `c ∣ m`,
which is what the doubled-index core (`doubled_index_core`) needs.

The argument writes `A² − 1 = d₀ s₀²` with `d₀` squarefree, identifies both
`(A, s₀)` and the relaxed solution with powers of the fundamental unit
`ε = (F, y₀)` of `x² − d₀ y² = 1` (Mathlib's `Pell.IsFundamental`, a classical
pre-1980 theorem), and compares indices through the strong divisibility
`gcd(ψ_F(n), ψ_F(ep)) = ψ_F(gcd(n, ep))` (Lucas 1878).

This file proves the number-theoretic tools:

1. `yn_gcd`: `gcd(ψ_a(u), ψ_a(v)) = ψ_a(gcd(u, v))`;
2. `comp_xn_yn`: for `A = χ_F(e)`, `χ_A(p) = χ_F(ep)` and `ψ_A(p) ψ_F(e) = ψ_F(ep)`;
3. `pow_x_y`: the components of `ε^k` are `χ_F(k)` and `y₀ ψ_F(k)`;
4. `xn_yn_modEq_pow`: `χ_A(n) ≡ Aⁿ` and `ψ_A(n+1) ≡ (n+1)Aⁿ` modulo `A² − 1`.
-/

namespace Jones1980

open Pell

/-! ### Strong divisibility -/

section Gcd

variable {a : ℕ} (a1 : 1 < a)

/-- `gcd(ψ(u), ψ(u·k + w)) = gcd(ψ(u), ψ(w))`. -/
theorem gcd_yn_add_mul (u k w : ℕ) :
    Nat.gcd (yn a1 u) (yn a1 (u * k + w)) = Nat.gcd (yn a1 u) (yn a1 w) := by
  rw [yn_add]
  have hdvd : yn a1 u ∣ yn a1 (u * k) := (y_dvd_iff a1 u (u * k)).2 (dvd_mul_right u k)
  have hcop : Nat.Coprime (xn a1 (u * k)) (yn a1 u) :=
    Nat.Coprime.coprime_dvd_right hdvd (xy_coprime a1 (u * k))
  obtain ⟨t, ht⟩ := hdvd
  rw [ht, show xn a1 (u * k) * yn a1 w + yn a1 u * t * xn a1 w
      = xn a1 (u * k) * yn a1 w + yn a1 u * (t * xn a1 w) by ring,
    Nat.gcd_add_mul_left_right]
  exact Nat.Coprime.gcd_mul_left_cancel_right (yn a1 w) hcop

/-- Strong divisibility (Lucas): `gcd(ψ(u), ψ(v)) = ψ(gcd(u, v))`. -/
theorem yn_gcd (u v : ℕ) : Nat.gcd (yn a1 u) (yn a1 v) = yn a1 (Nat.gcd u v) := by
  induction u, v using Nat.gcd.induction with
  | H0 n => simp [yn_zero]
  | H1 m n _ ih =>
    rw [Nat.gcd_rec m n, ← ih, Nat.gcd_comm (yn a1 (n % m))]
    have := gcd_yn_add_mul a1 m (n / m) (n % m)
    rwa [Nat.div_add_mod] at this

end Gcd

/-! ### Composition of Pell parameters -/

section Comp

variable {F : ℕ} (hF : 1 < F) (e : ℕ) (hA : 1 < xn hF e)

/-- For `A = χ_F(e)`: `χ_A(p) = χ_F(ep)` and `ψ_A(p) ψ_F(e) = ψ_F(ep)`. -/
theorem comp_xn_yn : ∀ p, xn hA p = xn hF (e * p) ∧ yn hA p * yn hF e = yn hF (e * p)
  | 0 => by simp [xn_zero, yn_zero]
  | p + 1 => by
    obtain ⟨hx, hy⟩ := comp_xn_yn p
    have hd : xn hF e * xn hF e - 1 = (F * F - 1) * yn hF e * yn hF e := by
      have := pell_eq hF e
      change xn hF e * xn hF e - (F * F - 1) * yn hF e * yn hF e = 1 at this
      omega
    constructor
    · have h := xn_succ hA p
      change xn hA (p + 1) = xn hA p * xn hF e + (xn hF e * xn hF e - 1) * yn hA p at h
      have h2 := xn_add hF (e * p) e
      change xn hF (e * p + e) = xn hF (e * p) * xn hF e + (F * F - 1) * yn hF (e * p) * yn hF e
        at h2
      rw [h, show e * (p + 1) = e * p + e by ring, h2, hd, ← hx, ← hy]
      ring
    · have h := yn_succ hA p
      change yn hA (p + 1) = xn hA p + yn hA p * xn hF e at h
      have h2 := yn_add hF (e * p) e
      rw [h, show e * (p + 1) = e * p + e by ring, h2, ← hx, ← hy]
      ring

end Comp

/-! ### Powers of a solution of `x² − d y² = 1` -/

section Fundamental

variable {d : ℤ}

/-- The components of `ε^k` for a solution `ε = (F, y₀)` with `F ≥ 2`:
`(ε^k).x = χ_F(k)` and `(ε^k).y = y₀ ψ_F(k)`. -/
theorem pow_x_y (ε : Pell.Solution₁ d) {F : ℕ} (hF : 1 < F) (hx : ε.x = F) :
    ∀ k, (ε ^ k).x = xn hF k ∧ (ε ^ k).y = ε.y * yn hF k
  | 0 => by simp [xn_zero, yn_zero]
  | k + 1 => by
    obtain ⟨ihx, ihy⟩ := pow_x_y ε hF hx k
    have hprop := ε.prop
    rw [hx] at hprop
    rw [pow_succ, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul, ihx, ihy, hx]
    have hF1 : 1 ≤ F * F := Nat.one_le_iff_ne_zero.2 (by positivity)
    constructor
    · have h := xn_succ hF k
      change xn hF (k + 1) = xn hF k * F + (F * F - 1) * yn hF k at h
      rw [h]; push_cast [Nat.cast_sub hF1]
      linear_combination -(yn hF k : ℤ) * hprop
    · have h := yn_succ hF k
      change yn hF (k + 1) = xn hF k + yn hF k * F at h
      rw [h]; push_cast; ring

end Fundamental

/-! ### Congruences modulo `A² − 1` -/

section Modular

variable {A : ℕ} (hA : 1 < A)

/-- `χ_A(n) ≡ Aⁿ` and `ψ_A(n + 1) ≡ (n + 1) Aⁿ` modulo `A² − 1`. -/
theorem xn_yn_modEq_pow :
    ∀ n, xn hA n ≡ A ^ n [MOD A * A - 1] ∧ yn hA (n + 1) ≡ (n + 1) * A ^ n [MOD A * A - 1]
  | 0 => by simp [xn_zero, Nat.ModEq]
  | n + 1 => by
    obtain ⟨hx, hy⟩ := xn_yn_modEq_pow n
    have h0 : (A * A - 1) * yn hA n ≡ 0 [MOD A * A - 1] :=
      Nat.modEq_zero_iff_dvd.2 (dvd_mul_right _ _)
    have hx1 : xn hA (n + 1) ≡ A ^ (n + 1) [MOD A * A - 1] := by
      have h := xn_succ hA n
      change xn hA (n + 1) = xn hA n * A + (A * A - 1) * yn hA n at h
      rw [h, pow_succ]
      calc xn hA n * A + (A * A - 1) * yn hA n ≡ A ^ n * A + 0 [MOD A * A - 1] :=
            (hx.mul_right A).add h0
        _ = A ^ n * A := by ring
    refine ⟨hx1, ?_⟩
    have h := yn_succ hA (n + 1)
    change yn hA (n + 1 + 1) = xn hA (n + 1) + yn hA (n + 1) * A at h
    rw [h]
    calc xn hA (n + 1) + yn hA (n + 1) * A ≡ A ^ (n + 1) + (n + 1) * A ^ n * A [MOD A * A - 1] :=
          hx1.add (hy.mul_right A)
      _ = (n + 1 + 1) * A ^ (n + 1) := by ring

end Modular

end Jones1980
