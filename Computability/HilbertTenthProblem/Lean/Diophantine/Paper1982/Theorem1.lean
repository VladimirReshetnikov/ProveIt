import Diophantine.Paper1982.Master3
import Diophantine.Paper1982.Index
import Diophantine.Paper1976.Theorem39b

/-!
# Jones 1982, Theorem 1: the exponential-binomial universal system

> **Theorem 1.** In order that `x ∈ W_{⟨z,u,y⟩}`, it is necessary and sufficient that the
> following system of equations has a solution (in positive integers):
> `elg² + α = (b − xy)q²`, `q = b^(5^60)`, `λ + q⁴ = 1 + λb⁵`, `θ + 2z = b⁵`, `l = u + tθ`,
> `e = y + mθ`, `b = 2ʷ`,
> `C(g + q³ − 1 − bl + l, g) · C(θλ + e + lq², θλ) ·
>  C(b⁵q − 2q + 2(e − zλ)(1 + xb⁵ + g)⁴ + b⁵λ(1 + q⁴), b⁵q − 2q) = 2η + 1`.

Here the number of unknowns of the representing polynomial is a parameter `ν ≥ 1`
(`q = b^(5^(ν+2))`; the printed `5^60` is `ν = 58`), `⟨z, u, y⟩` is the coding triple (4.1) of
a normalized polynomial `P` of degree `≤ 4` (`Index`, `Normalized`), and the upper arguments
of the binomial coefficients, which are integer expressions, are read as natural numbers
using `Int.toNat`. The equations and positivity hypotheses imply their nonnegativity
(`top1_eq`, `UEqs.S3_nonneg`, `top3_eq`), so this conversion loses no information.
The `τ`-conditions of the master
equivalence become "the three binomial coefficients (4.12) are odd" by Kummer's theorem.
The separate claim that `(58, 4)` is a universal pair is not assumed or proved here.
-/

namespace Jones1982

open Polynomial Finset

/-- The system of Theorem 1 of the 1982 article. With `ν = 58` (exponent `5^60`)
it is, equation for equation, the system of Theorem 1 of the 1980 announcement
*Undecidable Diophantine Equations*, which is therefore not restated in `Paper1980`. -/
structure Thm1 (ν : ℕ) (x z u y : ℕ) (b e g l m q t w α η θ lam : ℕ) : Prop where
  E1 : (e : ℤ) * l * g ^ 2 + α = ((b : ℤ) - x * y) * q ^ 2
  E2 : q = b ^ (5 ^ (ν + 2))
  E3 : lam + q ^ 4 = 1 + lam * b ^ 5
  E4 : θ + 2 * z = b ^ 5
  E5 : l = u + t * θ
  E6 : e = y + m * θ
  E7 : b = 2 ^ w
  E8 : ((g : ℤ) + q ^ 3 - 1 - b * l + l).toNat.choose g *
        (θ * lam + e + l * q ^ 2).choose (θ * lam) *
        ((b : ℤ) ^ 5 * q - 2 * q + (2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 +
          b ^ 5 * lam * (1 + q ^ 4))).toNat.choose (b ^ 5 * q - 2 * q) = 2 * η + 1

section Theorem1

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

/-- The first upper argument is `g + M₁` with `M₁ = q³ − 1 − (b − 1)l`. -/
theorem top1_eq {b g l q : ℕ} (hb : 1 ≤ b) (hM : (b - 1) * l + 2 ≤ q ^ 3) :
    ((g : ℤ) + q ^ 3 - 1 - b * l + l).toNat = g + (q ^ 3 - 1 - (b - 1) * l) := by
  have : ((g : ℤ) + q ^ 3 - 1 - b * l + l) = ((g + (q ^ 3 - 1 - (b - 1) * l) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ q ^ 3), Nat.cast_sub (by omega : (b - 1) * l ≤ q ^ 3 - 1),
      Nat.cast_sub hb]
    ring
  rw [this, Int.toNat_natCast]

/-- The third upper argument is `T₃ + S₃` when `S₃ ≥ 0`. -/
theorem top3_eq {b q : ℕ} (hb : 2 ≤ b) {S : ℤ} (hS : 0 ≤ S) :
    ((b : ℤ) ^ 5 * q - 2 * q + S).toNat = (b ^ 5 - 2) * q + S.toNat := by
  have h2 : 2 ≤ b ^ 5 := le_trans hb (Nat.le_self_pow (by norm_num) b)
  have : ((b : ℤ) ^ 5 * q - 2 * q + S) = S + (((b ^ 5 - 2) * q : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h2]; ring
  rw [this, Int.toNat_add_nat hS, add_comm]

theorem T3_eq {b q : ℕ} : b ^ 5 * q - 2 * q = (b ^ 5 - 2) * q := by
  rw [Nat.sub_mul]

/-- Theorem 1 of the 1982 article; with `ν = 58` also Theorem 1 of the 1980 announcement. -/
theorem theorem_1 (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P)
    (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) :
    Wset P x ↔ ∃ b e g l m q t w α η θ lam : ℕ,
      0 < b ∧ 0 < e ∧ 0 < g ∧ 0 < l ∧ 0 < m ∧ 0 < q ∧ 0 < t ∧ 0 < w ∧ 0 < α ∧ 0 < η ∧ 0 < θ ∧
      0 < lam ∧ Thm1 ν x z u y b e g l m q t w α η θ lam := by
  constructor
  · intro hW
    obtain ⟨b, e, g, l, m, q, t, θ, lam, α, w, he, hg, hl, hm, hq, ht, hθ, hlam, hα, hw, hb,
      hU, hS3⟩ := USys_of_mem hν hP hnorm hI hx hW
    have hb2 : 2 ≤ b := by rw [hb]; exact Nat.one_lt_two_pow (by omega)
    obtain ⟨hbxy, h2zB, heq, hlq, hgq, hbq, heb, hlb, hlamE⟩ :=
      hU.toUEqs.sizes hI hx hb2 hg hl hm ht hα
    obtain ⟨⟨U6, U3, U4, U5, U7, U8⟩, τ1, τ2, τ3⟩ := hU
    have hM := M1_bounds hb2 hbq hlq
    -- the three binomial coefficients are odd
    have h1 : Odd (((g : ℤ) + q ^ 3 - 1 - b * l + l).toNat.choose g) := by
      rw [top1_eq (by omega) hM]; exact (τ_two_eq_zero_iff_odd _ _).1 τ1
    have h2 : Odd ((θ * lam + e + l * q ^ 2).choose (θ * lam)) := by
      have := (τ_two_eq_zero_iff_odd _ _).1 τ2
      rwa [Nat.choose_symm_add, add_comm, ← add_assoc] at this
    have h3 : Odd (((b : ℤ) ^ 5 * q - 2 * q + (2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 +
        b ^ 5 * lam * (1 + q ^ 4))).toNat.choose (b ^ 5 * q - 2 * q)) := by
      rw [top3_eq hb2 hS3, T3_eq]
      have := (τ_two_eq_zero_iff_odd _ _).1 τ3
      rwa [Nat.choose_symm_add, add_comm] at this
    have hodd := Nat.odd_mul.2 ⟨Nat.odd_mul.2 ⟨h1, h2⟩, h3⟩
    -- the product is at least `3`
    have hge : 2 ≤ ((g : ℤ) + q ^ 3 - 1 - b * l + l).toNat.choose g := by
      rw [top1_eq (by omega) hM]
      have := JSWW1976.le_choose_of_lt (n := g + (q ^ 3 - 1 - (b - 1) * l)) (k := g) hg (by omega)
      omega
    obtain ⟨η, hη⟩ := hodd
    refine ⟨b, e, g, l, m, q, t, w, α, η, θ, lam, by omega, he, hg, hl, hm, hq, ht, hw, hα, ?_,
      hθ, hlam, ⟨U6, U3, U4, U5, U7, U8, hb, hη⟩⟩
    have hpos2 : 0 < (θ * lam + e + l * q ^ 2).choose (θ * lam) := h2.pos
    have hpos3 : 0 < ((b : ℤ) ^ 5 * q - 2 * q + (2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 +
        b ^ 5 * lam * (1 + q ^ 4))).toNat.choose (b ^ 5 * q - 2 * q) := h3.pos
    have : 2 ≤ ((g : ℤ) + q ^ 3 - 1 - b * l + l).toNat.choose g *
        (θ * lam + e + l * q ^ 2).choose (θ * lam) *
        ((b : ℤ) ^ 5 * q - 2 * q + (2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 +
          b ^ 5 * lam * (1 + q ^ 4))).toNat.choose (b ^ 5 * q - 2 * q) := by
      calc 2 = 2 * 1 * 1 := by norm_num
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hge hpos2) hpos3
    omega
  · rintro ⟨b, e, g, l, m, q, t, w, α, η, θ, lam, -, he, hg, hl, hm, hq, ht, hw, hα, -, hθ, hlam,
      ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩⟩
    have hU : UEqs ν x z u y b e g l m q t θ lam α := ⟨E1, E2, E3, E4, E5, E6⟩
    have hb2 : 2 ≤ b := by rw [E7]; exact Nat.one_lt_two_pow (by omega)
    obtain ⟨hbxy, h2zB, heq, hlq, hgq, hbq, heb, hlb, hlamE⟩ :=
      hU.sizes hI hx hb2 hg hl hm ht hα
    have hM := M1_bounds hb2 hbq hlq
    have hS3 := hU.S3_nonneg hI hx hb2 hg hl hm ht hα
    have hodd : Odd (2 * η + 1) := ⟨η, rfl⟩
    rw [← E8, Nat.odd_mul, Nat.odd_mul] at hodd
    obtain ⟨⟨h1, h2⟩, h3⟩ := hodd
    refine mem_of_USys hν hP hI hx E7 hw hg hl hm ht hα ⟨hU, ?_, ?_, ?_⟩
    · rw [top1_eq (by omega) hM] at h1
      exact (τ_two_eq_zero_iff_odd _ _).2 h1
    · rw [τ_two_eq_zero_iff_odd, Nat.choose_symm_add, add_comm, ← add_assoc]
      exact h2
    · rw [top3_eq hb2 hS3, T3_eq] at h3
      rw [τ_two_eq_zero_iff_odd, Nat.choose_symm_add, add_comm]
      exact h3

end Theorem1

/-- Every normalized polynomial of degree at most four has a positive coding triple
whose twelve-witness system represents its positive inputs, uniformly in `x`.
The representing polynomial may have any positive number `ν` of witness variables. -/
theorem theorem_1_representation {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P) :
    ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧ Index ν P z u y ∧
      ∀ x : ℕ, 0 < x →
        (Wset P x ↔ ∃ b e g l m q t w α η θ lam : ℕ,
          0 < b ∧ 0 < e ∧ 0 < g ∧ 0 < l ∧ 0 < m ∧ 0 < q ∧ 0 < t ∧ 0 < w ∧
          0 < α ∧ 0 < η ∧ 0 < θ ∧ 0 < lam ∧ Thm1 ν x z u y b e g l m q t w α η θ lam) := by
  obtain ⟨z, u, y, hz, hu, hy, hI⟩ := exists_index P hν
  exact ⟨z, u, y, hz, hu, hy, hI, fun _ hx => theorem_1 hν hP hnorm hI hx⟩

end Jones1982
