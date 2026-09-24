import Diophantine.Common.PellInt
import Diophantine.Paper1982.Exponential
import Diophantine.Paper1980.PellDoubled

/-!
# The two exponent decodings of the 99-operation system

With the main parameter `A = a + 2` and `c = ψ_A(J)`, `d = χ_A(J)` (from the
doubled-index block):

* `E14 : d = U + a c + γ(8a + 15)` is the χ-congruence criterion of Lemma 2.22
  (1982) with base `4`, target `U` and index `J`, since `8a + 15 = 8A − 17`
  and `a = A − 4`; with `4^(3J) < A` and `U³ < A` it gives `U = 4^J` (`exp_U`).
* `E19 : μ² = 1 + (A² − 1)κ²` makes `κ = ψ_A(t₀)`, `μ = χ_A(t₀)`; the gap
  `κ < c` gives `t₀ < J`; `E20 : κ = ψ₄(L) + Δ a` and `ψ_A ≡ ψ₄ (mod a)` (the
  parameters are congruent modulo `a`) identify `t₀ = L` once `8^J ≤ a`; then
  `E18 : μ = q + κ(A − B) + ρ(2AB − B² − 1)` is the same criterion with base
  `B`, target `q`, index `L`, giving `q = B^L` (`exp_q`).
-/

namespace Jones1980

namespace Exp90

open Diophantine Pell

theorem two_lt_one : 1 < 2 := by norm_num

/-- `(a + 2)² − 1 = a² + 8a + 15`. -/
theorem sq_sub_one_eq (a : ℕ) : (a + 2) ^ 2 - 1 = a ^ 2 + 4 * a + 3 := by
  have : (a + 2) ^ 2 = a ^ 2 + 4 * a + 4 := by ring
  omega

/-- The first exponent decoding, `U = 4^J`. -/
theorem exp_U {a c d γ J U : ℕ} (hA : 1 < a + 2) (hc : c = ψ hA J) (hd : d = χ hA J)
    (hJ : 0 < J) (hsize1 : 2 ^ (3 * J) < a + 2) (hsize2 : U ^ 3 < a + 2)
    (E14 : d = U + a * c + γ * (4 * a + 3)) : U = 2 ^ J := by
  apply Jones1982.pow_of_χ_congruence (A := a + 2) (V := 2) (B := J) (W := U) (by norm_num) hJ hsize1
    hsize2 hA
  rw [← hc, ← hd]
  have h1 : 2 * (a + 2) * 2 - 2 * 2 - 1 = 4 * a + 3 := by omega
  have h2 : a + 2 - 2 = a := by omega
  rw [h1, h2, E14]
  have h3 : U + c * a ≤ U + a * c + γ * (4 * a + 3) := by
    rw [mul_comm c a]; exact Nat.le_add_right _ _
  refine ((Nat.modEq_iff_dvd' h3).2 ⟨γ, ?_⟩).symm
  rw [mul_comm c a, mul_comm (4 * a + 3) γ]
  omega

/-- `ψ_{a+2}(t) ≡ ψ_2(t) (mod a)`. -/
theorem yn_add_two_modEq (a : ℕ) (hA : 1 < a + 2) (t : ℕ) :
    (yn hA t : ℤ) ≡ yn two_lt_one t [ZMOD a] := by
  rw [yn_eq_yr hA, yn_eq_yr two_lt_one]
  apply yr_modEq
  rw [Int.modEq_iff_dvd]
  exact ⟨-1, by push_cast; ring⟩

/-- `ψ_2(t) < 4^t`. -/
theorem yn_two_lt (t : ℕ) : yn two_lt_one t < 4 ^ t := by
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; simp
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have := ψ_succ_le_pow two_lt_one s
    simp only [Diophantine.ψ] at this
    calc yn two_lt_one (s + 1) ≤ (2 * 2) ^ s := this
      _ < 4 ^ (s + 1) := by
        rw [show (2 * 2 : ℕ) = 4 by rfl]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- The second exponent decoding, `q = B^L`, together with the identification of the
gap witnesses `κ = ψ_A(L)`, `μ = χ_A(L)`. -/
theorem exp_q {a c κ μ ρ Δ q B L J Tindex : ℕ} (hA : 1 < a + 2) (hc : c = ψ hA J)
    (hL : 0 < L) (hLJ : L < J) (hκc : κ < c) (hκ : 0 < κ)
    (hT : Tindex = yn two_lt_one L) (hbig : 4 ^ J ≤ a)
    (hB : 0 < B) (hq : 0 < q) (hsize1 : B ^ (3 * L) < a + 2) (hsize2 : q ^ 3 < a + 2)
    (E18 : (μ : ℤ) = q + κ * ((a : ℤ) + 2 - B) +
      ρ * (2 * ((a : ℤ) + 2) * B - (B : ℤ) ^ 2 - 1))
    (E19 : μ ^ 2 = 1 + (a ^ 2 + 4 * a + 3) * κ ^ 2)
    (E20 : κ = Tindex + Δ * a) :
    q = B ^ L ∧ κ = ψ hA L ∧ μ = χ hA L := by
  -- the Pell pair of the gap
  obtain ⟨t₀, hμ, hκt⟩ : ∃ t₀, μ = xn hA t₀ ∧ κ = yn hA t₀ := by
    apply eq_pell_of_sq hA
    rw [sq_sub_one_eq]; exact E19
  have ht₀J : t₀ < J := by
    have hcJ : c = yn hA J := hc
    have : yn hA t₀ < yn hA J := by rw [← hκt, ← hcJ]; exact hκc
    exact (strictMono_y hA).lt_iff_lt.1 this
  have ht₀ : 0 < t₀ := by
    by_contra h
    push Not at h
    have : t₀ = 0 := by omega
    rw [this, yn_zero] at hκt; omega
  -- `ψ_4(t₀) ≡ ψ_4(L) (mod a)`, both below `a`
  have h1 : (yn two_lt_one t₀ : ℤ) ≡ yn two_lt_one L [ZMOD a] := by
    have e1 := yn_add_two_modEq a hA t₀
    rw [← hκt] at e1
    have e2 : (κ : ℤ) ≡ yn two_lt_one L [ZMOD a] := by
      rw [Int.modEq_iff_dvd, E20, hT]
      exact ⟨-Δ, by push_cast; ring⟩
    exact e1.symm.trans e2
  have h2 : yn two_lt_one t₀ ≡ yn two_lt_one L [MOD a] := Int.natCast_modEq_iff.1 h1
  have hlt1 : yn two_lt_one t₀ < a :=
    lt_of_lt_of_le (yn_two_lt t₀) (le_trans (Nat.pow_le_pow_right (by norm_num) ht₀J.le) hbig)
  have hlt2 : yn two_lt_one L < a :=
    lt_of_lt_of_le (yn_two_lt L) (le_trans (Nat.pow_le_pow_right (by norm_num) hLJ.le) hbig)
  have ht₀L : t₀ = L :=
    (strictMono_y two_lt_one).injective (Nat.ModEq.eq_of_lt_of_lt h2 hlt1 hlt2)
  rw [ht₀L] at hμ hκt
  refine ⟨?_, hκt, hμ⟩
  -- the criterion with base `B`, target `q`, index `L`
  have hBA : B < a + 2 := by
    have : B ≤ B ^ (3 * L) := Nat.le_self_pow (by omega) B
    omega
  apply Jones1982.pow_of_χ_congruence (A := a + 2) (V := B) (B := L) (W := q) hB hL hsize1 hsize2 hA
  show xn hA L ≡ q + yn hA L * (a + 2 - B) [MOD 2 * (a + 2) * B - B * B - 1]
  rw [← hκt, ← hμ]
  rw [Nat.modEq_iff_dvd]
  have hmod : ((2 * (a + 2) * B - B * B - 1 : ℕ) : ℤ) = 2 * ((a : ℤ) + 2) * B - (B : ℤ) ^ 2 - 1 := by
    have hle : B * B + 1 ≤ 2 * (a + 2) * B := by nlinarith
    push_cast [Nat.cast_sub (by omega : B * B ≤ 2 * (a + 2) * B),
      Nat.cast_sub (by omega : 1 ≤ 2 * (a + 2) * B - B * B)]
    ring
  rw [hmod]
  push_cast [Nat.cast_sub hBA.le]
  exact ⟨-ρ, by rw [E18]; ring⟩

end Exp90

end Jones1980
