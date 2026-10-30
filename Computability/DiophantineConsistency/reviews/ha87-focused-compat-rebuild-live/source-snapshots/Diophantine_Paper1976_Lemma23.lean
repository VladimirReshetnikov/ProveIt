import Diophantine.Common.Pell
import Mathlib.NumberTheory.Pell

/-!
# JSWW 1976, Lemma 2.3 (and Definition 3.7 / Lemma 2.4 of Jones 1978)

> **Lemma 2.3.** For `2 ≤ e`, the condition `e³(e+2)(n+1)² + 1 = □` implies
> `e - 1 + e^(e-2) ≤ n`.  Conversely, for any positive integers `e` and `t`, it is
> possible to satisfy (2.3) with `n` such that `t ∣ n+1`.

The same statement is Lemma 2.4 of Jones 1978 (with `J` for `e`, `r` for `n`) and,
through `U(x,y) = (x+2)³(x+4)(y+1)² + 1`, Definition 3.7 of JSWW 1976.
-/

namespace JSWW1976

open Pell Diophantine

/-- The key numerical inequality behind Lemma 2.3:
`e(e-1) + e^(e-1) < (2e+1)^(e-1)` for `e ≥ 2`. -/
theorem key_ineq {e : ℕ} (he : 2 ≤ e) : e * (e - 1) + e ^ (e - 1) < (2 * e + 1) ^ (e - 1) := by
  rcases Nat.lt_or_ge e 3 with h3 | h3
  · have : e = 2 := by omega
    subst this; norm_num
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 3 := ⟨e - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega]
  have hA : (2 * (m + 3)) ^ (m + 2) ≤ (2 * (m + 3) + 1) ^ (m + 2) :=
    Nat.pow_le_pow_left (by omega) _
  have hB : (2 * (m + 3)) ^ (m + 2) = 2 ^ (m + 2) * (m + 3) ^ (m + 2) := by rw [mul_pow]
  have h4 : 4 ≤ 2 ^ (m + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : (m + 3) * (m + 3) ≤ (m + 3) ^ (m + 2) := by
    calc (m + 3) * (m + 3) = (m + 3) ^ 2 := by ring
      _ ≤ (m + 3) ^ (m + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpos : 0 < (m + 3) ^ (m + 2) := by positivity
  nlinarith

/-- No perfect square lies strictly between `k²` and `(k+1)²`. -/
theorem not_isSquare_of_between {k m : ℕ} (h1 : k * k < m) (h2 : m < (k + 1) * (k + 1)) :
    ¬IsSquare m := by
  rintro ⟨u, rfl⟩
  have hku : k < u := Nat.mul_self_lt_mul_self_iff.1 h1
  have huk : u < k + 1 := Nat.mul_self_lt_mul_self_iff.1 h2
  omega

/-- `e(e+2)` is never a perfect square for `e ≥ 1`. -/
theorem not_isSquare_mul_add_two {e : ℕ} (he : 1 ≤ e) : ¬IsSquare (e * (e + 2)) :=
  not_isSquare_of_between (by nlinarith) (by nlinarith)

/-- Lemma 2.3, size bound.  `x` is the square root witness. -/
theorem lemma_2_3 {e n x : ℕ} (he : 2 ≤ e) (h : e ^ 3 * (e + 2) * (n + 1) ^ 2 + 1 = x * x) :
    e - 1 + e ^ (e - 2) ≤ n := by
  have a1 : 1 < e + 1 := by omega
  -- the Pell equation for a = e+1 and y = e(n+1)
  have hD : (e + 1) * (e + 1) - 1 = e * (e + 2) := by
    have : (e + 1) * (e + 1) = e * (e + 2) + 1 := by ring
    omega
  have hpell : x * x - ((e + 1) * (e + 1) - 1) * (e * (n + 1)) * (e * (n + 1)) = 1 := by
    have : ((e + 1) * (e + 1) - 1) * (e * (n + 1)) * (e * (n + 1)) = e ^ 3 * (e + 2) * (n + 1) ^ 2 := by
      rw [hD]; ring
    rw [this]; omega
  obtain ⟨j, hx, hy⟩ := eq_pell a1 hpell
  -- e ∣ j, from ψ(j) ≡ j (mod e) and e ∣ ψ(j) = e(n+1)
  have hmod : yn a1 j ≡ j [MOD e] := by
    have := yn_modEq_a_sub_one a1 j
    rwa [show e + 1 - 1 = e by omega] at this
  have hdvd : e ∣ j := by
    have h0 : e ∣ yn a1 j := ⟨n + 1, hy.symm⟩
    exact (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 h0)))
  have hj : j ≠ 0 := by
    rintro rfl
    simp [yn_zero] at hy
    omega
  have hje : e ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj) hdvd
  have h1 : yn a1 e ≤ yn a1 j := (strictMono_y a1).monotone hje
  have h2 : (2 * (e + 1) - 1) ^ (e - 1) ≤ yn a1 e := by
    have := pow_le_ψ_succ a1 (e - 1)
    rwa [show e - 1 + 1 = e by omega] at this
  have h4 : e * ((e - 1) + e ^ (e - 2)) = e * (e - 1) + e ^ (e - 1) := by
    have : e ^ (e - 1) = e * e ^ (e - 2) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; ring
  have hlt : e * ((e - 1) + e ^ (e - 2)) < e * (n + 1) := by
    calc e * ((e - 1) + e ^ (e - 2)) = e * (e - 1) + e ^ (e - 1) := h4
      _ < (2 * e + 1) ^ (e - 1) := key_ineq he
      _ = (2 * (e + 1) - 1) ^ (e - 1) := by rw [show 2 * (e + 1) - 1 = 2 * e + 1 by omega]
      _ ≤ yn a1 e := h2
      _ ≤ yn a1 j := h1
      _ = e * (n + 1) := hy.symm
  have := Nat.lt_of_mul_lt_mul_left hlt
  omega

/-- Lemma 2.3, converse: for positive `e` and `t` there are `n` and `x` with
`e³(e+2)(n+1)² + 1 = x²` and `t ∣ n+1`. -/
theorem lemma_2_3_converse {e t : ℕ} (he : 1 ≤ e) (ht : 1 ≤ t) :
    ∃ n x : ℕ, e ^ 3 * (e + 2) * (n + 1) ^ 2 + 1 = x * x ∧ t ∣ n + 1 := by
  -- d = e³(e+2)t² = (et)² · e(e+2) is positive and not a square
  set d : ℤ := ((e ^ 3 * (e + 2) * t ^ 2 : ℕ) : ℤ) with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hns : ¬IsSquare d := by
    rintro ⟨r, hr⟩
    -- pass to ℕ
    have hnat : e ^ 3 * (e + 2) * t ^ 2 = r.natAbs * r.natAbs := by
      have : (d : ℤ).natAbs = (r * r).natAbs := by rw [hr]
      rw [hd, Int.natAbs_natCast, Int.natAbs_mul] at this
      exact this
    -- (et)² ∣ s² hence et ∣ s
    have hfac : e ^ 3 * (e + 2) * t ^ 2 = (e * t) ^ 2 * (e * (e + 2)) := by ring
    rw [hfac] at hnat
    have hdvd : (e * t) ^ 2 ∣ r.natAbs ^ 2 := ⟨e * (e + 2), by rw [sq, ← hnat]⟩
    have hdvd' : e * t ∣ r.natAbs := (Nat.pow_dvd_pow_iff (by norm_num)).1 hdvd
    obtain ⟨u, hu⟩ := hdvd'
    have het : 0 < (e * t) ^ 2 := by positivity
    have : e * (e + 2) = u * u := by
      have h' : (e * t) ^ 2 * (e * (e + 2)) = (e * t) ^ 2 * (u * u) := by
        rw [hnat, hu]; ring
      exact Nat.eq_of_mul_eq_mul_left het h'
    exact not_isSquare_mul_add_two he ⟨u, this⟩
  obtain ⟨s, hs1, hs2⟩ := Pell.Solution₁.exists_pos_of_not_isSquare hd0 hns
  -- take n + 1 = t * y
  refine ⟨t * s.y.natAbs - 1, s.x.natAbs, ?_, ?_⟩
  · have hy : 0 < s.y.natAbs := Int.natAbs_pos.2 hs2.ne'
    have hn : t * s.y.natAbs - 1 + 1 = t * s.y.natAbs := by
      have : 1 ≤ t * s.y.natAbs := Nat.mul_pos ht hy
      omega
    rw [hn]
    have hprop := s.prop  -- s.x ^ 2 - d * s.y ^ 2 = 1
    have : ((e ^ 3 * (e + 2) * (t * s.y.natAbs) ^ 2 + 1 : ℕ) : ℤ) = ((s.x.natAbs * s.x.natAbs : ℕ) : ℤ) := by
      push_cast
      rw [← sq, sq_abs, mul_pow, sq_abs]
      have : (s.x : ℤ) ^ 2 = d * s.y ^ 2 + 1 := by linarith
      have hd' : d = (e : ℤ) ^ 3 * ((e : ℤ) + 2) * (t : ℤ) ^ 2 := by rw [hd]; push_cast; ring
      have hmul : d * s.y ^ 2 = (e : ℤ) ^ 3 * ((e : ℤ) + 2) * (t : ℤ) ^ 2 * s.y ^ 2 :=
        congrArg (fun z : ℤ => z * s.y ^ 2) hd'
      rw [this]
      linarith [hmul]
    exact_mod_cast this
  · have hy : 0 < s.y.natAbs := Int.natAbs_pos.2 hs2.ne'
    have h1 : 1 ≤ t * s.y.natAbs := Nat.mul_pos ht hy
    exact ⟨s.y.natAbs, by omega⟩

end JSWW1976
