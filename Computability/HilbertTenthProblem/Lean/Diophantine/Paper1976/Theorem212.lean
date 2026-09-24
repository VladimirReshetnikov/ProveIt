import Diophantine.Paper1976.Cor26
import Diophantine.Paper1976.Lemma211
import Diophantine.Paper1976.Wilson

/-!
# JSWW 1976, Theorem 2.12: the primes are Diophantine

> **Theorem 2.12.** For any number `k ≥ 1`, in order that `k+1` be prime it is necessary
> and sufficient that there exist numbers `a, b, c, d, e, f, g, h, i, j, l, m, n, o, p, q,
> r, s, t, u, v, w, x, y, z` such that (1)–(14) hold.

The fourteen equations are polynomial identities in the integers with unknowns
ranging over the nonnegative integers; those involving subtraction are stated
over `ℤ` (with the natural-number unknowns cast).
-/

namespace JSWW1976

open Pell Diophantine

/-- The system (1)–(14) of Theorem 2.12. -/
def Thm212System (k a b c d e f g h i j l m n o p q r s t u v w x y z : ℕ) : Prop :=
  q = w * z + h + j ∧                                                      -- (1)
  z = (g * k + g + k) * (h + j) + h ∧                                      -- (2)
  (2 * k) ^ 3 * (2 * k + 2) * (n + 1) ^ 2 + 1 = f * f ∧                    -- (3)
  e = p + q + z + 2 * n ∧                                                  -- (4)
  e ^ 3 * (e + 2) * (a + 1) ^ 2 + 1 = o * o ∧                              -- (5)
  (x : ℤ) * x = ((a : ℤ) * a - 1) * y * y + 1 ∧                            -- (6)
  (u : ℤ) * u = 16 * ((a : ℤ) * a - 1) * r * r * (y : ℤ) ^ 4 + 1 ∧          -- (7)
  ((x : ℤ) + c * u) * ((x : ℤ) + c * u) =                                  -- (8)
    (((a : ℤ) + u * u * ((u : ℤ) * u - a)) * ((a : ℤ) + u * u * ((u : ℤ) * u - a)) - 1)
      * ((n : ℤ) + 4 * d * y) * ((n : ℤ) + 4 * d * y) + 1 ∧
  (m : ℤ) * m = ((a : ℤ) * a - 1) * l * l + 1 ∧                            -- (9)
  (l : ℤ) = k + i * ((a : ℤ) - 1) ∧                                        -- (10)
  n + l + v = y ∧                                                          -- (11)
  (m : ℤ) = p + l * ((a : ℤ) - n - 1)                                      -- (12)
    + b * (2 * a * ((n : ℤ) + 1) - ((n : ℤ) + 1) * ((n : ℤ) + 1) - 1) ∧
  (x : ℤ) = q + y * ((a : ℤ) - p - 1)                                      -- (13)
    + s * (2 * a * ((p : ℤ) + 1) - ((p : ℤ) + 1) * ((p : ℤ) + 1) - 1) ∧
  (p : ℤ) * m = z + p * l * ((a : ℤ) - p) + t * (2 * a * (p : ℤ) - (p : ℤ) * p - 1)  -- (14)

/-- `n + ψ_a(n-1) ≤ ψ_a(n)` for `n ≥ 1` (used for equation (11)). -/
theorem add_yn_pred_le {a : ℕ} (a1 : 1 < a) {n : ℕ} (hn : 1 ≤ n) :
    n + yn a1 (n - 1) ≤ yn a1 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [yn_succ]
  have h1 : m ≤ yn a1 m := yn_ge_n a1 m
  have h2 : 1 ≤ xn a1 m := x_pos a1 m
  have h3 : yn a1 m * 2 ≤ yn a1 m * a := Nat.mul_le_mul_left _ a1
  omega

/-- Size bounds available before `p = (n+1)^k` is known: from `e - 1 + e^(e-2) ≤ a`
with `e = p+q+z+2n`, `n ≥ 2`, `k < n`. -/
theorem size_bounds_A {k n p q z e a : ℕ} (hk : 1 ≤ k) (hn : 2 ≤ n) (hkn : k < n)
    (he : e = p + q + z + 2 * n) (ha : e - 1 + e ^ (e - 2) ≤ a) :
    p < a ∧ q < a ∧ z < a ∧ (n + 1) ^ k < a ∧ (n + 1) * (n + 1) + 1 < a := by
  have he4 : 2 * n ≤ e := by omega
  have hB : (2 * n) ^ (2 * n - 2) ≤ e ^ (e - 2) :=
    le_trans (Nat.pow_le_pow_left he4 _) (Nat.pow_le_pow_right (by omega) (by omega))
  have hpos : 1 ≤ e ^ (e - 2) := Nat.one_le_pow _ _ (by omega)
  have hea : e ≤ a := by
    have := Nat.sub_add_cancel (show 1 ≤ e by omega)
    omega
  have hA : (n + 1) ^ k < (2 * n) ^ (2 * n - 2) :=
    lt_of_lt_of_le (Nat.pow_lt_pow_left (by omega) (by omega : k ≠ 0))
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hsq : (2 * n) * (2 * n) ≤ (2 * n) ^ (2 * n - 2) := by
    calc (2 * n) * (2 * n) = (2 * n) ^ 2 := by ring
      _ ≤ (2 * n) ^ (2 * n - 2) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · have : (n + 1) ^ k ≤ (n + 1) ^ n := Nat.pow_le_pow_right (by omega) hkn.le
    omega
  · nlinarith

/-- Size bounds after `p = (n+1)^k` is known. -/
theorem size_bounds_B {k n p q z e a : ℕ} (hk : 1 ≤ k) (hn : 2 ≤ n) (hkn : k < n) (hp : p = (n + 1) ^ k)
    (he : e = p + q + z + 2 * n) (ha : e - 1 + e ^ (e - 2) ≤ a) :
    (p + 1) ^ n < a ∧ p ^ (k + 1) < a ∧ (p + 1) * (p + 1) + 1 < a ∧ p * p + 1 < a := by
  have hp1 : n + 1 ≤ p := by rw [hp]; exact Nat.le_self_pow (by omega) _
  have he4 : p + 2 * n ≤ e := by omega
  have hB : (p + 2 * n) ^ (p + 2 * n - 2) ≤ e ^ (e - 2) :=
    le_trans (Nat.pow_le_pow_left he4 _) (Nat.pow_le_pow_right (by omega) (by omega))
  have hpos : 1 ≤ e ^ (e - 2) := Nat.one_le_pow _ _ (by omega)
  have hea : e ≤ a := by
    have := Nat.sub_add_cancel (show 1 ≤ e by omega)
    omega
  have hA : (p + 1) ^ n < (p + 2 * n) ^ (p + 2 * n - 2) :=
    lt_of_lt_of_le (Nat.pow_lt_pow_left (by omega) (by omega))
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hsq : (p + 2 * n) * (p + 2 * n) ≤ (p + 2 * n) ^ (p + 2 * n - 2) := by
    calc (p + 2 * n) * (p + 2 * n) = (p + 2 * n) ^ 2 := by ring
      _ ≤ (p + 2 * n) ^ (p + 2 * n - 2) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨by omega, ?_, ?_, ?_⟩
  · have : p ^ (k + 1) ≤ p ^ n := Nat.pow_le_pow_right (by omega) hkn
    have : p ^ n ≤ (p + 1) ^ n := Nat.pow_le_pow_left (by omega) _
    omega
  · nlinarith
  · nlinarith

/-- An integer of absolute value below a positive divisor is zero. -/
theorem eq_of_dvd_of_lt {M D : ℤ} (hM : 0 < M) (hdvd : M ∣ D) (h1 : -M < D) (h2 : D < M) :
    D = 0 := by
  obtain ⟨c, rfl⟩ := hdvd
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have : M * c ≤ -M := by nlinarith
    linarith
  · simp [hc]
  · have : M ≤ M * c := by nlinarith
    linarith

set_option maxHeartbeats 1000000 in
/-- Theorem 2.12, sufficiency: a solution of (1)–(14) forces `k+1` to be prime. -/
theorem theorem_2_12_of {k a b c d e f g h i j l m n o p q r s t u v w x y z : ℕ} (hk : 1 ≤ k)
    (hs : Thm212System k a b c d e f g h i j l m n o p q r s t u v w x y z) :
    Nat.Prime (k + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hs
  -- (1'), (2'): 2 ≤ n and k < n
  have hn23 := lemma_2_3 (e := 2 * k) (by omega) h3
  have hpow1 : 1 ≤ (2 * k) ^ (2 * k - 2) := Nat.one_le_pow _ _ (by omega)
  have hn2 : 2 ≤ n := by omega
  have hkn : k < n := by omega
  -- (3'), (4')
  have he2 : 2 ≤ e := by omega
  have ha3 := lemma_2_3 (e := e) he2 h5
  have hepos : 1 ≤ e ^ (e - 2) := Nat.one_le_pow _ _ (by omega)
  have hna : n < a := by omega
  have a1 : 1 < a := by omega
  obtain ⟨hpa, hqa, hza, hnka, hn2a⟩ := size_bounds_A hk hn2 hkn h4 ha3
  -- Corollary 2.6: y = ψ_a(n)
  have hy : y = yn a1 n := corollary_2_6_eq_of a1 (by omega) ⟨h6, h7, h8, by omega⟩
  have ha1 : 1 ≤ a * a := Nat.one_le_iff_ne_zero.2 (by positivity)
  -- (9), (10), (11): m = χ_a(k), l = ψ_a(k)
  have h9' : m * m - (a * a - 1) * l * l = 1 := by
    have : ((m * m : ℕ) : ℤ) = (((a * a - 1) * l * l + 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub ha1]; linarith
    have := (Nat.cast_injective (R := ℤ)) this
    omega
  obtain ⟨k', hm', hl'⟩ := eq_pell a1 h9'
  have hlt : l < y := by omega
  have hk'n : k' < n := by
    by_contra hge
    push_neg at hge
    have := (strictMono_y a1).monotone hge
    omega
  have hl10 : l = k + i * (a - 1) := by
    have : ((l : ℕ) : ℤ) = ((k + i * (a - 1) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub a1.le]; linarith
    exact_mod_cast this
  have hkk' : k' = k := by
    have hmod1 : yn a1 k' ≡ k' [MOD a - 1] := yn_modEq_a_sub_one a1 k'
    have hmod2 : l ≡ k [MOD a - 1] := by
      rw [hl10]
      exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
        (Dvd.intro i (by rw [Nat.add_sub_cancel_left]; exact Nat.mul_comm (a - 1) i))).symm
    have : k' ≡ k [MOD a - 1] := (hl' ▸ hmod1).symm.trans hmod2
    exact Nat.ModEq.eq_of_lt_of_lt this (by omega) (by omega)
  rw [hkk'] at hm' hl'
  -- (5'): p = (n+1)^k, from Lemma 2.4 (Mathlib's `x_sub_y_dvd_pow`) and (12)
  have hn2a' : ((n + 1) * (n + 1) + 1 : ℤ) < a := by exact_mod_cast hn2a
  have han : (0 : ℤ) ≤ (a : ℤ) * n := by positivity
  have hM1 : (0 : ℤ) < 2 * a * ((n : ℤ) + 1) - ((n : ℤ) + 1) * ((n : ℤ) + 1) - 1 := by linarith
  have hM1a : (a : ℤ) ≤ 2 * a * ((n : ℤ) + 1) - ((n : ℤ) + 1) * ((n : ℤ) + 1) - 1 := by linarith
  have hp5 : p = (n + 1) ^ k := by
    have hdvd := x_sub_y_dvd_pow a1 (n + 1) k
    simp only [xz, yz, hm', hl'] at h12 hdvd
    push_cast at hdvd
    -- p - (n+1)^k = (m - (l(a-n-1) + (n+1)^k)) - b M1
    have hD : (2 * a * ((n : ℤ) + 1) - ((n : ℤ) + 1) * ((n : ℤ) + 1) - 1) ∣ (p : ℤ) - (n + 1) ^ k := by
      have e1 : (p : ℤ) - (n + 1) ^ k =
          -((yn a1 k : ℤ) * (a - (n + 1)) + (n + 1) ^ k - xn a1 k)
          - b * (2 * a * ((n : ℤ) + 1) - ((n : ℤ) + 1) * ((n : ℤ) + 1) - 1) := by
        linear_combination -h12
      rw [e1]
      exact dvd_sub (dvd_neg.2 hdvd) (dvd_mul_left _ _)
    have hpa' : (p : ℤ) < a := by exact_mod_cast hpa
    have hnka' : ((n + 1) ^ k : ℤ) < a := by exact_mod_cast hnka
    have := eq_of_dvd_of_lt hM1 hD (by push_cast; linarith [(Nat.cast_nonneg p : (0:ℤ) ≤ p)])
      (by have : (0 : ℤ) ≤ (n + 1) ^ k := by positivity
          linarith)
    have : (p : ℤ) = (n + 1) ^ k := by linarith
    exact_mod_cast this
  obtain ⟨hpna, hpk1a, hp2a, hpp2a⟩ := size_bounds_B hk hn2 hkn hp5 h4 ha3
  have hp1 : n + 1 ≤ p := by rw [hp5]; exact Nat.le_self_pow (by omega) _
  -- (6'): q = (p+1)^n, from Lemma 2.4 with base p+1 and (13)
  have hp2a' : ((p + 1) * (p + 1) + 1 : ℤ) < a := by exact_mod_cast hp2a
  have hap : (0 : ℤ) ≤ (a : ℤ) * p := by positivity
  have hM2 : (0 : ℤ) < 2 * a * ((p : ℤ) + 1) - ((p : ℤ) + 1) * ((p : ℤ) + 1) - 1 := by linarith
  have hM2a : (a : ℤ) ≤ 2 * a * ((p : ℤ) + 1) - ((p : ℤ) + 1) * ((p : ℤ) + 1) - 1 := by linarith
  have hq6 : q = (p + 1) ^ n := by
    have hdvd := x_sub_y_dvd_pow a1 (p + 1) n
    have hx : x = xn a1 n := by
      have hpell := χ_sq a1 n
      simp only [χ, ψ] at hpell
      have hxx : x * x = xn a1 n * xn a1 n := by
        rw [hpell, ← hy]
        have : ((x * x : ℕ) : ℤ) = (((a * a - 1) * y * y + 1 : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub ha1]; linarith
        exact_mod_cast this
      exact Nat.mul_self_inj.1 hxx
    simp only [xz, yz] at hdvd
    push_cast at hdvd
    rw [hx, hy] at h13
    have hD : (2 * a * ((p : ℤ) + 1) - ((p : ℤ) + 1) * ((p : ℤ) + 1) - 1) ∣ (q : ℤ) - (p + 1) ^ n := by
      have e1 : (q : ℤ) - (p + 1) ^ n =
          -((yn a1 n : ℤ) * (a - (p + 1)) + (p + 1) ^ n - xn a1 n)
          - s * (2 * a * ((p : ℤ) + 1) - ((p : ℤ) + 1) * ((p : ℤ) + 1) - 1) := by
        linear_combination -h13
      rw [e1]
      exact dvd_sub (dvd_neg.2 hdvd) (dvd_mul_left _ _)
    have hqa' : (q : ℤ) < a := by exact_mod_cast hqa
    have hpna' : ((p + 1) ^ n : ℤ) < a := by exact_mod_cast hpna
    have := eq_of_dvd_of_lt hM2 hD (by push_cast; linarith [(Nat.cast_nonneg q : (0:ℤ) ≤ q)])
      (by have : (0 : ℤ) ≤ (p + 1) ^ n := by positivity
          linarith)
    have : (q : ℤ) = (p + 1) ^ n := by linarith
    exact_mod_cast this
  -- (7'): z = p^(k+1), from Lemma 2.4 with base p, multiplied by p, and (14)
  have hpp2a' : (p * p + 1 : ℤ) < a := by exact_mod_cast hpp2a
  have ha3p : (a : ℤ) * 3 ≤ (a : ℤ) * p :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : 3 ≤ p)) (by positivity)
  have hM3 : (0 : ℤ) < 2 * a * (p : ℤ) - (p : ℤ) * p - 1 := by linarith
  have hM3a : (a : ℤ) ≤ 2 * a * (p : ℤ) - (p : ℤ) * p - 1 := by linarith
  have hz7 : z = p ^ (k + 1) := by
    have hdvd := x_sub_y_dvd_pow a1 p k
    simp only [xz, yz, hm', hl'] at h14 hdvd
    push_cast at hdvd
    have hD : (2 * a * (p : ℤ) - (p : ℤ) * p - 1) ∣ (z : ℤ) - p ^ (k + 1) := by
      have e1 : (z : ℤ) - p ^ (k + 1) =
          -(p : ℤ) * ((yn a1 k : ℤ) * (a - p) + p ^ k - xn a1 k)
          - t * (2 * a * (p : ℤ) - (p : ℤ) * p - 1) := by
        linear_combination -h14
      rw [e1]
      exact dvd_sub (Dvd.dvd.mul_left hdvd _) (dvd_mul_left _ _)
    have hza' : (z : ℤ) < a := by exact_mod_cast hza
    have hpk1a' : (p ^ (k + 1) : ℤ) < a := by exact_mod_cast hpk1a
    have := eq_of_dvd_of_lt hM3 hD (by push_cast; linarith [(Nat.cast_nonneg z : (0:ℤ) ≤ z)])
      (by have : (0 : ℤ) ≤ (p : ℤ) ^ (k + 1) := by positivity
          linarith)
    have : (z : ℤ) = p ^ (k + 1) := by linarith
    exact_mod_cast this
  -- Lemma 2.11 gives gk+g+k = k!, then Wilson
  have hfac : g * k + g + k = k.factorial :=
    lemma_2_11_of hk (by omega) ⟨h1, h2, h3, hp5, hq6, hz7⟩
  rw [lemma_2_9 hk]
  exact ⟨g + 1, by rw [← hfac]; ring⟩

set_option maxHeartbeats 1000000 in
/-- Theorem 2.12, necessity: if `k+1` is prime, (1)–(14) have a solution. -/
theorem theorem_2_12_exists {k : ℕ} (hk : 1 ≤ k) (hprime : Nat.Prime (k + 1)) :
    ∃ a b c d e f g h i j l m n o p q r s t u v w x y z,
      Thm212System k a b c d e f g h i j l m n o p q r s t u v w x y z := by
  -- g with k! = gk + g + k
  obtain ⟨g', hg'⟩ := (lemma_2_9 hk).1 hprime
  have hg'pos : 1 ≤ g' := by
    rcases Nat.eq_zero_or_pos g' with rfl | h
    · simp at hg'
    · exact h
  obtain ⟨g, rfl⟩ : ∃ g, g' = g + 1 := ⟨g' - 1, by omega⟩
  have hfac : g * k + g + k = k.factorial := by nlinarith
  -- Lemma 2.11 witnesses
  obtain ⟨j, h, n, p, q, w, z, f, h1, h2, h3, h4p, h5q, h6z⟩ := lemma_2_11_exists hk
  have hn23 := lemma_2_3 (e := 2 * k) (by omega) h3
  have hpow1 : 1 ≤ (2 * k) ^ (2 * k - 2) := Nat.one_le_pow _ _ (by omega)
  have hn2 : 2 ≤ n := by omega
  have hkn : k < n := by omega
  -- e and a
  set e := p + q + z + 2 * n with he
  obtain ⟨a, o, h5, -⟩ := lemma_2_3_converse (e := e) (t := 1) (by omega) le_rfl
  have ha3 := lemma_2_3 (e := e) (by omega) h5
  have hepos : 1 ≤ e ^ (e - 2) := Nat.one_le_pow _ _ (by omega)
  have a1 : 1 < a := by omega
  obtain ⟨hpa, hqa, hza, hnka, hn2a⟩ := size_bounds_A hk hn2 hkn he ha3
  obtain ⟨hpna, hpk1a, hp2a, hpp2a⟩ := size_bounds_B hk hn2 hkn h4p he ha3
  have hp1 : n + 1 ≤ p := by rw [h4p]; exact Nat.le_self_pow (by omega) _
  -- y = ψ_a(n) and Corollary 2.6 witnesses
  obtain ⟨c, d, r, u, x, h6, h7, h8, hny⟩ := corollary_2_6_of_eq a1 (by omega : 1 ≤ n)
  set y := yn a1 n with hy
  set m := xn a1 k with hm
  set l := yn a1 k with hl
  have ha1 : 1 ≤ a * a := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hcast : ((a * a - 1 : ℕ) : ℤ) = (a : ℤ) * a - 1 := by push_cast [Nat.cast_sub ha1]; ring
  -- (9)
  have h9 : (m : ℤ) * m = ((a : ℤ) * a - 1) * l * l + 1 := by
    have := χ_sq a1 k
    simp only [χ, ψ] at this
    have := congrArg (fun v : ℕ => (v : ℤ)) this
    push_cast [hcast] at this
    linarith
  -- (10): l ≡ k (mod a-1), l ≥ k
  obtain ⟨i, hi⟩ : a - 1 ∣ l - k :=
    (Nat.modEq_iff_dvd' (yn_ge_n a1 k)).1 (yn_modEq_a_sub_one a1 k).symm
  have h10 : (l : ℤ) = k + i * ((a : ℤ) - 1) := by
    have hlk : k ≤ l := yn_ge_n a1 k
    have : l = k + (a - 1) * i := by omega
    rw [this]; push_cast [Nat.cast_sub a1.le]; ring
  -- (11): n + l ≤ y
  have h11' : n + l ≤ y := by
    have := add_yn_pred_le a1 (show 1 ≤ n by omega)
    have : yn a1 k ≤ yn a1 (n - 1) := (strictMono_y a1).monotone (by omega)
    omega
  -- (12): b from Lemma 2.4 (base n+1, exponent k)
  have hcong12 := χ_modEq_pow a1 (p := n + 1) (by omega) (by omega) k
  have hineq12 := pow_add_ψ_le_χ a1 (p := n + 1) (n := k) (by omega) hnka
  simp only [χ, ψ] at hcong12 hineq12
  obtain ⟨b, hb⟩ := (Nat.modEq_iff_dvd' hineq12).1 hcong12.symm
  have hM1n : (n + 1) * (n + 1) + 1 ≤ 2 * a * (n + 1) := by
    have : a ≤ 2 * a * (n + 1) := by
      calc a = a * 1 := (mul_one a).symm
        _ ≤ a * (2 * (n + 1)) := Nat.mul_le_mul_left a (by omega)
        _ = 2 * a * (n + 1) := by ring
    omega
  have h12 : (m : ℤ) = p + l * ((a : ℤ) - n - 1)
      + b * (2 * a * ((n : ℤ) + 1) - ((n : ℤ) + 1) * ((n : ℤ) + 1) - 1) := by
    have : xn a1 k = (n + 1) ^ k + yn a1 k * (a - (n + 1)) + (2 * a * (n + 1) - (n + 1) * (n + 1) - 1) * b := by
      omega
    have := congrArg (fun v : ℕ => (v : ℤ)) this
    push_cast [Nat.cast_sub (show n + 1 ≤ a by omega),
      Nat.cast_sub (show (n + 1) * (n + 1) ≤ 2 * a * (n + 1) by omega),
      Nat.cast_sub (show 1 ≤ 2 * a * (n + 1) - (n + 1) * (n + 1) by omega)] at this
    rw [hm, hl, h4p]; push_cast
    linear_combination this
  -- (13): s from Lemma 2.4 (base p+1, exponent n)
  have hcong13 := χ_modEq_pow a1 (p := p + 1) (by omega) (by omega) n
  have hineq13 := pow_add_ψ_le_χ a1 (p := p + 1) (n := n) (by omega) hpna
  simp only [χ, ψ] at hcong13 hineq13
  obtain ⟨s, hs⟩ := (Nat.modEq_iff_dvd' hineq13).1 hcong13.symm
  have hM2n : (p + 1) * (p + 1) + 1 ≤ 2 * a * (p + 1) := by
    have : a ≤ 2 * a * (p + 1) := by
      calc a = a * 1 := (mul_one a).symm
        _ ≤ a * (2 * (p + 1)) := Nat.mul_le_mul_left a (by omega)
        _ = 2 * a * (p + 1) := by ring
    omega
  have hx : x = xn a1 n := by
    have hpell := χ_sq a1 n
    simp only [χ, ψ] at hpell
    have hxx : x * x = xn a1 n * xn a1 n := by
      rw [hpell]
      have : ((x * x : ℕ) : ℤ) = (((a * a - 1) * yn a1 n * yn a1 n + 1 : ℕ) : ℤ) := by
        push_cast [hcast]; linarith
      exact_mod_cast this
    exact Nat.mul_self_inj.1 hxx
  have h13 : (x : ℤ) = q + y * ((a : ℤ) - p - 1)
      + s * (2 * a * ((p : ℤ) + 1) - ((p : ℤ) + 1) * ((p : ℤ) + 1) - 1) := by
    have : xn a1 n = (p + 1) ^ n + yn a1 n * (a - (p + 1)) + (2 * a * (p + 1) - (p + 1) * (p + 1) - 1) * s := by
      omega
    have := congrArg (fun v : ℕ => (v : ℤ)) this
    push_cast [Nat.cast_sub (show p + 1 ≤ a by omega),
      Nat.cast_sub (show (p + 1) * (p + 1) ≤ 2 * a * (p + 1) by omega),
      Nat.cast_sub (show 1 ≤ 2 * a * (p + 1) - (p + 1) * (p + 1) by omega)] at this
    rw [hx, hy, h5q]; push_cast
    linear_combination this
  -- (14): t from Lemma 2.4 (base p, exponent k), multiplied by p
  have hpka : p ^ k < a := lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (Nat.le_succ k)) hpk1a
  have hcong14 := χ_modEq_pow a1 (p := p) (by omega) (by omega) k
  have hineq14 := pow_add_ψ_le_χ a1 (p := p) (n := k) (by omega) hpka
  simp only [χ, ψ] at hcong14 hineq14
  obtain ⟨t0, ht0⟩ := (Nat.modEq_iff_dvd' hineq14).1 hcong14.symm
  have hM3n : p * p + 1 ≤ 2 * a * p := by
    have : a ≤ 2 * a * p := by
      calc a = a * 1 := (mul_one a).symm
        _ ≤ a * (2 * p) := Nat.mul_le_mul_left a (by omega)
        _ = 2 * a * p := by ring
    omega
  have h14 : (p : ℤ) * m = z + p * l * ((a : ℤ) - p) + (p * t0) * (2 * a * (p : ℤ) - (p : ℤ) * p - 1) := by
    have : xn a1 k = p ^ k + yn a1 k * (a - p) + (2 * a * p - p * p - 1) * t0 := by omega
    have hmain := congrArg (fun v : ℕ => (v : ℤ)) this
    push_cast [Nat.cast_sub (show p ≤ a by omega),
      Nat.cast_sub (show p * p ≤ 2 * a * p by omega),
      Nat.cast_sub (show 1 ≤ 2 * a * p - p * p by omega)] at hmain
    rw [hm, hl, h6z]; push_cast
    linear_combination (p : ℤ) * hmain
  exact ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p, q, r, s, p * t0, u, y - n - l, w, x, y, z,
    h1, by rw [← hfac] at h2; exact h2, h3, rfl, h5, h6, h7, h8, h9, h10, by omega, h12, h13, h14⟩

/-- Theorem 2.12. -/
theorem theorem_2_12 {k : ℕ} (hk : 1 ≤ k) :
    Nat.Prime (k + 1) ↔ ∃ a b c d e f g h i j l m n o p q r s t u v w x y z,
      Thm212System k a b c d e f g h i j l m n o p q r s t u v w x y z := by
  constructor
  · exact theorem_2_12_exists hk
  · rintro ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, hs⟩
    exact theorem_2_12_of hk hs

end JSWW1976
