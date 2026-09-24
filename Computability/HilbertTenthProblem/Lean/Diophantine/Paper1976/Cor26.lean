import Diophantine.Common.Pell
import Mathlib.Tactic.LinearCombination

/-!
# JSWW 1976, Lemma 2.5 / Corollary 2.6: a Diophantine definition of `ψ_a(n)`

> **Corollary 2.6.** For numbers `a, n, y` with `n ≥ 1` and `a ≥ 2`, in order that
> `y = ψ_a(n)` it is necessary and sufficient that there exist numbers `c, d, r, u, x`
> such that
> (I) `x² = (a²-1)y² + 1`, (II) `u² = 16(a²-1)r²y⁴ + 1`,
> (III) `(x+cu)² = ((a+u²(u²-a))²-1)(n+4dy)² + 1`, (IV) `n ≤ y`.

The equations are polynomial identities in the integers with unknowns ranging over
the nonnegative integers, so they are stated over `ℤ` with `ℕ` variables cast.  (With
truncated subtraction in `ℕ` the system would be strictly weaker: for `r = 0` one gets
`u = 1` and `u² - a` would truncate to `0`, admitting e.g. `a = 2, n = 1, y = 4`.)

The proof derives both directions from Mathlib's `Pell.matiyasevic`, Davis's system
with the Matiyasevič–Robinson witnesses, exactly as the article says its system
"most resembles" Davis's Theorem 3.1 with equation V due to Matijasevič.
-/

namespace JSWW1976

open Pell Diophantine

/-- The four conditions of Corollary 2.6, as integer equations in natural unknowns. -/
def Cor26System (a n y c d r u x : ℕ) : Prop :=
  (x : ℤ) * x = ((a : ℤ) * a - 1) * y * y + 1 ∧
  (u : ℤ) * u = 16 * ((a : ℤ) * a - 1) * r * r * (y : ℤ) ^ 4 + 1 ∧
  ((x : ℤ) + c * u) * ((x : ℤ) + c * u) =
    (((a : ℤ) + u * u * ((u : ℤ) * u - a)) * ((a : ℤ) + u * u * ((u : ℤ) * u - a)) - 1)
      * ((n : ℤ) + 4 * d * y) * ((n : ℤ) + 4 * d * y) + 1 ∧
  n ≤ y

/-- Monotonicity of the Pell sequences in the parameter `a`. -/
theorem xn_yn_mono {a b : ℕ} (a1 : 1 < a) (b1 : 1 < b) (hab : a ≤ b) (n : ℕ) :
    xn a1 n ≤ xn b1 n ∧ yn a1 n ≤ yn b1 n := by
  induction n with
  | zero => simp [xn_zero, yn_zero]
  | succ n ih =>
    have hd : a * a - 1 ≤ b * b - 1 := by
      have : a * a ≤ b * b := Nat.mul_le_mul hab hab
      omega
    constructor
    · rw [xn_succ, xn_succ]
      gcongr
      · exact ih.1
      · exact hd
      · exact ih.2
    · rw [yn_succ, yn_succ]
      gcongr
      · exact ih.1
      · exact ih.2

/-- `ψ_a(4m) = 4 χ_a(2m) χ_a(m) ψ_a(m)`. -/
theorem yn_four_mul {a : ℕ} (a1 : 1 < a) (m : ℕ) :
    yn a1 (4 * m) = 4 * xn a1 (2 * m) * xn a1 m * yn a1 m := by
  have h2 : yn a1 (2 * m) = 2 * xn a1 m * yn a1 m := by
    rw [two_mul, yn_add]; ring
  have h4 : yn a1 (4 * m) = 2 * xn a1 (2 * m) * yn a1 (2 * m) := by
    rw [show 4 * m = 2 * m + 2 * m by ring, yn_add]; ring
  rw [h4, h2]; ring

/-- `b - 1 = (u²-1)(u²-a+1)` for `b = a + u²(u²-a)`, when `1 ≤ a ≤ u²`. -/
theorem b_sub_one {a u : ℕ} (ha : 1 ≤ a) (hua : a ≤ u * u) :
    a + u * u * (u * u - a) - 1 = (u * u - 1) * (u * u - a + 1) := by
  have hu1 : 1 ≤ u * u := le_trans ha hua
  have h1 : 1 ≤ a + u * u * (u * u - a) := le_trans ha (Nat.le_add_right _ _)
  zify [h1, hua, hu1]
  ring

/-- Corollary 2.6, necessity: `y = ψ_a(n)` gives witnesses. -/
theorem corollary_2_6_of_eq {a n : ℕ} (a1 : 1 < a) (hn : 1 ≤ n) :
    ∃ c d r u x, Cor26System a n (yn a1 n) c d r u x := by
  set y := yn a1 n with hy
  have hy0 : 0 < y := by
    have := strictMono_y a1 (show 0 < n by omega)
    rw [yn_zero] at this
    exact this
  have ha1 : 1 ≤ a * a := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hcast : ((a * a - 1 : ℕ) : ℤ) = (a : ℤ) * a - 1 := by push_cast [Nat.cast_sub ha1]; ring
  -- v = ψ(4m) = 4 r y², u = χ(4m) with m = n y
  set m := n * y with hm
  obtain ⟨q, hq⟩ : y * y ∣ yn a1 m := ysq_dvd_yy a1 n
  set r := xn a1 (2 * m) * xn a1 m * q with hr
  set u := xn a1 (4 * m) with hu
  have hv : yn a1 (4 * m) = 4 * r * y * y := by
    rw [yn_four_mul, hq, hr]; ring
  have hu2 : u * u = 16 * (a * a - 1) * r * r * y ^ 4 + 1 := by
    have := χ_sq a1 (4 * m)
    simp only [χ, ψ] at this
    rw [hv] at this
    rw [hu, this]; ring
  have hu2z : (u : ℤ) * u = 16 * ((a : ℤ) * a - 1) * r * r * (y : ℤ) ^ 4 + 1 := by
    have := congrArg (fun k : ℕ => (k : ℤ)) hu2
    push_cast [hcast] at this
    linarith
  -- b = a + u²(u² - a), with u² ≥ a
  have hua : a ≤ u * u := by
    have h1 : a ≤ u := by
      calc a = xn a1 1 := (xn_one a1).symm
        _ ≤ xn a1 (4 * m) := (strictMono_x a1).monotone (by
            have : 1 ≤ m := Nat.mul_pos hn hy0
            omega)
    exact le_trans h1 (Nat.le_mul_self u)
  set b := a + u * u * (u * u - a) with hb
  have hab : a ≤ b := Nat.le_add_right _ _
  have b1 : 1 < b := lt_of_lt_of_le a1 hab
  have hbu : u ∣ b - a := ⟨u * (u * u - a), by rw [hb, Nat.add_sub_cancel_left]; ring⟩
  have h4y : 4 * y ∣ u * u - 1 :=
    ⟨4 * (a * a - 1) * r * r * y ^ 3, by rw [hu2, Nat.add_sub_cancel]; ring⟩
  have hb1 : 4 * y ∣ b - 1 := by
    rw [hb, b_sub_one a1.le hua]
    exact Dvd.dvd.mul_right h4y _
  -- s = χ_b(n), t = ψ_b(n)
  set s := xn b1 n with hs
  set t := yn b1 n with ht
  have hsx : xn a1 n ≤ s := (xn_yn_mono a1 b1 hab n).1
  have hsmod : xn a1 n ≡ s [MOD u] :=
    (xy_modEq_of_modEq a1 b1 ((Nat.modEq_iff_dvd' hab).2 hbu) n).1
  obtain ⟨c, hc⟩ : u ∣ s - xn a1 n := (Nat.modEq_iff_dvd' hsx).1 hsmod
  have htn : n ≤ t := yn_ge_n b1 n
  have htmod : t ≡ n [MOD 4 * y] := Nat.ModEq.of_dvd hb1 (yn_modEq_a_sub_one b1 n)
  obtain ⟨d, hd⟩ : 4 * y ∣ t - n := (Nat.modEq_iff_dvd' htn).1 htmod.symm
  refine ⟨c, d, r, u, xn a1 n, ?_, hu2z, ?_, yn_ge_n a1 n⟩
  · have := χ_sq a1 n
    simp only [χ, ψ] at this
    have := congrArg (fun k : ℕ => (k : ℤ)) this
    push_cast [hcast] at this
    linarith
  · have hs' : xn a1 n + c * u = s := by
      have : s = xn a1 n + u * c := by omega
      rw [this]; ring
    have ht' : n + 4 * d * y = t := by
      have : t = n + 4 * y * d := by omega
      rw [this]; ring
    have hbb : 1 ≤ b * b := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hpell := χ_sq b1 n
    simp only [χ, ψ] at hpell
    have hz := congrArg (fun k : ℕ => (k : ℤ)) hpell
    push_cast [Nat.cast_sub hbb] at hz
    have hbz : (b : ℤ) = (a : ℤ) + u * u * ((u : ℤ) * u - a) := by
      rw [hb]; push_cast [Nat.cast_sub hua]; ring
    have hsz : ((xn a1 n : ℕ) : ℤ) + c * u = (s : ℤ) := by exact_mod_cast hs'
    have htz : (n : ℤ) + 4 * d * y = (t : ℤ) := by exact_mod_cast ht'
    rw [hsz, htz, ← hbz]
    linarith

/-- Corollary 2.6, sufficiency: the witnesses force `y = ψ_a(n)`. -/
theorem corollary_2_6_eq_of {a n y c d r u x : ℕ} (a1 : 1 < a) (hn : 1 ≤ n)
    (h : Cor26System a n y c d r u x) : y = yn a1 n := by
  obtain ⟨hI, hII, hIII, hIV⟩ := h
  have hy0 : 0 < y := by omega
  have ha1 : 1 ≤ a * a := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hcast : ((a * a - 1 : ℕ) : ℤ) = (a : ℤ) * a - 1 := by push_cast [Nat.cast_sub ha1]; ring
  -- ℕ forms of (I) and (II)
  have hI' : x * x = (a * a - 1) * y * y + 1 := by
    have : ((x * x : ℕ) : ℤ) = (((a * a - 1) * y * y + 1 : ℕ) : ℤ) := by
      push_cast [hcast]; linarith
    exact_mod_cast this
  have hII' : u * u = 16 * (a * a - 1) * r * r * y ^ 4 + 1 := by
    have : ((u * u : ℕ) : ℤ) = ((16 * (a * a - 1) * r * r * y ^ 4 + 1 : ℕ) : ℤ) := by
      push_cast [hcast]; linarith
    exact_mod_cast this
  -- r ≠ 0: otherwise u = 1, the bracket in (III) vanishes and (x+c)² = 1, contradicting (I)
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exfalso
      have hu1 : u = 1 := by
        have : u * u = 1 := by rw [hII']; ring
        exact Nat.eq_one_of_mul_eq_one_right this
      subst hu1
      have h3 : ((x : ℤ) + c) * ((x : ℤ) + c) = 1 := by
        push_cast at hIII
        linear_combination hIII
      have hx1 : (x : ℤ) + c = 1 := by
        rcases mul_self_eq_one_iff.1 h3 with h | h
        · exact h
        · have : (0 : ℤ) ≤ (x : ℤ) + c := by positivity
          linarith
      have hx : (x : ℤ) ≤ 1 := by linarith [(Nat.cast_nonneg c : (0 : ℤ) ≤ c)]
      have hI2 : (x : ℤ) * x = ((a : ℤ) * a - 1) * ((y : ℤ) * y) + 1 := by linear_combination hI
      have hA : (3 : ℤ) ≤ (a : ℤ) * a - 1 := by
        have : (2 : ℤ) ≤ a := by exact_mod_cast a1
        nlinarith
      have hY : (1 : ℤ) ≤ (y : ℤ) * y := by
        have : (1 : ℤ) ≤ y := by exact_mod_cast hy0
        nlinarith
      have hprod : (3 : ℤ) * 1 ≤ ((a : ℤ) * a - 1) * ((y : ℤ) * y) :=
        mul_le_mul hA hY (by norm_num) (by linarith)
      have hxx : (x : ℤ) * x ≤ 1 := by
        have : (0 : ℤ) ≤ x := by positivity
        nlinarith
      linarith
    · exact hr
  have hua : a ≤ u * u := by
    have h1 : 1 ≤ r * r * y ^ 4 := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2a : 2 * a ≤ a * a := Nat.mul_le_mul_right a a1
    have h2 : 16 * (a * a - 1) ≤ 16 * (a * a - 1) * r * r * y ^ 4 := by
      calc 16 * (a * a - 1) = 16 * (a * a - 1) * 1 := by ring
        _ ≤ 16 * (a * a - 1) * (r * r * y ^ 4) := Nat.mul_le_mul_left _ h1
        _ = 16 * (a * a - 1) * r * r * y ^ 4 := by ring
    omega
  -- ℕ form of (III)
  have hIII' : (x + c * u) * (x + c * u) =
      ((a + u * u * (u * u - a)) * (a + u * u * (u * u - a)) - 1) * (n + 4 * d * y) * (n + 4 * d * y)
        + 1 := by
    set b := a + u * u * (u * u - a) with hb
    have hbb : 1 ≤ b * b := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hbz : (b : ℤ) = (a : ℤ) + u * u * ((u : ℤ) * u - a) := by
      rw [hb]; push_cast [Nat.cast_sub hua]; ring
    have : (((x + c * u) * (x + c * u) : ℕ) : ℤ) =
        (((b * b - 1) * (n + 4 * d * y) * (n + 4 * d * y) + 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hbb]
      rw [hbz]; linarith
    exact_mod_cast this
  -- assemble Mathlib's witnesses
  set b := a + u * u * (u * u - a) with hb
  have hab : a ≤ b := Nat.le_add_right _ _
  have b1 : 1 < b := lt_of_lt_of_le a1 hab
  have h4y : 4 * y ∣ u * u - 1 :=
    ⟨4 * (a * a - 1) * r * r * y ^ 3, by rw [hII', Nat.add_sub_cancel]; ring⟩
  have hb1 : b ≡ 1 [MOD 4 * y] := by
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' b1.le, hb, b_sub_one a1.le hua]
    exact Dvd.dvd.mul_right h4y _
  have hba : b ≡ a [MOD u] := by
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hab]
    exact ⟨u * (u * u - a), by rw [hb, Nat.add_sub_cancel_left]; ring⟩
  have key := (Pell.matiyasevic (a := a) (k := n) (x := x) (y := y)).2 ⟨a1, hIV, Or.inr
    ⟨u, 4 * r * y * y, x + c * u, n + 4 * d * y, b,
      by rw [hI']; omega,
      by rw [hII']; ring_nf; omega,
      by rw [hIII']; omega,
      b1, hb1, hba,
      by positivity,
      ⟨4 * r, by ring⟩,
      by
        rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (Nat.le_add_right _ _)]
        exact ⟨c, by rw [Nat.add_sub_cancel_left]; ring⟩,
      by
        rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (Nat.le_add_right _ _)]
        exact ⟨d, by rw [Nat.add_sub_cancel_left]; ring⟩⟩⟩
  obtain ⟨_, _, hy⟩ := key
  exact hy.symm

/-- Corollary 2.6 (both directions). -/
theorem corollary_2_6 {a n y : ℕ} (a1 : 1 < a) (hn : 1 ≤ n) :
    y = yn a1 n ↔ ∃ c d r u x, Cor26System a n y c d r u x := by
  constructor
  · rintro rfl; exact corollary_2_6_of_eq a1 hn
  · rintro ⟨c, d, r, u, x, h⟩; exact corollary_2_6_eq_of a1 hn h

end JSWW1976
