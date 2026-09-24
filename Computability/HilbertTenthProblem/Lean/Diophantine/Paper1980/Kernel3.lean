import Diophantine.Paper1980.PellRelaxedMain
import Diophantine.Paper1980.PellHalf90
import Diophantine.Paper1980.PellExponent3
import Diophantine.Paper1980.PellRatio3

/-!
# The base-three Pell kernel (ten equations, sixteen positive unknowns)

`Papers/1980/EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`, §§2–4 (and
`EXPLORATION_BASE_THREE_PELL_KERNEL.md`).  For a general positive scale `D₀` and a
central number `r`, with `U = w D₀`, `Y = s D₀`, `E = UY`, `Q = UY²`, `P = 2Q + 1`,
`a = Y(U+1)`, `A = a + 3`, `M = 6a + 8`, `D = A² − 1 = a² + M`, `J = 2r + 1`,
`R = i c²`, `K = R²`, `u = J + jc`, the ten equations (plus-sign variant) are

    τ(τ+1) = (E² + U)(Yk)²,  c = Yk + η,  k = η + ζ,  k = r + 1 + hE,  a = Y(U+1),
    d = U + ac + γM,  d² = 1 + Dc²,  R² = D(f² − 1),  K(u² − y²) = 1 − y²,  u = c + of.

* **Soundness** (`kernel3_sound`): under `D₀ ≥ 81`, `r ≥ 27`, `r < 2D₀` and positivity
  of the sixteen unknowns, `c = ψ_A(J)`, `d = χ_A(J)`, `k = ψ_P(r+1)`, `U^r ≤ Y`,
  `U^(r+1) < a`, `U = 3^J`, `D₀` is a power of three and `D₀ ∣ C(2r, r)`.
  The argument is that of the 90-operation Pell block (`Pell90.lean`) with the
  base shifted to `a + 3`: the two norms classify `(d, c)` and `(2τ+1, k)` as Pell
  pairs, the index congruence and growth force the main index `≥ r + 2`, the relaxed
  auxiliary norm and the half-parameter block fix the main index to `J`, the ratio
  block gives `k = ψ_P(r+1)` and `Y ≥ U^r`, the exponent congruence gives `U = 3^J`,
  and the exact binomial tail gives `Y ≡ C(2r,r) (mod U)`.
* **Positive converse** (`kernel3_witnesses`): if `D₀ = 3^N`, `D₀ < r²`, `r ≥ 2` is
  even and `D₀ ∣ C(2r, r)`, all sixteen unknowns exist (the plus-sign variant needs
  `J ≡ 1 (mod 4)`, i.e. `r` even, for the half-parameter witnesses).

No parity of `r` is used in the soundness direction.
-/

namespace Jones1980

open Diophantine Pell Exp3 Ratio3

/-- The ten kernel equations (plus-sign variant), with `U = w D₀`, `Y = s D₀`. -/
structure Kernel3 (D₀ r a c d f h i j k o s w τ η ζ γ y : ℕ) : Prop where
  /-- `τ(τ + 1) = (E² + U)(Yk)²`. -/
  E9 : τ * (τ + 1) = ((w * D₀ * (s * D₀)) ^ 2 + w * D₀) * (k * (s * D₀)) ^ 2
  /-- `c = kY + η`. -/
  E10a : c = k * (s * D₀) + η
  /-- `k = η + ζ`. -/
  E10b : k = η + ζ
  /-- `k = r + 1 + h U Y`. -/
  E11 : k = r + 1 + h * (w * D₀) * (s * D₀)
  /-- `a = Y(U + 1)`. -/
  E12 : a = s * D₀ * (w * D₀ + 1)
  /-- `d = U + a c + γ(6a + 8)`. -/
  E14 : d = w * D₀ + a * c + γ * (6 * a + 8)
  /-- `d² = 1 + (a² + 6a + 8) c²`. -/
  E15 : d ^ 2 = 1 + (a ^ 2 + 6 * a + 8) * c ^ 2
  /-- `(ic²)² = (a² + 6a + 8)(f² − 1)`. -/
  E16 : (i * c ^ 2) ^ 2 = (a ^ 2 + 6 * a + 8) * (f ^ 2 - 1)
  /-- `K(u² − y²) = 1 − y²` with `K = (a² + 6a + 8)(f² − 1)`, `u = 2r + 1 + jc`. -/
  E17 : (((a : ℤ) ^ 2 + 6 * a + 8) * (f ^ 2 - 1)) * ((2 * r + 1 + j * c) ^ 2 - (y : ℤ) ^ 2) =
    1 - (y : ℤ) ^ 2
  /-- `2r + 1 + jc = c + of`. -/
  E17b : 2 * r + 1 + j * c = c + o * f

/-- Positivity of the sixteen kernel unknowns. -/
structure KernelPos3 (a c d f h i j k o s w τ η ζ γ y : ℕ) : Prop where
  a : 0 < a
  c : 0 < c
  d : 0 < d
  f : 0 < f
  h : 0 < h
  i : 0 < i
  j : 0 < j
  k : 0 < k
  o : 0 < o
  s : 0 < s
  w : 0 < w
  τ : 0 < τ
  η : 0 < η
  ζ : 0 < ζ
  γ : 0 < γ
  y : 0 < y

/-- The conclusions of the kernel, for the fixed proofs `hA : 1 < a + 3` and `hPp : 1 < P`. -/
structure KernelOut3 (D₀ r a c d k s w : ℕ) (hA : 1 < a + 3)
    (hPp : 1 < 2 * (w * D₀ * (s * D₀) ^ 2) + 1) : Prop where
  c_eq : c = ψ hA (2 * r + 1)
  d_eq : d = χ hA (2 * r + 1)
  k_eq : k = ψ hPp (r + 1)
  Y_ge : (w * D₀) ^ r ≤ s * D₀
  a_gt : (w * D₀) ^ (r + 1) < a
  U_eq : w * D₀ = 3 ^ (2 * r + 1)
  central : D₀ ∣ (2 * r).choose r
  D₀_pow : ∃ N, D₀ = 3 ^ N

/-- Soundness of the kernel at the preliminary thresholds `D₀ ≥ 81`, `r ≥ 27`, `r < 2D₀`. -/
theorem kernel3_sound {D₀ r a c d f h i j k o s w τ η ζ γ y : ℕ}
    (hP : KernelPos3 a c d f h i j k o s w τ η ζ γ y)
    (hK : Kernel3 D₀ r a c d f h i j k o s w τ η ζ γ y)
    (hD₀ : 81 ≤ D₀) (hr : 27 ≤ r) (hr2 : r < 2 * D₀)
    (hA : 1 < a + 3) (hPp : 1 < 2 * (w * D₀ * (s * D₀) ^ 2) + 1) :
    KernelOut3 D₀ r a c d k s w hA hPp := by
  obtain ⟨U, hUdef⟩ : ∃ U, U = w * D₀ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = s * D₀ := ⟨_, rfl⟩
  have hPp' : 1 < 2 * (U * Y ^ 2) + 1 := by rw [hUdef, hYdef]; exact hPp
  have E9 : τ * (τ + 1) = (U * Y ^ 2) * (U * Y ^ 2 + 1) * k ^ 2 := by
    rw [hK.E9, hUdef, hYdef]; ring
  have E10a : c = k * Y + η := by rw [hYdef]; exact hK.E10a
  have E10b := hK.E10b
  have E11 : k = r + 1 + h * U * Y := by rw [hUdef, hYdef]; exact hK.E11
  have ha : a = Y * (U + 1) := by rw [hUdef, hYdef]; exact hK.E12
  have E14 : d = U + a * c + γ * (6 * a + 8) := by rw [hUdef]; exact hK.E14
  have E15 := hK.E15
  have E16 := hK.E16
  have E17 := hK.E17
  have E17b := hK.E17b
  -- sizes
  have hU : D₀ ≤ U := by rw [hUdef]; exact Nat.le_mul_of_pos_left _ hP.w
  have hY : D₀ ≤ Y := by rw [hYdef]; exact Nat.le_mul_of_pos_left _ hP.s
  have hY2 : 2 ≤ Y := by omega
  have hU81 : 81 ≤ U := by omega
  have hD₀sq : 4 * D₀ < D₀ * D₀ := by
    calc 4 * D₀ < 81 * D₀ := by omega
      _ ≤ D₀ * D₀ := Nat.mul_le_mul_right _ hD₀
  have hUY : r + 1 < U * Y := by
    calc r + 1 ≤ 4 * D₀ := by omega
      _ < D₀ * D₀ := hD₀sq
      _ ≤ U * Y := Nat.mul_le_mul hU hY
  have haJ : 2 * r + 1 < a := by
    rw [ha]
    calc 2 * r + 1 < 4 * D₀ := by omega
      _ < D₀ * D₀ := hD₀sq
      _ ≤ Y * (U + 1) := Nat.mul_le_mul hY (by omega)
  have hcJ : 2 * r + 1 < c := by
    have : U * Y ≤ h * U * Y := by
      have := hP.h
      calc U * Y = 1 * U * Y := by ring
        _ ≤ h * U * Y := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
    have hkY : k ≤ k * Y := Nat.le_mul_of_pos_right _ (by omega)
    have hkc : k ≤ c := by rw [E10a]; exact le_trans hkY (Nat.le_add_right _ _)
    have hk2 : r + 1 + U * Y ≤ k := by rw [E11]; exact Nat.add_le_add_left this _
    omega
  -- the main Pell pair
  have hDeq : (a + 3) ^ 2 - 1 = a ^ 2 + 6 * a + 8 := sq_sub_one_eq a
  obtain ⟨p', hd, hcp⟩ := eq_pell_of_sq hA (by rw [hDeq]; exact E15)
  have hp'0 : 0 < p' := by
    rcases Nat.eq_zero_or_pos p' with h0 | h0
    · rw [h0, yn_zero] at hcp; omega
    · exact h0
  -- the first Pell pair
  obtain ⟨t', hτ, hk⟩ := eq_pell_of_sq hPp' (x := 2 * τ + 1) (y := k) (by
    have e1 : (2 * (U * Y ^ 2) + 1) ^ 2 - 1 = 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) := by
      have : (2 * (U * Y ^ 2) + 1) ^ 2 = 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) + 1 := by ring
      omega
    rw [e1]
    calc (2 * τ + 1) ^ 2 = 1 + 4 * (τ * (τ + 1)) := by ring
      _ = 1 + 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1) * k ^ 2) := by rw [E9]
      _ = 1 + 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) * k ^ 2 := by ring)
  have ht'0 : 0 < t' := by
    rcases Nat.eq_zero_or_pos t' with h0 | h0
    · rw [h0, yn_zero] at hk; have := hP.k; omega
    · exact h0
  -- the first index is at least `r + 1`
  have ht'ge : r + 1 ≤ t' := by
    have hk1 : k ≡ r + 1 [MOD U * Y] := by
      show k % (U * Y) = (r + 1) % (U * Y)
      rw [E11, show r + 1 + h * U * Y = r + 1 + h * (U * Y) by ring,
        Nat.add_mul_mod_self_right]
    have hk2 : k ≡ t' [MOD U * Y] := by
      have hm := yn_modEq_a_sub_one hPp' t'
      rw [← hk] at hm
      have hdvd : U * Y ∣ 2 * (U * Y ^ 2) + 1 - 1 := by
        rw [Nat.add_sub_cancel]; exact Dvd.intro (2 * Y) (by ring)
      exact Nat.ModEq.of_dvd hdvd hm
    have h12 := hk1.symm.trans hk2
    by_contra hlt; push Not at hlt
    have := Nat.ModEq.eq_of_lt_of_lt h12 hUY (by omega)
    omega
  -- `P > 2A`: `2(a + 3) < 2P − 1`
  have hPA : 2 * (a + 3) < 2 * (2 * (U * Y ^ 2) + 1) - 1 := by
    have h1 : 4 * (Y * (U + 1) + 3) < 2 * (2 * (U * Y ^ 2) + 1) - 1 := two_A_lt (by omega) hY2
    calc 2 * (a + 3) ≤ 4 * (a + 3) := by omega
      _ = 4 * (Y * (U + 1) + 3) := by rw [ha]
      _ < _ := h1
  -- the main index is at least `r + 2`
  have hp'2 : r + 2 ≤ p' := by
    by_contra hlt; push Not at hlt
    have h1 : c ≤ (2 * (a + 3)) ^ (p' - 1) := by
      rw [hcp]
      have := ψ_succ_le_pow hA (p' - 1)
      rwa [Nat.sub_add_cancel hp'0] at this
    have h2 : (2 * (a + 3)) ^ (p' - 1) ≤ (2 * (a + 3)) ^ r :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (2 * (a + 3)) ^ r < (2 * (2 * (U * Y ^ 2) + 1) - 1) ^ r :=
      Nat.pow_lt_pow_left hPA (by omega)
    have h4 : (2 * (2 * (U * Y ^ 2) + 1) - 1) ^ r ≤ yn hPp' (r + 1) := pow_le_ψ_succ hPp' r
    have h5 : yn hPp' (r + 1) ≤ yn hPp' t' := (strictMono_y hPp').monotone ht'ge
    have h6 : k < c := by
      have hkY : k ≤ k * Y := Nat.le_mul_of_pos_right _ (by omega)
      calc k ≤ k * Y := hkY
        _ < k * Y + η := Nat.lt_add_of_pos_right hP.η
        _ = c := E10a.symm
    rw [← hk] at h5
    omega
  -- `c > A (A² − 1)²`
  have hbig : (a + 3) * ((a + 3) ^ 2 - 1) ^ 2 < c := by
    have h1 : (2 * (a + 3) - 1) ^ (p' - 1) ≤ c := by
      rw [hcp]
      have := pow_le_ψ_succ hA (p' - 1)
      rwa [Nat.sub_add_cancel hp'0] at this
    have h2 : (a + 3) ^ 6 ≤ (2 * (a + 3) - 1) ^ (p' - 1) :=
      calc (a + 3) ^ 6 ≤ (2 * (a + 3) - 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
        _ ≤ (2 * (a + 3) - 1) ^ (p' - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (a + 3) * ((a + 3) ^ 2 - 1) ^ 2 < (a + 3) ^ 6 := by
      have hlt : ((a + 3) ^ 2 - 1) ^ 2 < ((a + 3) ^ 2) ^ 2 :=
        Nat.pow_lt_pow_left (by have := Nat.one_le_pow 2 (a + 3) (by omega); omega) two_ne_zero
      calc (a + 3) * ((a + 3) ^ 2 - 1) ^ 2 < (a + 3) * ((a + 3) ^ 2) ^ 2 :=
            Nat.mul_lt_mul_of_pos_left hlt (by omega)
        _ = (a + 3) ^ 5 := by ring
        _ ≤ (a + 3) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  -- the relaxed auxiliary norm
  obtain ⟨m, hfm, -, hcm, hicm⟩ :=
    relaxed_aux hA hp'0 hcp hP.i hP.f (by rw [hDeq]; exact E16) hbig
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, yn_zero, mul_zero] at hicm
      have : 0 < i * c ^ 2 := by have := hP.i; have := hP.c; positivity
      omega
    · exact h0
  have hpm : 2 * p' ≤ m := by
    have h1 : 2 * p' ≤ yn hA p' := two_mul_le_yn hA (by omega)
    have h2 : c ≤ m := Nat.le_of_dvd hm0 hcm
    rw [← hcp] at h1; omega
  -- the half-parameter block: the main index is `J = 2r + 1`
  have hpJ : p' = 2 * r + 1 :=
    half_index hA (by omega) hcJ ⟨r, rfl⟩ hp'0 hd hcp hfm hpm hcm hicm hP.i rfl E17b hP.y
      (by
        push_cast
        rw [show ((a : ℤ) + 3) ^ 2 - 1 = (a : ℤ) ^ 2 + 6 * a + 8 by ring]
        exact E17)
  have hcJ' : c = ψ hA (2 * r + 1) := by rw [hcp, hpJ]
  have hdJ' : d = χ hA (2 * r + 1) := by rw [hd, hpJ]
  -- the ratio block
  have hk_eq : k = ψ hPp' (r + 1) :=
    k_index (h := h) (by omega) hY2 (by omega) rfl hA ha hPp' hcJ' E9 E10a E10b hP.ζ
      (by rw [E11]; ring) hUY
  have hYr : U ^ r ≤ Y :=
    Y_lower (by omega) (by omega) (by omega) rfl hA ha hPp' hcJ' hk_eq E10a E10b hP.ζ
  have hagt : U ^ (r + 1) < a := Ratio90.a_gt (by omega) ha hYr
  -- `U = 3^J`
  have hU3 : U = 3 ^ (2 * r + 1) := by
    apply exp_U hA hP.a hcJ' hdJ' (by omega) ?_ ?_ E14
    · have : U + 1 ≤ Y * (U + 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · have h1 : 3 ^ (2 * r + 1) = 3 * 9 ^ r := by rw [pow_succ, pow_mul]; ring
      have h2 : 9 ^ r ≤ U ^ r := Nat.pow_le_pow_left (by omega) r
      have h3 : 3 * U ^ r < U ^ (r + 1) := by
        rw [pow_succ, mul_comm 3]
        exact Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pow_pos (by omega))
      omega
  -- the central-binomial divisibility
  have hU2' : 2 ^ (2 * r + 1) ≤ U := by
    rw [hU3]; exact Nat.pow_le_pow_left (by norm_num) _
  have hlow := lower_estimate (by omega) (by omega) (by omega) rfl hA ha hPp' hcJ' hk_eq
  have h72 : 72 * r < U + 1 := by
    have := seventy_two_mul_lt_pow r (by omega)
    omega
  have hup := upper_estimate (by omega) (by omega) (by omega) rfl hA ha hPp' hcJ' hk_eq E10a E10b
    hP.ζ h72 hYr (by rw [← ha]; omega)
  obtain ⟨w', hw'⟩ := Ratio90.Y_eq_floor (by omega) hU2' hP.k hP.η E10a E10b hP.ζ hlow hup
  have hcentral : D₀ ∣ (2 * r).choose r :=
    central_dvd (Dvd.intro_left w hUdef.symm) (Dvd.intro_left s hYdef.symm) hw'
  -- `D₀` is a power of three
  have hD₀pow : ∃ N, D₀ = 3 ^ N := by
    have h1 : D₀ ∣ 3 ^ (2 * r + 1) := by rw [← hU3]; exact Dvd.intro_left w hUdef.symm
    obtain ⟨N, -, hN⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    exact ⟨N, hN⟩
  subst hUdef hYdef
  exact ⟨hcJ', hdJ', hk_eq, hYr, hagt, hU3, hcentral, hD₀pow⟩

set_option maxHeartbeats 2000000 in
/-- The positive converse: for `D₀ = 3^N < r²`, `r ≥ 2` even, and `D₀ ∣ C(2r, r)`, the
kernel has positive witnesses. -/
theorem kernel3_witnesses {D₀ r N : ℕ} (hD₀ : D₀ = 3 ^ N) (hr : 2 ≤ r) (hreven : 2 ∣ r)
    (hD₀r : D₀ < r ^ 2) (hcentral : D₀ ∣ (2 * r).choose r) :
    ∃ a c d f h i j k o s w τ η ζ γ y : ℕ,
      KernelPos3 a c d f h i j k o s w τ η ζ γ y ∧ Kernel3 D₀ r a c d f h i j k o s w τ η ζ γ y := by
  -- `J`, `U`
  obtain ⟨J, hJ⟩ : ∃ J, J = 2 * r + 1 := ⟨_, rfl⟩
  have hJ1 : 1 < J := by omega
  have hJ2 : 2 ≤ J := by omega
  have hJ4 : J % 4 = 1 := by obtain ⟨k, hk⟩ := hreven; omega
  obtain ⟨U, hU⟩ : ∃ U, U = 3 ^ J := ⟨_, rfl⟩
  have hU0 : 0 < U := by rw [hU]; positivity
  have hU2r : 2 ^ (2 * r + 1) ≤ U := by rw [hU, hJ]; exact Nat.pow_le_pow_left (by norm_num) _
  have hU81 : 81 ≤ U := by
    rw [hU]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ J := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hUr : r < U := by
    rw [hU]
    calc r < J := by omega
      _ < 3 ^ J := Nat.lt_pow_self (by norm_num)
  -- `D₀ ∣ U`: `3^N < r² < 3^J`
  have hNJ : N ≤ J := by
    have h1 : r ^ 2 < 3 ^ J := by
      have hr3 : r < 3 ^ r := Nat.lt_pow_self (by norm_num)
      have e : 3 ^ J = 3 ^ r * 3 ^ r * 3 := by rw [hJ, pow_succ, two_mul, pow_add]
      rw [e, sq]
      have := Nat.mul_lt_mul'' hr3 hr3
      omega
    have h2 : 3 ^ N < 3 ^ J := by rw [← hD₀]; omega
    exact ((Nat.pow_lt_pow_iff_right (by norm_num)).1 h2).le
  have hD₀U : D₀ ∣ U := by rw [hD₀, hU]; exact Nat.pow_dvd_pow 3 hNJ
  have hD₀0 : 0 < D₀ := by rw [hD₀]; positivity
  -- `Y`
  obtain ⟨Y, v, w', hsplit, hv, hY⟩ := Ratio90.binomial_floor_two (R := r) (U := U) (by omega) hU2r
  -- `U^r ≤ Y`
  have hYU : U ^ r ≤ Y := by
    by_contra hlt
    push Not at hlt
    have h1 : (Y + 1) * U ^ r ≤ U ^ r * U ^ r := Nat.mul_le_mul_right _ hlt
    have h2 : U ^ r * U ^ r ≤ (U + 1) ^ (2 * r) := by
      rw [← pow_add, show r + r = 2 * r by ring]
      exact Nat.pow_le_pow_left (by omega) _
    have h3 : v < U ^ r := by omega
    nlinarith
  have hY1 : 1 ≤ Y := le_trans (Nat.one_le_pow _ _ hU0) hYU
  -- `D₀ ∣ Y`
  have hD₀Y : D₀ ∣ Y := by rw [hY]; exact dvd_add hcentral (Dvd.dvd.mul_left hD₀U _)
  obtain ⟨w, hw⟩ := hD₀U
  obtain ⟨s, hs⟩ := hD₀Y
  have hU' : U = w * D₀ := by rw [hw]; ring
  have hY' : Y = s * D₀ := by rw [hs]; ring
  have hw0 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · rw [h] at hU'; simp at hU'; omega
    · exact h
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h] at hY'; simp at hY'; omega
    · exact h
  -- `a`, `A`, `P`
  obtain ⟨a, ha⟩ : ∃ a, a = Y * (U + 1) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hA : 1 < a + 3 := by omega
  have hra : r < a := by
    rw [ha]
    calc r < U := hUr
      _ ≤ U ^ r := Nat.le_self_pow (by omega) U
      _ ≤ Y := hYU
      _ ≤ Y * (U + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hQpos : 0 < U * Y ^ 2 := by positivity
  have hPp : 1 < 2 * (U * Y ^ 2) + 1 := by omega
  -- the first Pell pair: `k = ψ_P(r+1)`, `2τ + 1 = χ_P(r+1)`
  obtain ⟨k, hk⟩ : ∃ k, k = yn hPp (r + 1) := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; exact lt_of_lt_of_le (Nat.succ_pos r) (yn_ge_n hPp (r + 1))
  have hkr : r + 1 < k := by rw [hk]; exact lt_yn_of_two_le hPp (by omega)
  have hxodd : Odd (xn hPp (r + 1)) := by
    have h := xr_odd (z := ((2 * (U * Y ^ 2) + 1 : ℕ) : ℤ)) ⟨U * Y ^ 2, by push_cast; ring⟩ (r + 1)
    rw [← xn_eq_xr hPp] at h
    exact (Int.odd_coe_nat _).1 h
  obtain ⟨τ, hτ⟩ := hxodd
  have hτ0 : 0 < τ := by
    have : 2 * (U * Y ^ 2) + 1 ≤ xn hPp (r + 1) := by
      calc 2 * (U * Y ^ 2) + 1 = (2 * (U * Y ^ 2) + 1) ^ 1 := (pow_one _).symm
        _ ≤ (2 * (U * Y ^ 2) + 1) ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ xn hPp (r + 1) := xn_ge_a_pow hPp (r + 1)
    omega
  have E9 : τ * (τ + 1) = (U * Y ^ 2) * (U * Y ^ 2 + 1) * k ^ 2 := by
    have h := χ_sq hPp (r + 1)
    simp only [Diophantine.χ, Diophantine.ψ] at h
    rw [hτ, ← hk] at h
    have : 4 * (τ * (τ + 1)) = 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1) * k ^ 2) := by
      have e : (2 * (U * Y ^ 2) + 1) * (2 * (U * Y ^ 2) + 1) - 1 =
          4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) := by
        have : (2 * (U * Y ^ 2) + 1) * (2 * (U * Y ^ 2) + 1) =
            4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) + 1 := by ring
        omega
      rw [e] at h
      have e2 : (2 * τ + 1) * (2 * τ + 1) = 4 * (τ * (τ + 1)) + 1 := by ring
      have e3 : 4 * (U * Y ^ 2 * (U * Y ^ 2 + 1)) * k * k =
          4 * (U * Y ^ 2 * (U * Y ^ 2 + 1) * k ^ 2) := by ring
      omega
    omega
  -- the main Pell pair
  obtain ⟨c, hc⟩ : ∃ c, c = yn hA J := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = xn hA J := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact JSWW1976.ψ_pos_of_pos hA (by omega)
  have hd0 : 0 < d := by rw [hd]; exact xn_pos' hA J
  have hDeq : (a + 3) * (a + 3) - 1 = a ^ 2 + 6 * a + 8 := by
    have : (a + 3) * (a + 3) = a ^ 2 + 6 * a + 9 := by ring
    omega
  have E15 : d ^ 2 = 1 + (a ^ 2 + 6 * a + 8) * c ^ 2 := by
    have h := χ_sq hA J
    simp only [Diophantine.χ, Diophantine.ψ] at h
    rw [← hc, ← hd, hDeq] at h
    rw [sq, h]; ring
  -- the interval `kY < c < k(Y + 1)`
  have hlow := lower_estimate (U := U) (Y := Y) (by omega) hY1 (by omega) hJ hA ha hPp hc hk
  have hkYc : k * Y < c := by
    have h1 : k * Y * U ^ r ≤ k * (U + 1) ^ (2 * r) := by
      rw [hsplit]; nlinarith [Nat.zero_le (k * v)]
    have h2 : k * Y * U ^ r < c * U ^ r := lt_of_le_of_lt h1 hlow
    exact Nat.lt_of_mul_lt_mul_right h2
  have hUR : (0 : ℝ) < (U : ℝ) ^ r := by positivity
  have hξY' : ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r < Y + 1 := by
    rw [div_lt_iff₀ hUR]
    have h1 : ((U : ℝ) + 1) ^ (2 * r) = Y * (U : ℝ) ^ r + v := by exact_mod_cast hsplit
    have h2 : (v : ℝ) < (U : ℝ) ^ r := by
      have : v < U ^ r := by omega
      exact_mod_cast this
    rw [h1]; linarith
  have h72 : 72 * r < U + 1 := by
    have := seventy_two_mul_lt_pow r hr
    rw [hU, hJ]; omega
  have h3 : 3 ≤ Y * (U + 1) := by
    calc 3 ≤ 1 * (U + 1) := by omega
      _ ≤ Y * (U + 1) := Nat.mul_le_mul_right _ hY1
  have hup := upper_estimate' (U := U) (Y := Y) (by omega) hY1 (by omega) hJ hA ha hPp hc hk hξY'
    h72 hYU h3
  have hckY : c < k * (Y + 1) := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have h1 : (c : ℝ) / k < Y + 1 := by
      have hv4 : (v : ℝ) * 4 < (U : ℝ) ^ r := by
        have : 4 * v < U ^ r := hv
        have : ((4 * v : ℕ) : ℝ) < ((U ^ r : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at this; linarith
      have hξ : ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r < Y + 1 / 4 := by
        rw [div_lt_iff₀ hUR]
        have h1 : ((U : ℝ) + 1) ^ (2 * r) = Y * (U : ℝ) ^ r + v := by exact_mod_cast hsplit
        rw [h1]; nlinarith
      linarith
    rw [div_lt_iff₀ hkR] at h1
    have : (c : ℝ) < ((k * (Y + 1) : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hkY1 : k * (Y + 1) = k * Y + k := by ring
  obtain ⟨η, hη⟩ : ∃ η, η = c - k * Y := ⟨_, rfl⟩
  have hη0 : 0 < η := by omega
  have E10a : c = k * Y + η := by omega
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = k - η := ⟨_, rfl⟩
  have hζ0 : 0 < ζ := by
    have : η < k := by rw [hη]; omega
    omega
  have E10b : k = η + ζ := by
    have : η < k := by rw [hη]; omega
    omega
  -- `k ≡ r + 1 (mod UY)`
  have hmod : k ≡ r + 1 [MOD 2 * (U * Y ^ 2) + 1 - 1] := by rw [hk]; exact ψ_modEq hPp (r + 1)
  have hdvd : U * Y ∣ k - (r + 1) := by
    have h1 : 2 * (U * Y ^ 2) + 1 - 1 ∣ k - (r + 1) := (Nat.modEq_iff_dvd' (by omega)).1 hmod.symm
    have h2 : U * Y ∣ 2 * (U * Y ^ 2) + 1 - 1 := by
      rw [Nat.add_sub_cancel]; exact Dvd.intro (2 * Y) (by ring)
    exact dvd_trans h2 h1
  obtain ⟨h, hh⟩ := hdvd
  have hh0 : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · rw [h0, mul_zero] at hh; omega
    · exact h0
  have E11 : k = r + 1 + h * U * Y := by
    have : k - (r + 1) = h * U * Y := by rw [hh]; ring
    omega
  -- `γ`: the base-three exponent congruence
  obtain ⟨γ, hγ0, hγ⟩ := Jones1982.exists_positive_pell_power_quotient_int (A := a + 3) (B := 3)
    (L := J) hA (by norm_num) (by omega) hJ2
  have E14 : d = U + a * c + γ * (6 * a + 8) := by
    have h1 : (d : ℤ) = U + a * c + γ * (6 * a + 8) := by
      rw [hd, hU]
      have : (xn hA J : ℤ) = (χ hA J : ℤ) := rfl
      rw [this, hγ, hc]
      have : (yn hA J : ℤ) = (ψ hA J : ℤ) := rfl
      rw [this]
      push_cast
      ring
    exact_mod_cast h1
  -- the half-parameter auxiliary witnesses
  obtain ⟨f, i, o, j, y, hf0, hi0, ho0, hj0, hy0, E16', E17b', E17'⟩ := half_witnesses hA hJ1 hJ4
  rw [← hc] at E16' E17b' E17'
  have hD : (a + 3) ^ 2 - 1 = a ^ 2 + 6 * a + 8 := sq_sub_one_eq a
  rw [hD] at E16'
  have E17 : (((a : ℤ) ^ 2 + 6 * a + 8) * (f ^ 2 - 1)) * ((2 * r + 1 + j * c) ^ 2 - (y : ℤ) ^ 2) =
      1 - (y : ℤ) ^ 2 := by
    have e : (((a + 3 : ℕ) : ℤ) ^ 2 - 1) = (a : ℤ) ^ 2 + 6 * a + 8 := by push_cast; ring
    have hJZ : (J : ℤ) = 2 * r + 1 := by rw [hJ]; push_cast; ring
    rw [e, hJZ] at E17'
    exact E17'
  have E17b : 2 * r + 1 + j * c = c + o * f := by rw [← hJ]; exact E17b'
  refine ⟨a, c, d, f, h, i, j, k, o, s, w, τ, η, ζ, γ, y,
    ⟨ha0, hc0, hd0, hf0, hh0, hi0, hj0, hk0, ho0, hs0, hw0, hτ0, hη0, hζ0, hγ0, hy0⟩,
    ⟨?_, ?_, E10b, ?_, ?_, ?_, E15, E16', E17, E17b⟩⟩
  · rw [← hU', ← hY', E9]; ring
  · rw [← hY']; exact E10a
  · rw [← hU', ← hY']; exact E11
  · rw [← hU', ← hY']; exact ha
  · rw [← hU']; exact E14

end Jones1980
