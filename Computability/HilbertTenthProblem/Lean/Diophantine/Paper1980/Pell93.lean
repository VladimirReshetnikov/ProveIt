import Diophantine.Paper1980.Bootstrap93
import Diophantine.Paper1980.PellRelaxedMain
import Diophantine.Paper1980.PellExponent
import Diophantine.Paper1980.PellRatio

/-!
# The Pell block of the 93-operation system

Section 3 of `Papers/1980/AFFINE_RADIX_95_PROOF.md` (unchanged for the 94-
and 93-operation refinements), following `PELL_RELAXED_AUXILIARY_PROOF.md`
and `COMPOSED_97_PROOF.md`. From `Pos93` (including `0 < x`), `Sys93`,
and the bootstrap bounds, before any coefficient row is decoded:

* the main norm `E15` classifies `(d, c)` as a Pell pair of `A = a + 4`, and
  the first norm `E9` classifies `(2τ + 1, k)` as a Pell pair of
  `P = 2UY² + 1`; the index congruence `E11` gives a first index `≥ r + 1`,
  and growth forces the main index to be `≥ r + 2`, so that `c > A (A² − 1)²`;
* the relaxed auxiliary norm `E16` then supplies the integral auxiliary pair
  (`relaxed_aux`), and the doubled-index block `E17` fixes `c = ψ_A(J)`,
  `d = χ_A(J)` with `J = 2r + 1` (`doubled_index_core`);
* the ratio block gives `k = ψ_P(r + 1)`, `Y ≥ U^r`, `a > U^(r+1)`;
* the exponent congruences give `U = 4^J` (`exp_U`) and `q = B^L`
  (`exp_q`), `B = H + b + 4`, with `κ = ψ_A(L)`;
* the ratio estimates give `n² ∣ C(2r, r)` (`Y_eq_floor`, `central_dvd`);
* hence `q` and `B` are powers of two.

The index hypotheses used are `64 ≤ H`, `0 < L`, `3L ≤ H` and
`Tindex = ψ₄(L)`.
-/

namespace Jones1980

open Diophantine Pell

/-- `18 r < 16^r` for `r ≥ 2`. -/
theorem eighteen_mul_lt_pow (r : ℕ) (hr : 2 ≤ r) : 18 * r < 16 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r _ ih => rw [pow_succ]; omega

/-- The conclusions of the Pell block, for the fixed proofs `hA : 1 < a + 4` and
`hPp : 1 < P`. -/
structure PellBlock93 (a b c d k n q r s w κ H L : ℕ) (hA : 1 < a + 4)
    (hPp : 1 < 2 * (w * n ^ 2 * (s * n ^ 2) ^ 2) + 1) : Prop where
  c_eq : c = ψ hA (2 * r + 1)
  d_eq : d = χ hA (2 * r + 1)
  k_eq : k = ψ hPp (r + 1)
  Y_ge : (w * n ^ 2) ^ r ≤ s * n ^ 2
  a_gt : (w * n ^ 2) ^ (r + 1) < a
  U_eq : w * n ^ 2 = 4 ^ (2 * r + 1)
  q_eq : q = (H + b + 4) ^ L
  κ_eq : κ = ψ hA L
  central : n ^ 2 ∣ (2 * r).choose r
  q_pow2 : ∃ i, q = 2 ^ i
  B_pow2 : ∃ i, H + b + 4 = 2 ^ i

section Block

variable {x V H Tindex L a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω : ℕ}
  (hP : Pos93 x a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω)
  (hS : Sys93 x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω)

include hP hS

theorem pell_block (hH : 64 ≤ H) (hL : 0 < L) (hLH : 3 * L ≤ H)
    (hT : Tindex = yn four_lt_one L) (hA : 1 < a + 4)
    (hPp : 1 < 2 * (w * n ^ 2 * (s * n ^ 2) ^ 2) + 1) :
    PellBlock93 a b c d k n q r s w κ H L hA hPp := by
  -- sizes
  have hq9 := nine_le_q hP hS hH
  obtain ⟨hnr, hr2n⟩ := r_bounds hP hS (by omega)
  have hn := hS.E6
  have hn_big : 9 ^ 8 ≤ n := by rw [hn]; exact Nat.pow_le_pow_left hq9 8
  have hn2 : (9 ^ 8) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn_big 2
  set U := w * n ^ 2 with hUdef
  set Y := s * n ^ 2 with hYdef
  have hU : n ^ 2 ≤ U := Nat.le_mul_of_pos_left _ hP.w
  have hY : n ^ 2 ≤ Y := Nat.le_mul_of_pos_left _ hP.s
  have hn2' : 4096 ≤ n ^ 2 := by have h := hn2; norm_num at h; omega
  have hU64 : 4 ^ 6 ≤ U := by norm_num; omega
  have hY2 : 2 ≤ Y := by omega
  have hn3 : 4 * n ^ 3 + 1 ≤ n ^ 4 := by
    have e4 : n ^ 4 = n ^ 3 * n := by ring
    have h3 : 5 * n ^ 3 ≤ n ^ 3 * n := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    have h1 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hP.n
    omega
  have hn4 : n ^ 4 = n ^ 2 * n ^ 2 := by ring
  have hUY : r + 1 < U * Y := by
    calc r + 1 ≤ 2 * n ^ 3 := by omega
      _ < n ^ 4 := by omega
      _ = n ^ 2 * n ^ 2 := hn4
      _ ≤ U * Y := Nat.mul_le_mul hU hY
  have ha := hS.E12
  have haJ : 2 * r + 1 < a := by
    have h1 : n ^ 2 * n ^ 2 ≤ Y * (U + 1) := Nat.mul_le_mul hY (by omega)
    have h2 : 2 * r + 1 < n ^ 4 := by linarith
    calc 2 * r + 1 < n ^ 4 := h2
      _ = n ^ 2 * n ^ 2 := hn4
      _ ≤ Y * (U + 1) := h1
      _ = a := ha.symm
  have hcJ : 2 * r + 1 < c := by
    have h10 := hS.E10a; have h11 := hS.E11
    have : U * Y ≤ h * U * Y := by
      have := hP.h
      calc U * Y = 1 * U * Y := by ring
        _ ≤ h * U * Y := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
    have hkY : k ≤ k * Y := Nat.le_mul_of_pos_right _ (by omega)
    have hkc : k ≤ c := by rw [h10]; exact le_trans hkY (Nat.le_add_right _ _)
    have hk2 : r + 1 + U * Y ≤ k := by rw [h11]; exact Nat.add_le_add_left this _
    omega
  -- the main Pell pair
  have hDeq : (a + 4) ^ 2 - 1 = a ^ 2 + 8 * a + 15 := sq_sub_one_eq a
  obtain ⟨p', hd, hcp⟩ := eq_pell_of_sq hA (by rw [hDeq]; exact hS.E15)
  have hp'0 : 0 < p' := by
    rcases Nat.eq_zero_or_pos p' with h0 | h0
    · rw [h0, yn_zero] at hcp; omega
    · exact h0
  -- the first Pell pair
  obtain ⟨t', hτ, hk⟩ := eq_pell_of_sq hPp (x := 2 * τ + 1) (y := k) (by
    have h9 := hS.E9
    have e1 : (2 * (U * Y ^ 2) + 1) ^ 2 - 1 = 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) := by
      have : (2 * (U * Y ^ 2) + 1) ^ 2 = 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) + 1 := by ring
      omega
    rw [e1]
    calc (2 * τ + 1) ^ 2 = 1 + 4 * (τ * (τ + 1)) := by ring
      _ = 1 + 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1) * k ^ 2) := by rw [h9]
      _ = 1 + 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) * k ^ 2 := by ring)
  have ht'0 : 0 < t' := by
    rcases Nat.eq_zero_or_pos t' with h0 | h0
    · rw [h0, yn_zero] at hk; have := hP.k; omega
    · exact h0
  -- the first index is at least `r + 1`
  have ht'ge : r + 1 ≤ t' := by
    have hk1 : k ≡ r + 1 [MOD U * Y] := by
      show k % (U * Y) = (r + 1) % (U * Y)
      rw [hS.E11, show r + 1 + h * U * Y = r + 1 + h * (U * Y) by ring,
        Nat.add_mul_mod_self_right]
    have hk2 : k ≡ t' [MOD U * Y] := by
      have hm := yn_modEq_a_sub_one hPp t'
      rw [← hk] at hm
      have hdvd : U * Y ∣ 2 * (U * Y ^ 2) + 1 - 1 := by
        rw [Nat.add_sub_cancel]; exact Dvd.intro (2 * Y) (by ring)
      exact Nat.ModEq.of_dvd hdvd hm
    have h12 := hk1.symm.trans hk2
    by_contra hlt; push Not at hlt
    have := Nat.ModEq.eq_of_lt_of_lt h12 hUY (by omega)
    omega
  -- `P > 2A`: `2(a + 4) < 2P − 1`
  have hPA : 2 * (a + 4) < 2 * (2 * (U * Y ^ 2) + 1) - 1 := by
    have h1 : 4 * (Y * (U + 1) + 4) < 2 * (2 * (U * Y ^ 2) + 1) - 1 := four_A_lt (by omega) hY2
    calc 2 * (a + 4) ≤ 4 * (a + 4) := by omega
      _ = 4 * (Y * (U + 1) + 4) := by rw [ha]
      _ < _ := h1
  -- the main index is at least `r + 2`
  have hp'2 : r + 2 ≤ p' := by
    by_contra hlt; push Not at hlt
    have h1 : c ≤ (2 * (a + 4)) ^ (p' - 1) := by
      rw [hcp]
      have := ψ_succ_le_pow hA (p' - 1)
      rwa [Nat.sub_add_cancel hp'0] at this
    have h2 : (2 * (a + 4)) ^ (p' - 1) ≤ (2 * (a + 4)) ^ r :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (2 * (a + 4)) ^ r < (2 * (2 * (U * Y ^ 2) + 1) - 1) ^ r :=
      Nat.pow_lt_pow_left hPA (by omega)
    have h4 : (2 * (2 * (U * Y ^ 2) + 1) - 1) ^ r ≤ yn hPp (r + 1) := pow_le_ψ_succ hPp r
    have h5 : yn hPp (r + 1) ≤ yn hPp t' := (strictMono_y hPp).monotone ht'ge
    have h6 : k < c := by
      have h10 := hS.E10a
      have hkY : k ≤ k * Y := Nat.le_mul_of_pos_right _ (by omega)
      calc k ≤ k * Y := hkY
        _ < k * Y + η := Nat.lt_add_of_pos_right hP.η
        _ = c := h10.symm
    rw [← hk] at h5
    omega
  -- `c > A (A² − 1)²`
  have hbig : (a + 4) * ((a + 4) ^ 2 - 1) ^ 2 < c := by
    have h1 : (2 * (a + 4) - 1) ^ (p' - 1) ≤ c := by
      rw [hcp]
      have := pow_le_ψ_succ hA (p' - 1)
      rwa [Nat.sub_add_cancel hp'0] at this
    have h2 : (a + 4) ^ 6 ≤ (2 * (a + 4) - 1) ^ (p' - 1) :=
      calc (a + 4) ^ 6 ≤ (2 * (a + 4) - 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
        _ ≤ (2 * (a + 4) - 1) ^ (p' - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (a + 4) * ((a + 4) ^ 2 - 1) ^ 2 < (a + 4) ^ 6 := by
      have hlt : ((a + 4) ^ 2 - 1) ^ 2 < ((a + 4) ^ 2) ^ 2 :=
        Nat.pow_lt_pow_left (by have := Nat.one_le_pow 2 (a + 4) (by omega); omega) two_ne_zero
      calc (a + 4) * ((a + 4) ^ 2 - 1) ^ 2 < (a + 4) * ((a + 4) ^ 2) ^ 2 :=
            Nat.mul_lt_mul_of_pos_left hlt (by omega)
        _ = (a + 4) ^ 5 := by ring
        _ ≤ (a + 4) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  -- the relaxed auxiliary norm
  obtain ⟨m, hfm, hpm, hcm, hicm⟩ :=
    relaxed_aux hA hp'0 hcp hP.i hP.f (by rw [hDeq]; exact hS.E16) hbig
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, yn_zero, mul_zero] at hicm
      have : 0 < i * c ^ 2 := by have := hP.i; have := hP.c; positivity
      omega
    · exact h0
  have hf2 : 2 ≤ f := by
    rw [hfm]
    calc 2 ≤ a + 4 := by omega
      _ = (a + 4) ^ 1 := (pow_one _).symm
      _ ≤ (a + 4) ^ m := Nat.pow_le_pow_right (by omega) hm0
      _ ≤ xn hA m := xn_ge_a_pow hA m
  have hcf : (c : ℤ) ∣ (f : ℤ) ^ 2 - 1 := by
    have hcy : c ∣ yn hA m := by rw [hcp]; exact (y_dvd_iff hA p' m).2 hpm
    have hD0 : 0 < (a + 4) ^ 2 - 1 := by rw [hDeq]; omega
    have hfsq : f ^ 2 - 1 = ((a + 4) ^ 2 - 1) * yn hA m ^ 2 := by
      have E16' : (i * c ^ 2) ^ 2 = ((a + 4) ^ 2 - 1) * (f ^ 2 - 1) := by
        rw [hDeq]; exact hS.E16
      have h1 : ((a + 4) ^ 2 - 1) * (f ^ 2 - 1) =
          ((a + 4) ^ 2 - 1) * (((a + 4) ^ 2 - 1) * yn hA m ^ 2) := by
        rw [← E16', hicm]; ring
      exact Nat.eq_of_mul_eq_mul_left hD0 h1
    obtain ⟨u, hu⟩ := hcy
    have hf1 : 1 ≤ f ^ 2 := Nat.one_le_pow _ _ hP.f
    have : (f : ℤ) ^ 2 - 1 = ((f ^ 2 - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub hf1]; ring
    rw [this, hfsq, hu]
    push_cast
    exact Dvd.intro (((((a + 4) ^ 2 - 1 : ℕ)) : ℤ) * c * u ^ 2) (by ring)
  -- the doubled-index block: `c = ψ_A(J)`, `d = χ_A(J)`
  obtain ⟨hcJ', hdJ'⟩ := doubled_index_core hA (by omega : 1 < 2 * r + 1) hcJ ⟨r, rfl⟩ hd hcp hfm hcm
    hf2 hcf (by
      push_cast
      rw [show ((a : ℤ) + 4) ^ 2 - 1 = (a : ℤ) ^ 2 + 8 * a + 15 by ring]
      exact hS.E17)
  -- the ratio block
  have hk_eq : k = ψ hPp (r + 1) :=
    k_index (U := w * n ^ 2) (Y := s * n ^ 2) (h := h) (by omega) hY2 (by omega) rfl hA ha hPp
      hcJ' hS.E9 hS.E10a hS.E10b hP.ζ (by rw [hS.E11]; ring) hUY
  have hYr : U ^ r ≤ Y :=
    Y_lower (U := w * n ^ 2) (Y := s * n ^ 2) (by omega) (by omega) (by omega) rfl hA ha hPp hcJ'
      hk_eq hS.E10a hS.E10b hP.ζ
  have hagt : U ^ (r + 1) < a := a_gt (by omega) ha hYr
  -- `U = 4^J`
  have hU4 : U = 4 ^ (2 * r + 1) := by
    apply exp_U hA hcJ' hdJ' (by omega) ?_ ?_ hS.E14
    · calc 4 ^ (3 * (2 * r + 1)) ≤ 4 ^ (6 * (r + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (4 ^ 6) ^ (r + 1) := by rw [pow_mul]
        _ ≤ U ^ (r + 1) := Nat.pow_le_pow_left hU64 _
        _ < a + 4 := by omega
    · calc U ^ 3 ≤ U ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        _ < a + 4 := by omega
  -- `q = B^L`
  have hBn : H + b + 4 < n := B_lt_n hP hS
  obtain ⟨hq_eq, hκ_eq, _⟩ := exp_q (B := H + b + 4) hA hcJ' hL (by omega) (by have := hS.E13; have := hP.φ; omega)
    hP.κ hT
    (by
      calc 8 ^ (2 * r + 1) ≤ 8 ^ (2 * (r + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 64 ^ (r + 1) := by rw [pow_mul]; norm_num
        _ ≤ U ^ (r + 1) := Nat.pow_le_pow_left (by omega) _
        _ ≤ a := hagt.le)
    (by omega) hP.q
    (by
      calc (H + b + 4) ^ (3 * L) ≤ n ^ (3 * L) := Nat.pow_le_pow_left hBn.le _
        _ ≤ n ^ (2 * r) := Nat.pow_le_pow_right (by omega) (by omega)
        _ = (n ^ 2) ^ r := by rw [pow_mul]
        _ ≤ U ^ r := Nat.pow_le_pow_left hU r
        _ ≤ U ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        _ < a + 4 := by omega)
    (by
      calc q ^ 3 ≤ q ^ 8 := Nat.pow_le_pow_right hP.q (by norm_num)
        _ = n := hn.symm
        _ < a + 4 := by omega)
    (by push_cast; exact hS.E18) hS.E19 hS.E20
  -- the central-binomial divisibility
  have hU4' : 4 * 2 ^ (2 * r) < U := by
    rw [hU4, pow_succ, mul_comm]
    have : 2 ^ (2 * r) < 4 ^ (2 * r) := Nat.pow_lt_pow_left (by norm_num) (by omega)
    omega
  have hlow := lower_estimate (U := w * n ^ 2) (Y := s * n ^ 2) (by omega) (by omega) (by omega) rfl
    hA ha hPp hcJ' hk_eq
  have h72 : 72 * r < U + 1 := by
    have h1 := eighteen_mul_lt_pow r (by omega)
    have : U = 4 * 16 ^ r := by rw [hU4, pow_succ, mul_comm, pow_mul]; norm_num
    omega
  have hup := upper_estimate (U := w * n ^ 2) (Y := s * n ^ 2) (by omega) (by omega) (by omega) rfl
    hA ha hPp hcJ' hk_eq hS.E10a hS.E10b hP.ζ h72 hYr (by rw [← ha]; omega)
  obtain ⟨w', hw'⟩ := Y_eq_floor (U := w * n ^ 2) (Y := s * n ^ 2) (by omega) hU4' hP.k hP.η hS.E10a
    hS.E10b hP.ζ hlow hup
  have hcentral : n ^ 2 ∣ (2 * r).choose r :=
    central_dvd (Dvd.intro_left w rfl) (Dvd.intro_left s rfl) hw'
  -- powers of two
  have hnpow : ∃ i, n = 2 ^ i := by
    have h1 : n ∣ U := dvd_trans (Dvd.intro n (by ring)) (Dvd.intro_left w rfl)
    rw [hU4, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] at h1
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact ⟨i, hi⟩
  have hqpow : ∃ i, q = 2 ^ i := by
    obtain ⟨i, hi⟩ := hnpow
    have : q ∣ 2 ^ i := by rw [← hi, hn]; exact Dvd.intro (q ^ 7) (by ring)
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
    exact ⟨j, hj⟩
  have hBpow : ∃ i, H + b + 4 = 2 ^ i := by
    obtain ⟨i, hi⟩ := hqpow
    have : H + b + 4 ∣ 2 ^ i := by
      rw [← hi, hq_eq]; exact dvd_pow_self (H + b + 4) hL.ne'
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
    exact ⟨j, hj⟩
  exact ⟨hcJ', hdJ', hk_eq, hYr, hagt, hU4, hq_eq, hκ_eq, hcentral, hqpow, hBpow⟩

end Block

end Jones1980
