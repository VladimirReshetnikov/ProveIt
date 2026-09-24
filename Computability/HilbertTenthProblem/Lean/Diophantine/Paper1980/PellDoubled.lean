import Diophantine.Common.PellInt
import Diophantine.Paper1976.MR
import Diophantine.Paper1982.Psi

/-!
# The doubled-index signed Pell block (`Papers/1980/PELL_DOUBLED_INDEX_PROOF.md`)

For the main Pell parameter `A` (`A = a + 4` in the system) the block

* `E15 : d² = 1 + (A² − 1) c²`,
* `E16 : f² = 1 + (A² − 1)(i c²)²`,
* `E17 : v(v + 1) = K(K − 1)(J + jc)²`, `v = o f − d²`, `K = (A² − 1)(f² − 1)`,

with `J = 2r + 1` odd, `1 < J < c`, forces `c = ψ_A(J)`, `d = χ_A(J)`
(`doubled_index_sufficiency`); conversely for `c = ψ_A(J)`, `d = χ_A(J)` the
witnesses `f, i, o, j` exist and are positive (`doubled_index_necessity`).

The proof reduces the auxiliary parameter `G = 2K − 1` modulo `f = χ_A(m)`
to `−χ_A(2)` and modulo `c` to `−1`, using the integer recurrences of
`Diophantine.Common.PellInt`, and then applies Mathlib's step-down lemma
`Pell.modEq_of_xn_modEq`.
-/

namespace Jones1980

open Diophantine Pell

/-- `ψ_A(p) ≥ 2p` for `p ≥ 2`. -/
theorem two_mul_le_yn {A p : ℕ} (hA : 1 < A) (hp : 2 ≤ p) : 2 * p ≤ yn hA p := by
  by_contra h
  push Not at h
  have := Jones1982.le_two_of_ψ_le hA h.le
  have hp2 : p = 2 := by omega
  subst hp2
  have h2 : yn hA 2 = 2 * A := ψ_two hA
  omega

/-- The Pell equation in the form `Pell.eq_pell` wants. -/
theorem eq_pell_of_sq {A x y : ℕ} (hA : 1 < A) (h : x ^ 2 = 1 + (A ^ 2 - 1) * y ^ 2) :
    ∃ t, x = xn hA t ∧ y = yn hA t := by
  have e : x * x = 1 + (A * A - 1) * y * y := by
    rw [← sq, h, sq A, sq y]; ring
  have e' : x * x - (A * A - 1) * y * y = 1 := by omega
  exact Pell.eq_pell hA e'

/-- `χ_A(2) = 2A² − 1`. -/
theorem xn_two {A : ℕ} (hA : 1 < A) : (xn hA 2 : ℤ) = 2 * (A : ℤ) ^ 2 - 1 := by
  have := xn_two_mul hA 1
  rw [show 2 * 1 = 2 by rfl] at this
  rw [this, xn_one]

/-- Positivity of `χ`. -/
theorem xn_pos' {A : ℕ} (hA : 1 < A) (t : ℕ) : 0 < xn hA t :=
  lt_of_lt_of_le (by positivity) (xn_ge_a_pow hA t)

/-- The signed χ step-down: if `χ_A(2t) ≡ ±χ_A(2p) (mod χ_A(m))` with `0 < 2p ≤ m`,
then `t ≡ ±p (mod m)`, stated as integer divisibility. -/
theorem step_down {A m p t : ℕ} (hA : 1 < A) (hp : 0 < p) (hpm : 2 * p ≤ m)
    (h : (xn hA m : ℤ) ∣ (xn hA (2 * t) : ℤ) - xn hA (2 * p) ∨
      (xn hA m : ℤ) ∣ (xn hA (2 * t) : ℤ) + xn hA (2 * p)) :
    (m : ℤ) ∣ (t : ℤ) - p ∨ (m : ℤ) ∣ (t : ℤ) + p := by
  have key : ∀ j, xn hA j ≡ xn hA (2 * p) [MOD xn hA m] →
      (4 * (m : ℤ)) ∣ (j : ℤ) - 2 * p ∨ (4 * (m : ℤ)) ∣ (j : ℤ) + 2 * p := by
    intro j hj
    rcases modEq_of_xn_modEq hA (by omega) hpm hj with h1 | h1
    · left
      have := (Nat.modEq_iff_dvd.1 h1.symm)
      push_cast at this
      exact this
    · right
      have := (Nat.modEq_iff_dvd.1 h1)
      push_cast at this
      simp only [zero_sub, dvd_neg] at this
      exact this
  rcases h with h | h
  · have hj : xn hA (2 * t) ≡ xn hA (2 * p) [MOD xn hA m] := by
      rw [Nat.modEq_iff_dvd]
      have e : (xn hA (2 * p) : ℤ) - xn hA (2 * t) = -((xn hA (2 * t) : ℤ) - xn hA (2 * p)) := by
        ring
      rw [e]; exact dvd_neg.2 h
    rcases key (2 * t) hj with h2 | h2
    · left; obtain ⟨k, hk⟩ := h2; exact ⟨2 * k, by push_cast at hk ⊢; linarith⟩
    · right; obtain ⟨k, hk⟩ := h2; exact ⟨2 * k, by push_cast at hk ⊢; linarith⟩
  · -- `χ_A(2m + 2t) ≡ −χ_A(2t) ≡ χ_A(2p)`
    have h3 := xn_modEq_x2n_add hA m (2 * t)
    have h3' := Nat.modEq_iff_dvd.1 h3
    push_cast at h3'
    simp only [zero_sub, dvd_neg] at h3'
    have hj : xn hA (2 * m + 2 * t) ≡ xn hA (2 * p) [MOD xn hA m] := by
      rw [Nat.modEq_iff_dvd]
      have e : (xn hA (2 * p) : ℤ) - xn hA (2 * m + 2 * t) =
          ((xn hA (2 * t) : ℤ) + xn hA (2 * p)) -
            ((xn hA (2 * m + 2 * t) : ℤ) + xn hA (2 * t)) := by
        ring
      rw [e]; exact dvd_sub h h3'
    rcases key (2 * m + 2 * t) hj with h2 | h2
    · left; obtain ⟨k, hk⟩ := h2; exact ⟨2 * k - 1, by push_cast at hk ⊢; linarith⟩
    · right; obtain ⟨k, hk⟩ := h2; exact ⟨2 * k - 1, by push_cast at hk ⊢; linarith⟩

/-- `3 ≤ A² − 1` for `A ≥ 2`. -/
theorem three_le_sq_sub_one {A : ℕ} (hA : 1 < A) : 3 ≤ A ^ 2 - 1 := by
  have : 2 ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left hA 2
  omega

/-- `2 ≤ f` when `f² = 1 + (A² − 1) i² c⁴` with positive `i, c`. -/
theorem two_le_of_aux {A f i c : ℕ} (hA : 1 < A) (hi : 0 < i) (hc : 0 < c)
    (E16 : f ^ 2 = 1 + (A ^ 2 - 1) * i ^ 2 * c ^ 4) : 2 ≤ f := by
  have h4 : 4 ≤ f ^ 2 := by
    rw [E16, mul_assoc]
    have h1 : 1 ≤ i ^ 2 * c ^ 4 := Nat.one_le_iff_ne_zero.2 (by positivity)
    have := Nat.mul_le_mul (three_le_sq_sub_one hA) h1
    omega
  by_contra hlt
  push Not at hlt
  interval_cases f <;> omega

/-- The auxiliary parameter `G = 2K − 1`, `K = (A² − 1)(f² − 1)`: it exceeds one and equals
`2(A² − 1)(f² − 1) − 1` as an integer. -/
theorem aux_param {A f : ℕ} (hA : 1 < A) (hf2 : 2 ≤ f) :
    1 < 2 * ((A ^ 2 - 1) * (f ^ 2 - 1)) - 1 ∧
      ((2 * ((A ^ 2 - 1) * (f ^ 2 - 1)) - 1 : ℕ) : ℤ) =
        2 * ((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1) - 1 := by
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hf4 : 4 ≤ f ^ 2 := Nat.pow_le_pow_left hf2 2
  have hK : 3 * 3 ≤ (A ^ 2 - 1) * (f ^ 2 - 1) :=
    Nat.mul_le_mul (three_le_sq_sub_one hA) (by omega : 3 ≤ f ^ 2 - 1)
  refine ⟨by omega, ?_⟩
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * ((A ^ 2 - 1) * (f ^ 2 - 1))),
    Nat.cast_sub hA2, Nat.cast_sub (by omega : 1 ≤ f ^ 2)]
  ring

/-- The core of the doubled-index argument, with the auxiliary pair supplied as
hypotheses: `f = χ_A(m)` with `c ∣ m`, `f ≥ 2`, and `c ∣ f² − 1`.  These follow from
the strict auxiliary norm `f² = 1 + (A² − 1)(i c²)²` (`doubled_index_sufficiency`) and
also from the relaxed norm `(i c²)² = (A² − 1)(f² − 1)` of the 95-operation system
(`PellRelaxed.lean`). -/
theorem doubled_index_core {A c d f o j J p m : ℕ} (hA : 1 < A) (hJ1 : 1 < J) (hJc : J < c)
    (hJodd : Odd J) (hd : d = xn hA p) (hcp : c = yn hA p) (hf : f = xn hA m) (hcm : c ∣ m)
    (hf2 : 2 ≤ f) (hcf : (c : ℤ) ∣ (f : ℤ) ^ 2 - 1)
    (E17 : ((o : ℤ) * f - d ^ 2) * ((o : ℤ) * f - d ^ 2 + 1) =
      (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1)) * (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1) - 1) *
        (J + j * c) ^ 2) :
    c = ψ hA J ∧ d = χ hA J := by
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hc : 0 < c := by omega
  have hp2 : 2 ≤ p := by
    by_contra h
    push Not at h
    have : c ≤ 1 := by
      rw [hcp]
      calc yn hA p ≤ yn hA 1 := (strictMono_y hA).monotone (by omega)
        _ = 1 := yn_one hA
    omega
  have hpc : p < c := by rw [hcp]; exact lt_yn_of_two_le hA hp2
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, xn_zero] at hf; omega
    · exact h
  have hcm' : c ≤ m := Nat.le_of_dvd hm0 hcm
  have h2p : 2 * p ≤ m := le_trans (by rw [hcp]; exact two_mul_le_yn hA hp2) hcm'
  obtain ⟨G, hG⟩ : ∃ G, G = 2 * ((A ^ 2 - 1) * (f ^ 2 - 1)) - 1 := ⟨_, rfl⟩
  obtain ⟨hG1, hGZ⟩ := aux_param hA hf2
  rw [← hG] at hG1 hGZ
  -- the signed root and the Pell pair for `G`
  obtain ⟨I, hI⟩ : ∃ I : ℕ, I = (2 * ((o : ℤ) * f - d ^ 2) + 1).natAbs := ⟨_, rfl⟩
  have hIsq : (I : ℤ) ^ 2 = (2 * ((o : ℤ) * f - d ^ 2) + 1) ^ 2 := by
    rw [hI, Int.natAbs_sq]
  have hI2 : (I : ℤ) ^ 2 = ((G : ℤ) ^ 2 - 1) * (J + j * c) ^ 2 + 1 := by
    rw [hIsq, hGZ]
    linear_combination 4 * E17
  obtain ⟨t, hIt, hHt⟩ : ∃ t, I = xn hG1 t ∧ J + j * c = yn hG1 t := by
    apply eq_pell_of_sq hG1
    have hG2 : 1 ≤ G ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e : ((I : ℕ) : ℤ) ^ 2 = ((1 + (G ^ 2 - 1) * (J + j * c) ^ 2 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hG2]; linarith
    exact_mod_cast e
  -- `G ≡ −χ_A(2) (mod f)` and `I ≡ ±(1 − 2d²) = ∓χ_A(2p) (mod f)`
  have hGf : (G : ℤ) ≡ -(xn hA 2 : ℤ) [ZMOD f] := by
    rw [Int.modEq_iff_dvd, hGZ, xn_two hA]
    exact ⟨-2 * ((A : ℤ) ^ 2 - 1) * f, by ring⟩
  have hx2p : (xn hA (2 * p) : ℤ) = 2 * (d : ℤ) ^ 2 - 1 := by
    have := xn_two_mul hA p; rw [← hd] at this; exact this
  have hIf : (f : ℤ) ∣ (I : ℤ) + xn hA (2 * p) ∨ (f : ℤ) ∣ (I : ℤ) - xn hA (2 * p) := by
    rcases Int.natAbs_eq (2 * ((o : ℤ) * f - d ^ 2) + 1) with h | h
    · left
      have : (I : ℤ) = 2 * ((o : ℤ) * f - d ^ 2) + 1 := by rw [hI]; exact h.symm
      rw [this, hx2p]; exact ⟨2 * o, by ring⟩
    · right
      have : (I : ℤ) = -(2 * ((o : ℤ) * f - d ^ 2) + 1) := by rw [hI]; linarith
      rw [this, hx2p]; exact ⟨-2 * o, by ring⟩
  -- `χ_G(t) ≡ (−1)^t χ_A(2t) (mod f)`
  have hxG : (xn hG1 t : ℤ) ≡ (-1) ^ t * xn hA (2 * t) [ZMOD f] := by
    rw [xn_eq_xr hG1, xn_two_mul_eq_xr hA t, ← xr_neg]
    exact xr_modEq hGf t
  have hstep : (xn hA m : ℤ) ∣ (xn hA (2 * t) : ℤ) - xn hA (2 * p) ∨
      (xn hA m : ℤ) ∣ (xn hA (2 * t) : ℤ) + xn hA (2 * p) := by
    rw [← hf]
    have h1 := (Int.modEq_iff_dvd.1 hxG)
    rw [← hIt] at h1
    rcases Nat.even_or_odd t with ht | ht
    · rw [ht.neg_one_pow, one_mul] at h1
      rcases hIf with h2 | h2
      · right
        have := dvd_add h1 h2
        rw [show (xn hA (2 * t) : ℤ) + xn hA (2 * p) =
          ((xn hA (2 * t) : ℤ) - I) + (I + xn hA (2 * p)) by ring]
        exact this
      · left
        have := dvd_add h1 h2
        rw [show (xn hA (2 * t) : ℤ) - xn hA (2 * p) =
          ((xn hA (2 * t) : ℤ) - I) + (I - xn hA (2 * p)) by ring]
        exact this
    · rw [ht.neg_one_pow, neg_one_mul] at h1
      rcases hIf with h2 | h2
      · left
        have := dvd_add h1 h2
        rw [show (xn hA (2 * t) : ℤ) - xn hA (2 * p) =
          -((-(xn hA (2 * t) : ℤ) - I) + (I + xn hA (2 * p))) by ring]
        exact dvd_neg.2 this
      · right
        have := dvd_add h1 h2
        rw [show (xn hA (2 * t) : ℤ) + xn hA (2 * p) =
          -((-(xn hA (2 * t) : ℤ) - I) + (I - xn hA (2 * p))) by ring]
        exact dvd_neg.2 this
  have hsd := step_down hA (by omega) h2p hstep
  -- `ψ_G(t) ≡ (−1)^(t+1) t (mod c)` from `G ≡ −1 (mod c)`
  have hGc : (G : ℤ) ≡ -1 [ZMOD c] := by
    rw [Int.modEq_iff_dvd, hGZ]
    obtain ⟨k, hk⟩ := hcf
    exact ⟨-2 * ((A : ℤ) ^ 2 - 1) * k, by rw [hk]; ring⟩
  have hyG : (yn hG1 t : ℤ) ≡ (-1) ^ (t + 1) * t [ZMOD c] := by
    rw [yn_eq_yr hG1]
    have := yr_modEq hGc t
    rw [show (-1 : ℤ) = -(1 : ℤ) by rfl, yr_neg, yr_one] at this
    exact this
  have hJt : (c : ℤ) ∣ (J : ℤ) - t ∨ (c : ℤ) ∣ (J : ℤ) + t := by
    have h1 := Int.modEq_iff_dvd.1 hyG
    have hJH : (J : ℤ) = yn hG1 t - j * c := by
      have := congrArg (Nat.cast : ℕ → ℤ) hHt; push_cast at this; linarith
    rcases Nat.even_or_odd t with ht | ht
    · right
      have e : (-1 : ℤ) ^ (t + 1) = -1 := by
        rw [pow_succ, ht.neg_one_pow]; ring
      rw [e] at h1
      rw [hJH]
      obtain ⟨k, hk⟩ := h1
      exact ⟨-k - j, by linarith⟩
    · left
      have e : (-1 : ℤ) ^ (t + 1) = 1 := by
        rw [pow_succ, ht.neg_one_pow]; ring
      rw [e] at h1
      rw [hJH]
      obtain ⟨k, hk⟩ := h1
      exact ⟨-k - j, by linarith⟩
  -- combine: `c ∣ J − p` or `c ∣ J + p`
  have hcm2 : (c : ℤ) ∣ (m : ℤ) := by exact_mod_cast hcm
  have hJp : (c : ℤ) ∣ (J : ℤ) - p ∨ (c : ℤ) ∣ (J : ℤ) + p := by
    rcases hsd with h1 | h1 <;> rcases hJt with h2 | h2
    · left
      rw [show (J : ℤ) - p = ((J : ℤ) - t) + ((t : ℤ) - p) by ring]
      exact dvd_add h2 (dvd_trans hcm2 h1)
    · right
      rw [show (J : ℤ) + p = ((J : ℤ) + t) - ((t : ℤ) - p) by ring]
      exact dvd_sub h2 (dvd_trans hcm2 h1)
    · right
      rw [show (J : ℤ) + p = ((J : ℤ) - t) + ((t : ℤ) + p) by ring]
      exact dvd_add h2 (dvd_trans hcm2 h1)
    · left
      rw [show (J : ℤ) - p = ((J : ℤ) + t) - ((t : ℤ) + p) by ring]
      exact dvd_sub h2 (dvd_trans hcm2 h1)
  have hpJ : p = J := by
    have hJZ : (1 : ℤ) < J := by exact_mod_cast hJ1
    have hJcZ : (J : ℤ) < c := by exact_mod_cast hJc
    have hpcZ : (p : ℤ) < c := by exact_mod_cast hpc
    have hp0Z : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
    have hc0Z : (0 : ℤ) ≤ c := by positivity
    rcases hJp with h | h
    · obtain ⟨k, hk⟩ := h
      have hk1 : k < 1 := lt_of_mul_lt_mul_left (by linarith : (c : ℤ) * k < c * 1) hc0Z
      have hk2 : -1 < k := lt_of_mul_lt_mul_left (by linarith : (c : ℤ) * (-1) < c * k) hc0Z
      have hk0 : k = 0 := by omega
      rw [hk0] at hk; omega
    · exfalso
      obtain ⟨k, hk⟩ := h
      have hk1 : k < 2 := lt_of_mul_lt_mul_left (by linarith : (c : ℤ) * k < c * 2) hc0Z
      have hk2 : 0 < k := lt_of_mul_lt_mul_left (by linarith : (c : ℤ) * 0 < c * k) hc0Z
      have hk1' : k = 1 := by omega
      rw [hk1', mul_one] at hk
      -- `J = c − p` is even since `c ≡ p (mod 2)`
      have hpar := yn_modEq_two hA p
      rw [← hcp] at hpar
      unfold Nat.ModEq at hpar
      obtain ⟨u, hu⟩ := hJodd
      omega
  subst hpJ
  exact ⟨hcp, hd⟩

/-- Sufficiency of the doubled-index signed block. -/
theorem doubled_index_sufficiency {A c d f i o j J : ℕ} (hA : 1 < A) (hJ1 : 1 < J) (hJc : J < c)
    (hJodd : Odd J) (hi : 0 < i)
    (E15 : d ^ 2 = 1 + (A ^ 2 - 1) * c ^ 2)
    (E16 : f ^ 2 = 1 + (A ^ 2 - 1) * i ^ 2 * c ^ 4)
    (E17 : ((o : ℤ) * f - d ^ 2) * ((o : ℤ) * f - d ^ 2 + 1) =
      (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1)) * (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1) - 1) *
        (J + j * c) ^ 2) :
    c = ψ hA J ∧ d = χ hA J := by
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hc : 0 < c := by omega
  obtain ⟨p, hd, hcp⟩ := eq_pell_of_sq hA E15
  obtain ⟨m, hf, hE⟩ : ∃ m, f = xn hA m ∧ i * c ^ 2 = yn hA m := by
    apply eq_pell_of_sq hA
    rw [E16]; ring
  have hcm : c ∣ m := by
    have : yn hA p * yn hA p ∣ yn hA m := by
      rw [← hcp, ← hE]; exact ⟨i, by ring⟩
    exact hcp ▸ dvd_of_ysq_dvd hA this
  have hf2 : 2 ≤ f := two_le_of_aux hA hi hc E16
  have hcf : (c : ℤ) ∣ (f : ℤ) ^ 2 - 1 := by
    have e : (f : ℤ) ^ 2 - 1 = ((A : ℤ) ^ 2 - 1) * i ^ 2 * c ^ 4 := by
      have := congrArg (Nat.cast : ℕ → ℤ) E16
      push_cast [Nat.cast_sub hA2] at this; linarith
    rw [e]; exact ⟨((A : ℤ) ^ 2 - 1) * i ^ 2 * c ^ 3, by ring⟩
  exact doubled_index_core hA hJ1 hJc hJodd hd hcp hf hcm hf2 hcf E17

/-- `c² ∣ ψ_A(2 c J)` for `c = ψ_A(J)`. -/
theorem sq_dvd_yn_two_mul {A J : ℕ} (hA : 1 < A) :
    yn hA J ^ 2 ∣ yn hA (2 * (J * yn hA J)) := by
  have h1 : yn hA J * yn hA J ∣ yn hA (J * yn hA J) := ysq_dvd_yy hA J
  have h2 : yn hA (J * yn hA J) ∣ yn hA (2 * (J * yn hA J)) := by
    rw [yn_two_mul hA (J * yn hA J)]; exact Dvd.intro_left _ rfl
  rw [sq]; exact dvd_trans h1 h2

/-- Necessity: the positive witnesses of the doubled-index block. -/
theorem doubled_index_necessity {A J : ℕ} (hA : 1 < A) (hJ1 : 1 < J) (hJodd : Odd J) :
    ∃ f i o j : ℕ, 0 < f ∧ 0 < i ∧ 0 < o ∧ 0 < j ∧
      f ^ 2 = 1 + (A ^ 2 - 1) * i ^ 2 * (yn hA J) ^ 4 ∧
      ((o : ℤ) * f - (xn hA J : ℤ) ^ 2) * ((o : ℤ) * f - (xn hA J : ℤ) ^ 2 + 1) =
        (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1)) * (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1) - 1) *
          (J + j * yn hA J) ^ 2 := by
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨c, hc⟩ : ∃ c, c = yn hA J := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = xn hA J := ⟨_, rfl⟩
  have hc2 : 2 ≤ c := by
    have := lt_yn_of_two_le hA (n := J) (by omega); omega
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * (J * c) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = xn hA m := ⟨_, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, yn hA m = i * c ^ 2 := by
    obtain ⟨i, hi⟩ := sq_dvd_yn_two_mul hA (J := J)
    exact ⟨i, by rw [hm, hc, hi]; ring⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  have hi0 : 0 < i := by
    have : 0 < yn hA m := JSWW1976.ψ_pos_of_pos hA hm0
    rw [hi] at this
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0] at this; simp at this
    · exact h0
  have hf0 : 0 < f := by rw [hf]; exact xn_pos' hA m
  -- E16
  have E16 : f ^ 2 = 1 + (A ^ 2 - 1) * i ^ 2 * c ^ 4 := by
    have := χ_sq hA m
    simp only [Diophantine.χ, Diophantine.ψ] at this
    rw [← hf, hi] at this
    rw [sq, this, sq A]
    ring
  -- `f` is odd
  have hfodd : f % 2 = 1 := by
    have := xn_two_mul hA (J * c)
    rw [← hm, ← hf] at this
    omega
  have hf2 : 2 ≤ f := two_le_of_aux hA hi0 (by omega) E16
  obtain ⟨G, hG⟩ : ∃ G, G = 2 * ((A ^ 2 - 1) * (f ^ 2 - 1)) - 1 := ⟨_, rfl⟩
  obtain ⟨hG1, hGZ⟩ := aux_param hA hf2
  rw [← hG] at hG1 hGZ
  have hGodd : Odd (G : ℤ) := by
    rw [hGZ]; exact ⟨((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1) - 1, by ring⟩
  obtain ⟨I, hI⟩ : ∃ I, I = xn hG1 J := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = yn hG1 J := ⟨_, rfl⟩
  -- `I ≡ 1 − 2d² (mod f)`
  have hGf : (G : ℤ) ≡ -(xn hA 2 : ℤ) [ZMOD f] := by
    rw [Int.modEq_iff_dvd, hGZ, xn_two hA]
    exact ⟨-2 * ((A : ℤ) ^ 2 - 1) * f, by ring⟩
  have hIf : (I : ℤ) ≡ 1 - 2 * (d : ℤ) ^ 2 [ZMOD f] := by
    have h1 : (xn hG1 J : ℤ) ≡ (-1) ^ J * xn hA (2 * J) [ZMOD f] := by
      rw [xn_eq_xr hG1, xn_two_mul_eq_xr hA J, ← xr_neg]
      exact xr_modEq hGf J
    rw [hJodd.neg_one_pow, neg_one_mul] at h1
    have hx2J : (xn hA (2 * J) : ℤ) = 2 * (d : ℤ) ^ 2 - 1 := by
      have := xn_two_mul hA J; rw [← hd] at this; exact this
    rw [hx2J, ← hI] at h1
    have e : -(2 * (d : ℤ) ^ 2 - 1) = 1 - 2 * d ^ 2 := by ring
    rw [e] at h1; exact h1
  have hIodd : Odd (I : ℤ) := by
    rw [hI, xn_eq_xr hG1]; exact xr_odd hGodd J
  -- `2f ∣ I + 2d² − 1`
  have hdiv : (2 * (f : ℤ)) ∣ (I : ℤ) + 2 * d ^ 2 - 1 := by
    have h1 : (f : ℤ) ∣ (I : ℤ) + 2 * d ^ 2 - 1 := by
      have := Int.modEq_iff_dvd.1 hIf
      have e : (I : ℤ) + 2 * d ^ 2 - 1 = -((1 - 2 * (d : ℤ) ^ 2) - I) := by ring
      rw [e]; exact dvd_neg.2 this
    have h2 : (2 : ℤ) ∣ (I : ℤ) + 2 * d ^ 2 - 1 := by
      obtain ⟨u, hu⟩ := hIodd
      exact ⟨u + d ^ 2, by rw [hu]; ring⟩
    have hcop : IsCoprime (2 : ℤ) (f : ℤ) := by
      have hfZ : (f : ℤ) = 2 * ((f / 2 : ℕ) : ℤ) + 1 := by omega
      refine ⟨-((f / 2 : ℕ) : ℤ), 1, ?_⟩
      rw [hfZ]; ring
    exact hcop.mul_dvd h2 h1
  obtain ⟨oZ, hoZ⟩ := hdiv
  have hI1 : 1 ≤ I := by rw [hI]; exact xn_pos' hG1 J
  have hd1 : 1 ≤ d := by rw [hd]; exact xn_pos' hA J
  have hoZpos : 0 < oZ := by
    have hpos : (0 : ℤ) < (I : ℤ) + 2 * d ^ 2 - 1 := by
      have : (1 : ℤ) ≤ I := by exact_mod_cast hI1
      have : (1 : ℤ) ≤ d := by exact_mod_cast hd1
      nlinarith
    rw [hoZ] at hpos
    have hf' : (0 : ℤ) < 2 * f := by positivity
    exact pos_of_mul_pos_right hpos hf'.le
  obtain ⟨o, ho⟩ : ∃ o : ℕ, (o : ℤ) = oZ := ⟨oZ.toNat, Int.toNat_of_nonneg hoZpos.le⟩
  have ho0 : 0 < o := by omega
  -- `H ≡ J (mod c)` and `H > J`
  have hcf : (c : ℤ) ∣ (f : ℤ) ^ 2 - 1 := by
    have e : (f : ℤ) ^ 2 - 1 = ((A : ℤ) ^ 2 - 1) * i ^ 2 * c ^ 4 := by
      have := congrArg (Nat.cast : ℕ → ℤ) E16
      push_cast [Nat.cast_sub hA2] at this; linarith
    rw [e]; exact ⟨((A : ℤ) ^ 2 - 1) * i ^ 2 * c ^ 3, by ring⟩
  have hGc : (G : ℤ) ≡ -1 [ZMOD c] := by
    rw [Int.modEq_iff_dvd, hGZ]
    obtain ⟨k, hk⟩ := hcf
    exact ⟨-2 * ((A : ℤ) ^ 2 - 1) * k, by rw [hk]; ring⟩
  have hHJ : (c : ℤ) ∣ (H : ℤ) - J := by
    have h1 : (yn hG1 J : ℤ) ≡ (-1) ^ (J + 1) * J [ZMOD c] := by
      rw [yn_eq_yr hG1]
      have := yr_modEq hGc J
      rw [show (-1 : ℤ) = -(1 : ℤ) by rfl, yr_neg, yr_one] at this
      exact this
    have e : (-1 : ℤ) ^ (J + 1) = 1 := by
      rw [pow_succ, hJodd.neg_one_pow]; ring
    rw [e, one_mul, ← hH] at h1
    have := Int.modEq_iff_dvd.1 h1
    have e2 : (H : ℤ) - J = -((J : ℤ) - H) := by ring
    rw [e2]; exact dvd_neg.2 this
  have hHgt : J < H := by rw [hH]; exact lt_yn_of_two_le hG1 (by omega)
  obtain ⟨jZ, hjZ⟩ := hHJ
  have hjZpos : 0 < jZ := by
    have hpos : (0 : ℤ) < (H : ℤ) - J := by
      have : (J : ℤ) < H := by exact_mod_cast hHgt
      linarith
    rw [hjZ] at hpos
    have hc' : (0 : ℤ) < c := by positivity
    exact pos_of_mul_pos_right hpos hc'.le
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = jZ := ⟨jZ.toNat, Int.toNat_of_nonneg hjZpos.le⟩
  have hj0 : 0 < j := by omega
  refine ⟨f, i, o, j, hf0, hi0, ho0, hj0, ?_, ?_⟩
  · rw [← hc]; exact E16
  -- E17
  rw [← hc, ← hd]
  have hHJ' : (J : ℤ) + j * c = H := by rw [hj]; linarith
  have hIH : (I : ℤ) ^ 2 = ((G : ℤ) ^ 2 - 1) * H ^ 2 + 1 := by
    have := χ_sq hG1 J
    simp only [Diophantine.χ, Diophantine.ψ] at this
    rw [← hI, ← hH] at this
    have e := congrArg (Nat.cast : ℕ → ℤ) this
    have hG2 : 1 ≤ G * G := Nat.one_le_iff_ne_zero.2 (by positivity)
    push_cast [Nat.cast_sub hG2] at e
    linear_combination e
  rw [hHJ']
  -- with `2(of − d²) = I − 1`
  have hv : 2 * ((o : ℤ) * f - d ^ 2) = I - 1 := by rw [ho]; linarith
  have hG' : 2 * (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1)) = G + 1 := by rw [hGZ]; ring
  have key : 4 * (((o : ℤ) * f - d ^ 2) * ((o : ℤ) * f - d ^ 2 + 1)) =
      4 * ((((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1)) * (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1) - 1) * H ^ 2) := by
    have l1 : 4 * (((o : ℤ) * f - d ^ 2) * ((o : ℤ) * f - d ^ 2 + 1)) = (I : ℤ) ^ 2 - 1 := by
      linear_combination (2 * ((o : ℤ) * f - d ^ 2) + I + 1) * hv
    have l2 : 4 * ((((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1)) * (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1) - 1)) =
        (G : ℤ) ^ 2 - 1 := by
      linear_combination (2 * (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1)) - 1 + G) * hG'
    rw [l1]
    calc (I : ℤ) ^ 2 - 1 = ((G : ℤ) ^ 2 - 1) * H ^ 2 := by rw [hIH]; ring
      _ = _ := by rw [← l2]; ring
  linarith [key]

end Jones1980
