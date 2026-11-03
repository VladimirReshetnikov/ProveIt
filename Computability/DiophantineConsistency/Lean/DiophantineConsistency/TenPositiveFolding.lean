import DiophantineConsistency.SignedPellResidue
import Diophantine.Common.PellMod

/-! # The signed all-index folding theorem (stage K4, over ℤ)

Package 163 (`compact/PROOF.md` §3, eq. (3.4)) recovers the omitted main
Pell root from the strong and auxiliary equations alone:

  if `A ≥ 3`, `0 < c ≤ I`, `f² − (A² − 1) I² = 1`, `S = (A² − 1) I`,
  `S² V² − (S² − 1) y² = 1` and `V ≡ −c (mod f)`, then `c = ψ_A(p)` with `p` odd.

The inherited proof (`candidates/ten-positive-zero-offset/source/QUADRATIC_PROOF.md`,
Lemmas 2.1–2.2, with the odd-index addendum of `FREE_J_PROOF.md`) uses the
odd quotient polynomials `χ_Z(2h+1) = Z Q_h(Z²)`. Here they are replaced by
one two-step recurrence: both `χ_S(2h+1) / S` and `(−1)^h ψ_A(2h+1)` equal
`x_z(h) + (z − 1) y_z(h)` for the integer-parameter Pell recurrences of
`Diophantine.Common.PellInt`, at `z = 2S² − 1` and `z = 1 − 2A²`
respectively. These parameters are congruent modulo `f`, so `xr_modEq` and
`yr_modEq` compare the two sequences.
-/
set_option autoImplicit false
namespace DiophantineConsistency.TenPositiveFolding
open Pell Diophantine

section Sequences
variable {a : ℕ} (a1 : 1 < a)

theorem xn_two_int : (xn a1 2 : ℤ) = 2 * (a : ℤ) ^ 2 - 1 := by
  have h := xr_succ_succ (a : ℤ) 0
  simp only [zero_add, xr_one', xr_zero] at h
  rw [xn_eq_xr, h]
  ring

/-- `χ_a(2h+1) = a (x_z(h) + (z − 1) y_z(h))` with `z = 2a² − 1`. -/
theorem xn_odd_eq : ∀ h : ℕ, (xn a1 (2 * h + 1) : ℤ) =
    a * (xr (2 * (a : ℤ) ^ 2 - 1) h + (2 * (a : ℤ) ^ 2 - 1 - 1) * yr (2 * (a : ℤ) ^ 2 - 1) h) := by
  refine two_step ?_ ?_ ?_
  · simp
  · have h3 : (xn a1 (2 * 1 + 1) : ℤ) = xn a1 3 := rfl
    rw [h3, xr_one', yr_one']
    have r := xn_eq_xr a1 3
    have r2 := xr_succ_succ (a : ℤ) 1
    have r1 := xr_succ_succ (a : ℤ) 0
    simp only [zero_add, xr_one', xr_zero, Nat.reduceAdd] at r1 r2
    rw [r, r2, r1]
    ring
  · intro t h1 h2
    have e := xn_add_two_add_sub_two a1 (m := 2 * (t + 1) + 1) (by omega)
    rw [show 2 * (t + 1) + 1 + 2 = 2 * (t + 2) + 1 by ring,
      show 2 * (t + 1) + 1 - 2 = 2 * t + 1 by omega, xn_two_int, h1, h2] at e
    rw [xr_succ_succ, yr_succ_succ]
    linear_combination e

/-- `(−1)^h ψ_a(2h+1) = x_z(h) + (z − 1) y_z(h)` with `z = 1 − 2a²`. -/
theorem yn_odd_eq : ∀ h : ℕ, (-1 : ℤ) ^ h * (yn a1 (2 * h + 1) : ℤ) =
    xr (1 - 2 * (a : ℤ) ^ 2) h + (1 - 2 * (a : ℤ) ^ 2 - 1) * yr (1 - 2 * (a : ℤ) ^ 2) h := by
  refine two_step ?_ ?_ ?_
  · simp
  · have r := yn_eq_yr a1 3
    have r2 := yr_succ_succ (a : ℤ) 1
    have r1 := yr_succ_succ (a : ℤ) 0
    simp only [zero_add, yr_one', yr_zero, Nat.reduceAdd] at r1 r2
    have h3 : (yn a1 (2 * 1 + 1) : ℤ) = yn a1 3 := rfl
    rw [h3, r, r2, r1, xr_one', yr_one']
    ring
  · intro t h1 h2
    have e := yn_add_two_add_sub_two a1 (m := 2 * (t + 1) + 1) (by omega)
    rw [show 2 * (t + 1) + 1 + 2 = 2 * (t + 2) + 1 by ring,
      show 2 * (t + 1) + 1 - 2 = 2 * t + 1 by omega, xn_two_int] at e
    rw [xr_succ_succ, yr_succ_succ]
    rw [pow_succ] at h2
    rw [pow_succ, pow_succ]
    linear_combination (-1 : ℤ) ^ t * e - h1 - 2 * (2 * (a : ℤ) ^ 2 - 1) * h2

/-- Folding of `ψ` modulo `χ_m`: every index `v` is congruent, up to sign,
to an index `p ≤ m` of the same parity. -/
theorem fold (m : ℕ) (hm : 1 ≤ m) : ∀ v : ℕ, ∃ p, p ≤ m ∧ p % 2 = v % 2 ∧
    ((xn a1 m : ℤ) ∣ (yn a1 v : ℤ) - yn a1 p ∨ (xn a1 m : ℤ) ∣ (yn a1 v : ℤ) + yn a1 p) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  by_cases hv : 2 * m ≤ v
  · obtain ⟨j, rfl⟩ : ∃ j, v = 2 * m + j := ⟨v - 2 * m, by omega⟩
    obtain ⟨p, hp, hpar, hd⟩ := ih j (by omega)
    have hdiv : (xn a1 m : ℤ) ∣ (yn a1 (2 * m + j) : ℤ) + yn a1 j := by
      exact_mod_cast xn_dvd_yn_two_mul_add a1 m j
    refine ⟨p, hp, by omega, ?_⟩
    rcases hd with hd | hd
    · right
      have e : (yn a1 (2 * m + j) : ℤ) + yn a1 p =
          ((yn a1 (2 * m + j) : ℤ) + yn a1 j) - ((yn a1 j : ℤ) - yn a1 p) := by ring
      rw [e]; exact dvd_sub hdiv hd
    · left
      have e : (yn a1 (2 * m + j) : ℤ) - yn a1 p =
          ((yn a1 (2 * m + j) : ℤ) + yn a1 j) - ((yn a1 j : ℤ) + yn a1 p) := by ring
      rw [e]; exact dvd_sub hdiv hd
  · by_cases hv' : v ≤ m
    · exact ⟨v, hv', rfl, Or.inl (by simp)⟩
    · obtain ⟨r, rfl⟩ : ∃ r, v = m + r := ⟨v - m, by omega⟩
      have hr : r ≤ m := by omega
      refine ⟨m - r, by omega, by omega, Or.inl ⟨2 * yn a1 r, ?_⟩⟩
      have h' : (yn a1 (m + r) : ℤ) = yn a1 (m - r) + 2 * xn a1 m * yn a1 r := by
        exact_mod_cast yn_reflect a1 hr
      rw [h']; ring

end Sequences

theorem dvd_comb {f x y z : ℤ} (hx : f ∣ x) (hy : f ∣ y) (k l : ℤ) (h : z = k * x + l * y) :
    f ∣ z :=
  h ▸ dvd_add (dvd_mul_of_dvd_right hx k) (dvd_mul_of_dvd_right hy l)

/-- Strong classification: `f² − (A² − 1) I² = 1` gives `f = χ_A(m)`, `I = ψ_A(m)`. -/
theorem classify_strong {A : ℕ} (a1 : 1 < A) {f I : ℕ}
    (hstrong : (f : ℤ) ^ 2 - ((A : ℤ) ^ 2 - 1) * (I : ℤ) ^ 2 = 1) :
    ∃ m, f = xn a1 m ∧ I = yn a1 m := by
  have hAA : 1 ≤ A * A := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine Pell.eq_pell a1 (x := f) (y := I) ?_
  change f * f - (A * A - 1) * I * I = 1
  have hn : f * f = (A * A - 1) * I * I + 1 := by
    have : ((f * f : ℕ) : ℤ) = (((A * A - 1) * I * I + 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hAA]
      linear_combination hstrong
    exact_mod_cast this
  omega

/-- Auxiliary classification at a Pell parameter `S > 1`: `|V|` is the odd
quotient `χ_S(2h+1) / S`. -/
theorem classify_aux {S : ℕ} (aS : 1 < S) {V y : ℤ}
    (haux : (S : ℤ) ^ 2 * V ^ 2 - ((S : ℤ) ^ 2 - 1) * y ^ 2 = 1) :
    ∃ h, |V| = xr (2 * (S : ℤ) ^ 2 - 1) h +
      (2 * (S : ℤ) ^ 2 - 1 - 1) * yr (2 * (S : ℤ) ^ 2 - 1) h := by
  have hSS : 1 ≤ S * S := Nat.one_le_iff_ne_zero.mpr (by positivity)
  obtain ⟨v, hxv, -⟩ := Pell.eq_pell aS (x := S * V.natAbs) (y := y.natAbs) (by
    change (S * V.natAbs) * (S * V.natAbs) - (S * S - 1) * y.natAbs * y.natAbs = 1
    have hn : (S * V.natAbs) * (S * V.natAbs) = (S * S - 1) * y.natAbs * y.natAbs + 1 := by
      have : (((S * V.natAbs) * (S * V.natAbs) : ℕ) : ℤ) =
          (((S * S - 1) * y.natAbs * y.natAbs + 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hSS]
        have hv2 : |V| ^ 2 = V ^ 2 := sq_abs V
        have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
        linear_combination haux + (S : ℤ) ^ 2 * hv2 - ((S : ℤ) ^ 2 - 1) * hy2
      exact_mod_cast this
    omega)
  have hd : S ∣ xn aS v := by rw [← hxv]; exact dvd_mul_right S V.natAbs
  obtain ⟨h, hh⟩ := SignedPellResidue.odd_index_of_base_dvd aS hd
  refine ⟨h, ?_⟩
  have hU := xn_odd_eq aS h
  rw [← hh, ← hxv] at hU
  push_cast at hU
  have hSne : (S : ℤ) ≠ 0 := by positivity
  exact mul_left_cancel₀ hSne hU

/-- The odd quotient at `S = (A² − 1) I` is `±ψ_A(2h+1)` modulo `f`, so
`V ≡ −c` gives `ψ_A(2h+1) ≡ ±c`. -/
theorem psi_pm {A : ℕ} (a1 : 1 < A) {S f I c : ℕ} {V : ℤ} (h : ℕ)
    (hSZ : (S : ℤ) = ((A : ℤ) ^ 2 - 1) * I)
    (hstrong : (f : ℤ) ^ 2 - ((A : ℤ) ^ 2 - 1) * (I : ℤ) ^ 2 = 1)
    (hV : (f : ℤ) ∣ V + c)
    (hVabs : |V| = xr (2 * (S : ℤ) ^ 2 - 1) h +
      (2 * (S : ℤ) ^ 2 - 1 - 1) * yr (2 * (S : ℤ) ^ 2 - 1) h) :
    (f : ℤ) ∣ (yn a1 (2 * h + 1) : ℤ) - c ∨ (f : ℤ) ∣ (yn a1 (2 * h + 1) : ℤ) + c := by
  have hz : 2 * (S : ℤ) ^ 2 - 1 ≡ 1 - 2 * (A : ℤ) ^ 2 [ZMOD f] := by
    refine Int.modEq_iff_dvd.mpr ⟨-2 * ((A : ℤ) ^ 2 - 1) * f, ?_⟩
    rw [hSZ]
    linear_combination (2 * ((A : ℤ) ^ 2 - 1)) * hstrong
  have hW : |V| ≡ (-1 : ℤ) ^ h * (yn a1 (2 * h + 1) : ℤ) [ZMOD f] := by
    rw [hVabs, yn_odd_eq a1 h]
    exact (xr_modEq hz h).add (((hz.sub_right 1)).mul (yr_modEq hz h))
  have hW' := Int.modEq_iff_dvd.mp hW
  rcases neg_one_pow_eq_or ℤ h with hs | hs <;> rw [hs] at hW' <;>
    rcases abs_choice V with hv | hv <;> rw [hv] at hW'
  · right; exact dvd_comb hW' hV 1 1 (by ring)
  · left; exact dvd_comb hW' hV 1 (-1) (by ring)
  · left; exact dvd_comb hW' hV (-1) (-1) (by ring)
  · right; exact dvd_comb hW' hV (-1) 1 (by ring)

/-- `f > 2I` from the strong norm when `A ≥ 3`. -/
theorem two_I_lt_f {A f I : ℕ} (hA : 3 ≤ A)
    (hstrong : (f : ℤ) ^ 2 - ((A : ℤ) ^ 2 - 1) * (I : ℤ) ^ 2 = 1) : 2 * (I : ℤ) < f := by
  have h3 : (3 : ℤ) ≤ A := by exact_mod_cast hA
  have h8 : (8 : ℤ) ≤ (A : ℤ) ^ 2 - 1 := by nlinarith only [h3]
  have hsq : (2 * (I : ℤ)) ^ 2 < (f : ℤ) ^ 2 := by
    nlinarith only [hstrong, mul_le_mul_of_nonneg_right h8 (sq_nonneg (I : ℤ))]
  have hf0 : (0 : ℤ) ≤ f := by positivity
  by_contra hc
  push_neg at hc
  nlinarith only [hsq, hc, hf0]

/-- **The signed all-index folding theorem.** -/
theorem folding {A : ℕ} (hA : 3 ≤ A) {c I f : ℕ} {V y : ℤ}
    (hc : 0 < c) (hcI : c ≤ I)
    (hstrong : (f : ℤ) ^ 2 - ((A : ℤ) ^ 2 - 1) * (I : ℤ) ^ 2 = 1)
    (haux : (((A : ℤ) ^ 2 - 1) * I) ^ 2 * V ^ 2 - ((((A : ℤ) ^ 2 - 1) * I) ^ 2 - 1) * y ^ 2 = 1)
    (hV : (f : ℤ) ∣ V + c) :
    ∃ p, Odd p ∧ c = yn (show 1 < A by omega) p := by
  have a1 : 1 < A := by omega
  have hAA : 1 ≤ A * A := by nlinarith
  have hI : 0 < I := lt_of_lt_of_le hc hcI
  obtain ⟨m, hfm, hIm⟩ := classify_strong a1 hstrong
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hIm; omega
    · exact h0
  obtain ⟨S, hS⟩ : ∃ S : ℕ, S = (A * A - 1) * I := ⟨_, rfl⟩
  have hSZ : (S : ℤ) = ((A : ℤ) ^ 2 - 1) * I := by
    rw [hS]; push_cast [Nat.cast_sub hAA]; ring
  have aS : 1 < S := by
    have h8 : 8 ≤ A * A - 1 := by
      have : 9 ≤ A * A := Nat.mul_le_mul hA hA
      omega
    have : 8 ≤ S := by rw [hS]; exact le_trans h8 (Nat.le_mul_of_pos_right _ hI)
    omega
  rw [← hSZ] at haux
  obtain ⟨h, hVabs⟩ := classify_aux aS haux
  have hpm := psi_pm a1 h hSZ hstrong hV hVabs
  obtain ⟨p, hpm', hpar, hfold⟩ := fold a1 m hm (2 * h + 1)
  rw [← hfm] at hfold
  have hpI : yn a1 p ≤ I := hIm ▸ (strictMono_y a1).monotone hpm'
  have hf2 := two_I_lt_f hA hstrong
  have key : (f : ℤ) ∣ (yn a1 p : ℤ) - c ∨ (f : ℤ) ∣ (yn a1 p : ℤ) + c := by
    rcases hpm with h1 | h1 <;> rcases hfold with h2 | h2
    · left; exact dvd_comb h1 h2 1 (-1) (by ring)
    · right; exact dvd_comb h1 h2 (-1) 1 (by ring)
    · right; exact dvd_comb h1 h2 1 (-1) (by ring)
    · left; exact dvd_comb h1 h2 (-1) 1 (by ring)
  have hpI' : (yn a1 p : ℤ) ≤ I := by exact_mod_cast hpI
  have hcI' : (c : ℤ) ≤ I := by exact_mod_cast hcI
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have hp0 : (0 : ℤ) ≤ yn a1 p := by positivity
  rcases key with k | k
  · have h0 := Int.eq_zero_of_abs_lt_dvd k (by rw [abs_lt]; constructor <;> linarith)
    refine ⟨p, ?_, ?_⟩
    · rw [Nat.odd_iff, hpar]; omega
    · have : (yn a1 p : ℤ) = c := by linarith
      exact_mod_cast this.symm
  · have h0 := Int.eq_zero_of_abs_lt_dvd k (by rw [abs_lt]; constructor <;> linarith)
    exfalso; linarith

end DiophantineConsistency.TenPositiveFolding
