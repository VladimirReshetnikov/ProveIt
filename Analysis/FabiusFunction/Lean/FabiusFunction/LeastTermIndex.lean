import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The least term of a Gevrey-1 series, and where it sits

The transseries volume's `p0:thm:optimal-truncation` bounds the error of an
asymptotic series with the Gevrey-1 coefficient growth
`|q_M| ≍ K Γ(M+β) A^{-M}` by truncating at `M(x) = ⌊Ax⌋`, and concludes that no
truncation does better than `e^{-Ax}` — the exponential floor.

Part (1) of that theorem, the envelope `K' x^{β-1/2} e^{-Ax}`, needs Stirling's
formula for `Γ(M+β)`.  The *choice* of `M(x)` does not, and neither does the
fact that the choice is optimal.  Both come from a one-line ratio law:

`T(M+1) / T(M) = (M + β) / (Ax)`,   `T(M) := Γ(M+β) / (Ax)^M`,

so the terms strictly decrease while `M + β < Ax` and strictly increase once
`M + β > Ax`.  The least term therefore sits where `M + β` crosses `Ax`, which
is `M(x) = ⌊Ax⌋` up to the shift `β`, and the sequence is unimodal — there is no
second, better, minimum further out.  That is the whole mechanism of optimal
truncation, and it is exact rather than asymptotic.

This module proves that.  It says nothing about the *size* of the least term,
which is where Stirling and the exponential floor live.

## Main results

* `Fabius.gevreyTerm`: `T(M) = Γ(M+β) / (Ax)^M`.
* `Fabius.gevreyTerm_succ`: the ratio law.
* `Fabius.gevreyTerm_succ_lt`: strict decrease below the crossing.
* `Fabius.gevreyTerm_lt_succ`: strict increase above it.
* `Fabius.gevreyTerm_antitoneOn` / `Fabius.gevreyTerm_monotoneOn`: the two
  monotone stretches, hence unimodality.

Not formalized here: the envelope `p0:eq:least-term`, the transported inverse
error `p0:eq:optimal-inverse`, and the floor `p0:eq:floor` — all three need
Stirling asymptotics for `Γ(M+β)`.
-/

set_option autoImplicit false

namespace Fabius

/-- The Gevrey-1 term profile `T(M) = Γ(M+β) / (Ax)^M`.  The variable `s` plays
the role of `Ax`. -/
noncomputable def gevreyTerm (β s : ℝ) (M : ℕ) : ℝ := Real.Gamma (M + β) / s ^ M

/-- The ratio law: `T(M+1) = T(M) · (M+β)/s`.  Everything below is a consequence
of this identity together with positivity of `Γ`. -/
theorem gevreyTerm_succ {β s : ℝ} (hs : s ≠ 0) {M : ℕ} (hM : (M : ℝ) + β ≠ 0) :
    gevreyTerm β s (M + 1) = gevreyTerm β s M * (((M : ℝ) + β) / s) := by
  simp only [gevreyTerm]
  push_cast
  rw [show (M : ℝ) + 1 + β = ((M : ℝ) + β) + 1 from by ring, Real.Gamma_add_one hM, pow_succ]
  field_simp

theorem gevreyTerm_pos {β s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 0 < (M : ℝ) + β) :
    0 < gevreyTerm β s M := by
  rw [gevreyTerm]
  exact div_pos (Real.Gamma_pos_of_pos hM) (pow_pos hs M)

/-- Below the crossing point the terms strictly decrease. -/
theorem gevreyTerm_succ_lt {β s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 0 < (M : ℝ) + β)
    (hlt : (M : ℝ) + β < s) :
    gevreyTerm β s (M + 1) < gevreyTerm β s M := by
  have hpos := gevreyTerm_pos hs hM
  rw [gevreyTerm_succ hs.ne' hM.ne']
  have hratio : ((M : ℝ) + β) / s < 1 := (div_lt_one hs).mpr hlt
  nlinarith

/-- Above the crossing point the terms strictly increase. -/
theorem gevreyTerm_lt_succ {β s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 0 < (M : ℝ) + β)
    (hlt : s < (M : ℝ) + β) :
    gevreyTerm β s M < gevreyTerm β s (M + 1) := by
  have hpos := gevreyTerm_pos hs hM
  rw [gevreyTerm_succ hs.ne' hM.ne']
  have hratio : 1 < ((M : ℝ) + β) / s := (one_lt_div hs).mpr hlt
  nlinarith

/-- On the stretch where `M + β ≤ s` the profile is antitone: truncating later
always helps, up to the crossing. -/
theorem gevreyTerm_antitoneOn {β s : ℝ} (hs : 0 < s) (hβ : 0 < β) {N : ℕ}
    (hN : (N : ℝ) + β ≤ s) :
    ∀ i j : ℕ, i ≤ j → j ≤ N → gevreyTerm β s j ≤ gevreyTerm β s i := by
  intro i j
  induction j with
  | zero =>
      intro hij _
      have hi : i = 0 := Nat.le_zero.mp hij
      subst hi
      exact le_rfl
  | succ k ih =>
      intro hij hjN
      rcases Nat.eq_or_lt_of_le hij with h | h
      · subst h
        exact le_rfl
      · have hik : i ≤ k := Nat.lt_succ_iff.mp h
        have hkN : k ≤ N := Nat.le_of_succ_le hjN
        have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hkpos : 0 < (k : ℝ) + β := by linarith
        have hk1 : ((k : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast hjN
        have hklt : (k : ℝ) + β < s := by linarith
        exact le_trans (le_of_lt (gevreyTerm_succ_lt hs hkpos hklt)) (ih hik hkN)

/-- On the stretch where `s ≤ M + β` the profile is monotone: past the crossing,
truncating later always hurts.  Together with `gevreyTerm_antitoneOn` this is
unimodality — there is no second, better, minimum further out. -/
theorem gevreyTerm_monotoneOn {β s : ℝ} (hs : 0 < s) (hβ : 0 < β) {N : ℕ}
    (hN : s < (N : ℝ) + β) :
    ∀ i j : ℕ, N ≤ i → i ≤ j → gevreyTerm β s i ≤ gevreyTerm β s j := by
  intro i j
  induction j with
  | zero =>
      intro _ hij
      have hi : i = 0 := Nat.le_zero.mp hij
      subst hi
      exact le_rfl
  | succ k ih =>
      intro hNi hij
      rcases Nat.eq_or_lt_of_le hij with h | h
      · subst h
        exact le_rfl
      · have hik : i ≤ k := Nat.lt_succ_iff.mp h
        have hNk : N ≤ k := le_trans hNi hik
        have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hkpos : 0 < (k : ℝ) + β := by linarith
        have hNkR : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hNk
        have hklt : s < (k : ℝ) + β := by linarith
        exact le_trans (ih hNi hik) (le_of_lt (gevreyTerm_lt_succ hs hkpos hklt))

end Fabius
