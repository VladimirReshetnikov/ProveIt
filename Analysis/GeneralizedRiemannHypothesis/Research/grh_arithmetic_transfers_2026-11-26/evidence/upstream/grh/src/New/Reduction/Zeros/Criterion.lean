import Lib.Analytic.Landau
import Lib.Analytic.QuadraticTwist
import New.Reduction.Zeros.PrimeError

/-!
# The one-sided criterion for a zero-free half-plane

`New.LFunction_ne_zero_of_primeRemainder_le`: an eventual upper bound `R_q(x) ≤ x ^ (β - 1)` for the
remainder of a sum over prime powers `≡ 1` mod `q` with weights depending on a prime `d`, for all
`d` of a suitable class, excludes zeros `s ≠ 1` of the `L(s, ψ)`, `ψ` mod `q`, in `re s > β`.

Notions from other files:
* `primeRemainder d q x`: the remainder `R_q(x) = ∑_{n ≤ x} λ(n) (1/n - 1/x) - log x / φ(q) - c_q`,
  where `λ(n) = Λ(n) (1 - (n/d))` for `n ≡ 1` mod `q` and `0` otherwise, and `c_q` is a constant.
* `entireL ψ`: the entire function `L(s, ψ)`, times `s - 1` if `ψ` is principal.
* `quadTwist ψ d`: the product of `ψ` and the Legendre symbol `(·/d)`.
* `IsPolar E r`: the transform `∫₀^∞ E(v) e^{(1-s)v} dv` continues meromorphically, with at most
  simple poles in `re s > 0` and residues `r`.

## Relation to the literature

The hypotheses concern only the remainders, for all primes `d` of the class, and not the real zeros
of the `L(s, ψ)`. In the literature: a one-sided bound for a weighted sum over primes `≡ 1` modulo
`q` gives a zero-free half-plane if there are no real zeros. Related work: M. Suzuki, On variants of
Chebyshev's conjecture, arXiv 2411.07436, 2024; Montgomery–Vaughan, Multiplicative Number Theory I,
§15.1–15.2, 2007; Landau, Über einen Satz von Tschebyschef, 1905.
-/

open Complex Filter Nat Real Set MeasureTheory Topology

/-- **One-sided criterion.** Let `q₀` be a positive multiple of `8`, let `d₀ ≡ 7` mod `8` be prime
to `q₀`, and let `β > 1/2`. Suppose that for each prime `d ≡ d₀` mod `q₀` the remainder
`primeRemainder d q₀ x = ∑_{n ≤ x} λ(n) (1/n - 1/x) - log x / φ(q₀) - c` is at most `x ^ (β - 1)`
for all large `x`; here `λ(n) = Λ(n) (1 - (n/d))` for `n ≡ 1` mod `q₀` and `0` otherwise, and `c` is
the constant for which the remainder tends to `0`. Then `L(ρ, ψ) ≠ 0` for every character `ψ` modulo
`q₀` and every `ρ ≠ 1` with `re ρ > β`. -/
theorem New.LFunction_ne_zero_of_primeRemainder_le {q₀ : ℕ} [NeZero q₀] (hq₀ : 8 ∣ q₀) {d₀ : ℕ}
    (hd₀_mod : d₀ % 8 = 7) (hd₀_cop : d₀.Coprime q₀) {β : ℝ} (hβ : 1 / 2 < β)
    (h_bound : ∀ d : Primes, (d : ℕ) ≡ d₀ [MOD q₀] →
      ∀ᶠ x : ℝ in atTop, primeRemainder d q₀ x ≤ x ^ (β - 1))
    (ψ : DirichletCharacter ℂ q₀) {ρ : ℂ} (hρ_ne : ρ ≠ 1) (hρ_re : β < ρ.re) :
    ψ.LFunction ρ ≠ 0 := by
  -- Choose `d` with no twisted zero in `β ≤ re s`, `|im s| ≤ |im ρ|`. There the residue `r s` of
  -- the transform of the remainder (`IsPolar`) is `n(s) / (φ(q₀) s (1 - s))`, with `n(s)` the sum
  -- of the orders at `s` of the `entireL χ` (`L(s, χ)`, times `s - 1` for principal `χ`), `χ` mod
  -- `q₀`. It is `≥ 0` at real `x > β`, so `0` at `ρ` by Landau's lemma.
  have h_mod (d : Primes) (hd : ((d : ℕ) : ZMod q₀) = d₀) : (d : ℕ) ≡ d₀ [MOD q₀] :=
    (ZMod.natCast_eq_natCast_iff d d₀ q₀).1 hd
  have h_class (d : Primes) (hd : ((d : ℕ) : ZMod q₀) = d₀) : (d : ℕ) % 8 = 7 ∧ q₀.Coprime d := by
    have h_mod_eight : (d : ℕ) % 8 = d₀ % 8 := (h_mod d hd).of_dvd hq₀
    exact ⟨h_mod_eight.trans hd₀_mod, Coprime.symm ((h_mod d hd).gcd_eq.trans hd₀_cop)⟩
  obtain ⟨d, hd, h_twist⟩ : ∃ d : Primes, ((d : ℕ) : ZMod q₀) = d₀ ∧
      ∀ (χ : DirichletCharacter ℂ q₀) (s : ℂ),
        β ≤ re s → |im s| ≤ |ρ.im| → entireL (quadTwist χ d) s ≠ 0 :=
    exists_entireL_quadTwist_ne_zero |ρ.im| hβ ((ZMod.isUnit_iff_coprime d₀ q₀).2 hd₀_cop) h_class
  obtain ⟨hd_mod, hd_cop⟩ := h_class d hd
  let n (s : ℂ) : ℕ := ∑ χ : DirichletCharacter ℂ q₀, analyticOrderNatAt (entireL χ) s
  obtain ⟨r, h_polar, hr⟩ : ∃ r : ℂ → ℂ, IsPolar (fun v : ℝ ↦ primeRemainder d q₀ v.exp) r ∧
      ∀ s : ℂ, β < s.re → |s.im| ≤ |ρ.im| → r s = n s / φ q₀ / (s * (1 - s)) := by
    refine ⟨_, isPolar_primeRemainder hd_mod hd_cop, fun s h_re h_im ↦ ?_⟩
    have h_twist_order (χ : DirichletCharacter ℂ q₀) :
        analyticOrderNatAt (entireL (quadTwist χ d)) s = 0 :=
      (analyticOrderNatAt_entireL_eq_zero_iff (quadTwist χ d) s).2 (h_twist χ s h_re.le h_im)
    simp [n, h_twist_order]
  -- `x (1 - x) ≥ 0` for `0 ≤ x ≤ 1`, and there is no zero at `x ≥ 1`.
  have h_nonneg (x : ℝ) (hx : β < x) : 0 ≤ (r x).re := by
    have h_real : r x = (n x / φ q₀ / (x * (1 - x)) : ℝ) := by simpa using hr x hx (by simp)
    rw [h_real, ofReal_re]
    obtain hx_le | hx_ge : x ≤ 1 ∨ 1 ≤ x := le_total x 1
    · have h_denom : 0 ≤ x * (1 - x) := mul_nonneg (by linarith) (sub_nonneg.2 hx_le)
      positivity
    · have hn : n x = 0 := Finset.sum_eq_zero fun χ _ ↦
        (analyticOrderNatAt_entireL_eq_zero_iff χ x).2 (entireL_ne_zero χ hx_ge)
      simp [hn]
  have h_exp : ∀ᶠ v : ℝ in atTop, primeRemainder d q₀ v.exp ≤ Real.exp ((β - 1) * v) := by
    filter_upwards [tendsto_exp_atTop.eventually (h_bound d (h_mod d hd))] with v hv
    rwa [mul_comm, exp_mul]
  have h_landau : r ρ = 0 := h_polar.landau (by linarith) h_nonneg h_exp hρ_re
  have hρ_ne_zero : ρ ≠ 0 := ne_zero_of_re_pos (by linarith)
  rw [hr ρ hρ_re le_rfl] at h_landau
  have h_count : n ρ = 0 := by
    simpa [hρ_ne_zero, sub_ne_zero.2 hρ_ne.symm, NeZero.ne] using h_landau
  have h_entire : entireL ψ ρ ≠ 0 := (analyticOrderNatAt_entireL_eq_zero_iff ψ ρ).1
    (Finset.sum_eq_zero_iff.1 h_count ψ (Finset.mem_univ ψ))
  -- Away from `s = 1`, `entireL ψ` is `L(s, ψ)` or `(s - 1) L(s, ψ)`.
  rw [entireL] at h_entire
  split_ifs at h_entire with hψ
  · subst hψ
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ_ne] at h_entire
    exact right_ne_zero_of_mul h_entire
  · exact h_entire
