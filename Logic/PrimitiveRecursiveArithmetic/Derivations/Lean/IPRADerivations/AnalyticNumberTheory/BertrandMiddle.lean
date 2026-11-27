import IPRADerivations.AnalyticNumberTheory.BinomialLcm
import IPRADerivations.DiophantineNumberTheory.ResidueFacts

/-!
# Bertrand's postulate: the primes of the middle third do not occur

Packet: `analytic-number-theory/bertrand_ipra`, `bertrand.tex`, §"Where the prime factors can occur", third row
of the table: for a prime `p` with `2n/3 < p ≤ n` and `p² > 2n`, the first carry `⌊2n/p⌋ − 2⌊n/p⌋ = 2 − 2`
vanishes and there is no other, so `p ∤ C(2n, n)`.

* `sum_first`: `Σ_{j<M} ⌊m/q^{j+1}⌋ = ⌊m/q⌋` when `m < q²` and `M ≥ 1` (only the first term of Legendre's sum
  survives);
* `val_middle`: `v_q(C(2k, k)) = 0` for a prime `q` with `q ≤ k`, `2k < 3q`, `2k < q²`, from Legendre's formula
  for the central coefficient (`BinomialLcm.binom_val`) with `⌊k/q⌋ = 1` and `⌊2k/q⌋ = 2`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.BertrandMiddle

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm (binom_val)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (qB' qB'_at quo_small dmu)
open LeanProofs.IPRA.Combinatorics.LegendreFact (shift_le_two)
open LeanProofs.IPRA.Combinatorics.Catalan (cb)
open LeanProofs.IPRA.DiophantineNumberTheory.ResidueFacts (pw_two)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `Σ_{j<M} ⌊m/q^{j+1}⌋ = ⌊m/q⌋` for `m < q²`, `M ≥ 1`. -/
theorem sum_first {q m M : PTm n} (hq2 : Γ ⊢[PRAAx] le two q) (hM : Γ ⊢[PRAAx] le one M)
    (hlt : Γ ⊢[PRAAx] lt m (q * q)) :
    Γ ⊢[PRAAx] ap2 (sumF qB') M (pairT q m) ≐ quo m q := by
  have hlt' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift m) (Syn.shift q * Syn.shift q) := by
    simpa [Fm.shift, Syn.shift] using hlt.shift
  have ext := sum_ext (Γ := Γ) qB' (B := zero) (N := M) (x := pairT q m) (fun Δ a hs ha => by
    rw [shift_pairT]
    have hq2' := (shift_le_two hq2).weaken hs
    have qpos' := p_pos hq2'
    have sz : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
    rw [sz] at ha
    have e2 : Δ ⊢[PRAAx] le two (succ a) := (succ_monus_succ _ _).eqTrans ha
    have b : Δ ⊢[PRAAx] le (Syn.shift q * Syn.shift q) (pw (Syn.shift q) (succ a)) :=
      le_congr (pw_two _) (.eqRefl _) (pw_le_exp qpos' e2)
    exact (qB'_at _ _ _).eqTrans (quo_small (pw_pos' qpos' _) (lt_of_lt_of_le (hlt'.weaken hs) b))) hM
  have s1 := sum_succ' (Γ := Γ) qB' zero (pairT q m)
  exact ext.eqTrans (s1.eqTrans ((congrAdd (sum_zero _ _) (qB'_at zero q m)).eqTrans
    ((zero_add _).eqTrans (congrAp2 quoF (.eqRefl _) (pw_one q)))))

/-- A prime `q` with `q ≤ k`, `2k < 3q` and `2k < q²` does not divide `C(2k, k)`. -/
theorem val_middle {q k : PTm n} (hq : Γ ⊢[PRAAx] prime q) (h1 : Γ ⊢[PRAAx] le q k)
    (h2 : Γ ⊢[PRAAx] lt (two * k) (succ two * q)) (h3 : Γ ⊢[PRAAx] lt (two * k) (q * q)) :
    Γ ⊢[PRAAx] val q (cb k) ≐ zero := by
  have hq2 := prime_two hq
  have qpos := p_pos hq2
  have e1 := natEq (eq_add_of_le h1)
  have hM : Γ ⊢[PRAAx] le one (two * k) := by ipra_le 2 * sl h1 + 2 * sl hq2 + 3
  have hkk : Γ ⊢[PRAAx] le k (two * k) := le_of_eq_add (d := k) (by ipra_ring)
  have S1 := sum_first hq2 hM (lt_of_le_of_lt hkk h3)
  have S2 := sum_first hq2 hM h3
  have r1 : Γ ⊢[PRAAx] lt (monus k q) q := by ipra_le sl h2 + sl h1 with e1
  have z1 : Γ ⊢[PRAAx] k ≐ q * one + monus k q := by ipra_lc e1
  have Q1 := Prf.andE₁ (dmu qpos z1 r1)
  have r2 : Γ ⊢[PRAAx] lt (two * monus k q) q := by ipra_le sl h2 with 2 * e1
  have z2 : Γ ⊢[PRAAx] two * k ≐ q * two + two * monus k q := by
    ipra_lc 2 * e1
  have Q2 := Prf.andE₁ (dmu qpos z2 r2)
  ipra_lc natEq (binom_val hq k) - 2 * natEq (S1.eqTrans Q1) + natEq (S2.eqTrans Q2)

end LeanProofs.IPRA.AnalyticNumberTheory.BertrandMiddle
