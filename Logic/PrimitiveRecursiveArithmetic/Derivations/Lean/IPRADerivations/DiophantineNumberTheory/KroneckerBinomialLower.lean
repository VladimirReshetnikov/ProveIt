import IPRADerivations.DiophantineNumberTheory.KroneckerBinomialTail
import IPRADerivations.Probability.BinomialLaw
import IPRADerivations.Core.CertificateTactics

/-!
# `C(r, k) ≥ (r/k)^k` and the full binomial kernel estimate

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`, Theorem `thm:kronecker`, the rational estimate before
`eq:kernel-tail`: "`C(r, k) = ∏_{j<k} (r − j)/(k − j) ≥ (r/k)^k`, because `r ≥ k` makes each factor at least
`r/k`", and with it "`(1 − δ)^r ≤ (1 + δ)^{−r} ≤ (C(r, k) δ^k)^{−1} ≤ (k/(rδ))^k`".

* `binom_power_lower`: `r^K ≤ K^K C(r, K)` for `K ≤ r`. The factors are indexed upwards: for `j ≤ K`,
  `r^j ≤ K^j C(r − K + j, j)`, by quantifier-free induction on `j` with the absorption identity
  `(j + 1) C(m + 1, j + 1) = (m + 1) C(m, j)` (`BinomialLaw.absorption`); the step needs
  `K (r − K + j + 1) ≥ (j + 1) r`, i.e. `(K − j − 1)(r − K) ≥ 0`, and then cancels `j + 1`;
* `gb_power_lower`: the same for the guarded coefficient `gb` of the binomial theorem;
* `kernel_binomial`: with `T = t² = T' + 1` and `k ≤ r`, `(T − 1)^r r^k ≤ k^k T^k T^r`, i.e.
  `(1 − δ)^r ≤ (k/(rδ))^k` for `δ = 1/T` (with `KroneckerBinomialTail.binom_tail`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.KroneckerBinomialLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.BinomialLaw (absorption)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb)
open LeanProofs.IPRA.Combinatorics.Stirling (gle_of_le)
open LeanProofs.IPRA.DiophantineNumberTheory.KroneckerBinomialTail (binom_tail)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem bp_base (r K : PTm n) : Γ ⊢[PRAAx] le (pw r zero) (pw K zero * binom (monus r K + zero) zero) := by
  have e1 := natEq (pw_zero (Γ := Γ) r)
  have e2 := natEq (pw_zero (Γ := Γ) K)
  have e3 := natEq (binom_zero' (Γ := Γ) (monus r K + zero))
  refine le_of_eq_add (d := zero) ?_
  apply deriveNat; ipra_simps
  rw [e1, e2, e3]; ring

theorem bp_step {r K j : PTm n} (hKr : Γ ⊢[PRAAx] le K r) (hj : Γ ⊢[PRAAx] le (succ j) K)
    (ih : Γ ⊢[PRAAx] le (pw r j) (pw K j * binom (monus r K + j) j)) :
    Γ ⊢[PRAAx] le (pw r (succ j)) (pw K (succ j) * binom (monus r K + succ j) (succ j)) := by
  have hjm : Γ ⊢[PRAAx] le j (monus r K + j) := le_add_left j (monus r K)
  have eab := natEq (absorption hjm)
  have eC := natEq (congrBinom (Γ := Γ) (show Γ ⊢[PRAAx] monus r K + succ j ≐ succ (monus r K + j) by
    ipra_ring) (.eqRefl (succ j)))
  have er := natEq (eq_add_of_le hKr)
  have pr := natEq (pw_succ (Γ := Γ) r j)
  have pK := natEq (pw_succ (Γ := Γ) K j)
  refine mul_le_cancel (d' := j) ?_
  ipra_le 𝔟 K * (𝔟 (monus r K) + 𝔟 j + 1) * sl ih + 𝔟 (pw r j) * 𝔟 (monus r K) * sl hj using
    simp only [pr, pK, eC, er]
    linear_combination (𝔟 K * 𝔟 (pw K j)) * eab

/-- Variables: `0 = j` (induction), `1 = r`, `2 = K`. -/
private abbrev bpF : Fm PTm 3 :=
  le (var 2) (var 1) ⟶ (le (var 0) (var 2) ⟶
    le (pw (var 1) (var 0)) (pw (var 2) (var 0) * binom (monus (var 1) (var 2) + var 0) (var 0)))

private theorem bp₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] bpF := by
  refine ind _ ⟨le_QF _ _, ⟨le_QF _ _, le_QF _ _⟩⟩ ?_ ?_
  · simp
    exact .impI (.impI (bp_base _ _))
  · simp
    refine .impI (.impI ?_)
    exact bp_step Prf.hyp1 Prf.hyp0
      (.impE (.impE Prf.hyp1.wk Prf.hyp1) (le_trans (le_succ_self _) Prf.hyp0))

/-- `r^K ≤ K^K C(r, K)` for `K ≤ r`: `C(r, K) ≥ (r/K)^K`. -/
theorem binom_power_lower {r K : PTm n} (hKr : Γ ⊢[PRAAx] le K r) :
    Γ ⊢[PRAAx] le (pw r K) (pw K K * binom r K) := by
  have h := inst (Γ := Γ) bp₀ (![K, r, K] : Fin 3 → PTm n)
  simp at h
  have h' := Prf.impE (Prf.impE h hKr) (le_refl K)
  have e : Γ ⊢[PRAAx] monus r K + K ≐ r := by
    ipra_lc -natEq (eq_add_of_le hKr)
  exact le_congr (.eqRefl _) (congrMul (.eqRefl _) (congrBinom e (.eqRefl K))) h'

/-- The same for the guarded coefficient. -/
theorem gb_power_lower {r K : PTm n} (hKr : Γ ⊢[PRAAx] le K r) :
    Γ ⊢[PRAAx] le (pw r K) (pw K K * gb r K) := by
  refine le_congr (.eqRefl _) (congrMul (.eqRefl _) ?_) (binom_power_lower hKr)
  exact ((one_mul _).eqSymm.eqTrans (congrMul (gle_of_le hKr).eqSymm (.eqRefl _)))

/-- `(1 − δ)^r ≤ (k/(rδ))^k`: `(T − 1)^r r^k ≤ k^k T^k T^r` for `T = T' + 1`, `k ≤ r`. -/
theorem kernel_binomial {T' r k : PTm n} (hk : Γ ⊢[PRAAx] le k r) :
    Γ ⊢[PRAAx] le (pw T' r * pw r k) (pw k k * (pw (succ T') k * pw (succ T') r)) := by
  have g := gb_power_lower hk
  have t := binom_tail (T' := T') hk
  ipra_le 𝔟 (pw T' r) * sl g + 𝔟 (pw k k) * sl t

end LeanProofs.IPRA.DiophantineNumberTheory.KroneckerBinomialLower
