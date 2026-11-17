import IPRADerivations.Combinatorics.Vandermonde
import IPRADerivations.Combinatorics.Catalan
import IPRADerivations.Core.ProdLemmas

/-!
# Squares of binomial coefficients and the Narayana sum

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16` (the Vandermonde steps of (2.13)–(2.14)
and of the square sum (2.20)). With `C(M, k)` guarded to vanish for `k > M`
(`Combinatorics/Vandermonde`):

* `gb_symm`: `C(M, M − j) = C(M, j)` for `j ≤ M`;
* `central_squares`: `∑_{k ≤ m} C(m, k)² = C(2m, m)`;
* `narayana_sum`: `∑_{k ≤ m} C(m + 1, k) C(m + 1, k + 1) = C(2m + 2, m)`;
* `narayana_catalan`: `∑_{k ≤ m} C(m + 1, k) C(m + 1, k + 1) = (m + 1) Cat_{m+1}`, i.e.
  `∑_{j=1}^{n} N(n, j) = Cat_n` for the Narayana numbers `n N(n, j) = C(n, j) C(n, j − 1)`, which is
  (2.14) `₂F₁(1 − n, −n; 2; 1) = Cat_n` after the term evaluation (2.13).

The square sum (2.20) is `Combinatorics/CatalanSquares`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanNarayana

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel catalan_ratio_open)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open LeanProofs.IPRA.Combinatorics.Bell (monus_monus monus_le')
open LeanProofs.IPRA.Combinatorics.Stirling (gle gle_of_le)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb vsB vs_at shift_y vandermonde)
open LeanProofs.IPRA.Combinatorics.Catalan (cat cb cat_spec succ_pos)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Symmetry -/

/-- `C(M, M − j) = C(M, j)` for `j ≤ M`. -/
theorem gb_symm {j M : PTm n} (h : Γ ⊢[PRAAx] le j M) : Γ ⊢[PRAAx] gb M (monus M j) ≐ gb M j := by
  have s : Γ ⊢[PRAAx] binom M (monus M j) ≐ binom M j := by
    refine mul_cancel (D := fact j * fact (monus M j)) (pos_mul' (fact_pos _) (fact_pos _)) ?_
    have b₁ := natEq (binom_eq (monus_le' h)); have b₀ := natEq (binom_eq h)
    have c := natEq (congrAp2 factF (monus_monus (Γ := Γ) h) (.eqRefl zero))
    apply deriveNat; ipra_simps
    linear_combination -b₁ + b₀ - 𝔞(fact (monus M j)) * 𝔞(binom M (monus M j)) * c
  have g₁ := natEq (gle_of_le (monus_le' h) : Γ ⊢[PRAAx] gle (monus M j) M ≐ one)
  have g₂ := natEq (gle_of_le h)
  have s' := natEq s
  apply deriveNat; ipra_simps
  linear_combination 𝔞(binom M (monus M j)) * g₁ - 𝔞(binom M j) * g₂ + s'

/-! ## Sums of squares -/

/-- `C(m, k)²`, over `0 = k`, `1 = m`. -/
abbrev sqB : PTm 2 := gb (var 1) (var 0) * gb (var 1) (var 0)
/-- `C(M, k) C(M, k + 1)`, over `0 = k`, `1 = M`. -/
abbrev nB : PTm 2 := gb (var 1) (var 0) * gb (var 1) (succ (var 0))

theorem inst2_sq (k m : PTm n) : inst2 sqB k m = gb m k * gb m k := by simp [inst2]
theorem inst2_n (k M : PTm n) : inst2 nB k M = gb M k * gb M (succ k) := by simp [inst2]

theorem le_of_lt_succ {k m : PTm n} (h : Γ ⊢[PRAAx] lt k (succ m)) : Γ ⊢[PRAAx] le k m :=
  (succ_monus_succ _ _).eqSymm.eqTrans h

/-- `∑_{k ≤ m} C(m, k)² = C(2m, m)`. -/
theorem central_squares (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF sqB) (succ m) m ≐ binom (m + m) m := by
  have c : Γ ⊢[PRAAx] ap2 (sumF sqB) (succ m) m ≐ ap2 (sumF vsB) (succ m) (pairT (pairT m m) m) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y, inst2_sq]
    have e : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
    rw [e] at *
    refine .eqTrans ?_ (vs_at _ _ _ _).eqSymm
    exact congrMul (.eqRefl _) (gb_symm (le_of_lt_succ Prf.hyp0)).eqSymm
  refine c.eqTrans ((vandermonde m m m).eqTrans ?_)
  exact (congrMul (gle_of_le (le_add_left m m)) (.eqRefl _)).eqTrans (one_mul _)

/-- `∑_{k ≤ m} C(m + 1, k) C(m + 1, k + 1) = C(2m + 2, m)`. -/
theorem narayana_sum (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF nB) (succ m) (succ m) ≐ binom (succ m + succ m) m := by
  have c : Γ ⊢[PRAAx] ap2 (sumF nB) (succ m) (succ m) ≐
      ap2 (sumF vsB) (succ m) (pairT (pairT (succ m) (succ m)) m) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y, inst2_n]
    have e : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
    rw [e] at *
    refine .eqTrans ?_ (vs_at _ _ _ _).eqSymm
    refine congrMul (.eqRefl _) ?_
    exact (gb_symm ((succ_monus_succ _ _).eqTrans (le_of_lt_succ Prf.hyp0))).eqSymm.eqTrans
      (congrGb (.eqRefl _) (succ_monus_succ _ _))
  refine c.eqTrans ((vandermonde _ _ _).eqTrans ?_)
  have l : Γ ⊢[PRAAx] le m (succ m + succ m) :=
    le_of_eq_add (d := succ (succ m)) (by apply deriveNat; ipra_simps; ring)
  exact (congrMul (gle_of_le l) (.eqRefl _)).eqTrans (one_mul _)

/-- `C(2M, M + 1) = M Cat_M` for `M = m + 1`. -/
theorem binom_succ_cat (m : PTm n) :
    Γ ⊢[PRAAx] binom (two * succ m) (succ (succ m)) ≐ succ m * cat (succ m) := by
  refine mul_cancel (D := succ (succ m)) (succ_pos _) ?_
  have r : Γ ⊢[PRAAx] succ m * cb (succ m) ≐ succ (succ m) * binom (two * succ m) (succ (succ m)) := by
    have h := inst (Γ := Γ) catalan_ratio_open (![m] : Fin 1 → PTm n)
    simpa using h
  have r' := natEq r; have s := natEq (cat_spec (Γ := Γ) (succ m))
  apply deriveNat; ipra_simps
  linear_combination -r' - (𝔞(m) + 1) * s

/-- `∑_{k ≤ m} C(m + 1, k) C(m + 1, k + 1) = (m + 1) Cat_{m+1}`: the Narayana numbers sum to the
Catalan number. -/
theorem narayana_catalan (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF nB) (succ m) (succ m) ≐ succ m * cat (succ m) := by
  refine (narayana_sum m).eqTrans ?_
  have hN : Γ ⊢[PRAAx] succ m + succ m ≐ two * succ m := by apply deriveNat; ipra_simps; ring
  have hj : Γ ⊢[PRAAx] le (succ (succ m)) (succ m + succ m) :=
    le_of_eq_add (d := m) (by apply deriveNat; ipra_simps; ring)
  have hm : Γ ⊢[PRAAx] monus (succ m + succ m) (succ (succ m)) ≐ m := by
    have e : Γ ⊢[PRAAx] succ m + succ m ≐ m + succ (succ m) := by apply deriveNat; ipra_simps; ring
    exact (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)
  -- `C(2M, m) = C(2M, M + 1)`, read through the guarded coefficient.
  have sy := (congrGb (.eqRefl _) hm).eqSymm.eqTrans (gb_symm hj)
  have l : Γ ⊢[PRAAx] le m (succ m + succ m) :=
    le_of_eq_add (d := succ (succ m)) (by apply deriveNat; ipra_simps; ring)
  have g₁ := natEq (gle_of_le l); have g₂ := natEq (gle_of_le hj)
  have sy' := natEq sy
  have b := natEq ((congrBinom hN (.eqRefl _)).eqTrans (binom_succ_cat (Γ := Γ) m))
  apply deriveNat; ipra_simps
  linear_combination -𝔞(binom (succ m + succ m) m) * g₁ + sy' + 𝔞(binom (succ m + succ m) (succ (succ m))) * g₂ + b

end LeanProofs.IPRA.Combinatorics.CatalanNarayana
