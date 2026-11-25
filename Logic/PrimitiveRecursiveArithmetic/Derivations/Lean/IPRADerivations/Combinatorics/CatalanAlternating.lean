import IPRADerivations.Combinatorics.CatalanTouchard
import IPRADerivations.Core.LinearCombination

/-!
# The alternating binomial transform of `C(k, ⌊k/2⌋)`

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16` (theorem "Alternating binomial transform",
(2.17)): `Cat_n = ∑_k (−1)^k 2^{n − k} C(n, k) C(k, ⌊k/2⌋)`. Separating even `k = 2j` and odd
`k = 2j + 1`, in natural numbers this is

  `E(n) = Cat_n + O(n)`,  `E(n) = ∑_j C(n, 2j) 2^{n − 2j} C(2j, j)`,
                          `O(n) = ∑_j C(n, 2j + 1) 2^{n − 2j − 1} C(2j + 1, j)`.

The packet proves (2.17) by generating functions. Here both halves are evaluated by creative
telescoping, as for `Combinatorics/CatalanTouchard`:

* `E(n) = C(2n, n)` (`even_sum`), from the certificate `V(j) = 4j² e(n + 1, j)` for
  `(n + 1) E(n + 1) = 2(2n + 1) E(n)`;
* `O(n) = n Cat_n = C(2n, n + 1)` (`odd_sum`), from the certificate `V(j) = 4j(j + 1) o(n + 1, j)`
  for `n(n + 2) O(n + 1) = 2(n + 1)(2n + 1) O(n)`;
* `alternating`: `E(n) = Cat_n + O(n)`, since `C(2n, n) = (n + 1) Cat_n`.

The ratio lemmas: `r1` (any index `i`): `(n + 1 − i) t(n + 1) = 2(n + 1) t(n)` for
`t(N) = C(N, i) 2^{N − i} w`; `r2e`, `r2o`: the step `j → j + 1` (two binomial ratios and the
ratio of `C(2j, j)`, resp. `(2j + 1) Cat_j`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanAlternating

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_self gb_above)
open LeanProofs.IPRA.Combinatorics.Catalan (cb cb_zero cb_rec cat cat_rec cat_zero cat_spec cat_odd_binom succ_pos)
open LeanProofs.IPRA.Combinatorics.CatalanConvolution (cat_one)
open LeanProofs.IPRA.Combinatorics.CatalanTouchard (t1aux t1aux0)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyRecurrence (gr gl uv)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The first ratio, for any index -/

/-- `(N + 1 − i) C(N + 1, i) 2^{N + 1 − i} w = 2(N + 1) C(N, i) 2^{N − i} w`. -/
theorem r1 (N i W : PTm n) :
    Γ ⊢[PRAAx] monus (succ N) i * (gb (succ N) i * pw two (monus (succ N) i) * W) ≐
      two * succ N * (gb N i * pw two (monus N i) * W) := by
  have L := gl (Γ := Γ) N i
  refine .orE (lt_or_le N i) ?_ ?_
  · exact t1aux0 L.wk (gb_above Prf.hyp0)
  · have hl : (le i N :: Γ) ⊢[PRAAx] le i N := Prf.hyp0
    have e : (le i N :: Γ) ⊢[PRAAx] monus (succ N) i ≐ succ (monus N i) := by
      have e₀ : (le i N :: Γ) ⊢[PRAAx] succ N ≐ succ (monus N i) + i := by
        ipra_lc natEq (eq_add_of_le hl)
      exact (congrMonus e₀ (.eqRefl _)).eqTrans (add_monus _ _)
    exact t1aux L.wk ((congrAp2 powF e (.eqRefl two)).eqTrans (pw_succ two _))

/-- `2^{N − i} = 2^{N − (i + 2)} · 2 · 2` for `i + 2 ≤ N`. -/
theorem pw_two_step {N i : PTm n} (h : Γ ⊢[PRAAx] le (succ (succ i)) N) :
    Γ ⊢[PRAAx] pw two (monus N i) ≐ pw two (monus N (succ (succ i))) * two * two := by
  have e₀ : Γ ⊢[PRAAx] N ≐ succ (succ (monus N (succ (succ i)))) + i := by
    ipra_lc natEq (eq_add_of_le h)
  have e : Γ ⊢[PRAAx] monus N i ≐ succ (succ (monus N (succ (succ i)))) :=
    (congrMonus e₀ (.eqRefl _)).eqTrans (add_monus _ _)
  exact (congrAp2 powF e (.eqRefl two)).eqTrans ((pw_succ two _).eqTrans (congrMul (pw_succ two _) (.eqRefl _)))

/-! ## The even terms `e(N, j) = C(N, 2j) 2^{N − 2j} C(2j, j)` -/

abbrev et {n : ℕ} (N k : PTm n) : PTm n := gb N (k + k) * pw two (monus N (k + k)) * cb k

theorem et_zero {N k : PTm n} (h : Γ ⊢[PRAAx] le (succ N) (k + k)) : Γ ⊢[PRAAx] et N k ≐ zero :=
  (congrMul (congrMul (gb_above h) (.eqRefl _)) (.eqRefl _)).eqTrans
    ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))

theorem e2aux {G0 Ga Gb Gb' Pb P0 C Cs K U V : PTm n} (E : Γ ⊢[PRAAx] Gb' ≐ Gb)
    (r₁ : Γ ⊢[PRAAx] succ (K + K) * Ga ≐ U * G0) (r₂ : Γ ⊢[PRAAx] succ (succ (K + K)) * Gb ≐ V * Ga)
    (cr : Γ ⊢[PRAAx] succ K * Cs ≐ two * succ (two * K) * C) (hp : Γ ⊢[PRAAx] P0 ≐ Pb * two * two) :
    Γ ⊢[PRAAx] num 4 * (succ K * succ K) * (Gb' * Pb * Cs) ≐ U * V * (G0 * P0 * C) := by
  refine mul_cancel (succ_pos (K + K)) ?_
  ipra_lc (2 * 𝔞 K + 1) * 4 * (𝔞 K + 1) ^ 2 * 𝔞 Pb * 𝔞 Cs * natEq E +
    2 * (2 * 𝔞 K + 1) * 𝔞 Pb * (𝔞 K + 1) * 𝔞 Cs * natEq r₂ + 2 * (2 * 𝔞 K + 1) * 𝔞 Pb * 𝔞 V * 𝔞 Ga * natEq cr +
    4 * (2 * 𝔞 K + 1) * 𝔞 Pb * 𝔞 V * 𝔞 C * natEq r₁ - (2 * 𝔞 K + 1) * 𝔞 U * 𝔞 V * 𝔞 G0 * 𝔞 C * natEq hp

/-- `4(k + 1)² e(N, k + 1) = (N − 2k)(N − 2k − 1) e(N, k)`. -/
theorem r2e (N k : PTm n) :
    Γ ⊢[PRAAx] num 4 * (succ k * succ k) * et N (succ k) ≐ monus N (k + k) * monus N (succ (k + k)) * et N k := by
  have E : Γ ⊢[PRAAx] gb N (succ k + succ k) ≐ gb N (succ (succ (k + k))) := congrGb (.eqRefl _) (by ipra_ring)
  have Ep : Γ ⊢[PRAAx] pw two (monus N (succ k + succ k)) ≐ pw two (monus N (succ (succ (k + k)))) :=
    congrAp2 powF (congrMonus (.eqRefl _) (by ipra_ring)) (.eqRefl two)
  refine .orE (lt_or_le (succ (k + k)) N) ?_ ?_
  · have hp := (pw_two_step (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := lt (succ (k + k)) N))).eqTrans
      (congrMul (congrMul Ep.wk.eqSymm (.eqRefl _)) (.eqRefl _))
    exact e2aux E.wk (gr N (k + k)) (gr N (succ (k + k))) (cb_rec k) hp
  · have hl : (le N (succ (k + k)) :: Γ) ⊢[PRAAx] le N (succ (k + k)) := Prf.hyp0
    have gz : (le N (succ (k + k)) :: Γ) ⊢[PRAAx] gb N (succ (succ (k + k))) ≐ zero :=
      gb_above ((succ_monus_succ _ _).eqTrans hl)
    have tz : (le N (succ (k + k)) :: Γ) ⊢[PRAAx] et N (succ k) ≐ zero :=
      (congrMul (congrMul (E.wk.eqTrans gz) (.eqRefl _)) (.eqRefl _)).eqTrans
        ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))
    exact ((congrMul (.eqRefl _) tz).eqTrans (mul_zero _)).eqTrans
      ((congrMul ((congrMul (.eqRefl _) hl).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm

theorem eaux {N K T tp t0 u v : PTm n} (hR1 : Γ ⊢[PRAAx] u * T ≐ two * succ N * t0)
    (hR2 : Γ ⊢[PRAAx] num 4 * (succ K * succ K) * tp ≐ u * v * T)
    (hu : Γ ⊢[PRAAx] succ N ≐ (K + K) + u) (hv : Γ ⊢[PRAAx] v * u + u ≐ u * u) :
    Γ ⊢[PRAAx] succ N * succ N * T + num 4 * (succ K * succ K) * tp ≐
      two * succ N * (two * N + one) * t0 + num 4 * (K * K) * T := by
  have r₁ := natEq hR1; have r₂ := natEq hR2; have e := natEq hu; have f := natEq hv
  apply deriveNat; ipra_simps
  have eN : Groth.ι (Q.mk Γ N) = 2 * Groth.ι (Q.mk Γ K) + Groth.ι (Q.mk Γ u) - 1 := by linear_combination e
  rw [eN] at r₁ ⊢
  linear_combination r₂ + (2 * (2 * 𝔞 K + 𝔞 u - 1) + 1) * r₁ + 𝔞 T * f

theorem eaux0 {N K T tp t0 u v : PTm n} (hR1 : Γ ⊢[PRAAx] u * T ≐ two * succ N * t0)
    (hR2 : Γ ⊢[PRAAx] num 4 * (succ K * succ K) * tp ≐ u * v * T) (hT : Γ ⊢[PRAAx] T ≐ zero) :
    Γ ⊢[PRAAx] succ N * succ N * T + num 4 * (succ K * succ K) * tp ≐
      two * succ N * (two * N + one) * t0 + num 4 * (K * K) * T := by
  ipra_lc natEq hR2 + (2 * 𝔞 N + 1) * natEq hR1 +
    ((𝔞 N + 1) ^ 2 + 𝔞 u * 𝔞 v - (2 * 𝔞 N + 1) * 𝔞 u - 4 * 𝔞 K ^ 2) * natEq hT

/-- `(n + 1)² e(n + 1, k) + V(k + 1) = 2(n + 1)(2n + 1) e(n, k) + V(k)`, `V(k) = 4k² e(n + 1, k)`. -/
theorem ept (N k : PTm n) :
    Γ ⊢[PRAAx] succ N * succ N * et (succ N) k + num 4 * (succ k * succ k) * et (succ N) (succ k) ≐
      two * succ N * (two * N + one) * et N k + num 4 * (k * k) * et (succ N) k := by
  have hR1 := r1 (Γ := Γ) N (k + k) (cb k)
  have hR2 := (r2e (Γ := Γ) (succ N) k).eqTrans (congrMul (congrMul (.eqRefl _) (succ_monus_succ _ _)) (.eqRefl _))
  refine .orE (lt_or_le (succ N) (k + k)) ?_ ?_
  · exact eaux0 hR1.wk hR2.wk (et_zero Prf.hyp0)
  · exact eaux hR1.wk hR2.wk (eq_add_of_le Prf.hyp0) (uv N (k + k))

/-! ## The odd terms `o(N, j) = C(N, 2j + 1) 2^{N − 2j − 1} (2j + 1) Cat_j` -/

abbrev ot {n : ℕ} (N k : PTm n) : PTm n :=
  gb N (succ (k + k)) * pw two (monus N (succ (k + k))) * (succ (two * k) * cat k)

theorem ot_zero {N k : PTm n} (h : Γ ⊢[PRAAx] le (succ N) (succ (k + k))) : Γ ⊢[PRAAx] ot N k ≐ zero :=
  (congrMul (congrMul (gb_above h) (.eqRefl _)) (.eqRefl _)).eqTrans
    ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))

theorem o2aux {G0 Ga Gb Gb' Pb P0 C Cs K U V : PTm n} (E : Γ ⊢[PRAAx] Gb' ≐ Gb)
    (r₁ : Γ ⊢[PRAAx] succ (succ (K + K)) * Ga ≐ U * G0)
    (r₂ : Γ ⊢[PRAAx] succ (succ (succ (K + K))) * Gb ≐ V * Ga)
    (cr : Γ ⊢[PRAAx] succ (succ K) * Cs ≐ two * succ (two * K) * C) (hp : Γ ⊢[PRAAx] P0 ≐ Pb * two * two) :
    Γ ⊢[PRAAx] num 4 * (succ K * succ (succ K)) * (Gb' * Pb * (succ (two * succ K) * Cs)) ≐
      U * V * (G0 * P0 * (succ (two * K) * C)) := by
  refine mul_cancel (succ_pos (succ (succ (K + K)))) ?_
  ipra_lc (2 * 𝔞 K + 3) * 4 * (𝔞 K + 1) * (𝔞 K + 2) * 𝔞 Pb * (2 * 𝔞 K + 3) * 𝔞 Cs * natEq E +
    4 * (𝔞 K + 1) * (𝔞 K + 2) * (2 * 𝔞 K + 3) * 𝔞 Pb * 𝔞 Cs * natEq r₂ +
    4 * (𝔞 K + 1) * (2 * 𝔞 K + 3) * 𝔞 Pb * 𝔞 V * 𝔞 Ga * natEq cr +
    4 * (2 * 𝔞 K + 3) * (2 * 𝔞 K + 1) * 𝔞 Pb * 𝔞 V * 𝔞 C * natEq r₁ -
    (2 * 𝔞 K + 3) * (2 * 𝔞 K + 1) * 𝔞 U * 𝔞 V * 𝔞 G0 * 𝔞 C * natEq hp

/-- `4(k + 1)(k + 2) o(N, k + 1) = (N − 2k − 1)(N − 2k − 2) o(N, k)`. -/
theorem r2o (N k : PTm n) :
    Γ ⊢[PRAAx] num 4 * (succ k * succ (succ k)) * ot N (succ k) ≐
      monus N (succ (k + k)) * monus N (succ (succ (k + k))) * ot N k := by
  have E : Γ ⊢[PRAAx] gb N (succ (succ k + succ k)) ≐ gb N (succ (succ (succ (k + k)))) :=
    congrGb (.eqRefl _) (by ipra_ring)
  have Ep : Γ ⊢[PRAAx] pw two (monus N (succ (succ k + succ k))) ≐ pw two (monus N (succ (succ (succ (k + k))))) :=
    congrAp2 powF (congrMonus (.eqRefl _) (by ipra_ring)) (.eqRefl two)
  refine .orE (lt_or_le (succ (succ (k + k))) N) ?_ ?_
  · have hp := (pw_two_step (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := lt (succ (succ (k + k))) N))).eqTrans
      (congrMul (congrMul Ep.wk.eqSymm (.eqRefl _)) (.eqRefl _))
    exact o2aux E.wk (gr N (succ (k + k))) (gr N (succ (succ (k + k)))) (cat_rec k) hp
  · have hl : (le N (succ (succ (k + k))) :: Γ) ⊢[PRAAx] le N (succ (succ (k + k))) := Prf.hyp0
    have gz : (le N (succ (succ (k + k))) :: Γ) ⊢[PRAAx] gb N (succ (succ (succ (k + k)))) ≐ zero :=
      gb_above ((succ_monus_succ _ _).eqTrans hl)
    have tz : (le N (succ (succ (k + k))) :: Γ) ⊢[PRAAx] ot N (succ k) ≐ zero :=
      (congrMul (congrMul (E.wk.eqTrans gz) (.eqRefl _)) (.eqRefl _)).eqTrans
        ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))
    exact ((congrMul (.eqRefl _) tz).eqTrans (mul_zero _)).eqTrans
      ((congrMul ((congrMul (.eqRefl _) hl).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm

theorem oaux {N K T tp t0 u v : PTm n} (hR1 : Γ ⊢[PRAAx] u * T ≐ two * succ N * t0)
    (hR2 : Γ ⊢[PRAAx] num 4 * (succ K * succ (succ K)) * tp ≐ u * v * T)
    (hu : Γ ⊢[PRAAx] succ N ≐ succ (K + K) + u) (hv : Γ ⊢[PRAAx] v * u + u ≐ u * u) :
    Γ ⊢[PRAAx] N * (N + two) * T + num 4 * (succ K * succ (succ K)) * tp ≐
      two * succ N * (two * N + one) * t0 + num 4 * (K * succ K) * T := by
  have r₁ := natEq hR1; have r₂ := natEq hR2; have e := natEq hu; have f := natEq hv
  apply deriveNat; ipra_simps
  have eN : Groth.ι (Q.mk Γ N) = 2 * Groth.ι (Q.mk Γ K) + Groth.ι (Q.mk Γ u) := by linear_combination e
  rw [eN] at r₁ ⊢
  linear_combination r₂ + (2 * (2 * 𝔞 K + 𝔞 u) + 1) * r₁ + 𝔞 T * f

theorem oaux0 {N K T tp t0 u v : PTm n} (hR1 : Γ ⊢[PRAAx] u * T ≐ two * succ N * t0)
    (hR2 : Γ ⊢[PRAAx] num 4 * (succ K * succ (succ K)) * tp ≐ u * v * T) (hT : Γ ⊢[PRAAx] T ≐ zero) :
    Γ ⊢[PRAAx] N * (N + two) * T + num 4 * (succ K * succ (succ K)) * tp ≐
      two * succ N * (two * N + one) * t0 + num 4 * (K * succ K) * T := by
  ipra_lc natEq hR2 + (2 * 𝔞 N + 1) * natEq hR1 +
    (𝔞 N * (𝔞 N + 2) + 𝔞 u * 𝔞 v - (2 * 𝔞 N + 1) * 𝔞 u - 4 * 𝔞 K * (𝔞 K + 1)) * natEq hT

/-- `n(n + 2) o(n + 1, k) + V(k + 1) = 2(n + 1)(2n + 1) o(n, k) + V(k)`, `V(k) = 4k(k + 1) o(n + 1, k)`. -/
theorem opt (N k : PTm n) :
    Γ ⊢[PRAAx] N * (N + two) * ot (succ N) k + num 4 * (succ k * succ (succ k)) * ot (succ N) (succ k) ≐
      two * succ N * (two * N + one) * ot N k + num 4 * (k * succ k) * ot (succ N) k := by
  have hR1 := r1 (Γ := Γ) N (succ (k + k)) (succ (two * k) * cat k)
  have hR2 := (r2o (Γ := Γ) (succ N) k).eqTrans (congrMul (congrMul (.eqRefl _) (succ_monus_succ _ _)) (.eqRefl _))
  refine .orE (lt_or_le (succ N) (succ (k + k))) ?_ ?_
  · exact oaux0 hR1.wk hR2.wk (ot_zero Prf.hyp0)
  · exact oaux hR1.wk hR2.wk (eq_add_of_le Prf.hyp0) (uv N (succ (k + k)))

/-! ## Telescoping -/

abbrev eB : PTm 2 := et (var 1) (var 0)
abbrev oB : PTm 2 := ot (var 1) (var 0)

theorem inst2_e (k x : PTm n) : inst2 eB k x = et x k := by simp [inst2]
theorem inst2_o (k x : PTm n) : inst2 oB k x = ot x k := by simp [inst2]

abbrev phiLe {n : ℕ} (N K : PTm n) : PTm n :=
  succ N * succ N * ap2 (sumF eB) K (succ N) + num 4 * (K * K) * et (succ N) K
abbrev phiRe {n : ℕ} (N K : PTm n) : PTm n := two * succ N * (two * N + one) * ap2 (sumF eB) K N

abbrev phiLo {n : ℕ} (N K : PTm n) : PTm n :=
  N * (N + two) * ap2 (sumF oB) K (succ N) + num 4 * (K * succ K) * ot (succ N) K
abbrev phiRo {n : ℕ} (N K : PTm n) : PTm n := two * succ N * (two * N + one) * ap2 (sumF oB) K N

theorem phie_base (N : PTm n) : Γ ⊢[PRAAx] phiLe N zero ≐ phiRe N zero := by
  ipra_lc (𝔞 N + 1) ^ 2 * natEq (sum_zero (Γ := Γ) eB (succ N)) -
    2 * (𝔞 N + 1) * (2 * 𝔞 N + 1) * natEq (sum_zero (Γ := Γ) eB N)

theorem phie_step {N K : PTm n} (ih : Γ ⊢[PRAAx] phiLe N K ≐ phiRe N K) :
    Γ ⊢[PRAAx] phiLe N (succ K) ≐ phiRe N (succ K) := by
  have s₁ := sum_succ' (Γ := Γ) eB K (succ N); have s₂ := sum_succ' (Γ := Γ) eB K N
  rw [inst2_e] at s₁ s₂
  ipra_lc natEq ih + (𝔞 N + 1) ^ 2 * natEq s₁ - 2 * (𝔞 N + 1) * (2 * 𝔞 N + 1) * natEq s₂ + natEq (ept (Γ := Γ) N K)

theorem phio_base (N : PTm n) : Γ ⊢[PRAAx] phiLo N zero ≐ phiRo N zero := by
  ipra_lc 𝔞 N * (𝔞 N + 2) * natEq (sum_zero (Γ := Γ) oB (succ N)) -
    2 * (𝔞 N + 1) * (2 * 𝔞 N + 1) * natEq (sum_zero (Γ := Γ) oB N)

theorem phio_step {N K : PTm n} (ih : Γ ⊢[PRAAx] phiLo N K ≐ phiRo N K) :
    Γ ⊢[PRAAx] phiLo N (succ K) ≐ phiRo N (succ K) := by
  have s₁ := sum_succ' (Γ := Γ) oB K (succ N); have s₂ := sum_succ' (Γ := Γ) oB K N
  rw [inst2_o] at s₁ s₂
  ipra_lc natEq ih + 𝔞 N * (𝔞 N + 2) * natEq s₁ - 2 * (𝔞 N + 1) * (2 * 𝔞 N + 1) * natEq s₂ + natEq (opt (Γ := Γ) N K)

/-- Variables: `0 = K`, `1 = N`. -/
private abbrev phieF : Fm PTm 2 := phiLe (var 1) (var 0) ≐ phiRe (var 1) (var 0)
private abbrev phioF : Fm PTm 2 := phiLo (var 1) (var 0) ≐ phiRo (var 1) (var 0)

private theorem phie₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] phieF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact phie_base _
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact phie_step Prf.hyp0

private theorem phio₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] phioF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact phio_base _
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact phio_step Prf.hyp0

theorem phie (N K : PTm n) : Γ ⊢[PRAAx] phiLe N K ≐ phiRe N K := by
  have h := inst (Γ := Γ) phie₀ (![K, N] : Fin 2 → PTm n)
  simpa using h

theorem phio (N K : PTm n) : Γ ⊢[PRAAx] phiLo N K ≐ phiRo N K := by
  have h := inst (Γ := Γ) phio₀ (![K, N] : Fin 2 → PTm n)
  simpa using h

/-! ## The even sum -/

/-- `E(n) = ∑_{j ≤ n} C(n, 2j) 2^{n − 2j} C(2j, j)`. -/
abbrev Es {n : ℕ} (N : PTm n) : PTm n := ap2 (sumF eB) (succ N) N
/-- `O(n) = ∑_{j ≤ n} C(n, 2j + 1) 2^{n − 2j − 1} (2j + 1) Cat_j`. -/
abbrev Os {n : ℕ} (N : PTm n) : PTm n := ap2 (sumF oB) (succ N) N

/-- `(n + 1) E(n + 1) = 2(2n + 1) E(n)`. -/
theorem even_rec (N : PTm n) : Γ ⊢[PRAAx] succ N * Es (succ N) ≐ two * succ (two * N) * Es N := by
  refine mul_cancel (succ_pos N) ?_
  have h := natEq (phie (Γ := Γ) N (succ (succ N)))
  have z := natEq (et_zero (Γ := Γ) (le_add_right (succ (succ N)) (succ (succ N))))
  have s := sum_succ' (Γ := Γ) eB (succ N) N
  rw [inst2_e] at s
  have s' := natEq s
  have z' := natEq (et_zero (Γ := Γ) (le_add_right (succ N) (succ N)))
  apply deriveNat; ipra_simps
  linear_combination h - 4 * (𝔞 N + 2) ^ 2 * z + 2 * (𝔞 N + 1) * (2 * 𝔞 N + 1) * s' +
    2 * (𝔞 N + 1) * (2 * 𝔞 N + 1) * z'

theorem Es_zero : Γ ⊢[PRAAx] Es (zero : PTm n) ≐ cb zero := by
  have s := sum_succ' (Γ := Γ) eB zero (zero : PTm n)
  rw [inst2_e] at s
  have g : Γ ⊢[PRAAx] gb (zero : PTm n) (zero + zero) ≐ one := (congrGb (.eqRefl _) (add_zero _)).eqTrans (gb_zero _)
  have p : Γ ⊢[PRAAx] pw two (monus (zero : PTm n) (zero + zero)) ≐ one :=
    (congrAp2 powF (zero_monus _) (.eqRefl two)).eqTrans (pw_zero two)
  have t : Γ ⊢[PRAAx] et (zero : PTm n) zero ≐ one :=
    (congrMul (congrMul g p) cb_zero).eqTrans ((congrMul (one_mul _) (.eqRefl _)).eqTrans (one_mul _))
  exact s.eqTrans ((congrAdd (sum_zero _ _) t).eqTrans ((zero_add _).eqTrans cb_zero.eqSymm))

theorem Es_step {N : PTm n} (ih : Γ ⊢[PRAAx] Es N ≐ cb N) : Γ ⊢[PRAAx] Es (succ N) ≐ cb (succ N) := by
  refine mul_cancel (succ_pos N) ?_
  ipra_lc natEq (even_rec (Γ := Γ) N) - natEq (cb_rec (Γ := Γ) N) + 2 * (2 * 𝔞 N + 1) * natEq ih

private abbrev evenF : Fm PTm 1 := Es (var 0) ≐ cb (var 0)

private theorem even₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] evenF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact Es_zero
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact Es_step Prf.hyp0

/-- `∑_j C(n, 2j) 2^{n − 2j} C(2j, j) = C(2n, n)`. -/
theorem even_sum (N : PTm n) : Γ ⊢[PRAAx] Es N ≐ cb N := by
  have h := inst (Γ := Γ) even₀ (![N] : Fin 1 → PTm n)
  simpa using h

/-! ## The odd sum -/

/-- `n(n + 2) O(n + 1) = 2(n + 1)(2n + 1) O(n)`. -/
theorem odd_rec (N : PTm n) : Γ ⊢[PRAAx] N * (N + two) * Os (succ N) ≐ two * succ N * (two * N + one) * Os N := by
  have h := natEq (phio (Γ := Γ) N (succ (succ N)))
  have z := natEq (ot_zero (Γ := Γ)
    (le_trans (le_add_right (succ (succ N)) (succ (succ N))) (le_succ_self _)))
  have s := sum_succ' (Γ := Γ) oB (succ N) N
  rw [inst2_o] at s
  have s' := natEq s
  have z' := natEq (ot_zero (Γ := Γ) (le_trans (le_add_right (succ N) (succ N)) (le_succ_self _)))
  apply deriveNat; ipra_simps
  linear_combination h - 4 * (𝔞 N + 2) * (𝔞 N + 3) * z + 2 * (𝔞 N + 1) * (2 * 𝔞 N + 1) * s' +
    2 * (𝔞 N + 1) * (2 * 𝔞 N + 1) * z'

theorem ot_00 : Γ ⊢[PRAAx] ot (zero : PTm n) zero ≐ zero :=
  ot_zero (le_congr (.eqRefl _) (congrSucc (add_zero _)).eqSymm (le_refl _))

theorem Os_zero : Γ ⊢[PRAAx] Os (zero : PTm n) ≐ zero := by
  have s := sum_succ' (Γ := Γ) oB zero (zero : PTm n)
  rw [inst2_o] at s
  exact s.eqTrans ((congrAdd (sum_zero _ _) ot_00).eqTrans (add_zero _))

theorem Os_one : Γ ⊢[PRAAx] Os (succ (zero : PTm n)) ≐ succ zero * cat (succ zero) := by
  have s₁ := sum_succ' (Γ := Γ) oB (succ zero) (succ (zero : PTm n))
  have s₀ := sum_succ' (Γ := Γ) oB zero (succ (zero : PTm n))
  rw [inst2_o] at s₁ s₀
  have z₁ : Γ ⊢[PRAAx] ot (succ (zero : PTm n)) (succ zero) ≐ zero :=
    ot_zero (le_congr (.eqRefl _) (by ipra_ring) (le_add_right (succ (succ (zero : PTm n))) one))
  have g : Γ ⊢[PRAAx] gb (succ (zero : PTm n)) (succ (zero + zero)) ≐ one :=
    (congrGb (.eqRefl _) (congrSucc (add_zero _))).eqTrans (gb_self _)
  have p : Γ ⊢[PRAAx] pw two (monus (succ (zero : PTm n)) (succ (zero + zero))) ≐ one :=
    (congrAp2 powF ((congrMonus (.eqRefl _) (congrSucc (add_zero _))).eqTrans (monus_self _)) (.eqRefl two)).eqTrans
      (pw_zero two)
  ipra_lc natEq s₁ + natEq s₀ + natEq (sum_zero (Γ := Γ) oB (succ (zero : PTm n))) + natEq z₁ +
    𝔞 (pw two (monus (succ (zero : PTm n)) (succ (zero + zero)))) * 𝔞 (cat (zero : PTm n)) * natEq g +
    𝔞 (cat (zero : PTm n)) * natEq p + natEq (cat_zero (Γ := Γ)) - natEq (cat_one (Γ := Γ))

theorem Os_step {N : PTm n} (ih : Γ ⊢[PRAAx] Os (succ N) ≐ succ N * cat (succ N)) :
    Γ ⊢[PRAAx] Os (succ (succ N)) ≐ succ (succ N) * cat (succ (succ N)) := by
  have hD : Γ ⊢[PRAAx] succ N * (succ N + two) ≐ succ (pred (succ N * (succ N + two))) :=
    pos_mul' (succ_pos N) (pos_of_eq_succ (c := succ (succ N)) (by ipra_ring))
  refine mul_cancel hD ?_
  have r := natEq (odd_rec (Γ := Γ) (succ N)); have c := natEq (cat_rec (Γ := Γ) (succ N)); have i := natEq ih
  apply deriveNat; ipra_simps
  linear_combination r + 2 * (𝔞 N + 2) * (2 * 𝔞 N + 3) * i - (𝔞 N + 1) * (𝔞 N + 2) * c

private abbrev oddF : Fm PTm 1 := Os (succ (var 0)) ≐ succ (var 0) * cat (succ (var 0))

private theorem odd₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] oddF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact Os_one
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact Os_step Prf.hyp0

theorem odd_succ (N : PTm n) : Γ ⊢[PRAAx] Os (succ N) ≐ succ N * cat (succ N) := by
  have h := inst (Γ := Γ) odd₀ (![N] : Fin 1 → PTm n)
  simpa using h

/-- `O(n)`, as a body over `0 = n`. -/
abbrev oddB : PTm 2 := Os (var 0)
/-- `n Cat_n`, as a body over `0 = n`. -/
abbrev ncB : PTm 2 := var 0 * cat (var 0)

/-- `∑_j C(n, 2j + 1) 2^{n − 2j − 1} (2j + 1) Cat_j = n Cat_n`. -/
theorem odd_sum (N : PTm n) : Γ ⊢[PRAAx] Os N ≐ N * cat N := by
  refine .orE (zero_or_succ N) ?_ ?_
  · have h : ((N ≐ zero) :: Γ) ⊢[PRAAx] N ≐ zero := Prf.hyp0
    exact (cO' h).eqTrans (Os_zero.eqTrans ((zero_mul _).eqSymm.eqTrans (cN' h).eqSymm))
  · have h : ((N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp0
    exact (cO' h).eqTrans ((odd_succ _).eqTrans (cN' h).eqSymm)
where
  cO' {Δ : List (Fm PTm n)} {a b : PTm n} (h : Δ ⊢[PRAAx] a ≐ b) : Δ ⊢[PRAAx] Os a ≐ Os b := by
    have := congrInst2 (Γ := Δ) oddB h (.eqRefl zero)
    simpa [inst2] using this
  cN' {Δ : List (Fm PTm n)} {a b : PTm n} (h : Δ ⊢[PRAAx] a ≐ b) : Δ ⊢[PRAAx] a * cat a ≐ b * cat b := by
    have := congrInst2 (Γ := Δ) ncB h (.eqRefl zero)
    simpa [inst2] using this

/-! ## (2.17) -/

/-- The odd terms with `C(2j + 1, j)` in place of `(2j + 1) Cat_j`. -/
abbrev obB : PTm 2 :=
  gb (var 1) (succ (var 0 + var 0)) * pw two (monus (var 1) (succ (var 0 + var 0))) *
    binom (succ (two * var 0)) (var 0)

theorem odd_binom (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF oB) (succ N) N ≐ ap2 (sumF obB) (succ N) N := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [inst2_o]
  have e : inst2 obB (var 0) (Syn.shift N) = gb (Syn.shift N) (succ (var 0 + var 0)) *
      pw two (monus (Syn.shift N) (succ (var 0 + var 0))) * binom (succ (two * var 0)) (var 0) := by simp [inst2]
  rw [e]
  exact congrMul (.eqRefl _) (cat_odd_binom _)

/-- (2.17), even and odd `k` separated: with `a_k = C(k, ⌊k/2⌋)`,
`∑_{k even} 2^{n − k} C(n, k) a_k = Cat_n + ∑_{k odd} 2^{n − k} C(n, k) a_k`. -/
theorem alternating (N : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF eB) (succ N) N ≐ cat N + ap2 (sumF obB) (succ N) N := by
  ipra_lc natEq (even_sum (Γ := Γ) N : Γ ⊢[PRAAx] ap2 (sumF eB) (succ N) N ≐ cb N) -
    natEq ((odd_binom (Γ := Γ) N).eqSymm.eqTrans (odd_sum N)) - natEq (cat_spec (Γ := Γ) N)

end LeanProofs.IPRA.Combinatorics.CatalanAlternating
