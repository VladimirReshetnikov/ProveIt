import IPRADerivations.DiophantineNumberTheory.AperyRecurrence
import IPRADerivations.Combinatorics.CatalanConvolution
import IPRADerivations.Core.CertificateTactics

/-!
# The two-colored Motzkin sum (Touchard's identity)

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16` (theorem "Two-colored Motzkin sum",
(2.15)): for `n ≥ 1`, `Cat_n = ∑_k Cat_k 2^{n − 2k − 1} C(n − 1, 2k)`, i.e. with `M(n) =
∑_{k ≤ n} C(n, 2k) 2^{n − 2k} Cat_k`,

  `M(n) = Cat_{n + 1}`  for every `n`.

The packet proves this by a bijection with Dyck paths. Here the proof is by creative
telescoping. With `t(n, k) = C(n, 2k) 2^{n − 2k} Cat_k` (guarded, zero for `2k > n`):

* `t1`, `t2`: `(n + 1 − 2k) t(n + 1, k) = 2(n + 1) t(n, k)` and
  `4(k + 1)(k + 2) t(N, k + 1) = (N − 2k)(N − 2k − 1) t(N, k)` for every `k`, from the guarded
  binomial ratios of `DiophantineNumberTheory/AperyRecurrence` and the Catalan ratio recurrence;
* `tpt`: the certificate identity `(n + 1)(n + 3) t(n + 1, k) + V(k + 1) = 2(n + 1)(2n + 3) t(n, k)
  + V(k)` with `V(k) = 4k(k + 1) t(n + 1, k)`, i.e. `G(n, k) = −V(k)/(n + 1)` is a certificate for
  `(n + 3) M(n + 1) = 2(2n + 3) M(n)`;
* `phi`: summing `tpt` over `k < K` telescopes `V`;
* `touch_rec`: at `K = n + 2`, `V(K) = 0`, so `(n + 3) M(n + 1) = 2(2n + 3) M(n)`;
* `touchard`: `M(0) = 1 = Cat_1`, and `(n + 3) Cat_{n + 2} = 2(2n + 3) Cat_{n + 1}` gives
  `M(n) = Cat_{n + 1}` by induction.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanTouchard

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_above)
open LeanProofs.IPRA.Combinatorics.Catalan (cb cat cat_rec cat_zero succ_pos)
open LeanProofs.IPRA.Combinatorics.CatalanConvolution (cat_one)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyRecurrence (gr gl uv)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `t(N, k) = C(N, 2k) 2^{N − 2k} Cat_k`. -/
abbrev mt {n : ℕ} (N k : PTm n) : PTm n := gb N (k + k) * pw two (monus N (k + k)) * cat k

theorem mt_zero {N k : PTm n} (h : Γ ⊢[PRAAx] le (succ N) (k + k)) : Γ ⊢[PRAAx] mt N k ≐ zero :=
  (congrMul (congrMul (gb_above h) (.eqRefl _)) (.eqRefl _)).eqTrans
    ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))

/-! ## The two ratios -/

theorem t1aux {U G1 G0 P1 P0 C S : PTm n} (L : Γ ⊢[PRAAx] U * G1 ≐ S * G0) (hp : Γ ⊢[PRAAx] P1 ≐ P0 * two) :
    Γ ⊢[PRAAx] U * (G1 * P1 * C) ≐ two * S * (G0 * P0 * C) := by
  ipra_lc 𝔞 P1 * 𝔞 C * natEq L + 𝔞 S * 𝔞 G0 * 𝔞 C * natEq hp

theorem t1aux0 {U G1 G0 P1 P0 C S : PTm n} (L : Γ ⊢[PRAAx] U * G1 ≐ S * G0) (hz : Γ ⊢[PRAAx] G0 ≐ zero) :
    Γ ⊢[PRAAx] U * (G1 * P1 * C) ≐ two * S * (G0 * P0 * C) := by
  ipra_lc 𝔞 P1 * 𝔞 C * natEq L + 𝔞 S * (𝔞 P1 * 𝔞 C - 2 * 𝔞 P0 * 𝔞 C) * natEq hz

/-- `(n + 1 − 2k) t(n + 1, k) = 2(n + 1) t(n, k)`. -/
theorem t1 (N k : PTm n) : Γ ⊢[PRAAx] monus (succ N) (k + k) * mt (succ N) k ≐ two * succ N * mt N k := by
  have L := gl (Γ := Γ) N (k + k)
  refine .orE (lt_or_le N (k + k)) ?_ ?_
  · exact t1aux0 L.wk (gb_above Prf.hyp0)
  · have hl : (le (k + k) N :: Γ) ⊢[PRAAx] le (k + k) N := Prf.hyp0
    have e : (le (k + k) N :: Γ) ⊢[PRAAx] monus (succ N) (k + k) ≐ succ (monus N (k + k)) := by
      have e₀ : (le (k + k) N :: Γ) ⊢[PRAAx] succ N ≐ succ (monus N (k + k)) + (k + k) := by
        ipra_lc natEq (eq_add_of_le hl)
      exact (congrMonus e₀ (.eqRefl _)).eqTrans (add_monus _ _)
    exact t1aux L.wk ((congrAp2 powF e (.eqRefl two)).eqTrans (pw_succ two _))

theorem t2aux {G0 Ga Gb Gb' Pb P0 C Cs K U V : PTm n} (E : Γ ⊢[PRAAx] Gb' ≐ Gb)
    (r1 : Γ ⊢[PRAAx] succ (K + K) * Ga ≐ U * G0) (r2 : Γ ⊢[PRAAx] succ (succ (K + K)) * Gb ≐ V * Ga)
    (cr : Γ ⊢[PRAAx] succ (succ K) * Cs ≐ two * succ (two * K) * C) (hp : Γ ⊢[PRAAx] P0 ≐ Pb * two * two) :
    Γ ⊢[PRAAx] num 4 * (succ K * succ (succ K)) * (Gb' * Pb * Cs) ≐ U * V * (G0 * P0 * C) := by
  ipra_lc 4 * (𝔞 K + 1) * (𝔞 K + 2) * 𝔞 Pb * 𝔞 Cs * natEq E + 2 * 𝔞 Pb * (𝔞 K + 2) * 𝔞 Cs * natEq r2 +
    2 * 𝔞 Pb * 𝔞 V * 𝔞 Ga * natEq cr + 4 * 𝔞 Pb * 𝔞 V * 𝔞 C * natEq r1 - 𝔞 U * 𝔞 V * 𝔞 G0 * 𝔞 C * natEq hp

/-- `4(k + 1)(k + 2) t(N, k + 1) = (N − 2k)(N − 2k − 1) t(N, k)`. -/
theorem t2 (N k : PTm n) :
    Γ ⊢[PRAAx] num 4 * (succ k * succ (succ k)) * mt N (succ k) ≐
      monus N (k + k) * monus N (succ (k + k)) * mt N k := by
  have E : Γ ⊢[PRAAx] gb N (succ k + succ k) ≐ gb N (succ (succ (k + k))) := congrGb (.eqRefl _) (by ipra_ring)
  refine .orE (lt_or_le (succ (k + k)) N) ?_ ?_
  · have hl : (lt (succ (k + k)) N :: Γ) ⊢[PRAAx] lt (succ (k + k)) N := Prf.hyp0
    have hl' : (lt (succ (k + k)) N :: Γ) ⊢[PRAAx] le (succ k + succ k) N :=
      (congrMonus (by ipra_ring) (.eqRefl _)).eqTrans hl
    have e₀ : (lt (succ (k + k)) N :: Γ) ⊢[PRAAx] N ≐ succ (succ (monus N (succ k + succ k))) + (k + k) := by
      ipra_lc natEq (eq_add_of_le hl')
    have e : (lt (succ (k + k)) N :: Γ) ⊢[PRAAx] monus N (k + k) ≐ succ (succ (monus N (succ k + succ k))) :=
      (congrMonus e₀ (.eqRefl _)).eqTrans (add_monus _ _)
    have hp := (congrAp2 powF e (.eqRefl two)).eqTrans ((pw_succ two _).eqTrans (congrMul (pw_succ two _) (.eqRefl _)))
    exact t2aux E.wk (gr N (k + k)) (gr N (succ (k + k))) (cat_rec k) hp
  · have hl : (le N (succ (k + k)) :: Γ) ⊢[PRAAx] le N (succ (k + k)) := Prf.hyp0
    have gz : (le N (succ (k + k)) :: Γ) ⊢[PRAAx] gb N (succ (succ (k + k))) ≐ zero :=
      gb_above ((succ_monus_succ _ _).eqTrans hl)
    have tz : (le N (succ (k + k)) :: Γ) ⊢[PRAAx] mt N (succ k) ≐ zero :=
      (congrMul (congrMul (E.wk.eqTrans gz) (.eqRefl _)) (.eqRefl _)).eqTrans
        ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))
    exact ((congrMul (.eqRefl _) tz).eqTrans (mul_zero _)).eqTrans
      ((congrMul ((congrMul (.eqRefl _) hl).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm

/-! ## The certificate -/

theorem ptaux {N K T tp t0 u v : PTm n} (hR1 : Γ ⊢[PRAAx] u * T ≐ two * succ N * t0)
    (hR2 : Γ ⊢[PRAAx] num 4 * (succ K * succ (succ K)) * tp ≐ u * v * T)
    (hu : Γ ⊢[PRAAx] succ N ≐ (K + K) + u) (hv : Γ ⊢[PRAAx] v * u + u ≐ u * u) :
    Γ ⊢[PRAAx] succ N * (N + num 3) * T + num 4 * (succ K * succ (succ K)) * tp ≐
      two * succ N * (two * N + num 3) * t0 + num 4 * (K * succ K) * T := by
  have r1 := natEq hR1; have r2 := natEq hR2; have e := natEq hu; have f := natEq hv
  apply deriveNat; ipra_simps
  have eN : Groth.ι (Q.mk Γ N) = 2 * Groth.ι (Q.mk Γ K) + Groth.ι (Q.mk Γ u) - 1 := by linear_combination e
  rw [eN] at r1 ⊢
  linear_combination r2 + (2 * (2 * 𝔞 K + 𝔞 u - 1) + 3) * r1 + 𝔞 T * f

theorem ptaux0 {N K T tp t0 u v : PTm n} (hR1 : Γ ⊢[PRAAx] u * T ≐ two * succ N * t0)
    (hR2 : Γ ⊢[PRAAx] num 4 * (succ K * succ (succ K)) * tp ≐ u * v * T) (hT : Γ ⊢[PRAAx] T ≐ zero) :
    Γ ⊢[PRAAx] succ N * (N + num 3) * T + num 4 * (succ K * succ (succ K)) * tp ≐
      two * succ N * (two * N + num 3) * t0 + num 4 * (K * succ K) * T := by
  ipra_lc natEq hR2 + (2 * 𝔞 N + 3) * natEq hR1 +
    ((𝔞 N + 1) * (𝔞 N + 3) + 𝔞 u * 𝔞 v - (2 * 𝔞 N + 3) * 𝔞 u - 4 * 𝔞 K * (𝔞 K + 1)) * natEq hT

/-- `(n + 1)(n + 3) t(n + 1, k) + V(k + 1) = 2(n + 1)(2n + 3) t(n, k) + V(k)`, `V(k) = 4k(k + 1) t(n + 1, k)`. -/
theorem tpt (N k : PTm n) :
    Γ ⊢[PRAAx] succ N * (N + num 3) * mt (succ N) k + num 4 * (succ k * succ (succ k)) * mt (succ N) (succ k) ≐
      two * succ N * (two * N + num 3) * mt N k + num 4 * (k * succ k) * mt (succ N) k := by
  have hR1 := t1 (Γ := Γ) N k
  have hR2 := (t2 (Γ := Γ) (succ N) k).eqTrans (congrMul (congrMul (.eqRefl _) (succ_monus_succ _ _)) (.eqRefl _))
  refine .orE (lt_or_le (succ N) (k + k)) ?_ ?_
  · exact ptaux0 hR1.wk hR2.wk (mt_zero Prf.hyp0)
  · exact ptaux hR1.wk hR2.wk (eq_add_of_le Prf.hyp0) (uv N (k + k))

/-! ## Telescoping -/

/-- `t(x, k)`, over `0 = k`, `1 = x`. -/
abbrev mtB : PTm 2 := mt (var 1) (var 0)

theorem inst2_mt (k x : PTm n) : inst2 mtB k x = mt x k := by simp [inst2]

/-- `∑_{k < K} t(x, k)`. -/
abbrev Sx {n : ℕ} (K x : PTm n) : PTm n := ap2 (sumF mtB) K x

abbrev phiL {n : ℕ} (N K : PTm n) : PTm n :=
  succ N * (N + num 3) * Sx K (succ N) + num 4 * (K * succ K) * mt (succ N) K
abbrev phiR {n : ℕ} (N K : PTm n) : PTm n := two * succ N * (two * N + num 3) * Sx K N

theorem phi_base (N : PTm n) : Γ ⊢[PRAAx] phiL N zero ≐ phiR N zero := by
  ipra_lc (𝔞 N + 1) * (𝔞 N + 3) * natEq (sum_zero (Γ := Γ) mtB (succ N)) -
    2 * (𝔞 N + 1) * (2 * 𝔞 N + 3) * natEq (sum_zero (Γ := Γ) mtB N)

theorem phi_step {N K : PTm n} (ih : Γ ⊢[PRAAx] phiL N K ≐ phiR N K) :
    Γ ⊢[PRAAx] phiL N (succ K) ≐ phiR N (succ K) := by
  have s₁ := sum_succ' (Γ := Γ) mtB K (succ N); have s₂ := sum_succ' (Γ := Γ) mtB K N
  rw [inst2_mt] at s₁ s₂
  ipra_lc natEq ih + (𝔞 N + 1) * (𝔞 N + 3) * natEq s₁ - 2 * (𝔞 N + 1) * (2 * 𝔞 N + 3) * natEq s₂ +
    natEq (tpt (Γ := Γ) N K)

/-- Variables: `0 = K`, `1 = N`. -/
private abbrev phiF : Fm PTm 2 := phiL (var 1) (var 0) ≐ phiR (var 1) (var 0)

private theorem phi₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] phiF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact phi_base _
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact phi_step Prf.hyp0

theorem phi (N K : PTm n) : Γ ⊢[PRAAx] phiL N K ≐ phiR N K := by
  have h := inst (Γ := Γ) phi₀ (![K, N] : Fin 2 → PTm n)
  simpa using h

/-! ## The recurrence and the identity -/

/-- `M(n) = ∑_{k ≤ n} C(n, 2k) 2^{n − 2k} Cat_k`. -/
abbrev M {n : ℕ} (N : PTm n) : PTm n := Sx (succ N) N

/-- `(n + 3) M(n + 1) = 2(2n + 3) M(n)`. -/
theorem touch_rec (N : PTm n) :
    Γ ⊢[PRAAx] succ (succ (succ N)) * M (succ N) ≐ two * (two * N + num 3) * M N := by
  refine mul_cancel (succ_pos N) ?_
  have h := natEq (phi (Γ := Γ) N (succ (succ N)))
  have z := natEq (mt_zero (Γ := Γ) (le_add_right (succ (succ N)) (succ (succ N))))
  have s := sum_succ' (Γ := Γ) mtB (succ N) N
  rw [inst2_mt] at s
  have s' := natEq s
  have z' := natEq (mt_zero (Γ := Γ) (le_add_right (succ N) (succ N)))
  apply deriveNat; ipra_simps
  linear_combination h - 4 * (𝔞 N + 2) * (𝔞 N + 3) * z + 2 * (𝔞 N + 1) * (2 * 𝔞 N + 3) * s' +
    2 * (𝔞 N + 1) * (2 * 𝔞 N + 3) * z'

theorem M_zero : Γ ⊢[PRAAx] M (zero : PTm n) ≐ cat (succ zero) := by
  have s := sum_succ' (Γ := Γ) mtB zero (zero : PTm n)
  rw [inst2_mt] at s
  have g : Γ ⊢[PRAAx] gb (zero : PTm n) (zero + zero) ≐ one := (congrGb (.eqRefl _) (add_zero _)).eqTrans (gb_zero _)
  have p : Γ ⊢[PRAAx] pw two (monus (zero : PTm n) (zero + zero)) ≐ one :=
    (congrAp2 powF (zero_monus _) (.eqRefl two)).eqTrans (pw_zero two)
  have t : Γ ⊢[PRAAx] mt (zero : PTm n) zero ≐ one :=
    (congrMul (congrMul g p) cat_zero).eqTrans ((congrMul (one_mul _) (.eqRefl _)).eqTrans (one_mul _))
  exact s.eqTrans ((congrAdd (sum_zero _ _) t).eqTrans ((zero_add _).eqTrans cat_one.eqSymm))

theorem M_step {N : PTm n} (ih : Γ ⊢[PRAAx] M N ≐ cat (succ N)) : Γ ⊢[PRAAx] M (succ N) ≐ cat (succ (succ N)) := by
  refine mul_cancel (succ_pos (succ (succ N))) ?_
  ipra_lc natEq (touch_rec (Γ := Γ) N) - natEq (cat_rec (Γ := Γ) (succ N)) + 2 * (2 * 𝔞 N + 3) * natEq ih

/-- Variable: `0 = N`. -/
private abbrev touchF : Fm PTm 1 := M (var 0) ≐ cat (succ (var 0))

private theorem touch₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] touchF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact M_zero
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, PTm.subst_num,
      Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact M_step Prf.hyp0

/-- (2.15): `∑_{k ≤ n} C(n, 2k) 2^{n − 2k} Cat_k = Cat_{n + 1}`. -/
theorem touchard (N : PTm n) : Γ ⊢[PRAAx] M N ≐ cat (succ N) := by
  have h := inst (Γ := Γ) touch₀ (![N] : Fin 1 → PTm n)
  simpa using h

end LeanProofs.IPRA.Combinatorics.CatalanTouchard
