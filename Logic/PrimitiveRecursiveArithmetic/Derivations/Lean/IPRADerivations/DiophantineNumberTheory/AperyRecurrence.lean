import IPRADerivations.DiophantineNumberTheory.AperyNumbers
import IPRADerivations.Combinatorics.CatalanBallot
import IPRADerivations.Probability.BinomialLaw

/-!
# The Apéry recurrence

Packet: `diophantine-number-theory/apery_ipra` (`prop:recurrence` for `y = a`, from the
telescoper `lem:telescoper`). For every `n ≥ 1`,

  `(n + 1)³ a_{n+1} + n³ a_{n−1} = P_n a_n`,  `P_n = (2n + 1)(17n² + 17n + 5)`,

for the Apéry numbers `a_n = ∑_k C(n, k)² C(n + k, k)²` of `DiophantineNumberTheory/AperyNumbers`.
The packet obtains it by applying a partial-fraction functional to the rational telescoper; for the
sequence `a` alone, the same certificate `s_n(t) = 4(2n + 1)(−2t² + t + (2n + 1)²)` acts directly
on the summands `b(n, k) = c(n, k)²`, `c(n, k) = C(n, k) C(n + k, k)` (the coefficients of the
double poles of `R_n`), with no rational functions:

* `gr`, `ga`, `gl`: `(k + 1) C(M, k + 1) = (M − k) C(M, k)`, `(k + 1) C(M + 1, k + 1) = (M + 1) C(M, k)`
  and `(M + 1 − k) C(M + 1, k) = (M + 1) C(M, k)` for the guarded coefficients and every `k`;
* `cA`, `cB`, `cC`: `c(n + 1, k + 1)`, `c(n, k + 1)` and `c(n − 1, k + 1)` times `(k + 1)²` are
  `c(n, k)` times `(n + k + 1)(n + k + 2)`, `(n + k + 1)(n − k)` and `(n − k)(n − 1 − k)`;
* `pt`: with `τ = 4(2n + 1)³` and `σ(k) = 4(2n + 1) k(2k + 1)`, so that `s_n(−k) = σ(k) − τ`,
  the certificate identity in natural numbers
  `(n + 1)³ b(n + 1, k + 1) + n³ b(n − 1, k + 1) + τ b(n, k + 1) + σ(k) b(n, k)
     = P_n b(n, k + 1) + σ(k + 1) b(n, k + 1) + τ b(n, k)`
  for every `k`: multiplied by `(k + 1)⁴` it is `b(n, k)` times a fixed polynomial identity in
  `n, k` (`pt_main`), and for `k > n` everything vanishes (`pt_zero`);
* `phi_base`, `phi_step`: summing `pt` over `k < K` telescopes the `τ` and `σ` terms;
* `apery_rec`: at `K = n + 1` the boundary terms are `τ b(n, 0) = τ` and zero, and
  `(n + 1)³ + n³ + τ = P_n` closes the recurrence.

The sequence `b_n`, the Wronskian and the irrationality argument are not formalized.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyRecurrence

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.Combinatorics.Stirling (gle gle_of_le)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_above zB zsum inst2_z)
open LeanProofs.IPRA.Combinatorics.CatalanBallot (binom_ratio)
open LeanProofs.IPRA.Combinatorics.Catalan (succ_pos)
open LeanProofs.IPRA.Combinatorics.CatalanNarayana (le_of_lt_succ)
open LeanProofs.IPRA.Probability.BinomialLaw (absorption)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyNumbers (apB inst2_ap apery)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Ratios of guarded binomial coefficients -/

/-- `(k + 1) C(M, k + 1) = (M − k) C(M, k)` for every `k`. -/
theorem gr (M k : PTm n) : Γ ⊢[PRAAx] succ k * gb M (succ k) ≐ monus M k * gb M k := by
  refine .orE (lt_or_le k M) ?_ ?_
  · have hl : (lt k M :: Γ) ⊢[PRAAx] lt k M := Prf.hyp0
    ipra_lc (𝔞 k + 1) * 𝔞(binom M (succ k)) * natEq (gle_of_le hl) -
      𝔞(monus M k) * 𝔞(binom M k) * natEq (gle_of_le (le_of_lt hl)) - natEq (binom_ratio hl)
  · have hl : (le M k :: Γ) ⊢[PRAAx] le M k := Prf.hyp0
    have z₁ : (le M k :: Γ) ⊢[PRAAx] gb M (succ k) ≐ zero := gb_above ((succ_monus_succ _ _).eqTrans hl)
    exact ((congrMul (.eqRefl _) z₁).eqTrans (mul_zero _)).eqTrans
      ((congrMul hl (.eqRefl _)).eqTrans (zero_mul _)).eqSymm

/-- `(k + 1) C(M + 1, k + 1) = (M + 1) C(M, k)` for every `k`. -/
theorem ga (M k : PTm n) : Γ ⊢[PRAAx] succ k * gb (succ M) (succ k) ≐ succ M * gb M k := by
  refine .orE (lt_or_le M k) ?_ ?_
  · have hl : (lt M k :: Γ) ⊢[PRAAx] lt M k := Prf.hyp0
    have z₁ : (lt M k :: Γ) ⊢[PRAAx] gb (succ M) (succ k) ≐ zero := gb_above ((succ_monus_succ _ _).eqTrans hl)
    have z₀ : (lt M k :: Γ) ⊢[PRAAx] gb M k ≐ zero := gb_above hl
    exact ((congrMul (.eqRefl _) z₁).eqTrans (mul_zero _)).eqTrans
      ((congrMul (.eqRefl _) z₀).eqTrans (mul_zero _)).eqSymm
  · have hl : (le k M :: Γ) ⊢[PRAAx] le k M := Prf.hyp0
    have hs : (le k M :: Γ) ⊢[PRAAx] le (succ k) (succ M) := (succ_monus_succ _ _).eqTrans hl
    ipra_lc (𝔞 k + 1) * 𝔞(binom (succ M) (succ k)) * natEq (gle_of_le hs) -
      (𝔞 M + 1) * 𝔞(binom M k) * natEq (gle_of_le hl) + natEq (absorption hl)

/-- `(M + 1 − k) C(M + 1, k) = (M + 1) C(M, k)` for every `k`. -/
theorem gl (M k : PTm n) : Γ ⊢[PRAAx] monus (succ M) k * gb (succ M) k ≐ succ M * gb M k :=
  (gr (succ M) k).eqSymm.eqTrans (ga M k)

/-- `(N + 1) C(N + k + 1, k) = (N + k + 1) C(N + k, k)`. -/
theorem l1 (N k : PTm n) : Γ ⊢[PRAAx] succ N * gb (succ (N + k)) k ≐ succ (N + k) * gb (N + k) k := by
  have e₀ : Γ ⊢[PRAAx] succ (N + k) ≐ succ N + k := by ipra_ring
  have e : Γ ⊢[PRAAx] monus (succ (N + k)) k ≐ succ N := (congrMonus e₀ (.eqRefl _)).eqTrans (add_monus _ _)
  exact (congrMul e.eqSymm (.eqRefl _)).eqTrans (gl (N + k) k)

/-! ## The coefficients `c(n, k) = C(n, k) C(n + k, k)` -/

/-- `c(N, k) = C(N, k) C(N + k, k)`, zero for `k > N`. -/
abbrev cf {n : ℕ} (N k : PTm n) : PTm n := gb N k * gb (N + k) k

/-- `b(N, k) = c(N, k)²`. -/
abbrev bb {n : ℕ} (N k : PTm n) : PTm n := cf N k * cf N k

theorem congrCf {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] cf a b ≐ cf a' b' :=
  congrMul (congrGb ha hb) (congrGb (congrAdd ha hb) hb)

theorem cf_zero (N : PTm n) : Γ ⊢[PRAAx] cf N zero ≐ one :=
  (congrMul (gb_zero N) (gb_zero _)).eqTrans (one_mul _)

theorem bb_zero (N : PTm n) : Γ ⊢[PRAAx] bb N zero ≐ one :=
  (congrMul (cf_zero N) (cf_zero N)).eqTrans (one_mul _)

theorem bb_above {N k : PTm n} (h : Γ ⊢[PRAAx] le (succ N) k) : Γ ⊢[PRAAx] bb N k ≐ zero :=
  (congrMul ((congrMul (gb_above h) (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (zero_mul _)

theorem auxA {g₁ gX gY gN gZ gW K N1 S1 S2 : PTm n} (E : Γ ⊢[PRAAx] gX ≐ gY)
    (G1 : Γ ⊢[PRAAx] K * g₁ ≐ N1 * gN) (G2 : Γ ⊢[PRAAx] K * gY ≐ S2 * gZ)
    (G3 : Γ ⊢[PRAAx] N1 * gZ ≐ S1 * gW) : Γ ⊢[PRAAx] (g₁ * gX) * (K * K) ≐ (gN * gW) * (S1 * S2) := by
  ipra_lc 𝔞 K ^ 2 * 𝔞 g₁ * natEq E + 𝔞 K * 𝔞 gY * natEq G1 + 𝔞 N1 * 𝔞 gN * natEq G2 + 𝔞 gN * 𝔞 S2 * natEq G3

theorem auxB {gA gX gY gN gW K U S : PTm n} (E : Γ ⊢[PRAAx] gX ≐ gY)
    (R : Γ ⊢[PRAAx] K * gA ≐ U * gN) (G : Γ ⊢[PRAAx] K * gY ≐ S * gW) :
    Γ ⊢[PRAAx] (gA * gX) * (K * K) ≐ (gN * gW) * (S * U) := by
  ipra_lc 𝔞 K ^ 2 * 𝔞 gA * natEq E + 𝔞 K * 𝔞 gY * natEq R + 𝔞 U * 𝔞 gN * natEq G

theorem auxC {gA gX gY gM gW gS gV gZ K V U Sm S : PTm n} (E : Γ ⊢[PRAAx] gX ≐ gY)
    (R : Γ ⊢[PRAAx] K * gA ≐ V * gM) (G : Γ ⊢[PRAAx] K * gY ≐ S * gW)
    (L : Γ ⊢[PRAAx] U * gS ≐ Sm * gM) (E' : Γ ⊢[PRAAx] gV ≐ gZ) (L1 : Γ ⊢[PRAAx] Sm * gZ ≐ S * gW) :
    Γ ⊢[PRAAx] (gA * gX) * (K * K) ≐ (gS * gV) * (U * V) := by
  have e := natEq E; have a := natEq R; have b := natEq G; have c := natEq L; have e' := natEq E'
  have d := natEq L1
  apply deriveNat; ipra_simps
  linear_combination 𝔞 K ^ 2 * 𝔞 gA * e + 𝔞 K * 𝔞 gY * a + 𝔞 V * 𝔞 gM * b - 𝔞 gV * 𝔞 V * c -
    𝔞 Sm * 𝔞 gM * 𝔞 V * e' - 𝔞 gM * 𝔞 V * d

/-- `c(N + 1, k + 1)(k + 1)² = c(N, k)(N + k + 1)(N + k + 2)`. -/
theorem cA (N k : PTm n) :
    Γ ⊢[PRAAx] cf (succ N) (succ k) * (succ k * succ k) ≐ cf N k * (succ (N + k) * succ (succ (N + k))) := by
  have E : Γ ⊢[PRAAx] gb (succ N + succ k) (succ k) ≐ gb (succ (succ (N + k))) (succ k) :=
    congrGb (by ipra_ring) (.eqRefl _)
  exact auxA E (ga N k) (ga (succ (N + k)) k) (l1 N k)

/-- `c(N, k + 1)(k + 1)² = c(N, k)(N + k + 1)(N − k)`. -/
theorem cB (N k : PTm n) :
    Γ ⊢[PRAAx] cf N (succ k) * (succ k * succ k) ≐ cf N k * (succ (N + k) * monus N k) := by
  have E : Γ ⊢[PRAAx] gb (N + succ k) (succ k) ≐ gb (succ (N + k)) (succ k) := congrGb (by ipra_ring) (.eqRefl _)
  exact auxB E (gr N k) (ga (N + k) k)

/-- `c(m, k + 1)(k + 1)² = c(m + 1, k)(m + 1 − k)(m − k)`. -/
theorem cC (m k : PTm n) :
    Γ ⊢[PRAAx] cf m (succ k) * (succ k * succ k) ≐ cf (succ m) k * (monus (succ m) k * monus m k) := by
  have E : Γ ⊢[PRAAx] gb (m + succ k) (succ k) ≐ gb (succ (m + k)) (succ k) := congrGb (by ipra_ring) (.eqRefl _)
  have E' : Γ ⊢[PRAAx] gb (succ m + k) k ≐ gb (succ (m + k)) k := congrGb (by ipra_ring) (.eqRefl _)
  exact auxC E (gr m k) (ga (m + k) k) (gl m k) E' (l1 m k)

/-! ## The certificate -/

abbrev cube {n : ℕ} (a : PTm n) : PTm n := a * a * a
/-- `τ = 4(2N + 1)³`. -/
abbrev tau {n : ℕ} (N : PTm n) : PTm n := num 4 * cube (two * N + one)
/-- `σ(k) = 4(2N + 1) k(2k + 1)`; `s_N(−k) = σ(k) − τ`. -/
abbrev sig {n : ℕ} (N k : PTm n) : PTm n := num 4 * (two * N + one) * (k * (two * k + one))
/-- `P_N = (2N + 1)(17N² + 17N + 5)`. -/
abbrev Pn {n : ℕ} (N : PTm n) : PTm n := (two * N + one) * (num 17 * (N * N) + num 17 * N + num 5)

/-- The left side of the certificate identity, over opaque coefficients. -/
abbrev lhsE {n : ℕ} (N k d c0 cp cm : PTm n) : PTm n :=
  cube (succ N) * (cp * cp) + cube N * (cm * cm) + tau N * (c0 * c0) + sig N k * (d * d)
/-- The right side of the certificate identity. -/
abbrev rhsE {n : ℕ} (N k d c0 : PTm n) : PTm n :=
  Pn N * (c0 * c0) + sig N (succ k) * (c0 * c0) + tau N * (d * d)

theorem k4_pos (k : PTm n) :
    Γ ⊢[PRAAx] succ k * succ k * (succ k * succ k) ≐ succ (pred (succ k * succ k * (succ k * succ k))) :=
  pos_mul' (pos_mul' (succ_pos k) (succ_pos k)) (pos_mul' (succ_pos k) (succ_pos k))

/-- The certificate identity for `k ≤ N`, cleared of `(k + 1)⁴`; `u = N − k`, `v = N − 1 − k`. -/
theorem pt_main {N k u v d c0 cp cm : PTm n}
    (hA : Γ ⊢[PRAAx] cp * (succ k * succ k) ≐ d * (succ (N + k) * succ (succ (N + k))))
    (hB : Γ ⊢[PRAAx] c0 * (succ k * succ k) ≐ d * (succ (N + k) * u))
    (hC : Γ ⊢[PRAAx] cm * (succ k * succ k) ≐ d * (u * v))
    (hu : Γ ⊢[PRAAx] N ≐ k + u) (hv : Γ ⊢[PRAAx] v * u + u ≐ u * u) :
    Γ ⊢[PRAAx] lhsE N k d c0 cp cm ≐ rhsE N k d c0 := by
  refine mul_cancel (k4_pos k) ?_
  have a := natEq hA; have b := natEq hB; have c := natEq hC; have e := natEq hu; have f := natEq hv
  apply deriveNat; ipra_simps
  rw [e] at a b ⊢
  linear_combination ((𝔞 k + 𝔞 u) + 1)^3 * (𝔞 cp * (𝔞 k + 1)^2 + 𝔞 d * (((𝔞 k + 𝔞 u) + 𝔞 k + 1) * ((𝔞 k + 𝔞 u) + 𝔞 k + 2))) * a + ((4 * (2 * (𝔞 k + 𝔞 u) + 1)^3) - ((2 * (𝔞 k + 𝔞 u) + 1) * (17 * (𝔞 k + 𝔞 u)^2 + 17 * (𝔞 k + 𝔞 u) + 5)) - (4 * (2 * (𝔞 k + 𝔞 u) + 1) * ((𝔞 k + 1) * (2 * (𝔞 k + 1) + 1)))) * (𝔞 c0 * (𝔞 k + 1)^2 + 𝔞 d * (((𝔞 k + 𝔞 u) + 𝔞 k + 1) * 𝔞 u)) * b + (𝔞 k + 𝔞 u)^3 * (𝔞 cm * (𝔞 k + 1)^2 + 𝔞 d * (𝔞 u * 𝔞 v)) * c + (𝔞 k + 𝔞 u)^3 * (𝔞 d)^2 * (𝔞 u * 𝔞 v + (𝔞 u)^2 - 𝔞 u) * f

/-- The certificate identity when `c(N, k) = 0`. -/
theorem pt_zero {N k u v d c0 cp cm : PTm n}
    (hA : Γ ⊢[PRAAx] cp * (succ k * succ k) ≐ d * (succ (N + k) * succ (succ (N + k))))
    (hB : Γ ⊢[PRAAx] c0 * (succ k * succ k) ≐ d * (succ (N + k) * u))
    (hC : Γ ⊢[PRAAx] cm * (succ k * succ k) ≐ d * (u * v)) (hd : Γ ⊢[PRAAx] d ≐ zero) :
    Γ ⊢[PRAAx] lhsE N k d c0 cp cm ≐ rhsE N k d c0 := by
  refine mul_cancel (k4_pos k) ?_
  have a := natEq hA; have b := natEq hB; have c := natEq hC; have hd := natEq hd
  apply deriveNat; ipra_simps
  linear_combination (𝔞 N + 1)^3 * (𝔞 cp * (𝔞 k + 1)^2 + 𝔞 d * ((𝔞 N + 𝔞 k + 1) * (𝔞 N + 𝔞 k + 2))) * a + ((4 * (2 * 𝔞 N + 1)^3) - ((2 * 𝔞 N + 1) * (17 * (𝔞 N)^2 + 17 * 𝔞 N + 5)) - (4 * (2 * 𝔞 N + 1) * ((𝔞 k + 1) * (2 * (𝔞 k + 1) + 1)))) * (𝔞 c0 * (𝔞 k + 1)^2 + 𝔞 d * ((𝔞 N + 𝔞 k + 1) * 𝔞 u)) * b + (𝔞 N)^3 * (𝔞 cm * (𝔞 k + 1)^2 + 𝔞 d * (𝔞 u * 𝔞 v)) * c + 𝔞 d * ((𝔞 N + 1)^3 * ((𝔞 N + 𝔞 k + 1) * (𝔞 N + 𝔞 k + 2))^2 + (𝔞 N)^3 * (𝔞 u * 𝔞 v)^2 + ((4 * (2 * 𝔞 N + 1)^3) - ((2 * 𝔞 N + 1) * (17 * (𝔞 N)^2 + 17 * 𝔞 N + 5)) - (4 * (2 * 𝔞 N + 1) * ((𝔞 k + 1) * (2 * (𝔞 k + 1) + 1)))) * ((𝔞 N + 𝔞 k + 1) * 𝔞 u)^2 + ((4 * (2 * 𝔞 N + 1) * (𝔞 k * (2 * 𝔞 k + 1))) - (4 * (2 * 𝔞 N + 1)^3)) * (𝔞 k + 1)^4) * hd

/-- `(m − k)(m + 1 − k) + (m + 1 − k) = (m + 1 − k)²`. -/
theorem uv (m k : PTm n) :
    Γ ⊢[PRAAx] monus m k * monus (succ m) k + monus (succ m) k ≐ monus (succ m) k * monus (succ m) k := by
  refine .orE (lt_or_le m k) ?_ ?_
  · ipra_lc (𝔞(monus m k) + 1 - 𝔞(monus (succ m) k)) * natEq (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := lt m k))
  · have hl : (le k m :: Γ) ⊢[PRAAx] le k m := Prf.hyp0
    have e : (le k m :: Γ) ⊢[PRAAx] monus (succ m) k ≐ succ (monus m k) := by
      have e₀ : (le k m :: Γ) ⊢[PRAAx] succ m ≐ succ (monus m k) + k := by
        ipra_lc natEq (eq_add_of_le hl)
      exact (congrMonus e₀ (.eqRefl _)).eqTrans (add_monus _ _)
    ipra_lc (-𝔞(monus (succ m) k)) * natEq e

/-- The certificate identity for `n = m + 1` and every `k`. -/
theorem pt (m k : PTm n) :
    Γ ⊢[PRAAx] lhsE (succ m) k (cf (succ m) k) (cf (succ m) (succ k)) (cf (succ (succ m)) (succ k)) (cf m (succ k)) ≐
      rhsE (succ m) k (cf (succ m) k) (cf (succ m) (succ k)) := by
  have hA := cA (Γ := Γ) (succ m) k; have hB := cB (Γ := Γ) (succ m) k; have hC := cC (Γ := Γ) m k
  refine .orE (lt_or_le (succ m) k) ?_ ?_
  · have hl : (lt (succ m) k :: Γ) ⊢[PRAAx] lt (succ m) k := Prf.hyp0
    have hd : (lt (succ m) k :: Γ) ⊢[PRAAx] cf (succ m) k ≐ zero :=
      (congrMul (gb_above hl) (.eqRefl _)).eqTrans (zero_mul _)
    exact pt_zero hA.wk hB.wk hC.wk hd
  · exact pt_main hA.wk hB.wk hC.wk (eq_add_of_le Prf.hyp0) (uv m k)

/-! ## Telescoping the certificate -/

/-- `b(x, k)`, over `0 = k`, `1 = x`. -/
abbrev bbB : PTm 2 := bb (var 1) (var 0)

theorem inst2_bb (k x : PTm n) : inst2 bbB k x = bb x k := by simp [inst2]

/-- `∑_{k < K} b(x, k + 1)`. -/
abbrev Ssum {n : ℕ} (K x : PTm n) : PTm n := ap2 (sumF (shiftBody bbB)) K x

/-- The partial sums of the certificate identity over `k < K`, for `n = m + 1`. -/
abbrev phiL {n : ℕ} (m K : PTm n) : PTm n :=
  cube (succ (succ m)) * Ssum K (succ (succ m)) + cube (succ m) * Ssum K m + tau (succ m) * bb (succ m) K +
    sig (succ m) zero * bb (succ m) zero
abbrev phiR {n : ℕ} (m K : PTm n) : PTm n :=
  Pn (succ m) * Ssum K (succ m) + sig (succ m) K * bb (succ m) K + tau (succ m) * bb (succ m) zero

theorem phi_base (m : PTm n) : Γ ⊢[PRAAx] phiL m zero ≐ phiR m zero := by
  ipra_lc (𝔞 m + 2) ^ 3 * natEq (sum_zero (shiftBody bbB) (succ (succ m))) +
    (𝔞 m + 1) ^ 3 * natEq (sum_zero (shiftBody bbB) m) -
    (2 * (𝔞 m + 1) + 1) * (17 * (𝔞 m + 1) ^ 2 + 17 * (𝔞 m + 1) + 5) * natEq (sum_zero (shiftBody bbB) (succ m))

theorem phi_step {m K : PTm n} (ih : Γ ⊢[PRAAx] phiL m K ≐ phiR m K) :
    Γ ⊢[PRAAx] phiL m (succ K) ≐ phiR m (succ K) := by
  have s₁ := sum_succ' (Γ := Γ) (shiftBody bbB) K (succ (succ m))
  have s₂ := sum_succ' (Γ := Γ) (shiftBody bbB) K m
  have s₃ := sum_succ' (Γ := Γ) (shiftBody bbB) K (succ m)
  rw [inst2_shiftBody, inst2_bb] at s₁ s₂ s₃
  ipra_lc natEq ih + (𝔞 m + 2) ^ 3 * natEq s₁ + (𝔞 m + 1) ^ 3 * natEq s₂ -
    (2 * (𝔞 m + 1) + 1) * (17 * (𝔞 m + 1) ^ 2 + 17 * (𝔞 m + 1) + 5) * natEq s₃ + natEq (pt m K)

/-- Variables: `0 = K`, `1 = m`. -/
private abbrev phiF : Fm PTm 2 := phiL (var 1) (var 0) ≐ phiR (var 1) (var 0)

private theorem phi₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] phiF := by
  ipra_ind [subst_ap2]
  · exact phi_base _
  · exact phi_step Prf.hyp0

theorem phi (m K : PTm n) : Γ ⊢[PRAAx] phiL m K ≐ phiR m K := by
  have h := inst (Γ := Γ) phi₀ (![K, m] : Fin 2 → PTm n)
  simpa using h

/-! ## The recurrence -/

/-- `a_N = ∑_{k ≤ N} b(N, k)`. -/
theorem apery_bb (N : PTm n) : Γ ⊢[PRAAx] apery N ≐ ap2 (sumF bbB) (succ N) N := by
  refine sum_congr_bounded apB bbB N N (succ N) (.allI (.impI ?_))
  have e₁ : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  rw [inst2_ap, inst2_bb, e₁]
  have hk := le_of_lt_succ (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift) (φ := lt (var 0) (succ (Syn.shift N))))
  have hc := congrMul ((congrMul (gle_of_le hk) (.eqRefl (binom (Syn.shift N) (var 0)))).eqTrans (one_mul _))
    ((congrMul (gle_of_le (le_add_left (var 0) (Syn.shift N)))
      (.eqRefl (binom (Syn.shift N + var 0) (var 0)))).eqTrans (one_mul _))
  refine .eqTrans ?_ (congrMul hc hc).eqSymm
  ipra_ring

/-- The sum of `b(N, k)` may run past `k = N`. -/
theorem bb_ext {j N : PTm n} (h : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] ap2 (sumF bbB) (succ N) j ≐ ap2 (sumF bbB) (succ j) j := by
  have eD : Γ ⊢[PRAAx] succ N ≐ succ j + monus N j := by
    ipra_lc natEq (eq_add_of_le h)
  refine (congrAp2 (sumF bbB) eD (.eqRefl _)).eqTrans ((sum_split bbB (succ j) (monus N j) j).eqTrans ?_)
  refine (congrAdd (.eqRefl _) ?_).eqTrans (add_zero _)
  refine (sum_congr_bounded (offB bbB) zB (pairT (succ j) j) (pairT (succ j) j) _ (.allI (.impI ?_))).eqTrans
    (zsum _ _)
  have e₂ : Syn.shift (pairT (succ j) j) = pairT (succ (Syn.shift j)) (Syn.shift j) := by simp [Syn.shift]
  rw [e₂, inst2_z, inst2_offB, inst2_bb]
  exact (congrMul (congrCf (snd_pair _ _) (congrAdd (fst_pair _ _) (.eqRefl _)))
    (congrCf (snd_pair _ _) (congrAdd (fst_pair _ _) (.eqRefl _)))).eqTrans (bb_above (le_add_right _ _))

/-- `a_N = b(N, 0) + ∑_{k < K} b(N, k + 1)` for `N < K`. -/
theorem apery_split {N K : PTm n} (h : Γ ⊢[PRAAx] le N K) :
    Γ ⊢[PRAAx] apery N ≐ bb N zero + Ssum K N := by
  have s := sum_shift (Γ := Γ) bbB K N
  rw [inst2_bb] at s
  exact (apery_bb N).eqTrans ((bb_ext h).eqSymm.eqTrans s)

/-- `prop:recurrence` for `y = a`: `(n + 1)³ a_{n+1} + n³ a_{n−1} = P_n a_n`, `n = m + 1`. -/
theorem apery_rec (m : PTm n) :
    Γ ⊢[PRAAx] cube (succ (succ m)) * apery (succ (succ m)) + cube (succ m) * apery m ≐
      Pn (succ m) * apery (succ m) := by
  ipra_lc (𝔞 m + 2) ^ 3 * natEq (apery_split (le_refl (succ (succ m)))) +
    (𝔞 m + 1) ^ 3 * natEq (apery_split (le_trans (le_succ_self m) (le_succ_self (succ m)))) -
    (2 * (𝔞 m + 1) + 1) * (17 * (𝔞 m + 1) ^ 2 + 17 * (𝔞 m + 1) + 5) * natEq (apery_split (le_succ_self (succ m))) +
    (𝔞 m + 2) ^ 3 * natEq (bb_zero (succ (succ m))) + (𝔞 m + 1) ^ 3 * natEq (bb_zero m) +
    (4 * (2 * (𝔞 m + 1) + 1) ^ 3 - (2 * (𝔞 m + 1) + 1) * (17 * (𝔞 m + 1) ^ 2 + 17 * (𝔞 m + 1) + 5)) * natEq (bb_zero (succ m)) +
    natEq (phi m (succ (succ m))) +
    (4 * (2 * (𝔞 m + 1) + 1) * ((𝔞 m + 2) * (2 * (𝔞 m + 2) + 1)) - 4 * (2 * (𝔞 m + 1) + 1) ^ 3) * natEq (bb_above (le_refl (succ (succ m))))

end LeanProofs.IPRA.DiophantineNumberTheory.AperyRecurrence
