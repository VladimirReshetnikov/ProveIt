import IPRADerivations.AnalyticNumberTheory.SieveWeightForm
import IPRADerivations.AnalyticNumberTheory.PowerResidue
import IPRADerivations.Core.CertificateTactics

/-!
# The explicit sieve weights at `d = 1`

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:sieve-normalization`:
"Since `μ(r)² = 1` on `D`, equations `eq:sieve-diagonal` and `eq:sieve-inversion` show that `λ_1 = 1`".

With the denominators cleared (`SieveWeightValues`, `SieveWeightForm`), the weights are `λ = λ⁺ − λ⁻` with the natural
parts `lB UPw`, `lB UNw`, and `A = z! G = Σ_{r ≤ z} (Y⁺_r + Y⁻_r) = Σ_{r ≤ z} μ(r)² [gcd(r, q) = 1] z!/φ(r)`
(`Asum`). The module derives

  `λ⁺_1 = A`,   `λ⁻_1 = 0`                                             (`lam_P`, `lam_N`),

which is `λ_1 = 1` after division by `A`, together with

  `Σ_{r ≤ z} z! (Y⁺_r + Y⁻_r) = z! · A`                                (`ky_sum`),
  `z! ≤ A` for `z ≥ 1`                                                  (`A_ge`),

the second from the summand at `r = 1`: `G ≥ 1`.

* `w_one`: the summand of the inverted weight at `d = 1` is `a(r) [r ≥ 1] y_r`;
* `wPP`, `wNN`, `wPN`, `wNP`: for the four combinations of the parts of `μ` and of `y`, from `μ^± μ^± = μ^±` and
  `μ⁺ μ⁻ = 0`;
* `u_keep`, `u_kill`: the weight at `d = 1` as a sum over `r`;
* `muP_one`, `YP_one`: `μ⁺(1) = 1` and `Y⁺_1 = z!`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightOne

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN om_two_one sq_two_one congrSg zero_mul_l congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (sg_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (rem_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (phi_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (gcd_one_left)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (aPB aNB inst2_aP inst2_aN)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveInversion (hS inst2_hS wB wB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion (lB inst2_lB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightRows (sg_idem uB inst2_uB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightValues (YP YN YP_at YN_at muP_idem muN_idem mu_disj)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightForm (UPw UNw kyB inst2_kyB)
open LeanProofs.IPRA.Probability.Independence (row_pt sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Facts at `1` -/

theorem one_pos : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm

theorem quo_one (N : PTm n) : Γ ⊢[PRAAx] quo N one ≐ N :=
  quo_eq (q := N) (r := zero) one_pos (by ipra_ring) (le_refl _)

/-- `μ⁺(1) = 1`. -/
theorem muP_one : Γ ⊢[PRAAx] muP (succ one) (one : PTm n) ≐ one := by
  have s0 : Γ ⊢[PRAAx] eqb (Mobius.sq (succ one) (one : PTm n)) zero ≐ one :=
    (congrEqb' sq_two_one (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _))
  have o0 : Γ ⊢[PRAAx] rem (Mobius.om (succ one) (one : PTm n)) two ≐ zero :=
    (congrAp2 remF om_two_one (.eqRefl _)).eqTrans (rem_zero _)
  exact (congrMul s0 ((congrEqb' o0 (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _)))).eqTrans
    (by ipra_ring)

theorem one3 (u : PTm n) : Γ ⊢[PRAAx] one * ((one * one) * u) ≐ u := by
  ipra_ring

theorem one_alg (a Y : PTm n) : Γ ⊢[PRAAx] ((one * one) * (one * a)) * Y ≐ a * Y := by
  ipra_ring

/-- `m (s (g ((s m) w))) = g ((s m) w)` for idempotent `m`, `s`. -/
theorem keep_alg {m s g w : PTm n} (hm : Γ ⊢[PRAAx] m * m ≐ m) (hs : Γ ⊢[PRAAx] s * s ≐ s) :
    Γ ⊢[PRAAx] m * (s * (g * ((s * m) * w))) ≐ g * ((s * m) * w) := by
  ipra_lc 𝔞 g * 𝔞 w * 𝔞 s * 𝔞 s * natEq hm + 𝔞 g * 𝔞 w * 𝔞 m * natEq hs

/-- `m (s (g ((s m') w))) = 0` when `m m' = 0`. -/
theorem kill_alg {m m' s g w : PTm n} (h : Γ ⊢[PRAAx] m * m' ≐ zero) :
    Γ ⊢[PRAAx] m * (s * (g * ((s * m') * w))) ≐ zero := by
  ipra_lc 𝔞 s * 𝔞 s * 𝔞 g * 𝔞 w * natEq h

/-! ## The summand at `d = 1` -/

/-- The summand of the inverted weight at `d = 1`: `a(r) [r ≥ 1] y_r`. -/
theorem w_one (y a : PTm 2) (r p : PTm n) :
    Γ ⊢[PRAAx] inst3 (wB y a) one r (pairT one p) ≐ inst2 a r one * (sg r * inst2 y r p) := by
  have h := (wB_at (Γ := Γ) y a one r one p).eqTrans (congrMul (cv_at hS a one r one) (.eqRefl _))
  rw [inst2_hS] at h
  exact h.eqTrans ((congrMul (congrMul (congrMul (sg_pos one_pos) (eqb_of_eq (rem_one r)))
    (congrMul (eqb_of_eq (rem_one one)) (congrInst2 a (quo_one r) (.eqRefl _)))) (.eqRefl _)).eqTrans
    (one_alg _ _))

theorem wPP (r P : PTm n) : Γ ⊢[PRAAx] inst3 (wB YP aPB) one r (pairT one P) ≐ inst2 YP r P := by
  have h := w_one (Γ := Γ) YP aPB r P
  rw [inst2_aP, YP_at] at h
  rw [YP_at]
  exact h.eqTrans (keep_alg (muP_idem _ _) (sg_idem r))

theorem wNN (r P : PTm n) : Γ ⊢[PRAAx] inst3 (wB YN aNB) one r (pairT one P) ≐ inst2 YN r P := by
  have h := w_one (Γ := Γ) YN aNB r P
  rw [inst2_aN, YN_at] at h
  rw [YN_at]
  exact h.eqTrans (keep_alg (muN_idem _ _) (sg_idem r))

theorem wPN (r P : PTm n) : Γ ⊢[PRAAx] inst3 (wB YN aPB) one r (pairT one P) ≐ zero := by
  have h := w_one (Γ := Γ) YN aPB r P
  rw [inst2_aP, YN_at] at h
  exact h.eqTrans (kill_alg (mu_disj _ _))

theorem wNP (r P : PTm n) : Γ ⊢[PRAAx] inst3 (wB YP aNB) one r (pairT one P) ≐ zero := by
  have h := w_one (Γ := Γ) YP aNB r P
  rw [inst2_aN, YP_at] at h
  exact h.eqTrans (kill_alg ((mul_comm _ _).eqTrans (mu_disj _ _)))

/-! ## The weight at `d = 1` -/

/-- The weight at `d = 1` is the sum of a body that agrees with its summands. -/
theorem u_keep (a y Yb : PTm 2)
    (hpt : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (r P : PTm k),
      Δ ⊢[PRAAx] inst3 (wB y a) one r (pairT one P) ≐ inst2 Yb r P) (P : PTm n) :
    Γ ⊢[PRAAx] inst2 (uB a y) one P ≐ ap2 (sumF Yb) (succ (sndT (sndT P))) P := by
  rw [inst2_uB]
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have s1 : Syn.shift (pairT one (pairT one P)) = pairT one (pairT one (Syn.shift P)) := by simp [Syn.shift]
  rw [s1]
  exact (row_pt (wB y a) _ _ _).eqTrans (hpt _ _)

/-- The weight at `d = 1` vanishes when all its summands do. -/
theorem u_kill (a y : PTm 2)
    (hpt : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (r P : PTm k),
      Δ ⊢[PRAAx] inst3 (wB y a) one r (pairT one P) ≐ zero) (P : PTm n) :
    Γ ⊢[PRAAx] inst2 (uB a y) one P ≐ zero := by
  rw [inst2_uB]
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  have s1 : Syn.shift (pairT one (pairT one P)) = pairT one (pairT one (Syn.shift P)) := by simp [Syn.shift]
  rw [s1]
  exact (row_pt (wB y a) _ _ _).eqTrans (hpt _ _)

/-- `A = z! G = Σ_{r ≤ z} (Y⁺_r + Y⁻_r)`, for `P = ⟨q, ⟨a, z⟩⟩`. -/
abbrev Asum (P : PTm n) : PTm n :=
  ap2 (sumF YP) (succ (sndT (sndT P))) P + ap2 (sumF YN) (succ (sndT (sndT P))) P

theorem UP_one (P : PTm n) : Γ ⊢[PRAAx] inst2 UPw one P ≐ Asum P := by
  rw [UPw, inst2_addBody]
  exact congrAdd (u_keep aPB YP YP (fun r P => wPP r P) P) (u_keep aNB YN YN (fun r P => wNN r P) P)

theorem UN_one (P : PTm n) : Γ ⊢[PRAAx] inst2 UNw one P ≐ zero := by
  rw [UNw, inst2_addBody]
  exact (congrAdd (u_kill aPB YN (fun r P => wPN r P) P) (u_kill aNB YP (fun r P => wNP r P) P)).eqTrans
    (add_zero _)

/-- `λ_1` in terms of the weight at `1`. -/
theorem lB_one (U : PTm 2) (P : PTm n) : Γ ⊢[PRAAx] inst2 (lB U) one P ≐ inst2 U one P := by
  rw [inst2_lB]
  exact (congrMul (.eqRefl _) (congrMul (congrMul (sg_pos one_pos) (eqb_of_eq (gcd_one_left _))) (.eqRefl _))).eqTrans
    (one3 _)

/-- `λ⁺_1 = A`. -/
theorem lam_P (P : PTm n) : Γ ⊢[PRAAx] inst2 (lB UPw) one P ≐ Asum P := (lB_one UPw P).eqTrans (UP_one P)

/-- `λ⁻_1 = 0`. -/
theorem lam_N (P : PTm n) : Γ ⊢[PRAAx] inst2 (lB UNw) one P ≐ zero := (lB_one UNw P).eqTrans (UN_one P)

/-! ## The value `z! · A` and the bound `z! ≤ A` -/

/-- `Σ_{r ≤ z} z! (Y⁺_r + Y⁻_r) = z! · A`. -/
theorem ky_sum (P : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF kyB) (succ (sndT (sndT P))) P ≐ fact (sndT (sndT P)) * Asum P := by
  refine (sum_scale kyB (addBody YP YN) (succ (sndT (sndT P))) (fact (sndT (sndT P))) P P
    (.allI (.impI ?_))).eqTrans (congrMul (.eqRefl _) (sum_add YP YN _ _))
  have hK : Syn.shift (fact (sndT (sndT P))) = fact (sndT (sndT (Syn.shift P))) := by simp [Syn.shift]
  rw [hK, inst2_kyB, inst2_addBody]
  exact .eqRefl _

/-- `Y⁺_1 = z!`. -/
theorem YP_one (P : PTm n) : Γ ⊢[PRAAx] inst2 YP one P ≐ fact (sndT (sndT P)) := by
  rw [YP_at]
  exact (congrMul (eqb_of_eq (gcd_one_left _)) (congrMul (congrMul (sg_pos one_pos) muP_one)
    ((congrAp2 quoF (.eqRefl _) phi_one).eqTrans (quo_one _)))).eqTrans (one3 _)

/-- `z! ≤ A` for `z ≥ 1`: `G ≥ 1`. -/
theorem A_ge {P : PTm n} (hz : Γ ⊢[PRAAx] le one (sndT (sndT P))) :
    Γ ⊢[PRAAx] le (fact (sndT (sndT P))) (Asum P) := by
  have h1 : Γ ⊢[PRAAx] lt one (succ (sndT (sndT P))) := (succ_monus_succ _ _).eqTrans hz
  exact le_trans (le_congr (YP_one P) (.eqRefl _) (term_le_sum YP (x := P) h1)) (le_add_right _ _)

end LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightOne
