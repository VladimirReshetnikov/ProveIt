import IPRADerivations.AnalyticNumberTheory.BlockChain
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Every dyadic block carries the deficit (`pnt_ipra_constructive_2026-11-14`, `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:one-step`:
"Place consecutive full blocks of length `H` … By Lemma con:deficit, …". The blocks are `E_k < d ≤ E_{k+1}`,
`E_k = E₀ Q^k` with `Q = 2^{2h}`, halved at `E_k 2^h`. Both halves have harmonic length `≥ F H₀` once
`h ≥ 2H₀ + 1` and `2x ≤ F` (`half_len`, from `Doubling.S_pow2_lower`), so `BlockDeficitMain.block_deficit` applies
to every block (`block_at`). Its error `D₂ + ⌊x/D₁⌋` is bounded uniformly by `N + ⌊x/E₀⌋`, which gives the block
hypothesis of `BlockChain.chain_sum` (`blocks_of`) and the chain bound (`chain_deficit`)

  `B u_{E₀} 3A²Fx ≤ 48 D Σ_{E₀<d≤E_B} u_d g + B u_N 100 A D F (N + ⌊x/E₀⌋)`.

All size conditions are global (`x ≤ K`, `K x^x ≤ L`, …): every quotient `⌊x/d⌋` is at most `x`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockInstance

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit (gzB Bs' OnBlock stg)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficitMain (Concl block_deficit)
open LeanProofs.IPRA.AnalyticNumberTheory.HeadDeficit (hgB)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockFamily (Lay)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw' e0_le ek_le Blocks chain_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.Doubling (S_pow2_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola (quo_le_self)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Size and length facts -/

theorem quo_le_x {D : PTm n} (x : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] le (quo x D) x :=
  le_trans (quo_anti (F := x) (pos_of_one_le (le_refl one)) hD) (quo_le_self zero x)

theorem nn_of {P x K L : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hP : Γ ⊢[PRAAx] le P x)
    (hNN : Γ ⊢[PRAAx] le (K * pw x x) L) : Γ ⊢[PRAAx] le (K * pw P P) L :=
  le_trans (le_scale K (le_trans (pw_le_pw P hP) (pw_le_exp (pos_of_one_le hx) hP))) hNN

/-- A dyadic half `M < d ≤ M 2^h` has harmonic length `≥ F H₀` when `h ≥ 2H₀ + 1` and `2 M 2^h ≤ 2x ≤ F`. -/
theorem half_len {M F H0 h x : PTm n} (hM : Γ ⊢[PRAAx] le one M) (hh : Γ ⊢[PRAAx] le (two * H0 + one) h)
    (hMx : Γ ⊢[PRAAx] le (M * pw two h) x) (hF : Γ ⊢[PRAAx] le (two * x) F) :
    Γ ⊢[PRAAx] le (S M F + F * H0) (S (M * pw two h) F) := by
  have p := S_pow2_lower F h hM
  have q := le_scale F hh
  refine mul_le_cancel (d' := one) ?_
  ipra_le sl p + sl q + 2 * sl hMx + sl hF

/-- Shrinking the block of an `OnBlock` hypothesis. -/
theorem onblock_sub {x D₁ D₂ E₁ E₂ : PTm n} {φ : Fm PTm (n + 1)} (h1 : Γ ⊢[PRAAx] le E₁ D₁)
    (h2 : Γ ⊢[PRAAx] le D₂ E₂) (h : Γ ⊢[PRAAx] OnBlock x E₁ E₂ φ) : Γ ⊢[PRAAx] OnBlock x D₁ D₂ φ := by
  have h1' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift E₁) (Syn.shift D₁) := by simpa [Fm.shift, Syn.shift] using h1.shift
  have h2' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift D₂) (Syn.shift E₂) := by simpa [Fm.shift, Syn.shift] using h2.shift
  have a := h.allOpen
  refine .allI (.impI (.impI (.impI ?_)))
  exact Prf.impE (Prf.impE (Prf.impE a.wk.wk.wk (.hyp (by simp)))
    (lt_of_le_of_lt h1'.wk.wk.wk (.hyp (by simp)))) (le_trans (.hyp (by simp)) h2'.wk.wk.wk)

/-! ## One block -/

section Block

variable {x E0 h k B N A Ds K L H0 : PTm n}

/-- `block_deficit` on the `k`-th block `E₀Q^k < d ≤ E₀Q^{k+1}`, `Q = 2^{2h}`, with the uniform error. -/
theorem block_at (hk : Γ ⊢[PRAAx] lt k B) (hE0 : Γ ⊢[PRAAx] le one E0)
    (hBN : Γ ⊢[PRAAx] le (E0 * pw (pw two (h + h)) B) N) (hNx : Γ ⊢[PRAAx] le N x) (hxL : Γ ⊢[PRAAx] le x L)
    (hK1 : Γ ⊢[PRAAx] le one K) (hxK : Γ ⊢[PRAAx] le x K) (hNN : Γ ⊢[PRAAx] le (K * pw x x) L)
    (hKx : Γ ⊢[PRAAx] le (K * x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hA1 : Γ ⊢[PRAAx] le one A) (hA4 : Γ ⊢[PRAAx] le A (two * (two * Ds)))
    (hH0 : Γ ⊢[PRAAx] le (num 3 * (A * A) + num 384 * (Ds * Ds)) (num 16 * (Ds * (A * H0))))
    (hh : Γ ⊢[PRAAx] le (two * H0 + one) h) (hF : Γ ⊢[PRAAx] le (two * x) (fact L))
    (hst : Γ ⊢[PRAAx] OnBlock x E0 N (stg x A Ds K L)) :
    Γ ⊢[PRAAx] le (num 3 * (A * (A * (fact L * x))))
      (num 48 * Ds * Bs' gzB x (E0 * pw (pw two (h + h)) k) (E0 * pw (pw two (h + h)) (succ k)) A Ds K L +
        num 100 * (A * (Ds * (fact L * (N + quo x E0))))) := by
  have h12 : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hQ : Γ ⊢[PRAAx] le one (pw two (h + h)) := one_le_pw' h12 _
  have hk' : Γ ⊢[PRAAx] le (succ k) B := hk
  have h1 : Γ ⊢[PRAAx] le one (E0 * pw (pw two (h + h)) k) := le_trans hE0 (e0_le hQ k)
  have h1h := e0_le (E0 := E0 * pw (pw two (h + h)) k) h12 h
  have e12 : Γ ⊢[PRAAx] E0 * pw (pw two (h + h)) (succ k) ≐ E0 * pw (pw two (h + h)) k * pw two h * pw two h := by
    ipra_lc 𝔞 E0 * natEq (pw_succ (Γ := Γ) (pw two (h + h)) k) +
      𝔞 E0 * 𝔞 (pw (pw two (h + h)) k) * natEq (pw_add (Γ := Γ) two h h)
  have hh2 := le_congr (.eqRefl _) e12.eqSymm (e0_le (E0 := E0 * pw (pw two (h + h)) k * pw two h) h12 h)
  have hEN := le_trans (ek_le (E0 := E0) hQ hk') hBN
  have hEB := le_trans hEN hNx
  have hDx := le_trans hh2 hEB
  have h1d := le_trans h1 h1h
  have hx1 := le_trans h1d hDx
  have hSa := le_congr (.eqRefl _) (congrAp2 (sumF hB) e12 (.eqRefl (fact L))).eqSymm
    (half_len h1d hh (le_congr e12 (.eqRefl x) hEB) hF)
  have hSb := half_len h1 hh hDx hF
  have hst' := onblock_sub (e0_le hQ k) hEN hst
  have c := block_deficit h1 h1h hh2 hEB (le_trans hEB hxL) hK1 (le_trans (quo_le_x x h1) hxK)
    (le_trans (quo_le_x x h1d) hxK) (le_trans (quo_le_x x (le_trans h1d hh2)) hxK)
    (nn_of hx1 (quo_le_x x h1) hNN) (nn_of hx1 (quo_le_x x h1d) hNN) (nn_of hx1 (quo_le_x x (le_trans h1d hh2)) hNN)
    hKx hP hA1 hA4 hSa hSb hH0 hst'
  have w2 := quo_anti (F := x) (pos_of_one_le hE0) (e0_le (E0 := E0) hQ k)
  ipra_le sl c + 100 * 𝔞 A * 𝔞 Ds * 𝔞 (fact L) * (sl hEN + sl w2)

end Block

/-! ## All blocks -/

section Chain

variable {x E0 h B N A Ds K L H0 : PTm n}

/-- The block hypothesis of `chain_sum` for the dyadic chain `Q = 2^{2h}`. -/
theorem blocks_of (hE0 : Γ ⊢[PRAAx] le one E0)
    (hBN : Γ ⊢[PRAAx] le (E0 * pw (pw two (h + h)) B) N) (hNx : Γ ⊢[PRAAx] le N x) (hxL : Γ ⊢[PRAAx] le x L)
    (hK1 : Γ ⊢[PRAAx] le one K) (hxK : Γ ⊢[PRAAx] le x K) (hNN : Γ ⊢[PRAAx] le (K * pw x x) L)
    (hKx : Γ ⊢[PRAAx] le (K * x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hA1 : Γ ⊢[PRAAx] le one A) (hA4 : Γ ⊢[PRAAx] le A (two * (two * Ds)))
    (hH0 : Γ ⊢[PRAAx] le (num 3 * (A * A) + num 384 * (Ds * Ds)) (num 16 * (Ds * (A * H0))))
    (hh : Γ ⊢[PRAAx] le (two * H0 + one) h) (hF : Γ ⊢[PRAAx] le (two * x) (fact L))
    (hst : Γ ⊢[PRAAx] OnBlock x E0 N (stg x A Ds K L)) :
    Γ ⊢[PRAAx] Blocks x E0 (pw two (h + h)) B A Ds K L (num 3 * (A * (A * (fact L * x)))) (num 48 * Ds)
      (num 100 * (A * (Ds * (fact L * (N + quo x E0))))) := by
  have s1 : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift E0) := by simpa [Fm.shift, Syn.shift] using hE0.shift
  have s2 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift E0 * pw (pw two (Syn.shift h + Syn.shift h)) (Syn.shift B))
      (Syn.shift N) := by simpa [Fm.shift, Syn.shift] using hBN.shift
  have s3 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift N) (Syn.shift x) := by simpa [Fm.shift, Syn.shift] using hNx.shift
  have s4 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift x) (Syn.shift L) := by simpa [Fm.shift, Syn.shift] using hxL.shift
  have s5 : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK1.shift
  have s6 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift x) (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hxK.shift
  have s7 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * pw (Syn.shift x) (Syn.shift x)) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hNN.shift
  have s8 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift x) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hKx.shift
  have s9 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * pw two (two * (two * Syn.shift x))) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hP.shift
  have s10 : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift A) := by simpa [Fm.shift, Syn.shift] using hA1.shift
  have s11 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift A) (two * (two * Syn.shift Ds)) := by
    simpa [Fm.shift, Syn.shift] using hA4.shift
  have s12 : (Γ.map Fm.shift) ⊢[PRAAx] le (num 3 * (Syn.shift A * Syn.shift A) + num 384 * (Syn.shift Ds * Syn.shift Ds))
      (num 16 * (Syn.shift Ds * (Syn.shift A * Syn.shift H0))) := by
    simpa [Fm.shift, Syn.shift] using hH0.shift
  have s13 : (Γ.map Fm.shift) ⊢[PRAAx] le (two * Syn.shift H0 + one) (Syn.shift h) := by
    simpa [Fm.shift, Syn.shift] using hh.shift
  have s14 : (Γ.map Fm.shift) ⊢[PRAAx] le (two * Syn.shift x) (fact (Syn.shift L)) := by
    simpa [Fm.shift, Syn.shift] using hF.shift
  have s15 : (Γ.map Fm.shift) ⊢[PRAAx] OnBlock (Syn.shift x) (Syn.shift E0) (Syn.shift N)
      (stg (Syn.shift x) (Syn.shift A) (Syn.shift Ds) (Syn.shift K) (Syn.shift L)) := by
    have a := hst.shift
    simp only [OnBlock, stg, BlockDeficit.Pm, BlockDeficit.Qm, Fm.shift, Fm.subst_all, Fm.subst_imp, subst_le,
      subst_lt, subst_ap2, PTm.subst_mul, PTm.subst_add, PTm.subst_monus, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.up_zero, subst_up_shift_pal, subst_pairT] at a
    exact a
  refine .allI (.impI ?_)
  rw [show Syn.shift (num 3 * (A * (A * (fact L * x)))) =
      num 3 * (Syn.shift A * (Syn.shift A * (fact (Syn.shift L) * Syn.shift x))) by simp [Syn.shift],
    show Syn.shift (num 48 * Ds) = num 48 * Syn.shift Ds by simp [Syn.shift],
    show Syn.shift (num 100 * (A * (Ds * (fact L * (N + quo x E0))))) =
      num 100 * (Syn.shift A * (Syn.shift Ds * (fact (Syn.shift L) * (Syn.shift N + quo (Syn.shift x) (Syn.shift E0)))))
      by simp [Syn.shift],
    show Syn.shift (pw two (h + h)) = pw two (Syn.shift h + Syn.shift h) by simp [Syn.shift]]
  exact block_at Prf.hyp0 s1.wk s2.wk s3.wk s4.wk s5.wk s6.wk s7.wk s8.wk s9.wk s10.wk s11.wk s12.wk s13.wk s14.wk
    s15.wk

/-- The chain bound: `B u_{E₀} 3A²Fx ≤ 48 D Σ_{E₀<d≤E_B} u_d g + B u_N 100 A D F (N + ⌊x/E₀⌋)`. -/
theorem chain_deficit (hE0 : Γ ⊢[PRAAx] le one E0)
    (hBN : Γ ⊢[PRAAx] le (E0 * pw (pw two (h + h)) B) N) (hNx : Γ ⊢[PRAAx] le N x) (hxL : Γ ⊢[PRAAx] le x L)
    (hK1 : Γ ⊢[PRAAx] le one K) (hxK : Γ ⊢[PRAAx] le x K) (hNN : Γ ⊢[PRAAx] le (K * pw x x) L)
    (hKx : Γ ⊢[PRAAx] le (K * x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hA1 : Γ ⊢[PRAAx] le one A) (hA4 : Γ ⊢[PRAAx] le A (two * (two * Ds)))
    (hH0 : Γ ⊢[PRAAx] le (num 3 * (A * A) + num 384 * (Ds * Ds)) (num 16 * (Ds * (A * H0))))
    (hh : Γ ⊢[PRAAx] le (two * H0 + one) h) (hF : Γ ⊢[PRAAx] le (two * x) (fact L))
    (hst : Γ ⊢[PRAAx] OnBlock x E0 N (stg x A Ds K L)) :
    Γ ⊢[PRAAx] le (B * (U E0 K (fact L) * (num 3 * (A * (A * (fact L * x))))))
      (num 48 * Ds * ap2 (sumF hgB) (succ x) (Lay x E0 (E0 * pw (pw two (h + h)) B) A Ds K L) +
        B * (U N K (fact L) * (num 100 * (A * (Ds * (fact L * (N + quo x E0))))))) :=
  chain_sum (one_le_pw' (le_succ_self one) _) hBN
    (blocks_of hE0 hBN hNx hxL hK1 hxK hNN hKx hP hA1 hA4 hH0 hh hF hst)

end Chain

end LeanProofs.IPRA.AnalyticNumberTheory.BlockInstance
