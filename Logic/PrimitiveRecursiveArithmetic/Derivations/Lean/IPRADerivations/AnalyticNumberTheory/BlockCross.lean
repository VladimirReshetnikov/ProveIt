import IPRADerivations.AnalyticNumberTheory.BlockCases
import IPRADerivations.AnalyticNumberTheory.CrossAlg
import IPRADerivations.AnalyticNumberTheory.WeightedVariation

/-!
# The crossing case of the block deficit (`pnt_ipra_constructive_2026-11-14`, `con:deficit`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:deficit`,
third case: "Let `v` be the first index after `i₀` with `b_v ≤ −a/4`, and let `u < v` be the last index at or after
`i₀` with `b_u ≥ a/4` … `|r(t)| ≤ 9a/32 < a/2` (`t_u ≤ t ≤ t_v`) … `∫_{t_u}^{t_v} d(t) dt ≥ 3a²/64`."

In divisors the order of `m = ⌊x/d⌋` is reversed: a low sample at `d_u` and a high sample at `d_v > d_u` (so
`m_v ≤ m_u`), with neither test passing for `d_u < d < d_v`. `case_C_core` turns these into the uniform bound

  `3 A² F x ≤ 48 D Σ_{D₁<d≤D₂} g + 100 A D F (D₂ + ⌊x/D₁⌋)`

via `BlockDeficit.case_mid_sum` on the interior, `BlockCases.mass_interior`, `BlockTests.cross_gap`,
`BlockCases.block_mono` and `CrossAlg.crossC_alg`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockCross

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedVariation (psi_le_le)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit (gzB OnBlock Pm Qm Bs' case_mid_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockTests (four cross_gap)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockCases (mass_interior block_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.CrossAlg (crossC_alg)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `1 ≤ ⌊x/d⌋` for `1 ≤ d ≤ x`. -/
theorem one_le_quo {x d : PTm n} (hd : Γ ⊢[PRAAx] le one d) (hdx : Γ ⊢[PRAAx] le d x) :
    Γ ⊢[PRAAx] le one (quo x d) :=
  le_quo_of_mul_le (pos_of_one_le hd) (le_congr (by ipra_ring) (.eqRefl _) hdx)

theorem one_le_fact (L : PTm n) : Γ ⊢[PRAAx] le one (fact L) := by
  have f := natEq (Primes.fact_pos (Γ := Γ) L)
  ipra_le 𝔞 (pred (fact L)) with f

section Core

variable {x D₁ D₂ A Ds K L du dv : PTm n}

/-- The crossing case, for given samples `d_u < d_v`. -/
theorem case_C_core (h1 : Γ ⊢[PRAAx] le one D₁) (hdu : Γ ⊢[PRAAx] le D₁ du) (hlt : Γ ⊢[PRAAx] lt du dv)
    (hdv : Γ ⊢[PRAAx] le dv D₂) (h2x : Γ ⊢[PRAAx] le D₂ x) (h2L : Γ ⊢[PRAAx] le D₂ L)
    (hK1 : Γ ⊢[PRAAx] le one K) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hA1 : Γ ⊢[PRAAx] le one A) (hA4 : Γ ⊢[PRAAx] le A (two * (two * Ds)))
    (hlo : Γ ⊢[PRAAx] le (A * (fact L * quo x du))
      (four * (Ds * monus (fact L * quo x du) (Psi wt (quo x du) (pairT K (fact L))))))
    (hhi : Γ ⊢[PRAAx] le (A * (fact L * quo x dv))
      (four * (Ds * monus (Psi wt (quo x dv) (pairT K (fact L))) (fact L * quo x dv))))
    (hint : Γ ⊢[PRAAx] OnBlock x du (pred dv)
      (le (two * (Syn.shift Ds * absd (Pm x K L) (Qm x L))) (Syn.shift A * Qm x L))) :
    Γ ⊢[PRAAx] le (num 3 * (A * (A * (fact L * x))))
      (num 48 * (Ds * Bs' gzB x D₁ D₂ A Ds K L) + num 100 * (A * (Ds * (fact L * (D₂ + quo x D₁))))) := by
  have hdu1 : Γ ⊢[PRAAx] le one du := le_trans h1 hdu
  have hdv1 : Γ ⊢[PRAAx] le one dv := le_trans hdu1 (le_of_lt hlt)
  have hdvp : Γ ⊢[PRAAx] dv ≐ succ (pred dv) := pos_of_one_le hdv1
  have edv : Γ ⊢[PRAAx] dv ≐ pred dv + one := hdvp.eqTrans (by ipra_ring)
  have hb : Γ ⊢[PRAAx] le du (pred dv) := by
    have e := natEq hdvp; ipra_le sl hlt with e
  have hbdv : Γ ⊢[PRAAx] le (pred dv) dv := by
    have e := natEq hdvp; ipra_le 1 with e
  have hb1 : Γ ⊢[PRAAx] le one (pred dv) := le_trans hdu1 hb
  have hbx : Γ ⊢[PRAAx] le (pred dv) x := le_trans hbdv (le_trans hdv h2x)
  have hbL : Γ ⊢[PRAAx] le (pred dv) L := le_trans hbdv (le_trans hdv h2L)
  have hdux : Γ ⊢[PRAAx] le du x := le_trans hb hbx
  have hdvx : Γ ⊢[PRAAx] le dv x := le_trans hdv h2x
  have cm := case_mid_sum (le_trans (le_refl _) hb) hint
  have mi := mass_interior (w := pairT A Ds) (K := K) hb hbx hbL hb1
  have hs3 : Γ ⊢[PRAAx] le (quo x dv) (quo x (pred dv)) := quo_anti (pos_of_one_le hb1) hbdv
  have hxy : Γ ⊢[PRAAx] le (quo x dv) (quo x du) := quo_anti (pos_of_one_le hdu1) (le_of_lt hlt)
  have hPQ := psi_le_le (pairT K (fact L)) hxy
  have pk := psi_k hK1 hP (quo_le_self' hdv1)
  have hPs : Γ ⊢[PRAAx] le (Psi wt (quo x dv) (pairT K (fact L))) (four * (fact L * quo x dv)) := by
    ipra_le sl pk
  have cg := cross_gap hxy hPQ hPs (one_le_fact L) (one_le_quo hdv1 hdvx) hA1 hhi hlo
  have bm := block_mono (A := A) (Ds := Ds) (K := K) (L := L) (x := x) hdu (le_trans hbdv hdv) hb
  have hs9 : Γ ⊢[PRAAx] le (quo x dv) (quo x D₁) := quo_anti (pos_of_one_le h1) (le_trans hdu (le_of_lt hlt))
  have dU := div_mod_at (Γ := Γ) (x := x) (pos_of_one_le hdu1)
  have dV := div_mod_at (Γ := Γ) (x := x) hdvp
  exact crossC_alg cm mi hs3 cg bm hA4 hs9 (le_trans hbdv hdv) hdv (le_trans hb (le_trans hbdv hdv))
    (one_le_quo hdu1 hdux) (Prf.andE₂ dU) (Prf.andE₂ dV) (Prf.andE₁ dU) (Prf.andE₁ dV) edv
    (eq_add_of_le hxy) (eq_add_of_le hb)
where
  quo_le_self' {d : PTm n} (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] le (quo x d) x :=
    Division.quo_le_self (pos_of_one_le hd)

end Core

end LeanProofs.IPRA.AnalyticNumberTheory.BlockCross
