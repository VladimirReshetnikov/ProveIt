import IPRADerivations.AnalyticNumberTheory.BlockFamily
import IPRADerivations.AnalyticNumberTheory.Doubling
import IPRADerivations.AnalyticNumberTheory.PowerCleared
import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.Core.Header

/-!
# The chain of geometric blocks (`pnt_ipra_constructive_2026-11-14`, `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:one-step`:
"Place consecutive full blocks of length `H` starting at `s` … On all these blocks the weight `t − u` is at least
`t/2`. By Lemma con:deficit, …". Discretely the blocks are `E_k < d ≤ E_{k+1}` with `E_k = E₀ Q^k` (`Q ≥ 1`), and
the weight of a divisor `d` is its harmonic logarithm `u_d` (`HarmonicLogSquareSum.U`). If every block satisfies a
deficit bound `c₀ ≤ C₁ Σ_{E_k<d≤E_{k+1}} g + c₂` (the shape of `BlockDeficitMain.block_deficit`), then (`chain_sum`)

  `B u_{E₀} c₀ ≤ C₁ Σ_{E₀<d≤E_B} u_d g + B u_N c₂`  for `E_B ≤ N`,

by quantifier-free induction on the number of blocks: each step splits the weighted sum at `E_k`
(`BlockFamily.hg_split`), bounds the new block's weight from below by `u_{E_k} ≥ u_{E₀}` (`BlockFamily.hg_weight`)
and the error weight from above by `u_{E_k} ≤ u_N`. The step algebra is the generic `step_alg` over opaque terms.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockChain

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit (gzB Bs')
open LeanProofs.IPRA.AnalyticNumberTheory.HeadDeficit (hgB)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockFamily (Lay hg_split hg_weight monus_le_monus)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Geometric block ends and monotone weights -/

theorem one_le_pw' {Q : PTm n} (hQ : Γ ⊢[PRAAx] le one Q) (k : PTm n) : Γ ⊢[PRAAx] le one (pw Q k) :=
  le_congr (pw_one_base k) (.eqRefl _) (pw_le_pw k hQ)

/-- `E₀ ≤ E₀ Q^k`. -/
theorem e0_le {E0 Q : PTm n} (hQ : Γ ⊢[PRAAx] le one Q) (k : PTm n) : Γ ⊢[PRAAx] le E0 (E0 * pw Q k) := by
  have p := le_scale E0 (one_le_pw' hQ k)
  ipra_le sl p

/-- `E₀ Q^k ≤ E₀ Q^{k+1}`. -/
theorem esucc_le {E0 Q : PTm n} (hQ : Γ ⊢[PRAAx] le one Q) (k : PTm n) :
    Γ ⊢[PRAAx] le (E0 * pw Q k) (E0 * pw Q (succ k)) := by
  have e := natEq (pw_succ (Γ := Γ) Q k)
  have p := le_scale (E0 * pw Q k) hQ
  ipra_le sl p with 𝔞 E0 * e

/-- `E₀ Q^k ≤ E₀ Q^B` for `k ≤ B`. -/
theorem ek_le {E0 Q k B : PTm n} (hQ : Γ ⊢[PRAAx] le one Q) (h : Γ ⊢[PRAAx] le k B) :
    Γ ⊢[PRAAx] le (E0 * pw Q k) (E0 * pw Q B) :=
  le_scale E0 (pw_le_exp (pos_of_one_le hQ) h)

/-- The harmonic weight `u_a = S(Ka) − S(K)` is monotone. -/
theorem u_mono {a b : PTm n} (K F : PTm n) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (U a K F) (U b K F) :=
  monus_le_monus (S_mono F (le_scale K h))

/-! ## The step algebra -/

theorem base_alg (a b c : PTm n) : Γ ⊢[PRAAx] le (zero * a) (b + zero * c) := by
  ipra_le 𝔞 b

/-- One more block: `k u₀ c₀ ≤ C₁ G + k Û c₂` and the new block give the bound for `k + 1`. -/
theorem step_alg {k u0 uk Uh c0 C1 c2 G G' h Bs : PTm n}
    (ih : Γ ⊢[PRAAx] le (k * (u0 * c0)) (C1 * G + k * (Uh * c2)))
    (hs : Γ ⊢[PRAAx] G' ≐ G + h) (hw : Γ ⊢[PRAAx] le (uk * Bs) (one * h))
    (hb : Γ ⊢[PRAAx] le c0 (C1 * Bs + c2)) (h0 : Γ ⊢[PRAAx] le u0 uk) (h1 : Γ ⊢[PRAAx] le uk Uh) :
    Γ ⊢[PRAAx] le (succ k * (u0 * c0)) (C1 * G' + succ k * (Uh * c2)) := by
  have pa := le_scale c0 h0
  have pb := le_scale uk hb
  have pc := le_scale C1 hw
  have pd := le_scale c2 h1
  have e := natEq hs
  ipra_le sl ih + sl pa + sl pb + sl pc + sl pd with 𝔞 C1 * e

/-! ## The chain -/

/-- The block hypothesis of the chain: every block `E_k < d ≤ E_{k+1}`, `k < B`, has `c₀ ≤ C₁ Σ g + c₂`. -/
abbrev Blocks (x E0 Q B A Ds K L c0 C1 c2 : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift B) ⟶
    le (Syn.shift c0) (Syn.shift C1 * Bs' gzB (Syn.shift x) (Syn.shift E0 * pw (Syn.shift Q) (var 0))
      (Syn.shift E0 * pw (Syn.shift Q) (succ (var 0))) (Syn.shift A) (Syn.shift Ds) (Syn.shift K) (Syn.shift L) +
      Syn.shift c2))

/-- The chain invariant at `k = var 0`. -/
abbrev Inv (x E0 Q B N A Ds K L c0 C1 c2 : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (Syn.shift B) ⟶
    le (var 0 * (U (Syn.shift E0) (Syn.shift K) (fact (Syn.shift L)) * Syn.shift c0))
      (Syn.shift C1 * ap2 (sumF hgB) (succ (Syn.shift x)) (Lay (Syn.shift x) (Syn.shift E0)
          (Syn.shift E0 * pw (Syn.shift Q) (var 0)) (Syn.shift A) (Syn.shift Ds) (Syn.shift K) (Syn.shift L)) +
        var 0 * (U (Syn.shift N) (Syn.shift K) (fact (Syn.shift L)) * Syn.shift c2))

/-- `B u_{E₀} c₀ ≤ C₁ Σ_{E₀<d≤E_B} u_d g + B u_N c₂`. -/
theorem chain_sum {x E0 Q B N A Ds K L c0 C1 c2 : PTm n} (hQ : Γ ⊢[PRAAx] le one Q)
    (hN : Γ ⊢[PRAAx] le (E0 * pw Q B) N) (hblk : Γ ⊢[PRAAx] Blocks x E0 Q B A Ds K L c0 C1 c2) :
    Γ ⊢[PRAAx] le (B * (U E0 K (fact L) * c0))
      (C1 * ap2 (sumF hgB) (succ x) (Lay x E0 (E0 * pw Q B) A Ds K L) + B * (U N K (fact L) * c2)) := by
  have hQ' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift Q) := by simpa [Fm.shift, Syn.shift] using hQ.shift
  have hN' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift E0 * pw (Syn.shift Q) (Syn.shift B)) (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using hN.shift
  have hall : Γ ⊢[PRAAx] Fm.all (Inv x E0 Q B N A Ds K L c0 C1 c2) := by
    refine PRA.qfInd _ (by simp [Fm.QF, le_QF]) ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT, Inv,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact .impI (base_alg _ _ _)
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT, Inv,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      let Θ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift B) :: Inv x E0 Q B N A Ds K L c0 C1 c2 ::
        Γ.map Fm.shift
      have hle : Θ ⊢[PRAAx] le (var 0) (Syn.shift B) := le_trans (le_succ_self _) Prf.hyp0
      have ih := Prf.impE (Prf.hyp1 : Θ ⊢[PRAAx] Inv x E0 Q B N A Ds K L c0 C1 c2) hle
      have hb := Prf.impE (hblk.allOpen.wk.wk : Θ ⊢[PRAAx] _) (Prf.hyp0 : Θ ⊢[PRAAx] _)
      have hQΘ : Θ ⊢[PRAAx] le one (Syn.shift Q) := hQ'.wk.wk
      have hNΘ : Θ ⊢[PRAAx] le (Syn.shift E0 * pw (Syn.shift Q) (Syn.shift B)) (Syn.shift N) := hN'.wk.wk
      have h01 := e0_le (E0 := Syn.shift E0) hQΘ (var 0)
      have hk1 := esucc_le (E0 := Syn.shift E0) hQΘ (var 0)
      have h0 := u_mono (Syn.shift K) (fact (Syn.shift L)) h01
      have h1 := u_mono (Syn.shift K) (fact (Syn.shift L)) (le_trans (ek_le (E0 := Syn.shift E0) hQΘ hle) hNΘ)
      exact step_alg ih (hg_split (x := Syn.shift x) (A := Syn.shift A) (Ds := Syn.shift Ds) (K := Syn.shift K)
        (L := Syn.shift L) h01 hk1) (hg_weight hk1) hb h0 h1
  have h := Prf.allE B hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT, Inv,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact .impE h (le_refl B)

end LeanProofs.IPRA.AnalyticNumberTheory.BlockChain
