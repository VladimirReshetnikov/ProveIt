import IPRADerivations.AnalyticNumberTheory.StageInduction
import IPRADerivations.Core.Header

/-!
# The prime number theorem for `ψ` with an explicit modulus (`pnt_ipra_constructive_2026-11-14`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex` (con:psi-at-recursive-threshold:
"After `J` steps, `|ψ(x) − x| ≤ x/q` (`x ≥ P_J`)") and `pnt_ipra.tex` (eq:psi-modulus). In the packet's finite
convention the logarithm is the harmonic logarithm `λ_K` at mesh `K` over the denominator `F = L!`, and
`ψ_w(x) = Σ_{p^a ≤ x} F λ_K(p)` (`LcmUpto.Psi wt`). For every `x` the mesh and the denominator are fixed by `x`
alone (`Kx`, `Lx`): `K = (x + 1)⁴`, `L = K((x + 1)⁴ + 2^{4x} + x^x)`.

`psi_modulus`: with `q = p + 1`, `D = 2^{20} q³`, for every `x ≥ 2^{s_J}` (the exponent of `StageInduction`)

  `D |ψ_w(x) − Fx| ≤ A_J F x`,   `A_J = 4D − 3J ≤ 2^{20} q² + 2` (`aJ_le`),

i.e. `|ψ_w(x)/F − x| ≤ (1/q + 2/D) x`. The size conditions of the contraction are all instances of
`le_fact` (`L ≤ L!`) and elementary polynomial comparisons.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PsiModulus

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw')
open LeanProofs.IPRA.AnalyticNumberTheory.ContractionSplit (Stage)
open LeanProofs.IPRA.AnalyticNumberTheory.StageAdvance (q4_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.StageInduction (Aj Amin Jst sT stages s_ge)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTThresholds (Dq Q3)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `L ≤ L!`. -/
theorem le_fact (L : PTm n) : Γ ⊢[PRAAx] le L (fact L) := by
  refine .orE (lt_or_le zero L) ?_ ?_
  · have pL := pos_of_one_le (Prf.hyp0 : (lt zero L :: Γ) ⊢[PRAAx] le one L)
    have ef := natEq ((congrAp2 factF pL (.eqRefl zero)).eqTrans (fact_succ (Γ := lt zero L :: Γ) (pred L) zero))
    have fp := natEq (LeanProofs.IPRA.AnalyticNumberTheory.Primes.fact_pos (Γ := lt zero L :: Γ) (pred L))
    have pL' := natEq pL
    ipra_le 𝔞 (pred (fact (pred L))) * (𝔞 (pred L) + 1) with ef + (𝔞 (pred L) + 1) * fp - pL'
  · have hz : (le L zero :: Γ) ⊢[PRAAx] L ≐ zero := (monus_zero L).eqSymm.eqTrans Prf.hyp0
    exact le_congr hz.eqSymm (.eqRefl _) (zero_le _)

/-- The mesh `K = (x + 1)⁴`. -/
abbrev Kx (x : PTm n) : PTm n := Q4 x
/-- `L = K((x + 1)⁴ + 2^{4x} + x^x)`. -/
abbrev Lx (x : PTm n) : PTm n := Kx x * (Q4 x + pw two (two * (two * x)) + pw x x)

/-- `A_J ≤ 2^{20} q² + 2`. -/
theorem aJ_le (p : PTm n) : Γ ⊢[PRAAx] le (Aj (Jst p) (Dq p)) (Amin p + two) := by
  have hm : Γ ⊢[PRAAx] le (Amin p) (num 4 * Dq p) := by
    ipra_le 4194304 * 𝔞 p ^ 3 + 11534336 * 𝔞 p ^ 2 + 10485760 * 𝔞 p + 3145728
  have f0 := natEq (eq_add_of_le hm)
  have dm := div_mod_at (Γ := Γ) (x := monus (num 4 * Dq p) (Amin p)) (y := num 3) (c := two) (.eqRefl _)
  have e0 := natEq (Prf.andE₁ dm)
  have r0 := Prf.andE₂ dm
  have h3 : Γ ⊢[PRAAx] le (num 3 * Jst p) (num 4 * Dq p) := by
    ipra_le 𝔞 (rem (monus (num 4 * Dq p) (Amin p)) (num 3)) + 1048576 * (𝔞 p + 1) ^ 2 with f0 + e0
  have f1 := natEq (eq_add_of_le h3)
  unfold Aj
  ipra_le sl r0 with f1 - f0 - e0

theorem psi_modulus {p x : PTm n} (hx : Γ ⊢[PRAAx] le (pw two (sT (Jst p) (Dq p))) x) :
    Γ ⊢[PRAAx] le (Dq p * absd (Psi wt x (pairT (Kx x) (fact (Lx x)))) (fact (Lx x) * x))
      (Aj (Jst p) (Dq p) * (fact (Lx x) * x)) := by
  have p2 : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := pos_of_one_le (le_succ_self one)
  have hs1 : Γ ⊢[PRAAx] le one (sT (Jst p) (Dq p)) :=
    le_trans (by ipra_le 1048576 * (𝔞 p + 1) ^ 3 + 1599) (s_ge _ _)
  have hx2 : Γ ⊢[PRAAx] le two x := le_trans (le_congr (pw_one two) (.eqRefl _) (pw_le_exp p2 hs1)) hx
  have hX1 : Γ ⊢[PRAAx] le one x := le_trans (le_succ_self one) hx2
  have hK : Γ ⊢[PRAAx] le one (Kx x) := by ipra_le 𝔞 x ^ 4 + 4 * 𝔞 x ^ 3 + 6 * 𝔞 x ^ 2 + 4 * 𝔞 x
  have hq16 : Γ ⊢[PRAAx] le (num 16) (Q4 x) := le_congr (by apply deriveNat; ipra_simps; norm_num) (.eqRefl _) (q4_mono hX1)
  have hLf := le_fact (Γ := Γ) (Lx x)
  have hKL : Γ ⊢[PRAAx] le (Kx x * Q4 x) (Lx x) := by
    ipra_le (𝔞 x + 1) ^ 4 * (𝔞 (pw two (two * (two * x))) + 𝔞 (pw x x))
  have hxK : Γ ⊢[PRAAx] le x (Kx x) := by ipra_le 𝔞 x ^ 4 + 4 * 𝔞 x ^ 3 + 6 * 𝔞 x ^ 2 + 3 * 𝔞 x + 1
  have hKxL : Γ ⊢[PRAAx] le (Kx x * x) (Lx x) := le_trans (le_scale _ hxK) hKL
  have hxL : Γ ⊢[PRAAx] le x (Lx x) := le_trans hxK (le_trans (by
    have a := le_scale (Kx x) (le_trans hX1 hxK)
    ipra_le sl a) hKL)
  have h2K : Γ ⊢[PRAAx] le (two * (Kx x * x)) (Lx x) := by
    have a := le_scale (Kx x) (show Γ ⊢[PRAAx] le (two * x) (Q4 x) by
      ipra_le 𝔞 x ^ 4 + 4 * 𝔞 x ^ 3 + 6 * 𝔞 x ^ 2 + 2 * 𝔞 x + 1)
    ipra_le sl a + (𝔞 x + 1) ^ 4 * (𝔞 (pw two (two * (two * x))) + 𝔞 (pw x x))
  have hF4 : Γ ⊢[PRAAx] le (num 4 * Kx x + two) (Lx x) := by
    have a := le_scale (Kx x) hq16
    ipra_le sl a + 12 * sl hK + 10 + (𝔞 x + 1) ^ 4 * (𝔞 (pw two (two * (two * x))) + 𝔞 (pw x x))
  have st := stages (p := p) hK hX1 (le_refl _) hKL
    (by ipra_le (𝔞 x + 1) ^ 4 * ((𝔞 x + 1) ^ 4 + 𝔞 (pw x x)))
    hKxL hxL hxK (by ipra_le (𝔞 x + 1) ^ 4 * ((𝔞 x + 1) ^ 4 + 𝔞 (pw two (two * (two * x)))))
    (le_trans (le_trans (by ipra_le 2 * 𝔞 x ^ 5 + 8 * 𝔞 x ^ 4 + 12 * 𝔞 x ^ 3 + 8 * 𝔞 x ^ 2) h2K) hLf) (le_trans h2K hLf) (le_trans hF4 hLf)
  have a := Prf.allE x st
  simp only [Stage, Fm.subst_imp, subst_le, subst_lt, subst_ap2, PTm.subst_mul, PTm.subst_add, PTm.subst_monus,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    subst_pairT] at a
  exact Prf.impE (Prf.impE a (le_refl _)) hx

end LeanProofs.IPRA.AnalyticNumberTheory.PsiModulus
