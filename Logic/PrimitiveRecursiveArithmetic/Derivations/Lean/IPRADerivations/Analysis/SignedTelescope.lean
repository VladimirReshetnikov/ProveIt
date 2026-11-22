import IPRADerivations.Analysis.ErrorBudgets
import IPRADerivations.DiophantineNumberTheory.RungeProduct

/-!
# Signed telescoping with an error budget

Packet: `analysis/calculus_ipra`, `report.tex`, Section "A fully rational Euler–Maclaurin certificate":
"Summing `eq:localdefect` over `H` fine cells in each of `L` unit cells telescopes exactly, because repeated
endpoints use the same sample. Therefore `|E_j| ≤ L D ε` (`eq:Ejbound`)." The same step is the finite
fundamental theorem of calculus in signed form.

The cells are `c < N`. A signed sequence `G(c) = G⁺(c) − G⁻(c)` has, at the right end of cell `c`, the value
`R(c) = R⁺(c) − R⁻(c)`, and the main term of the cell is `m(c) = m⁺(c) − m⁻(c)`; all are natural bodies:

* `ad_eq_of_cross`: `|p − q| = |p′ − q′|` when `p − q = p′ − q′` (as `p + q′ = p′ + q`);
* `signed_telescope`: if the right end of each cell is the start of the next, `R(c) = G(c + 1)`
  ("repeated endpoints use the same sample"), and every cell defect satisfies `|R(c) − G(c) − m(c)| ≤ δ`,
  then `|G(N) − G(0) − ∑_{c<N} m(c)| ≤ N δ`.

For `eq:Ejbound`: `G(c) = P_j(t_c) f̂_{j−1}(x_c)` on the fine grid (with `P_j(1) = P_j(0)` for `j ≥ 2`),
`m(c) = h (P_j f̂_j + P_{j−1} f̂_{j−1})(c)`, so that `∑ m = Q_{j−1} + Q_j`, `G(N) − G(0) = b_j`, and
`δ = h D ε` from `Analysis/EulerMaclaurinCertificate.defect_bound`; with `N h = L` this is `|E_j| ≤ L D ε`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.SignedTelescope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_add_le)
open LeanProofs.IPRA.DiophantineNumberTheory.RungeProduct (ad_of_eq_add ad_of_eq_add')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `|p − q| = |p′ − q′|` when `p + q′ = p′ + q`. -/
theorem ad_eq_of_cross {p q p' q' : PTm n} (h : Γ ⊢[PRAAx] p + q' ≐ p' + q) : Γ ⊢[PRAAx] ad p q ≐ ad p' q' := by
  refine .orE (le_total p q) ?_ ?_
  · have e₁ := eq_add_of_le (Prf.hyp0 : (le p q :: Γ) ⊢[PRAAx] le p q)
    have e₂ : (le p q :: Γ) ⊢[PRAAx] q' ≐ p' + monus q p := by
      have a := natEq (h.wk (ψ := le p q)); have b := natEq e₁
      apply deriveNat; ipra_simps; linear_combination a + b
    exact (ad_of_eq_add' e₁).eqTrans (ad_of_eq_add' e₂).eqSymm
  · have e₁ := eq_add_of_le (Prf.hyp0 : (le q p :: Γ) ⊢[PRAAx] le q p)
    have e₂ : (le q p :: Γ) ⊢[PRAAx] p' ≐ q' + monus p q := by
      have a := natEq (h.wk (ψ := le q p)); have b := natEq e₁
      apply deriveNat; ipra_simps; linear_combination -a + b
    exact (ad_of_eq_add e₁).eqTrans (ad_of_eq_add e₂).eqSymm

section Telescope

variable (Gp Gn Rp Rn Mp Mn : PTm 2)

/-- The two sides of `G(K) − G(0) − ∑_{c<K} m(c)` as natural numbers. -/
abbrev TX (K x : PTm n) : PTm n := inst2 Gp K x + inst2 Gn zero x + ap2 (sumF Mn) K x
abbrev TY (K x : PTm n) : PTm n := inst2 Gn K x + inst2 Gp zero x + ap2 (sumF Mp) K x
/-- The two sides of the defect `R(c) − G(c) − m(c)` of cell `c`. -/
abbrev DU (c x : PTm n) : PTm n := inst2 Rp c x + inst2 Gn c x + inst2 Mn c x
abbrev DV (c x : PTm n) : PTm n := inst2 Rn c x + inst2 Gp c x + inst2 Mp c x

theorem tel_step {K x δ : PTm n}
    (hR : Γ ⊢[PRAAx] inst2 Rp K x + inst2 Gn (succ K) x ≐ inst2 Rn K x + inst2 Gp (succ K) x)
    (hd : Γ ⊢[PRAAx] le (ad (DU Gn Rp Mn K x) (DV Gp Rn Mp K x)) δ)
    (ih : Γ ⊢[PRAAx] le (ad (TX Gp Gn Mn K x) (TY Gp Gn Mp K x)) (K * δ)) :
    Γ ⊢[PRAAx] le (ad (TX Gp Gn Mn (succ K) x) (TY Gp Gn Mp (succ K) x)) (succ K * δ) := by
  have sn := natEq (sum_succ' (Γ := Γ) Mn K x)
  have sp := natEq (sum_succ' (Γ := Γ) Mp K x)
  have r := natEq hR
  have c : Γ ⊢[PRAAx] ad (TX Gp Gn Mn (succ K) x) (TY Gp Gn Mp (succ K) x) ≐
      ad (TX Gp Gn Mn K x + DU Gn Rp Mn K x) (TY Gp Gn Mp K x + DV Gp Rn Mp K x) := by
    refine ad_eq_of_cross ?_
    apply deriveNat; ipra_simps
    linear_combination sn - sp - r
  have t := ad_add_le (Γ := Γ) (TX Gp Gn Mn K x) (DU Gn Rp Mn K x) (TY Gp Gn Mp K x) (DV Gp Rn Mp K x)
  have e := natEq c
  ipra_le sl t + sl ih + sl hd using linear_combination -e

/-- `|G(N) − G(0) − ∑_{c<N} m(c)| ≤ N δ` from `R(c) = G(c + 1)` and `|R(c) − G(c) − m(c)| ≤ δ` for `c < N`. -/
theorem signed_telescope (N δ x : PTm n)
    (hR : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 Rp (var 0) (Syn.shift x) + inst2 Gn (succ (var 0)) (Syn.shift x) ≐
        inst2 Rn (var 0) (Syn.shift x) + inst2 Gp (succ (var 0)) (Syn.shift x))))
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (ad (DU Gn Rp Mn (var 0) (Syn.shift x)) (DV Gp Rn Mp (var 0) (Syn.shift x))) (Syn.shift δ))) :
    Γ ⊢[PRAAx] le (ad (TX Gp Gn Mn N x) (TY Gp Gn Mp N x)) (N * δ) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (ad (TX Gp Gn Mn (var 0) (Syn.shift x)) (TY Gp Gn Mp (var 0) (Syn.shift x))) (var 0 * Syn.shift δ)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [TX, TY, Fm.subst_imp, subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul,
        PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      have s₁ := natEq (sum_zero (Γ := le zero N :: Γ) Mn x)
      have s₂ := natEq (sum_zero (Γ := le zero N :: Γ) Mp x)
      have c : (le zero N :: Γ) ⊢[PRAAx]
          ad (inst2 Gp zero x + inst2 Gn zero x + ap2 (sumF Mn) zero x)
            (inst2 Gn zero x + inst2 Gp zero x + ap2 (sumF Mp) zero x) ≐ ad zero zero := by
        refine ad_eq_of_cross ?_
        apply deriveNat; ipra_simps; rw [s₁, s₂]; ring
      have e := natEq c
      have z := natEq (monus_self (Γ := le zero N :: Γ) (zero : PTm n))
      ipra_le 0 using linear_combination -e - 2 * z
    · simp only [TX, TY, Fm.subst_imp, subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul,
        PTm.subst_monus, Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have hk : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶
            le (ad (TX Gp Gn Mn (var 0) (Syn.shift x)) (TY Gp Gn Mp (var 0) (Syn.shift x))) (var 0 * Syn.shift δ)) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift N) := Prf.hyp0
      exact tel_step Gp Gn Rp Rn Mp Mn (Prf.impE hR.allOpen.wk.wk hk) (Prf.impE hd.allOpen.wk.wk hk)
        (Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk))
  have h2 := Prf.allE N hall
  simp only [TX, TY, Fm.subst_imp, subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul,
    PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

end Telescope

end LeanProofs.IPRA.Analysis.SignedTelescope
