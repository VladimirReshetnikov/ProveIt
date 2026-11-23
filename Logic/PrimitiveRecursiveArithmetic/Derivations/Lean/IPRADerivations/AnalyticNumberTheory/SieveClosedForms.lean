import IPRADerivations.AnalyticNumberTheory.SieveBilinear
import IPRADerivations.AnalyticNumberTheory.SieveDiagonal

/-!
# The main term and the error term of the bilinear sieve estimate

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, proof of `thm:finite-sieve`:
the main term `(x/q) Σ_{d,e} λ_d λ'_e / [d, e]` and the error term `Σ_{d,e} |λ_d| |λ'_e| = (Σ_d |λ_d|)(Σ_e |λ'_e|)`.

`SieveBilinear` bounds `q N` by double sums `C` and `E` whose summands carry the indicator `ind`. Here the
indicators are absorbed into the weights:

* `C_closed`: `C = (χ X) · Σ_{d<Z} Σ_{e<Z} [d ≥ 1] u_d v_e gcd(d, e)` with `u_d = [gcd(d, q) = 1] U_d` (`gU`) and
  `v_e = [e ≥ 1][gcd(e, q) = 1] V_e` (`sgV`); the double sum is the body `Lb` of `SieveDiagonal`, the bilinear form
  that `SieveDiagonal.diag` diagonalizes;
* `E_closed`: `E = (χ q) · (Σ_{d<Z} λ_d)(Σ_{e<Z} λ'_e)` with `λ_d = d [d ≥ 1][gcd(d, q) = 1] U_d`
  (`Independence.sum_mul_sum`);
* `bil_le`, `bil_ge`: for `q = fst P ≥ 2` and `gcd(a, q) = 1`,
  `q N ≤ X G + q L L'` and `X G ≤ q N + q L L'`, where `G` is that bilinear form and `L`, `L'` are the two weight
  sums. This is `|N − (X/q) Σ λ_d λ'_e / [d, e]| ≤ (Σ λ_d)(Σ λ'_e)` for natural weights.

`χ = [2 ≤ q][gcd(a, q) = 1]`; both closed forms hold at all terms, by `Foundations/DoubleSumScale.dsum_scale`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveClosedForms

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.SievePairSum (subst_gcd' Cm inst3_Cm inst3_wB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion (cB lB inst2_lB kT at1_kT)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveBilinear (Em inst3_Em ooq kq bil_upper bil_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveDiagonal (Lb inst3_Lb)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorExchange (LW)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.Foundations.DoubleSumScale (at1 dsum_scale)
open LeanProofs.IPRA.Probability.Independence (dsum pmB inst3_pmB sum_mul_sum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Algebra -/

/-- `ind · ((U V) (g X)) = (χ X) · (sd (gd U) ((se ge) V) g)`. -/
theorem c_alg (c1 c2 sd gd se ge Ud Ve g X : PTm n) :
    Γ ⊢[PRAAx] (c1 * (c2 * (sd * (gd * (se * (ge * one)))))) * ((Ud * Ve) * (g * X)) ≐
      ((c1 * c2) * X) * (sd * (gd * Ud) * ((se * ge) * Ve) * g) := by
  apply deriveNat; ipra_simps; ring

/-- `ind · ((U V) (q (d e))) = (χ q) · ((d ((sd gd) U)) (e ((se ge) V)))`. -/
theorem e_alg (c1 c2 sd gd se ge Ud Ve q d e : PTm n) :
    Γ ⊢[PRAAx] (c1 * (c2 * (sd * (gd * (se * (ge * one)))))) * ((Ud * Ve) * (q * (d * e))) ≐
      ((c1 * c2) * q) * ((d * ((sd * gd) * Ud)) * (e * ((se * ge) * Ve))) := by
  apply deriveNat; ipra_simps; ring

/-! ## The weights with their indicators -/

/-- `[gcd(d, q) = 1] U(d, P)` over `0 = d`, `1 = P`. -/
def gU (U : PTm 2) : PTm 2 := eqb (gcd (var 0) (fstT (var 1))) one * U

theorem inst2_gU (U : PTm 2) (d P : PTm n) : inst2 (gU U) d P = eqb (gcd d (fstT P)) one * inst2 U d P := by
  simp only [inst2, gU, LeanProofs.IPRA.PTm.subst_mul, subst_eqb, subst_gcd', subst_fstT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

/-- `[e ≥ 1][gcd(e, q) = 1] V(e, P)` over `0 = e`, `1 = P`. -/
def sgV (V : PTm 2) : PTm 2 := (sg (var 0) * eqb (gcd (var 0) (fstT (var 1))) one) * V

theorem inst2_sgV (V : PTm 2) (e P : PTm n) :
    inst2 (sgV V) e P = (sg e * eqb (gcd e (fstT P)) one) * inst2 V e P := by
  simp only [inst2, sgV, LeanProofs.IPRA.PTm.subst_mul, subst_eqb, LeanProofs.IPRA.PTm.subst_monus, subst_gcd',
    subst_fstT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- `χ · X` as a term in the parameter `y = ⟨X, P⟩`. -/
def kC : PTm 1 :=
  (eqb (monus one (fstT (sndT (var 0)))) zero * eqb (gcd (fstT (sndT (sndT (var 0)))) (fstT (sndT (var 0)))) one) *
    fstT (var 0)

theorem at1_kC (y : PTm n) : at1 kC y =
    (eqb (monus one (fstT (sndT y))) zero * eqb (gcd (fstT (sndT (sndT y))) (fstT (sndT y))) one) * fstT y := by
  simp only [at1, kC, LeanProofs.IPRA.PTm.subst_mul, subst_eqb, LeanProofs.IPRA.PTm.subst_monus, subst_gcd',
    subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

section Forms

variable (U V : PTm 2)

/-! ## The main term -/

theorem C_pt (i j y : PTm n) :
    Γ ⊢[PRAAx] inst3 (Cm U V) i j y ≐ at1 kC y * inst3 (Lb (sndB (gU U)) (sndB (sgV V))) i j y := by
  rw [inst3_Cm, inst3_wB, at1_kC, inst3_Lb, inst2_sndB, inst2_sndB, inst2_gU, inst2_sgV]
  exact c_alg _ _ _ _ _ _ _ _ _ _

/-- `C = (χ X) · Σ_{d<Z} Σ_{e<Z} [d ≥ 1] u_d v_e gcd(d, e)`. -/
theorem C_closed (Z y : PTm n) :
    Γ ⊢[PRAAx] dsum (Cm U V) Z Z y ≐ at1 kC y * dsum (Lb (sndB (gU U)) (sndB (sgV V))) Z Z y :=
  dsum_scale (Cm U V) (Lb (sndB (gU U)) (sndB (sgV V))) kC (fun i j y => C_pt U V i j y) Z Z y

/-! ## The error term -/

theorem E_pt (i j y : PTm n) :
    Γ ⊢[PRAAx] inst3 (Em U V) i j y ≐ at1 kT y * inst3 (pmB (sndB (lB U)) (sndB (lB V))) i j y := by
  rw [inst3_Em, inst3_wB, at1_kT, inst3_pmB, inst2_sndB, inst2_sndB, inst2_lB, inst2_lB]
  exact e_alg _ _ _ _ _ _ _ _ _ _ _

/-- `E = (χ q) · (Σ_{d<Z} λ_d)(Σ_{e<Z} λ'_e)`. -/
theorem E_closed (Z y : PTm n) :
    Γ ⊢[PRAAx] dsum (Em U V) Z Z y ≐
      at1 kT y * (ap2 (sumF (sndB (lB U))) Z y * ap2 (sumF (sndB (lB V))) Z y) :=
  (dsum_scale (Em U V) (pmB (sndB (lB U)) (sndB (lB V))) kT (fun i j y => E_pt U V i j y) Z Z y).eqTrans
    (congrMul (.eqRefl _) (sum_mul_sum (sndB (lB U)) (sndB (lB V)) Z Z y))

/-! ## The estimate -/

/-- Under `q ≥ 1` and `gcd(a, q) = 1`, the factor `χ X` is `X`. -/
theorem kX {X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) :
    Γ ⊢[PRAAx] at1 kC (pairT X P) ≐ X := by
  rw [at1_kC]
  have s := snd_pair (Γ := Γ) X P
  have cq : Γ ⊢[PRAAx] fstT (sndT (pairT X P)) ≐ fstT P := congrFst s
  have ca : Γ ⊢[PRAAx] fstT (sndT (sndT (pairT X P))) ≐ fstT (sndT P) := congrFst (congrSnd s)
  have k1 : Γ ⊢[PRAAx] eqb (monus one (fstT (sndT (pairT X P)))) zero ≐ one :=
    (congrEqb' (congrMonus (.eqRefl _) cq) (.eqRefl _)).eqTrans (eqb_of_eq hq)
  have k2 : Γ ⊢[PRAAx] eqb (gcd (fstT (sndT (sndT (pairT X P)))) (fstT (sndT (pairT X P)))) one ≐ one :=
    (congrEqb' (congrGcd ca cq) (.eqRefl _)).eqTrans (eqb_of_eq ha)
  exact (congrMul (congrMul k1 k2) (fst_pair X P)).eqTrans (ooq _)

/-- `q N ≤ X G + q L L'`. -/
theorem bil_le {X Z P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) :
    Γ ⊢[PRAAx] le (fstT P * ap2 (sumF (LW (LW cB (lB V)) (sndB (lB U)))) X (pairT Z (pairT Z P)))
      (X * dsum (Lb (sndB (gU U)) (sndB (sgV V))) Z Z (pairT X P) +
        fstT P * (ap2 (sumF (sndB (lB U))) Z (pairT X P) * ap2 (sumF (sndB (lB V))) Z (pairT X P))) :=
  le_congr (.eqRefl _)
    (congrAdd ((C_closed U V Z (pairT X P)).eqTrans (congrMul (kX hq ha) (.eqRefl _)))
      ((E_closed U V Z (pairT X P)).eqTrans (congrMul (kq hq ha) (.eqRefl _))))
    (bil_upper U V hq ha)

/-- `X G ≤ q N + q L L'`. -/
theorem bil_ge {X Z P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) :
    Γ ⊢[PRAAx] le (X * dsum (Lb (sndB (gU U)) (sndB (sgV V))) Z Z (pairT X P))
      (fstT P * ap2 (sumF (LW (LW cB (lB V)) (sndB (lB U)))) X (pairT Z (pairT Z P)) +
        fstT P * (ap2 (sumF (sndB (lB U))) Z (pairT X P) * ap2 (sumF (sndB (lB V))) Z (pairT X P))) :=
  le_congr ((C_closed U V Z (pairT X P)).eqTrans (congrMul (kX hq ha) (.eqRefl _)))
    (congrAdd (.eqRefl _) ((E_closed U V Z (pairT X P)).eqTrans (congrMul (kq hq ha) (.eqRefl _))))
    (bil_lower U V hq ha)

end Forms

end LeanProofs.IPRA.AnalyticNumberTheory.SieveClosedForms
