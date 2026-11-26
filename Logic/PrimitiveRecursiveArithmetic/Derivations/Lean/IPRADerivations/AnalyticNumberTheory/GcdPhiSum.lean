import IPRADerivations.AnalyticNumberTheory.MobiusInversion
import IPRADerivations.DiophantineNumberTheory.GcdList
import IPRADerivations.AnalyticNumberTheory.DivisorFactor
import IPRADerivations.Core.Header

/-!
# The greatest common divisor as a totient sum over common divisors

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, the first step of the
diagonalization `eq:sieve-diagonal` of the Selberg quadratic form: "substitute
`gcd(d, e) = Σ_{r ∣ d, r ∣ e} φ(r)` into the double sum", which is `eq:divisor-identities` (`Σ_{r ∣ n} φ(r) = n`)
at `n = gcd(d, e)`.

* `div_gcd`: for `r ≥ 1`, `[r ∣ gcd(d, e)] = [r ∣ d] [r ∣ e]` (indicators), from the universal property of the gcd;
* `gB`, `gB_at`: the body `[r ∣ d] [r ∣ e] φ(r)` over `(r, ⟨d, e⟩)`;
* `gcd_phi_sum`: for `1 ≤ d ≤ Z`, `Σ_{r ≤ Z} [r ∣ d] [r ∣ e] φ(r) = gcd(d, e)` — `SumPhi.sum_phi_at` at the gcd, with
  the range extended from `gcd(d, e)` to `Z` (`MobiusBounds.sum_ext`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.GcdPhiSum

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (dpB inst2_dp sum_phi_at)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (eqb_rem_big)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_greatest' gcd_dvd' dvd_le')
open LeanProofs.IPRA.DiophantineNumberTheory.GcdList (gcd_dvd_all dvd_trans_all)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `[r ∣ gcd(d, e)] = [r ∣ d] [r ∣ e]` for `r ≥ 1`. -/
theorem div_gcd {r d e : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ (pred r)) :
    Γ ⊢[PRAAx] eqb (rem (gcd d e) r) zero ≐ eqb (rem d r) zero * eqb (rem e r) zero := by
  refine .orE (eq_or_ne (rem d r) zero) ?_ ?_
  · refine .orE (eq_or_ne (rem e r) zero) ?_ ?_
    · have hd : ((rem e r ≐ zero) :: (rem d r ≐ zero) :: Γ) ⊢[PRAAx] dvd r d := Prf.hyp1
      have he : ((rem e r ≐ zero) :: (rem d r ≐ zero) :: Γ) ⊢[PRAAx] dvd r e := Prf.hyp0
      have hg := gcd_greatest' hr.wk.wk hd he
      exact (eqb_of_eq hg).eqTrans ((congrMul (eqb_of_eq hd) (eqb_of_eq he)).eqTrans (one_mul one)).eqSymm
    · have hne : (neg (rem e r ≐ zero) :: (rem d r ≐ zero) :: Γ) ⊢[PRAAx] neg (rem e r ≐ zero) := Prf.hyp0
      have hn : (neg (rem e r ≐ zero) :: (rem d r ≐ zero) :: Γ) ⊢[PRAAx] neg (rem (gcd d e) r ≐ zero) :=
        .impI (Prf.impE hne.wk (dvd_trans_all Prf.hyp0 (Prf.andE₂ (gcd_dvd_all d e))))
      exact (eqb_of_ne hn).eqTrans ((congrMul (.eqRefl _) (eqb_of_ne hne)).eqTrans (mul_zero _)).eqSymm
  · have hne : (neg (rem d r ≐ zero) :: Γ) ⊢[PRAAx] neg (rem d r ≐ zero) := Prf.hyp0
    have hn : (neg (rem d r ≐ zero) :: Γ) ⊢[PRAAx] neg (rem (gcd d e) r ≐ zero) :=
      .impI (Prf.impE hne.wk (dvd_trans_all Prf.hyp0 (Prf.andE₁ (gcd_dvd_all d e))))
    exact (eqb_of_ne hn).eqTrans ((congrMul (eqb_of_ne hne) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm

/-- `[r ∣ d] [r ∣ e] φ(r)` over `0 = r`, `1 = ⟨d, e⟩`. -/
abbrev gB : PTm 2 :=
  eqb (rem (fstT (var 1)) (var 0)) zero * eqb (rem (sndT (var 1)) (var 0)) zero * ap2 (sumF totBody) (var 0) (var 0)

theorem inst2_gB (r y : PTm n) :
    inst2 gB r y = eqb (rem (fstT y) r) zero * eqb (rem (sndT y) r) zero * phi r := by
  simp only [inst2, PTm.subst_mul, subst_eqb, subst_ap2, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_zero]

theorem gB_at (r d e : PTm n) :
    Γ ⊢[PRAAx] inst2 gB r (pairT d e) ≐ eqb (rem d r) zero * eqb (rem e r) zero * phi r := by
  rw [inst2_gB]
  exact congrMul (congrMul (congrEqb' (congrAp2 remF (fst_pair d e) (.eqRefl r)) (.eqRefl zero))
    (congrEqb' (congrAp2 remF (snd_pair d e) (.eqRefl r)) (.eqRefl zero))) (.eqRefl _)

/-- The summand at `(r, ⟨d, e⟩)` is the summand `[r ∣ gcd(d, e)] φ(r)` of the totient sum. -/
theorem gB_pt (r d e : PTm n) : Γ ⊢[PRAAx] inst2 gB r (pairT d e) ≐ inst2 dpB r (gcd d e) := by
  rw [inst2_dp]
  refine (gB_at r d e).eqTrans ?_
  refine .orE (zero_or_succ r) ?_ ?_
  · have h0 : ((r ≐ zero) :: Γ) ⊢[PRAAx] r ≐ zero := Prf.hyp0
    have p0 : ((r ≐ zero) :: Γ) ⊢[PRAAx] phi r ≐ zero :=
      (congrAp2 (sumF totBody) h0 h0).eqTrans (sum_zero totBody zero)
    exact ((congrMul (.eqRefl _) p0).eqTrans (mul_zero _)).eqTrans
      ((congrMul (.eqRefl _) p0).eqTrans (mul_zero _)).eqSymm
  · exact congrMul (div_gcd Prf.hyp0).eqSymm (.eqRefl _)

/-- `Σ_{r ≤ Z} [r ∣ d] [r ∣ e] φ(r) = gcd(d, e)` for `1 ≤ d ≤ Z`. -/
theorem gcd_phi_sum {d e Z : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hdZ : Γ ⊢[PRAAx] le d Z) :
    Γ ⊢[PRAAx] ap2 (sumF gB) (succ Z) (pairT d e) ≐ gcd d e := by
  have hg : Γ ⊢[PRAAx] gcd d e ≐ succ (pred (gcd d e)) := gcd_pos hd
  have hgd : Γ ⊢[PRAAx] le (gcd d e) d := dvd_le' hg (Prf.andE₁ (gcd_dvd' hd)) hd
  have hgZ : Γ ⊢[PRAAx] le (succ (gcd d e)) (succ Z) := (succ_monus_succ _ _).eqTrans (le_trans hgd hdZ)
  have s1 := sum_phi_at hg
  have hg' := shift_pos hg
  have s2 : Γ ⊢[PRAAx] ap2 (sumF dpB) (succ Z) (gcd d e) ≐ ap2 (sumF dpB) (succ (gcd d e)) (gcd d e) := by
    refine sum_ext dpB (fun Δ a hs hl => ?_) hgZ
    rw [inst2_dp]
    exact (congrMul (eqb_rem_big (hg'.weaken hs) hl) (.eqRefl _)).eqTrans (zero_mul _)
  have s3 : Γ ⊢[PRAAx] ap2 (sumF gB) (succ Z) (pairT d e) ≐ ap2 (sumF dpB) (succ Z) (gcd d e) := by
    refine sum_congr_bounded gB dpB (pairT d e) (gcd d e) (succ Z) (.allI (.impI ?_))
    rw [shift_pairT, LeanProofs.IPRA.AnalyticNumberTheory.DivisorFactor.shift_gcd]
    exact gB_pt _ _ _
  exact s3.eqTrans (s2.eqTrans s1)

end LeanProofs.IPRA.AnalyticNumberTheory.GcdPhiSum
