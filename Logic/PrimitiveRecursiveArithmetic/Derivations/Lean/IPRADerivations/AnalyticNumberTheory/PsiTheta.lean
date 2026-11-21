import IPRADerivations.AnalyticNumberTheory.PiTheta

/-!
# Prime powers of exponent at least two (`pnt_ipra_constructive_2026-11-14`, Lemma `lem:pi-conversion`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `pnt_ipra.tex`, proof of `lem:pi-conversion`:
"Prime powers of exponent at least two contribute `0 ≤ ψ(x) − ϑ(x) = Σ_{a≥2} ϑ(x^{1/a}) ≤ …`." Through
`ψ_w(N) = L_w(lcm(1, …, N))` (`LcmUpto.psi_lcm`) and the valuation of the initial lcm
(`LcmUpto.lcm_valuation`: `p^e ≤ N < p^{e+1}` for `e = v_p(lcm(1, …, N))`):

* `v_tail`: `e = 0` for a prime `p > N`; `v_mid`: `e ≤ 1` for `p ≥ r + 1` when `N < (r + 1)²`;
  `v_low`: `e ≤ L` when `N < 2^{L+1}`;
* `psi_theta`: `ψ_w(N) ≤ θ(N) + L θ(r)` for `r ≤ N < (r + 1)²` and `N < 2^{L+1}`: the sum over primes is
  truncated at `N` (`MobiusBounds.sum_ext`), split at `r`; below `r` each prime weighs at most `L` times
  (`ell_low`), above `r` at most once (`ell_mid`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PsiTheta

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (ellB Lw inst2_ell)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (isP isP_01 prime_of_isP val)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi lcmu lcmuF lcm_valuation lcmu_dvd lcmu_pos psi_lcm)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrVal zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.PiTheta (thB inst2_thB Theta split_at wt_at)
open LeanProofs.IPRA.AnalyticNumberTheory.StepCondition (mul_le2)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlock (sum_le_lin1)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_le')
open LeanProofs.IPRA.Foundations.BoundedFormulas (sg_of_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.Signum (sg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The valuation of the initial lcm -/

/-- For `e = v_p(lcm(1, …, N)) ≥ 1`: `p^e ≤ N`. -/
theorem pe_le {p N : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (he : Γ ⊢[PRAAx] val p (lcmu N) ≐ succ (pred (val p (lcmu N)))) :
    Γ ⊢[PRAAx] le (pw p (val p (lcmu N))) N :=
  le_congr ((congrMul (sg_of_pos he) (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) (Prf.andE₁ (lcm_valuation hp N))

theorem v_tail {p N : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hNp : Γ ⊢[PRAAx] lt N p) :
    Γ ⊢[PRAAx] val p (lcmu N) ≐ zero := by
  have hp0 : Γ ⊢[PRAAx] p ≐ succ (pred p) := pos_of_one_le (le_trans (le_succ_self one) (prime_two hp))
  refine .orE (zero_or_succ (val p (lcmu N))) Prf.hyp0 ?_
  have hs : ((val p (lcmu N) ≐ succ (pred (val p (lcmu N)))) :: Γ) ⊢[PRAAx]
      val p (lcmu N) ≐ succ (pred (val p (lcmu N))) := Prf.hyp0
  have hp1 := hp0.wk (ψ := val p (lcmu N) ≐ succ (pred (val p (lcmu N))))
  have he1 : ((val p (lcmu N) ≐ succ (pred (val p (lcmu N)))) :: Γ) ⊢[PRAAx] le one (val p (lcmu N)) :=
    le_congr (.eqRefl _) hs.eqSymm ((succ_monus_succ _ _).eqTrans (zero_le _))
  have a := le_trans (le_congr (pw_one p) (.eqRefl _) (pw_le_exp hp1 he1)) (pe_le hp.wk hs)
  exact lt_irrefl _ _ (lt_of_lt_of_le hNp.wk a)

theorem v_mid {p N r : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hrp : Γ ⊢[PRAAx] le (succ r) p)
    (hr : Γ ⊢[PRAAx] lt N (succ r * succ r)) : Γ ⊢[PRAAx] le (val p (lcmu N)) one := by
  refine .orE (lt_or_le one (val p (lcmu N))) ?_ Prf.hyp0
  let Θ : List (Fm PTm n) := lt one (val p (lcmu N)) :: Γ
  have h2 : Θ ⊢[PRAAx] le two (val p (lcmu N)) := Prf.hyp0
  have hs : Θ ⊢[PRAAx] val p (lcmu N) ≐ succ (pred (val p (lcmu N))) :=
    pos_of_one_le (le_trans (le_succ_self one) h2)
  have hp1 : Θ ⊢[PRAAx] p ≐ succ (pred p) := pos_of_one_le (le_trans (le_succ_self one) (prime_two hp.wk))
  have e2 : Θ ⊢[PRAAx] pw p two ≐ p * p := (pw_succ p one).eqTrans (congrMul (pw_one p) (.eqRefl _))
  have a := le_trans (mul_le2 hrp.wk hrp.wk)
    (le_trans (le_congr e2 (.eqRefl _) (pw_le_exp hp1 h2)) (pe_le hp.wk hs))
  exact lt_irrefl _ _ (lt_of_lt_of_le hr.wk a)

theorem v_low {p N L : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hL : Γ ⊢[PRAAx] lt N (pw two (succ L))) :
    Γ ⊢[PRAAx] le (val p (lcmu N)) L := by
  refine .orE (lt_or_le L (val p (lcmu N))) ?_ Prf.hyp0
  let Θ : List (Fm PTm n) := lt L (val p (lcmu N)) :: Γ
  have h1 : Θ ⊢[PRAAx] le (succ L) (val p (lcmu N)) := Prf.hyp0
  have hs : Θ ⊢[PRAAx] val p (lcmu N) ≐ succ (pred (val p (lcmu N))) :=
    pos_of_one_le (le_trans ((succ_monus_succ _ _).eqTrans (zero_le _)) h1)
  have p2 : Θ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := pos_of_one_le (le_succ_self one)
  have a := le_trans (pw_le_exp p2 h1)
    (le_trans (pw_le_pw (val p (lcmu N)) (prime_two hp.wk)) (pe_le hp.wk hs))
  exact lt_irrefl _ _ (lt_of_lt_of_le hL.wk a)

theorem le_lcmu (N : PTm n) : Γ ⊢[PRAAx] le N (lcmu N) := by
  refine .orE (zero_or_succ N) ?_ ?_
  · exact le_congr (Prf.hyp0 : ((N ≐ zero) :: Γ) ⊢[PRAAx] N ≐ zero).eqSymm (.eqRefl _) (zero_le _)
  · have hs : ((N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp0
    have d := Prf.andE₂ (lcmu_dvd (Γ := (N ≐ succ (pred N)) :: Γ) (pred N))
    have a := dvd_le' (congrSucc (pred_succ _).eqSymm) d (lcmu_pos _)
    exact le_congr hs.eqSymm (congrAp2 lcmuF hs.eqSymm (.eqRefl zero)) a

/-! ## Pointwise comparisons of the weights -/

section Points

variable {q N K F : PTm n}

theorem ell_eq (q M K F : PTm n) :
    Γ ⊢[PRAAx] inst2 (ellB wt) q (pairT M (pairT K F)) ≐ (isP q * val q M) * U q K F := by
  rw [inst2_ell]
  exact congrMul (congrMul (.eqRefl _) (congrVal (.eqRefl _) (fst_pair _ _)))
    ((congrInst2 wt (.eqRefl _) (snd_pair _ _)).eqTrans (wt_at _ _ _))

theorem th_eq (q K F : PTm n) : Γ ⊢[PRAAx] inst2 thB q (pairT K F) ≐ isP q * U q K F := by
  rw [inst2_thB]; exact congrMul (.eqRefl _) (wt_at _ _ _)

theorem ell_tail (hNq : Γ ⊢[PRAAx] lt N q) : Γ ⊢[PRAAx] inst2 (ellB wt) q (pairT (lcmu N) (pairT K F)) ≐ zero := by
  refine (ell_eq q (lcmu N) K F).eqTrans ?_
  refine .orE (isP_01 q) ?_ ?_
  · exact zero_mul_l (zero_mul_l Prf.hyp0 _) _
  · have hv := v_tail (prime_of_isP (Prf.hyp0 : ((isP q ≐ one) :: Γ) ⊢[PRAAx] isP q ≐ one)) hNq.wk
    exact zero_mul_l ((congrMul (.eqRefl _) hv).eqTrans (mul_zero _)) _

/-- A weight bound `v ≤ c` for primes gives `[q prime] v u_q ≤ c [q prime] u_q`. -/
theorem weigh {c : PTm n} (hv : ((isP q ≐ one) :: Γ) ⊢[PRAAx] le (val q (lcmu N)) c) :
    Γ ⊢[PRAAx] le (one * inst2 (ellB wt) q (pairT (lcmu N) (pairT K F))) (c * inst2 thB q (pairT K F)) := by
  refine le_congr (congrMul (.eqRefl _) (ell_eq q (lcmu N) K F)).eqSymm
    (congrMul (.eqRefl _) (th_eq q K F)).eqSymm ?_
  refine .orE (isP_01 q) ?_ ?_
  · have e := natEq (Prf.hyp0 : ((isP q ≐ zero) :: Γ) ⊢[PRAAx] isP q ≐ zero)
    ipra_le 0 with (𝔞 c * 𝔞 (U q K F) - 𝔞 (val q (lcmu N)) * 𝔞 (U q K F)) * e
  · have h1 : ((isP q ≐ one) :: Γ) ⊢[PRAAx] isP q ≐ one := Prf.hyp0
    have e := natEq h1
    have a := mul_le_mul_right (U q K F) hv
    ipra_le sl a with (𝔞 c * 𝔞 (U q K F) - 𝔞 (val q (lcmu N)) * 𝔞 (U q K F)) * e

end Points

/-! ## The comparison of the sums -/

/-- `ψ_w(N) ≤ θ(N) + L θ(r)` for `r ≤ N < (r + 1)²`, `N < 2^{L+1}`. -/
theorem psi_theta {N r L K F : PTm n} (hrN : Γ ⊢[PRAAx] le r N) (hr : Γ ⊢[PRAAx] lt N (succ r * succ r))
    (hL : Γ ⊢[PRAAx] lt N (pw two (succ L))) :
    Γ ⊢[PRAAx] le (Psi wt N (pairT K F)) (Theta N (pairT K F) + L * Theta r (pairT K F)) := by
  have hNs : (Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.shift N) (succ (Syn.shift r) * succ (Syn.shift r)) := by
    simpa [Fm.shift, Syn.shift] using hr.shift
  have hLs : (Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.shift N) (pw two (succ (Syn.shift L))) := by
    simpa [Fm.shift, Syn.shift] using hL.shift
  have e0 := natEq (psi_lcm (Γ := Γ) wt N (pairT K F))
  have e1 := natEq (sum_ext (Γ := Γ) (ellB wt) (B := N) (x := pairT (lcmu N) (pairT K F)) (N := succ (lcmu N))
    (fun Δ a hs hl => by
      rw [show Syn.shift (pairT (lcmu N) (pairT K F)) =
        pairT (lcmu (Syn.shift N)) (pairT (Syn.shift K) (Syn.shift F)) by simp [Syn.shift]]
      exact ell_tail hl)
    ((succ_monus_succ _ _).eqTrans (le_lcmu N)))
  have e2 := natEq (split_at (Γ := Γ) (g := ellB wt) (pairT (lcmu N) (pairT K F)) hrN)
  have et := natEq (split_at (Γ := Γ) (g := thB) (pairT K F) hrN)
  have hh := sum_le_lin1 (Γ := Γ) (ellB wt) thB one L (pairT (lcmu N) (pairT K F)) (pairT K F) (succ r)
    (.allI (.impI (by
      rw [show Syn.shift (pairT (lcmu N) (pairT K F)) =
          pairT (lcmu (Syn.shift N)) (pairT (Syn.shift K) (Syn.shift F)) by simp [Syn.shift],
        show Syn.shift (pairT K F) = pairT (Syn.shift K) (Syn.shift F) by simp [Syn.shift],
        show Syn.shift (one : PTm n) = one by simp [Syn.shift]]
      exact weigh (v_low (prime_of_isP Prf.hyp0) hLs.wk.wk))))
  have ht := sum_le_lin1 (Γ := Γ) (offB (ellB wt)) (offB thB) one one
    (pairT (succ r) (pairT (lcmu N) (pairT K F))) (pairT (succ r) (pairT K F)) (monus N r)
    (.allI (.impI (by
      simp only [inst2_offB]
      rw [show Syn.shift (pairT (succ r) (pairT (lcmu N) (pairT K F))) =
          pairT (succ (Syn.shift r)) (pairT (lcmu (Syn.shift N)) (pairT (Syn.shift K) (Syn.shift F))) by
          simp [Syn.shift],
        show Syn.shift (pairT (succ r) (pairT K F)) = pairT (succ (Syn.shift r)) (pairT (Syn.shift K) (Syn.shift F)) by
          simp [Syn.shift],
        show Syn.shift (one : PTm n) = one by simp [Syn.shift]]
      have ed1 : (lt (var 0) (Syn.shift (monus N r)) :: Γ.map Fm.shift) ⊢[PRAAx]
          fstT (pairT (succ (Syn.shift r)) (pairT (lcmu (Syn.shift N)) (pairT (Syn.shift K) (Syn.shift F)))) + var 0 ≐
            succ (Syn.shift r) + var 0 := congrAdd (fst_pair _ _) (.eqRefl _)
      have ed2 : (lt (var 0) (Syn.shift (monus N r)) :: Γ.map Fm.shift) ⊢[PRAAx]
          fstT (pairT (succ (Syn.shift r)) (pairT (Syn.shift K) (Syn.shift F))) + var 0 ≐ succ (Syn.shift r) + var 0 :=
        congrAdd (fst_pair _ _) (.eqRefl _)
      have b := weigh (Γ := lt (var 0) (Syn.shift (monus N r)) :: Γ.map Fm.shift) (q := succ (Syn.shift r) + var 0)
        (N := Syn.shift N) (K := Syn.shift K) (F := Syn.shift F) (c := one)
        (v_mid (prime_of_isP Prf.hyp0) (by ipra_le 𝔞 (var 0)) hNs.wk.wk)
      exact le_congr (congrMul (.eqRefl _) (congrInst2 (ellB wt) ed1 (snd_pair _ _))).eqSymm
        (congrMul (.eqRefl _) (congrInst2 thB ed2 (snd_pair _ _))).eqSymm b)))
  ipra_le sl hh + sl ht + 𝔞 (Theta r (pairT K F)) with et - e0 - e1 - e2

end LeanProofs.IPRA.AnalyticNumberTheory.PsiTheta
