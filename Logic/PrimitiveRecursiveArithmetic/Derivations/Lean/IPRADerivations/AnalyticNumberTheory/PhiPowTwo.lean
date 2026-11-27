import IPRADerivations.AnalyticNumberTheory.PhiLimsup

/-!
# Prime powers whose totient is a power of two

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Proposition (arithmetic
part of the constructible prime-power criterion, `T36`): for an odd prime `p` and `a = k + 1 ≥ 1`,
if `φ(p^a) = 2^m` then `a = 1` and `p − 1 = 2^m`.

`φ(p^{k+1}) = p^k (p − 1)` (`PhiLower.phi_ppow`). If `k ≥ 1` then `p ∣ φ(p^{k+1}) = 2^m`, while
`gcd(p, 2) = 1` (as `p` is odd) gives `gcd(p, 2^m) = 1` (`Totient.coprime_pow`), so `p = 1`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PhiPowTwo

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi coprime_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (phi_ppow)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- An odd positive `p` is coprime to `2`. -/
theorem gcd_two_of_odd {p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (hodd : Γ ⊢[PRAAx] rem p two ≐ one) :
    Γ ⊢[PRAAx] gcd p two ≐ one := by
  have hg := gcd_dvd' (b := two) hp
  have hgp := gcd_pos (B := two) hp
  have hle : Γ ⊢[PRAAx] le (gcd p two) two := dvd_le' hgp (Prf.andE₂ hg) two_pos'
  refine .orE (lt_or_eq_of_le hle) ?_ ?_
  · exact le_antisymm (Order.le_of_lt_succ Prf.hyp0) (one_le_of_pos hgp.wk)
  · have h2 : ((gcd p two ≐ two) :: Γ) ⊢[PRAAx] rem p two ≐ zero := dvd_congr_left Prf.hyp0 (Prf.andE₁ hg).wk
    exact succ_ne_zero' _ (hodd.wk.eqSymm.eqTrans h2)

/-- The proposition: `φ(p^{k+1}) = 2^m` forces `k = 0` and `p − 1 = 2^m`. -/
theorem phi_ppow_two {p k m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] rem p two ≐ one)
    (h : Γ ⊢[PRAAx] phi (pw p (succ k)) ≐ pw two m) :
    Γ ⊢[PRAAx] (k ≐ zero) ⋏ (monus p one ≐ pw two m) := by
  have hφ := phi_ppow hp k
  have hpos := prime_eq_succ_pred hp
  have hp2 : Γ ⊢[PRAAx] le two p := by have h := hp; unfold prime at h; exact Prf.andE₁ h
  refine .orE (zero_or_succ k) ?_ ?_
  · refine .andI Prf.hyp0 ?_
    have e : ((k ≐ zero) :: Γ) ⊢[PRAAx] pw p k ≐ one := (congrAp2 powF Prf.hyp0 (.eqRefl _)).eqTrans (pw_zero _)
    exact ((congrMul e (.eqRefl _)).eqTrans (one_mul _)).eqSymm.eqTrans (hφ.wk.eqSymm.eqTrans h.wk)
  · refine .botE _ ?_
    -- `p ∣ p^k (p − 1) = 2^m`.
    have hk : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] pw p k ≐ pw p (pred k) * p :=
      (congrAp2 powF Prf.hyp0 (.eqRefl _)).eqTrans (pw_succ _ _)
    have hd : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] dvd p (pw two m) := by
      refine dvd_of_eq' hpos.wk (w := pw p (pred k) * monus p one) ?_
      have e₀ : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] pw two m ≐ pw p k * monus p one := h.wk.eqSymm.eqTrans hφ.wk
      ipra_lc natEq e₀ + Groth.ι (IPRA.Q.mk _ (monus p one)) * natEq hk
    have hc := coprime_pow hpos (gcd_two_of_odd hpos hodd) m
    have h1 := eq_one_of_coprime_dvd hpos.wk hc.wk hd
    exact not_succ_le_self one _ (le_congr (.eqRefl _) h1 hp2.wk)

/-- Variables `0 = p`, `1 = a − 1`, `2 = m`. -/
abbrev phiPowTwoFormula : Fm PTm 3 :=
  prime (var 0) ⟶ rem (var 0) two ≐ one ⟶ phi (pw (var 0) (succ (var 1))) ≐ pw two (var 2) ⟶
    (var 1 ≐ zero) ⋏ (monus (var 0) one ≐ pw two (var 2))

theorem phi_pow_two : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 phiPowTwoFormula :=
  closeUniv 3 (.impI (.impI (.impI (phi_ppow_two Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.AnalyticNumberTheory.PhiPowTwo
