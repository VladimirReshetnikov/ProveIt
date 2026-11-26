import IPRADerivations.AnalyticNumberTheory.PhiUpper
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Finite witnesses for `limsup φ(n)/n = 1`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:limsup-phi`:
for every `K ≥ 1` the explicit prime `p = lpf(K! + 1)` satisfies `p > K` and
`K φ(p) ≥ (K − 1) p`.

Euclid's argument (`Primes.euclid`) is re-run for an arbitrary term `K`: a prime `p ≤ K` would
divide both `K!` and `K! + 1`. Then `φ(p) = p − 1` (`Radical.phi_prime`) and
`K (p − 1) = (K − 1) p + (p − K)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PhiLimsup

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (lpf μz lpf_dvd lpf_prime prime dvd_fact fact_pos not_dvd_one)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Radical (phi_prime)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Euclid's prime `lpf(K! + 1)`. -/
abbrev EP (K : PTm n) : PTm n := lpf (succ (succ (pred (fact K))))

/-- `K < lpf(K! + 1)`. -/
theorem lt_EP (K : PTm n) : Γ ⊢[PRAAx] lt K (EP K) := by
  refine .orE (lt_or_le K (EP K)) Prf.hyp0 ?_
  have harg : (le (EP K) K :: Γ) ⊢[PRAAx] succ (succ (pred (fact K))) ≐ succ (fact K) :=
    congrSucc (fact_pos _).eqSymm
  have h₁ := dvd_fact (d' := succ (μz (succ (succ (pred (fact K))))))
    (Prf.hyp0 : (le (EP K) K :: Γ) ⊢[PRAAx] _)
  have h₂ := Prf.andE₁ (lpf_dvd (Γ := le (EP K) K :: Γ) (pred (fact K)))
  have h₃ : (le (EP K) K :: Γ) ⊢[PRAAx] dvd (EP K) (one + fact K) :=
    dvd_congr (harg.eqTrans ((succ_eq_add_one _).eqTrans (add_comm _ _))) h₂
  exact not_dvd_one (p' := μz (succ (succ (pred (fact K))))) _ (dvd_sub h₃ h₁)

/-- `thm:limsup-phi` at a term `K ≥ 1`. -/
theorem limsup_at {K : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) :
    Γ ⊢[PRAAx] lt K (EP K) ⋏ (prime (EP K) ⋏ le (monus K one * EP K) (K * phi (EP K))) := by
  have hlt := lt_EP (Γ := Γ) K
  have hp : Γ ⊢[PRAAx] prime (EP K) := lpf_prime _
  have e := eq_add_of_le hlt
  -- `φ(p) = p − 1 = K + e`.
  have hφ : Γ ⊢[PRAAx] phi (EP K) ≐ K + monus (EP K) (succ K) :=
    (phi_prime hp).eqTrans ((congrMonus (e.eqTrans (succ_add _ _)) (.eqRefl _)).eqTrans
      ((succ_monus_succ _ _).eqTrans (monus_zero _)))
  refine .andI hlt (.andI hp (le_of_eq_add (d := succ (monus (EP K) (succ K))) ?_))
  have hm : Γ ⊢[PRAAx] monus K one ≐ pred K :=
    (congrMonus hK (.eqRefl _)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _))
  ipra_lc Groth.ι (IPRA.Q.mk Γ K) * natEq hφ - Groth.ι (IPRA.Q.mk Γ (pred K)) * natEq e +
    (Groth.ι (IPRA.Q.mk Γ K) + Groth.ι (IPRA.Q.mk Γ (monus (EP K) (succ K))) + 1) * natEq hK -
    (Groth.ι (IPRA.Q.mk Γ (μz (succ (succ (pred (fact K)))))) + 2) * natEq hm

/-- `thm:limsup-phi`: variable `0 = K − 1`. -/
abbrev limsupFormula : Fm PTm 1 :=
  lt (succ (var 0)) (EP (succ (var 0))) ⋏ (prime (EP (succ (var 0))) ⋏
    le (monus (succ (var 0)) one * EP (succ (var 0))) (succ (var 0) * phi (EP (succ (var 0)))))

theorem limsup_phi : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 limsupFormula :=
  closeUniv 1 (limsup_at (congrSucc (pred_succ _).eqSymm))

end LeanProofs.IPRA.AnalyticNumberTheory.PhiLimsup
