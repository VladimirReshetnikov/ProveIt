import IPRADerivations.AnalyticNumberTheory.Euler
import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.AnalyticNumberTheory.Radical
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.AnalyticNumberTheory.GcdFiber
import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc
import IPRADerivations.AnalyticNumberTheory.Mobius
import IPRADerivations.DiophantineNumberTheory.ModularCertificate
import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.Core.ParityArith
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# Three facts about residues modulo a prime

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, §"A square test from
an involution" ("From `(x − 1)(x + 1) ≡ 0`, the roots are precisely `1` and `p − 1`"; "Both signs are
distinguishable modulo `p`"; the residue half of `eq:euler`).

With `−1` represented by the residue `p − 1`:

* `neg_sq`, `neg_pow_even`, `neg_pow_odd`: `(p − 1)² ≡ 1`, hence `(p − 1)^k ≡ 1` for even `k` and
  `(p − 1)^k ≡ p − 1` for odd `k` (mod `p`), for `p ≥ 2`;
* `sq_one`: for a prime `p` and `1 ≤ x < p`, `x² ≡ 1 (mod p)` gives `x = 1` or `x = p − 1`
  (`p ∣ (x − 1)(x + 1)` and Gauss's lemma);
* `residue_pow`: for an odd prime `p = 2h + 1` and `gcd(x, p) = 1`, `(x²)^h ≡ 1 (mod p)`
  (`Euler.euler_at` with `φ(p) = p − 1`): a square has `a^h ≡ 1`.

Euler's criterion for nonresidues is not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ResidueFacts

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (rem_small)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (euler_at)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_rem_congr pw_one_base)
open LeanProofs.IPRA.AnalyticNumberTheory.Radical (phi_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gauss dvd_le' dvd_of_eq')
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_mul rem_mul_congr2)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Powers of `p − 1` -/

theorem sq_alg {p q1 m : PTm n} (x1 : Γ ⊢[PRAAx] p ≐ succ q1) (x2 : Γ ⊢[PRAAx] p ≐ two + m) :
    Γ ⊢[PRAAx] q1 * q1 ≐ p * m + one := by
  ipra_lc (1 - 𝔞 p - 𝔞 q1) * natEq x1 + 𝔞 p * natEq x2

/-- `(p − 1)² ≡ 1 (mod p)` for `p ≥ 2`. -/
theorem neg_sq {p : PTm n} (hq : Γ ⊢[PRAAx] le two p) : Γ ⊢[PRAAx] rem (pred p * pred p) p ≐ rem one p := by
  have hp1 := p_pos hq
  exact (congrAp2 remF (sq_alg hp1 (eq_add_of_le hq)) (.eqRefl _)).eqTrans (rem_add_mul hp1 _ _)

alias pw_two := Common.pw_two

/-- `x^{2m} = (x²)^m`. -/
theorem pw_two_mul (x m : PTm n) : Γ ⊢[PRAAx] pw x (two * m) ≐ pw (x * x) m :=
  (pw_mul x two m).eqSymm.eqTrans (congrPw (pw_two x) (.eqRefl _))

/-- `(p − 1)^{2m} ≡ 1 (mod p)`. -/
theorem neg_pow_even {p : PTm n} (hq : Γ ⊢[PRAAx] le two p) (m : PTm n) :
    Γ ⊢[PRAAx] rem (pw (pred p) (two * m)) p ≐ rem one p := by
  have hp1 := p_pos hq
  exact (congrAp2 remF (pw_two_mul _ _) (.eqRefl _)).eqTrans
    ((pw_rem_congr hp1 (neg_sq hq) m).eqTrans (congrAp2 remF (pw_one_base m) (.eqRefl _)))

theorem one_mul_alg (t : PTm n) : Γ ⊢[PRAAx] one * t ≐ t := one_mul t

/-- `(p − 1)^{2m+1} ≡ p − 1 (mod p)`. -/
theorem neg_pow_odd {p : PTm n} (hq : Γ ⊢[PRAAx] le two p) (m : PTm n) :
    Γ ⊢[PRAAx] rem (pw (pred p) (two * m + one)) p ≐ rem (pred p) p := by
  have hp1 := p_pos hq
  have e : Γ ⊢[PRAAx] pw (pred p) (two * m + one) ≐ pw (pred p) (two * m) * pred p :=
    (pw_add _ _ _).eqTrans (congrMul (.eqRefl _) (pw_one _))
  exact (congrAp2 remF e (.eqRefl _)).eqTrans
    ((rem_mul_congr2 hp1 (neg_pow_even hq m) (.eqRefl (rem (pred p) p))).eqTrans
      (congrAp2 remF (one_mul _) (.eqRefl _)))

/-- `(p − 1)^k (mod p)` by the parity of `k`. -/
theorem neg_pow {p : PTm n} (hq : Γ ⊢[PRAAx] le two p) (k : PTm n) :
    Γ ⊢[PRAAx] ((par k ≐ zero) ⋏ (rem (pw (pred p) k) p ≐ rem one p)) ⋎
      ((par k ≐ one) ⋏ (rem (pw (pred p) k) p ≐ rem (pred p) p)) := by
  refine .orE (par_cases k) ?_ ?_
  · have h0 : ((par k ≐ zero) :: Γ) ⊢[PRAAx] par k ≐ zero := Prf.hyp0
    exact .orI₁ (.andI h0 ((congrAp2 remF (congrPw (.eqRefl _) (even_of h0)) (.eqRefl _)).eqTrans
      (neg_pow_even hq.wk _)))
  · have h1 : ((par k ≐ one) :: Γ) ⊢[PRAAx] par k ≐ one := Prf.hyp0
    exact .orI₂ (.andI h1 ((congrAp2 remF (congrPw (.eqRefl _) (odd_of h1)) (.eqRefl _)).eqTrans
      (neg_pow_odd hq.wk _)))

/-! ## The square roots of `1` -/

theorem diff_sq {x u : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ u) : Γ ⊢[PRAAx] x * x ≐ u * succ x + one := by
  ipra_lc (𝔞 x + 1) * natEq hx

theorem cancel_one {m p Q : PTm n} (h : Γ ⊢[PRAAx] m + one ≐ p * Q + one) : Γ ⊢[PRAAx] m ≐ p * Q := by
  ipra_lc natEq h

/-- For a prime `p` and `1 ≤ x < p`: `x² ≡ 1 (mod p)` gives `x = 1` or `x = p − 1`. -/
theorem sq_one {p x : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hx1 : Γ ⊢[PRAAx] x ≐ succ (pred x))
    (hxp : Γ ⊢[PRAAx] lt x p) (h : Γ ⊢[PRAAx] rem (x * x) p ≐ rem one p) :
    Γ ⊢[PRAAx] (x ≐ one) ⋎ (x ≐ pred p) := by
  have hq := prime_two hp
  have hp1 := p_pos hq
  have r1 : Γ ⊢[PRAAx] rem (pred x * succ x + one) p ≐ one :=
    (congrAp2 remF (diff_sq hx1).eqSymm (.eqRefl _)).eqTrans (h.eqTrans (rem_small hq))
  have d0 := div_eq (Γ := Γ) (j := pred x * succ x + one) hp1
  have dv : Γ ⊢[PRAAx] dvd p (pred x * succ x) :=
    dvd_of_eq' hp1 (cancel_one (d0.eqTrans (congrAdd (.eqRefl _) r1)))
  have hpx : Γ ⊢[PRAAx] lt (pred x) p := le_congr hx1 (.eqRefl _) (le_of_lt hxp)
  refine .orE (eq_or_ne (rem (pred x) p) zero) ?_ ?_
  · have z : ((rem (pred x) p ≐ zero) :: Γ) ⊢[PRAAx] pred x ≐ zero :=
      (rem_small hpx.wk).eqSymm.eqTrans Prf.hyp0
    exact .orI₁ (hx1.wk.eqTrans (congrSucc z))
  · have g : (neg (rem (pred x) p ≐ zero) :: Γ) ⊢[PRAAx] gcd p (pred x) ≐ one := gcd_prime hp.wk Prf.hyp0
    have d2 := gauss hp1.wk g dv.wk
    have l := dvd_le' hp1.wk d2 (congrSucc (pred_succ _).eqSymm)
    have e : (neg (rem (pred x) p ≐ zero) :: Γ) ⊢[PRAAx] succ x ≐ p := le_antisymm hxp.wk l
    exact .orI₂ ((pred_succ x).eqSymm.eqTrans (congrPred e))

/-! ## Squares -/

theorem half_alg {p h : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * h + one) : Γ ⊢[PRAAx] monus p one ≐ two * h :=
  (congrMonus (ep.eqTrans (add_comm _ _)) (.eqRefl _)).eqTrans (add_monus' _ _)

/-- `(x²)^h ≡ 1 (mod p)` for an odd prime `p = 2h + 1` and `gcd(x, p) = 1`. -/
theorem residue_pow {p x : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (hu : Γ ⊢[PRAAx] gcd x p ≐ one) : Γ ⊢[PRAAx] rem (pw (x * x) (half p)) p ≐ rem one p := by
  have hp1 := p_pos (prime_two hp)
  have ep := odd_of hodd
  have e1 : Γ ⊢[PRAAx] phi p ≐ two * half p := (phi_prime hp).eqTrans (half_alg ep)
  have e2 : Γ ⊢[PRAAx] pw (x * x) (half p) ≐ pw x (phi p) :=
    (pw_two_mul x (half p)).eqSymm.eqTrans (congrPw (.eqRefl _) e1.eqSymm)
  exact (congrAp2 remF e2 (.eqRefl _)).eqTrans (euler_at hu hp1)

end LeanProofs.IPRA.DiophantineNumberTheory.ResidueFacts
