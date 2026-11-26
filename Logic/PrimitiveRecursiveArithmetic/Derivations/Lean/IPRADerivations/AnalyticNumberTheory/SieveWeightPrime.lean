import IPRADerivations.AnalyticNumberTheory.SieveWeightValues
import IPRADerivations.AnalyticNumberTheory.MobiusBounds
import IPRADerivations.AnalyticNumberTheory.Radical
import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.AnalyticNumberTheory.DivisorSplit
import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.Header

/-!
# The vector of the explicit sieve weights at `k p` for a prime `p`

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:weight-formula`:
"Since the indices in `eq:explicit-sieve-weights` are squarefree, writing `r = ds` yields
`λ_d = μ(d) d / (φ(d) G) · G_{dq}(z/d)`".

The paper uses `φ(ds) = φ(d) φ(s)` and `μ(ds) = μ(d) μ(s)` for squarefree `ds`. Here the same information is
derived one prime at a time, for the parts `Y^±_r = [gcd(r, q) = 1] [r ≥ 1] μ^±(r) z!/φ(r)` of the cleared vector
(`SieveWeightValues`), a prime `p` and `k ≥ 1`:

* `Y_kill`: `Y^±_{kp} = 0` when `p ∣ k` (`kp` is not squarefree; `Mobius.kill`);
* `Y_step`: `(p − 1) Y⁺_{kp} ≤ Y⁻_k` and `(p − 1) Y⁻_{kp} ≤ Y⁺_k` when `p ∤ k`, `kp ≤ z` and `q ≥ 1`
  (`Mobius.swap` with `MobiusBounds.mu_bound`, `φ(kp) = φ(k)(p − 1)` by `Multiplicative.phi_mul_at` and
  `Radical.phi_prime`, and the exact divisions `z! = φ(r) · (z!/φ(r))`);
* `abs_step`: `(p − 1) (Y⁺_{kp} + Y⁻_{kp}) ≤ Y⁺_k + Y⁻_k`, i.e. `(p − 1) |Y_{kp}| ≤ |Y_k|`.

With equality in place of `≤` these say `|Y_{kp}| = |Y_k| / (p − 1)` when `kp` is coprime to `q`; only the
inequality is needed for the weight bound.

* `val_pos`, `val_zero'`: `v_p(a) ≥ 1` when `p ∣ a`, and `v_p(a) = 0` when `p ∤ a`, for `a ≥ 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightPrime

open_ipra
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_unique p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN prime_two swap kill congrSg zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (mu_bound)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (sg_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.Radical (phi_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (phi_mul_at)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSplit (mul_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.CoprimeModulus (cop_of_mul pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightFacts (phi_quo)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightValues (YP YN YP_at YN_at)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_comm_one)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Valuation and divisibility -/

/-- `v_p(a) ≥ 1` when `p ∣ a`, for `p ≥ 2` and `a ≥ 1`. -/
theorem val_pos {p a : PTm n} (hp2 : Γ ⊢[PRAAx] le two p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hd : Γ ⊢[PRAAx] rem a p ≐ zero) : Γ ⊢[PRAAx] le one (val p a) := by
  refine .orE (lt_or_le zero (val p a)) Prf.hyp0 ?_
  have v0 : (le (val p a) zero :: Γ) ⊢[PRAAx] val p a ≐ zero := le_antisymm Prf.hyp0 (zero_le _)
  have nd : (le (val p a) zero :: Γ) ⊢[PRAAx] neg (dvd (pw p (succ (val p a))) a) :=
    Valuation.val_not_dvd hp2.wk ha.wk
  have e : (le (val p a) zero :: Γ) ⊢[PRAAx] pw p (succ (val p a)) ≐ p :=
    (congrPw (.eqRefl _) (congrSucc v0)).eqTrans (pw_one _)
  exact .botE _ (Prf.impE nd ((congrAp2 remF (.eqRefl _) e).eqTrans hd.wk))

/-- `v_p(a) = 0` when `p ∤ a`, for `p ≥ 2` and `a ≥ 1`. -/
theorem val_zero' {p a : PTm n} (hp2 : Γ ⊢[PRAAx] le two p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hna : Γ ⊢[PRAAx] neg (dvd p a)) : Γ ⊢[PRAAx] val p a ≐ zero :=
  val_unique hp2 ha (c := a) ((one_mul _).eqSymm.eqTrans (congrMul (pw_zero _).eqSymm (.eqRefl a))) hna

/-! ## Order facts for `k p` -/

/-- `p ≤ k p` for `k ≥ 1`. -/
theorem p_le_mul {k : PTm n} (p : PTm n) (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) : Γ ⊢[PRAAx] le p (k * p) := by
  refine le_of_eq_add (d := pred k * p) ?_
  ipra_lc 𝔞 p * natEq hk

/-- `k ≤ k p` for `p ≥ 1`. -/
theorem k_le_mul {p : PTm n} (k : PTm n) (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) : Γ ⊢[PRAAx] le k (k * p) := by
  refine le_of_eq_add (d := k * pred p) ?_
  ipra_lc 𝔞 k * natEq hp

/-! ## The case `p ∣ k` -/

theorem yz {g s m w : PTm n} (h : Γ ⊢[PRAAx] m ≐ zero) : Γ ⊢[PRAAx] g * ((s * m) * w) ≐ zero := by
  ipra_lc 𝔞 g * 𝔞 s * 𝔞 w * natEq h

/-- `Y^±_{kp} = 0` when `p ∣ k`. -/
theorem Y_kill {p k : PTm n} (P : PTm n) (hp : Γ ⊢[PRAAx] prime p) (hk : Γ ⊢[PRAAx] k ≐ succ (pred k))
    (hd : Γ ⊢[PRAAx] rem k p ≐ zero) :
    Γ ⊢[PRAAx] (inst2 YP (k * p) P ≐ zero) ⋏ (inst2 YN (k * p) P ≐ zero) := by
  have hp2 := prime_two hp
  have hpN : Γ ⊢[PRAAx] lt p (succ (k * p)) := (succ_monus_succ _ _).eqTrans (p_le_mul p hk)
  have kl := kill (N := succ (k * p)) hp hpN hk (val_pos hp2 hk hd)
  rw [YP_at, YN_at]
  exact .andI (yz (Prf.andE₁ kl)) (yz (Prf.andE₂ kl))

/-! ## The case `p ∤ k` -/

/-- `(p − 1) · (z!/φ(kp)) = z!/φ(k)` from the exact divisions and `φ(kp) = φ(k)(p − 1)`. -/
theorem w_alg {B φk φkp pm wk wkp : PTm n} (b1 : Γ ⊢[PRAAx] B ≐ φkp * wkp) (b2 : Γ ⊢[PRAAx] B ≐ φk * wk)
    (eφ : Γ ⊢[PRAAx] φkp ≐ φk * pm) : Γ ⊢[PRAAx] φk * (pm * wkp) ≐ φk * wk := by
  ipra_lc natEq b2 - natEq b1 - 𝔞 wkp * natEq eφ

theorem mid_alg {pm m w1 w2 : PTm n} (hw : Γ ⊢[PRAAx] pm * w1 ≐ w2) :
    Γ ⊢[PRAAx] pm * (one * ((one * m) * w1)) ≐ one * ((one * m) * w2) := by
  ipra_lc 𝔞 m * natEq hw

/-- The step for one part: `(p − 1) · [gcd(kp, q) = 1] [kp ≥ 1] m₁ z!/φ(kp) ≤ [gcd(k, q) = 1] [k ≥ 1] m₂ z!/φ(k)`
when `m₁ = m₂`. -/
theorem step_gen {p k P m1 m2 : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) (hp : Γ ⊢[PRAAx] prime p)
    (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hna : Γ ⊢[PRAAx] neg (dvd p k))
    (hz : Γ ⊢[PRAAx] le (k * p) (sndT (sndT P))) (hm : Γ ⊢[PRAAx] m1 ≐ m2) :
    Γ ⊢[PRAAx] le
      (monus p one * (eqb (gcd (k * p) (fstT P)) one *
        ((sg (k * p) * m1) * quo (fact (sndT (sndT P))) (phi (k * p)))))
      (eqb (gcd k (fstT P)) one * ((sg k * m2) * quo (fact (sndT (sndT P))) (phi k))) := by
  have hp1 := p_pos (prime_two hp)
  have hkp : Γ ⊢[PRAAx] k * p ≐ succ (pred (k * p)) := Combinatorics.LegendreDigits.pos_mul' hk hp1
  have hg : Γ ⊢[PRAAx] gcd k p ≐ one := gcd_comm_one hk (gcd_prime hp hna)
  have eφ : Γ ⊢[PRAAx] phi (k * p) ≐ phi k * monus p one :=
    (phi_mul_at hk hp1 hg).eqTrans (congrMul (.eqRefl _) (phi_prime hp))
  have b1 := phi_quo hkp hz
  have b2 := phi_quo hk (le_trans (k_le_mul k hp1) hz)
  have hw : Γ ⊢[PRAAx] monus p one * quo (fact (sndT (sndT P))) (phi (k * p)) ≐
      quo (fact (sndT (sndT P))) (phi k) := mul_cancel (Order.phi_pos hk) (w_alg b1 b2 eφ)
  refine .orE (eq_or_ne (gcd (k * p) (fstT P)) one) ?_ ?_
  · let C : List (Fm PTm n) := (gcd (k * p) (fstT P) ≐ one) :: Γ
    have g1 : C ⊢[PRAAx] gcd (k * p) (fstT P) ≐ one := Prf.hyp0
    have g2 : C ⊢[PRAAx] gcd k (fstT P) ≐ one :=
      cop_of_mul (pos_of_one_le hq.wk) ((congrGcd (mul_comm p k) (.eqRefl _)).eqTrans g1)
    have l : C ⊢[PRAAx] monus p one * (eqb (gcd (k * p) (fstT P)) one *
        ((sg (k * p) * m1) * quo (fact (sndT (sndT P))) (phi (k * p)))) ≐
        monus p one * (one * ((one * m2) * quo (fact (sndT (sndT P))) (phi (k * p)))) :=
      congrMul (.eqRefl _) (congrMul (eqb_of_eq g1) (congrMul (congrMul (sg_pos hkp.wk) hm.wk) (.eqRefl _)))
    have r : C ⊢[PRAAx] eqb (gcd k (fstT P)) one * ((sg k * m2) * quo (fact (sndT (sndT P))) (phi k)) ≐
        one * ((one * m2) * quo (fact (sndT (sndT P))) (phi k)) :=
      congrMul (eqb_of_eq g2) (congrMul (congrMul (sg_pos hk.wk) (.eqRefl _)) (.eqRefl _))
    exact le_congr (l.eqTrans ((mid_alg hw.wk).eqTrans r.eqSymm)).eqSymm (.eqRefl _) (le_refl _)
  · have z : (neg (gcd (k * p) (fstT P) ≐ one) :: Γ) ⊢[PRAAx]
        monus p one * (eqb (gcd (k * p) (fstT P)) one *
          ((sg (k * p) * m1) * quo (fact (sndT (sndT P))) (phi (k * p)))) ≐ zero :=
      (congrMul (.eqRefl _) (zero_mul_l (eqb_of_ne Prf.hyp0) _)).eqTrans (mul_zero _)
    exact le_congr z.eqSymm (.eqRefl _) (zero_le _)

/-- `(p − 1) Y⁺_{kp} ≤ Y⁻_k` and `(p − 1) Y⁻_{kp} ≤ Y⁺_k` for a prime `p ∤ k`, `k ≥ 1`, `kp ≤ z`, `q ≥ 1`. -/
theorem Y_step {p k P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) (hp : Γ ⊢[PRAAx] prime p)
    (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hna : Γ ⊢[PRAAx] neg (dvd p k))
    (hz : Γ ⊢[PRAAx] le (k * p) (sndT (sndT P))) :
    Γ ⊢[PRAAx] le (monus p one * inst2 YP (k * p) P) (inst2 YN k P) ⋏
      le (monus p one * inst2 YN (k * p) P) (inst2 YP k P) := by
  have hp2 := prime_two hp
  have hp1 := p_pos hp2
  have hpN : Γ ⊢[PRAAx] lt p (succ (k * p)) := (succ_monus_succ _ _).eqTrans (p_le_mul p hk)
  have sw := swap (N := succ (k * p)) hp hpN hk (val_zero' hp2 hk hna)
  have mb := mu_bound (N := succ (k * p)) hk ((succ_monus_succ _ _).eqTrans (k_le_mul k hp1))
  rw [YP_at, YN_at, YP_at, YN_at]
  exact .andI (step_gen hq hp hk hna hz ((Prf.andE₁ sw).eqTrans (Prf.andE₂ mb)))
    (step_gen hq hp hk hna hz ((Prf.andE₂ sw).eqTrans (Prf.andE₁ mb)))

theorem add_step {pm a b c d : PTm n} (h1 : Γ ⊢[PRAAx] le (pm * a) d) (h2 : Γ ⊢[PRAAx] le (pm * b) c) :
    Γ ⊢[PRAAx] le (pm * (a + b)) (c + d) := by
  ipra_le sl h1 + sl h2

/-- `(p − 1) (Y⁺_{kp} + Y⁻_{kp}) ≤ Y⁺_k + Y⁻_k`. -/
theorem abs_step {p k P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) (hp : Γ ⊢[PRAAx] prime p)
    (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hna : Γ ⊢[PRAAx] neg (dvd p k))
    (hz : Γ ⊢[PRAAx] le (k * p) (sndT (sndT P))) :
    Γ ⊢[PRAAx] le (monus p one * (inst2 YP (k * p) P + inst2 YN (k * p) P)) (inst2 YP k P + inst2 YN k P) := by
  have s := Y_step hq hp hk hna hz
  exact add_step (Prf.andE₁ s) (Prf.andE₂ s)

end LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightPrime
