import IPRADerivations.AnalyticNumberTheory.LcmBridgeLoss
import IPRADerivations.AnalyticNumberTheory.SigmaProduct

/-!
# The exact finite identity of the lcm bridge, pointwise

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex`, Lemma "Exact finite identity":
`A(L_P) = ∏_{p≤P} (1 − p^{−a_p(P)−1})/(1 − p^{−1})`. Over the prime-indexed products of `EulerProduct.PP` (range
`q ≤ L`, exponent `e(q) = [q prime][q ∣ L]`), with `L = lcm(1, …, P)`:

* `prod_mul`: `∏ (f g) = ∏ f · ∏ g` for arbitrary bodies;
* `e_low`, `e_high`: a prime `q` divides `L` iff `q ≤ P` (`eqb(L mod q, 0) = [q ≤ P]`);
* `exact`: `q^{v_q(L)+1} ⌊L²/q^{v_q(L)+1}⌋ = L²` for a prime `q ≤ P` (since `v_q(L) ≥ 1`);
* `factor_id`: with `u'_q = e(q) ⌊L²/q^{v_q(L)+1}⌋`, `(L² − u'_q) (q^{v_q(L)+1})^{e(q)} = L² (q^{v_q(L)+1} − 1)^{e(q)}` for
  every `q` — the Weierstrass factor `1 − q^{−a_q−1}` against the factor `G` of `SigmaProduct.sigma_product`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeExact

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP pw_pos' cof_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (lcmu lcmu_pos lcm_valuation pdvd_of_val_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeLoss (LD)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg)
open LeanProofs.IPRA.Signum (sg sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `q^{v_q(L)+1}`, as in `LcmBridgeLoss.ex` (a local name: `LeanProofs.IPRA.ex` is the existential). -/
abbrev ex (i P : PTm n) : PTm n := pw i (succ (val i (lcmu P)))

/-! ## Products of products -/

theorem prod_mul (f g : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF (f * g)) N x ≐ ap2 (prodF f) N x * ap2 (prodF g) N x :=
  prod_mul_body f g N x

/-! ## Which primes divide `L` -/

/-- `e(q) = [q prime][q ∣ L]`. -/
abbrev eL (i P : PTm n) : PTm n := isP i * eqb (rem (lcmu P) i) zero

/-- A prime `q ≤ P` has `v_q(L) ≥ 1`. -/
theorem val_pos_low {i P : PTm n} (hi : Γ ⊢[PRAAx] prime i) (hiP : Γ ⊢[PRAAx] le i P) :
    Γ ⊢[PRAAx] val i (lcmu P) ≐ succ (pred (val i (lcmu P))) := by
  have I2 := Prf.andE₂ (lcm_valuation hi P)
  refine .orE (zero_or_succ (val i (lcmu P))) ?_ Prf.hyp0
  have e1 : ((val i (lcmu P) ≐ zero) :: Γ) ⊢[PRAAx] ex i P ≐ i :=
    (congrAp2 powF (congrSucc Prf.hyp0) (.eqRefl i)).eqTrans
      ((pw_succ i zero).eqTrans ((congrMul (pw_zero i) (.eqRefl _)).eqTrans (one_mul i)))
  exact le_lt_absurd _ hiP.wk (le_congr (.eqRefl _) e1 I2.wk)

theorem e_low {i P : PTm n} (hi : Γ ⊢[PRAAx] prime i) (hiP : Γ ⊢[PRAAx] le i P) :
    Γ ⊢[PRAAx] eqb (rem (lcmu P) i) zero ≐ one :=
  eqb_of_eq (pdvd_of_val_pos (prime_two hi) (lcmu_pos P) (val_pos_low hi hiP))

theorem e_high {i P : PTm n} (hi : Γ ⊢[PRAAx] prime i) (hPi : Γ ⊢[PRAAx] lt P i) :
    Γ ⊢[PRAAx] eqb (rem (lcmu P) i) zero ≐ zero := by
  refine eqb_of_ne (.impI ?_)
  let C : List (Fm PTm n) := (rem (lcmu P) i ≐ zero) :: Γ
  have hp2 : C ⊢[PRAAx] le two i := (prime_two hi).wk
  have hd : C ⊢[PRAAx] dvd (pw i one) (lcmu P) := dvd_congr_left (pw_one i).eqSymm Prf.hyp0
  have l1 := (WeightedMangoldt.dvd_iff_le_val hp2 (lcmu_pos P)).1 hd
  have vp := BinomialThree.pos_of_one_le l1
  have I1 := Prf.andE₁ (lcm_valuation (Γ := C) hi.wk P)
  have s1 : C ⊢[PRAAx] sg (val i (lcmu P)) ≐ one := (congrSg vp).eqTrans (sg_succ _)
  have a : C ⊢[PRAAx] le (pw i (val i (lcmu P))) P :=
    le_congr ((congrMul s1 (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) I1
  have b : C ⊢[PRAAx] le i (pw i (val i (lcmu P))) :=
    le_base_pw l1
  exact le_lt_absurd _ (le_trans b a) hPi.wk

/-! ## Exactness -/

/-- `q^{v+1} ⌊L²/q^{v+1}⌋ = L²` for a prime `q ≤ P`. -/
theorem exact {i P : PTm n} (hi : Γ ⊢[PRAAx] prime i) (hiP : Γ ⊢[PRAAx] le i P) :
    Γ ⊢[PRAAx] ex i P * quo (LD P) (ex i P) ≐ LD P := by
  have hp2 := prime_two hi
  have vp := val_pos_low hi hiP
  have expos := pw_pos' (p_pos hp2) (succ (val i (lcmu P)))
  -- `L² = q^{v+1} · (q^{v−1} c²)`
  have hL : Γ ⊢[PRAAx] LD P ≐ ex i P * (pw i (pred (val i (lcmu P))) *
      (quo (lcmu P) (pw i (val i (lcmu P))) * quo (lcmu P) (pw i (val i (lcmu P))))) + zero := by
    ipra_lc (𝔞 (lcmu P) + 𝔞 (pw i (val i (lcmu P))) * 𝔞 (quo (lcmu P) (pw i (val i (lcmu P))))) * natEq (cof_eq (m := lcmu P) hp2) +
      (𝔞 (quo (lcmu P) (pw i (val i (lcmu P)))) * 𝔞 (quo (lcmu P) (pw i (val i (lcmu P)))) * 𝔞 (pw i (val i (lcmu P)))) * natEq ((congrAp2 (Γ := Γ) powF vp (.eqRefl i)).eqTrans (pw_succ i (pred (val i (lcmu P))))) -
      (𝔞 (quo (lcmu P) (pw i (val i (lcmu P)))) * 𝔞 (quo (lcmu P) (pw i (val i (lcmu P)))) * 𝔞 (pw i (pred (val i (lcmu P))))) * natEq (pw_succ i (val i (lcmu P)))
  have q := Totient.quo_eq expos hL (LcmUpto.lt_zero_of_pos expos)
  exact (congrMul (.eqRefl _) q).eqTrans ((hL.eqTrans (add_zero _)).eqSymm)

/-! ## The Weierstrass factor against `G` -/

/-- `(L² − u'_q)(q^{v+1})^{e} = L² (q^{v+1} − 1)^{e}` with `e = e(q)`, `u'_q = e ⌊L²/q^{v+1}⌋`, for every `q`. -/
theorem factor_id (i P : PTm n) :
    Γ ⊢[PRAAx] monus (LD P) (eL i P * quo (LD P) (ex i P)) * pw (ex i P) (eL i P) ≐
      LD P * pw (monus (ex i P) one) (eL i P) := by
  -- the case `e = 0`
  have z : ∀ {Δ : List (Fm PTm n)}, (Δ ⊢[PRAAx] eL i P ≐ zero) →
      (Δ ⊢[PRAAx] monus (LD P) (eL i P * quo (LD P) (ex i P)) * pw (ex i P) (eL i P) ≐
        LD P * pw (monus (ex i P) one) (eL i P)) := by
    intro Δ he
    have a : Δ ⊢[PRAAx] monus (LD P) (eL i P * quo (LD P) (ex i P)) ≐ LD P :=
      (congrMonus (.eqRefl _) ((congrMul he (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (monus_zero _)
    have b : Δ ⊢[PRAAx] pw (ex i P) (eL i P) ≐ one := (congrAp2 powF he (.eqRefl _)).eqTrans (pw_zero _)
    have c : Δ ⊢[PRAAx] pw (monus (ex i P) one) (eL i P) ≐ one := (congrAp2 powF he (.eqRefl _)).eqTrans (pw_zero _)
    exact (congrMul a b).eqTrans (congrMul (.eqRefl _) c).eqSymm
  refine .orE (isP_01 i) (z ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))) ?_
  let C : List (Fm PTm n) := (isP i ≐ one) :: Γ
  have hi : C ⊢[PRAAx] prime i := prime_of_isP Prf.hyp0
  refine .orE (lt_or_le P i) (z ((congrMul Prf.hyp1 (e_high hi.wk Prf.hyp0)).eqTrans (mul_zero _))) ?_
  -- the case `e = 1`: `q ≤ P`
  let C2 : List (Fm PTm n) := le i P :: C
  have hiP : C2 ⊢[PRAAx] le i P := Prf.hyp0
  have he : C2 ⊢[PRAAx] eL i P ≐ one :=
    (congrMul Prf.hyp1 (e_low hi.wk hiP)).eqTrans (one_mul _)
  have hu : C2 ⊢[PRAAx] eL i P * quo (LD P) (ex i P) ≐ quo (LD P) (ex i P) :=
    (congrMul he (.eqRefl _)).eqTrans (one_mul _)
  have p1 : C2 ⊢[PRAAx] pw (ex i P) (eL i P) ≐ ex i P := (congrAp2 powF he (.eqRefl _)).eqTrans (pw_one _)
  have p2 : C2 ⊢[PRAAx] pw (monus (ex i P) one) (eL i P) ≐ monus (ex i P) one :=
    (congrAp2 powF he (.eqRefl _)).eqTrans (pw_one _)
  refine (congrMul (congrMonus (.eqRefl _) hu) p1).eqTrans (.eqTrans ?_ (congrMul (.eqRefl _) p2).eqSymm)
  have hi2 : C2 ⊢[PRAAx] prime i := hi.wk
  have hx := exact hi2 hiP
  have expos := pw_pos' (p_pos (prime_two hi2)) (succ (val i (lcmu P)))
  have qle : C2 ⊢[PRAAx] le (quo (LD P) (ex i P)) (LD P) :=
    le_congr (one_mul _) hx (le_mul_mono (FactorVector.one_le_pos expos) (le_refl (quo (LD P) (ex i P))))
  ipra_lc (-(𝔞 (ex i P))) * natEq (eq_add_of_le qle) +
    (𝔞 (lcmu P) * 𝔞 (lcmu P)) * natEq (eq_add_of_le (FactorVector.one_le_pos expos)) - natEq hx

end LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeExact

export_ipra AnalyticNumberTheory.LcmBridgeExact (prod_mul)
