import IPRADerivations.AnalyticNumberTheory.SieveCount
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Counting a progression inside the common multiples of `d` and `e`

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, the application of
`eq:crt-count` in the proof of `thm:finite-sieve`: "For `l = [d, e]`, we have `gcd(l, q) = 1`. The simultaneous
conditions `n ≡ a (mod q)` and `l ∣ n` select one residue class modulo `q l`", used for the pairs `(d, e)` of the
expanded square `(Σ_{d ∣ n} λ_d)²`, together with `[d, e] = d e / gcd(d, e)`.

With `lc d e = d · (e / gcd(d, e))` for `d, e ≥ 1`:

* `gl_eq`: `gcd(d, e) · lc(d, e) = d e`; `lc_pos`; `d_dvd_lc`, `e_dvd_lc`;
* `dvd_pair`: `[d ∣ x] [e ∣ x] = [lc(d, e) ∣ x]` (indicators); the forward direction is
  `ChineseRemainder.crt_unique_at` against `0`;
* `lc_cop`: `gcd(lc(d, e), q) = 1` when `gcd(d, q) = gcd(e, q) = 1`, for `q ≥ 1`;
* `pair_pt`: the summand `[t ≡ a (mod q)] [d ∣ t] [e ∣ t]` is the summand of `SieveCount.cnt` at `l = lc(d, e)`;
* `pair_le`, `pair_ge`: with `K(X) = SieveCount.cnt X q (lc d e) a`,
  `q d e · K(X) ≤ gcd(d, e) · X + q d e` and `gcd(d, e) · X ≤ q d e · K(X) + q d e`, the two counting bounds
  multiplied by `gcd(d, e)`. Divided by `q d e` they read `|K(X) − X / (q [d, e])| ≤ 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SievePairCount

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.BrunCounting (gB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveCount (fB cnt cnt_pt count_le count_ge pos_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.CoprimeModulus (cop_mul cop_of_mul pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos crt_unique_at)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' dvd_of_eq' gcd_dvd' dvd_trans' pos_of_eq_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `lcm(d, e)` in the form `d · (e / gcd(d, e))`. -/
abbrev lc (d e : PTm n) : PTm n := d * quo e (gcd d e)

/-! ## The least common multiple -/

/-- `e = gcd(d, e) · (e / gcd(d, e))`. -/
theorem e_split {d e : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] e ≐ gcd d e * quo e (gcd d e) :=
  eq_of_dvd' (gcd_pos (B := e) hd) (Prf.andE₂ (gcd_dvd' (b := e) hd))

/-- `d = gcd(d, e) · (d / gcd(d, e))`. -/
theorem d_split {d e : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] d ≐ gcd d e * quo d (gcd d e) :=
  eq_of_dvd' (gcd_pos (B := e) hd) (Prf.andE₁ (gcd_dvd' (b := e) hd))

/-- `gcd(d, e) · lc(d, e) = d e`. -/
theorem gl_eq {d e : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) : Γ ⊢[PRAAx] gcd d e * lc d e ≐ d * e := by
  ipra_lc -𝔞 d * natEq (e_split (e := e) hd)

theorem lc_pos {d e : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) :
    Γ ⊢[PRAAx] lc d e ≐ succ (pred (lc d e)) :=
  pos_mul hd (pos_of_eq_mul he (e_split hd))

theorem d_dvd_lc {d e : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) : Γ ⊢[PRAAx] dvd d (lc d e) :=
  dvd_of_eq' hd (w := quo e (gcd d e)) (.eqRefl _)

theorem e_dvd_lc {d e : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) :
    Γ ⊢[PRAAx] dvd e (lc d e) := by
  refine dvd_of_eq' he (w := quo d (gcd d e)) ?_
  ipra_lc 𝔞 (quo e (gcd d e)) * natEq (d_split (e := e) hd) - 𝔞 (quo d (gcd d e)) * natEq (e_split (e := e) hd)

/-- `[d ∣ x] [e ∣ x] = [lc(d, e) ∣ x]`. -/
theorem dvd_pair {d e : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e))
    (x : PTm n) :
    Γ ⊢[PRAAx] eqb (rem x d) zero * eqb (rem x e) zero ≐ eqb (rem x (lc d e)) zero := by
  refine .orE (eq_or_ne (rem x d) zero) ?_ ?_
  · refine .orE (eq_or_ne (rem x e) zero) ?_ ?_
    · let C : List (Fm PTm n) := (rem x e ≐ zero) :: (rem x d ≐ zero) :: Γ
      have xd : C ⊢[PRAAx] rem x d ≐ zero := Prf.hyp1
      have xe : C ⊢[PRAAx] rem x e ≐ zero := Prf.hyp0
      have u : C ⊢[PRAAx] rem x (lc d e) ≐ zero :=
        (crt_unique_at hd.wk.wk he.wk.wk (xd.eqTrans (rem_zero d).eqSymm) (xe.eqTrans (rem_zero e).eqSymm)).eqTrans
          (rem_zero _)
      exact ((congrMul (eqb_of_eq xd) (eqb_of_eq xe)).eqTrans (one_mul one)).eqTrans (eqb_of_eq u).eqSymm
    · let C : List (Fm PTm n) := neg (rem x e ≐ zero) :: (rem x d ≐ zero) :: Γ
      have hne : C ⊢[PRAAx] neg (rem x e ≐ zero) := Prf.hyp0
      have hn : C ⊢[PRAAx] neg (rem x (lc d e) ≐ zero) := by
        refine .impI (Prf.impE hne.wk ?_)
        exact dvd_trans' he.wk.wk.wk (lc_pos hd he).wk.wk.wk (e_dvd_lc hd he).wk.wk.wk Prf.hyp0
      exact ((congrMul (.eqRefl _) (eqb_of_ne hne)).eqTrans (mul_zero _)).eqTrans (eqb_of_ne hn).eqSymm
  · let C : List (Fm PTm n) := neg (rem x d ≐ zero) :: Γ
    have hne : C ⊢[PRAAx] neg (rem x d ≐ zero) := Prf.hyp0
    have hn : C ⊢[PRAAx] neg (rem x (lc d e) ≐ zero) := by
      refine .impI (Prf.impE hne.wk ?_)
      exact dvd_trans' hd.wk.wk (lc_pos hd he).wk.wk (d_dvd_lc (e := e) hd).wk.wk Prf.hyp0
    exact ((congrMul (eqb_of_ne hne) (.eqRefl _)).eqTrans (zero_mul _)).eqTrans (eqb_of_ne hn).eqSymm

/-- `gcd(lc(d, e), q) = 1` when `d` and `e` are units modulo `q ≥ 1`. -/
theorem lc_cop {d e q : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hq : Γ ⊢[PRAAx] le one q)
    (hdq : Γ ⊢[PRAAx] gcd d q ≐ one) (heq : Γ ⊢[PRAAx] gcd e q ≐ one) :
    Γ ⊢[PRAAx] gcd (lc d e) q ≐ one := by
  have h := cop_mul (pos_of_one_le hq) hdq heq
  have h' : Γ ⊢[PRAAx] gcd (gcd d e * lc d e) q ≐ one := (congrGcd (gl_eq (e := e) hd) (.eqRefl _)).eqTrans h
  exact cop_of_mul (pos_of_one_le hq) h'

/-! ## The pair count -/

/-- The summand `[t ≡ a (mod q)] [d ∣ t] [e ∣ t]` is the summand of `cnt` at `l = lc(d, e)`. -/
theorem pair_pt {d e q a : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e))
    (hq : Γ ⊢[PRAAx] le one q) (t : PTm n) :
    Γ ⊢[PRAAx] eqb (rem t q) (rem a q) * (eqb (rem t d) zero * eqb (rem t e) zero) ≐
      inst2 (gB fB) t (pairT (succ (pred (q * lc d e))) (SieveCount.par q (lc d e) a)) :=
  (congrMul (.eqRefl _) (dvd_pair hd he t)).eqTrans (cnt_pt (a := a) hq (lc_pos hd he) t).eqSymm

/-- `g (q L C) = q D C` and `g (X + q L) = g X + q D` for `g L = D`. -/
theorem scale_l {g L D q C : PTm n} (h : Γ ⊢[PRAAx] g * L ≐ D) : Γ ⊢[PRAAx] g * (q * L * C) ≐ q * D * C := by
  ipra_lc 𝔞 q * 𝔞 C * natEq h

theorem scale_r {g L D q X : PTm n} (h : Γ ⊢[PRAAx] g * L ≐ D) : Γ ⊢[PRAAx] g * (X + q * L) ≐ g * X + q * D := by
  ipra_lc 𝔞 q * natEq h

theorem scale_r' {g L D q C : PTm n} (h : Γ ⊢[PRAAx] g * L ≐ D) :
    Γ ⊢[PRAAx] g * (q * L * C + q * L) ≐ q * D * C + q * D := by
  ipra_lc (𝔞 q * 𝔞 C + 𝔞 q) * natEq h

/-- `q d e · K(X) ≤ gcd(d, e) · X + q d e`. -/
theorem pair_le {d e q a : PTm n} (X : PTm n) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (hq : Γ ⊢[PRAAx] le one q) (hdq : Γ ⊢[PRAAx] gcd d q ≐ one)
    (heq : Γ ⊢[PRAAx] gcd e q ≐ one) (ha : Γ ⊢[PRAAx] gcd a q ≐ one) :
    Γ ⊢[PRAAx] le (q * (d * e) * cnt X q (lc d e) a) (gcd d e * X + q * (d * e)) := by
  have c := count_le (a := a) X hq (lc_pos hd he) (lc_cop hd hq hdq heq) ha
  have m := le_mul_mono (le_refl (gcd d e)) c
  exact le_congr (scale_l (gl_eq hd)) (scale_r (gl_eq hd)) m

/-- `gcd(d, e) · X ≤ q d e · K(X) + q d e`. -/
theorem pair_ge {d e q a : PTm n} (X : PTm n) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (hq : Γ ⊢[PRAAx] le one q) (hdq : Γ ⊢[PRAAx] gcd d q ≐ one)
    (heq : Γ ⊢[PRAAx] gcd e q ≐ one) (ha : Γ ⊢[PRAAx] gcd a q ≐ one) :
    Γ ⊢[PRAAx] le (gcd d e * X) (q * (d * e) * cnt X q (lc d e) a + q * (d * e)) := by
  have c := count_ge (a := a) X hq (lc_pos hd he) (lc_cop hd hq hdq heq) ha
  have m := le_mul_mono (le_refl (gcd d e)) c
  exact le_congr (.eqRefl _) (scale_r' (gl_eq hd)) m

end LeanProofs.IPRA.AnalyticNumberTheory.SievePairCount
