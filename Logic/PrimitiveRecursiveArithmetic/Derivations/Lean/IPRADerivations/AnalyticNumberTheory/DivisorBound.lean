import IPRADerivations.AnalyticNumberTheory.DivisorHarmonic
import IPRADerivations.AnalyticNumberTheory.HarmonicMertens
import IPRADerivations.DiophantineNumberTheory.HurwitzLoop
import IPRADerivations.Core.LinearCombination

/-!
# The divisor bound for the harmonic logarithm (`pnt_ipra_constructive_2026-11-14`, `sb:divisor-bound`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, Lemma `sb:divisor-approx`,
inequality `sb:divisor-bound`: `|D(y) − y log y − (2c − 1)y| ≤ 12√y` for `1 ≤ y ≤ x`, where
`c = H_M − log M` is a finite parameter fixed by the outer endpoint (`sb:finite-c`). With the packet's
rational logarithm `λ_K(a) = H_{Ka} − H_K` (`sec:log`), the outer endpoint `X`, the finite parameter
`c = H_X − λ_K(X)`, `m = ⌊√y⌋` and a common denominator `F = L!`, all in `F`-units (`H_j = S(j, F)/F`):

* `eta_bounds`: `0 ≤ η_m ≤ 1/m` for `η_m = (H_m − λ_K(m)) − (H_X − λ_K(X))` (`sb:harmonic-finite`,
  "`0 ≤ h_m − h_M ≤ 1/m − 1/M`"), from both conjuncts of `LogRefinement.log_refine` at mesh `1`;
* `lam_upper`: `a (λ_K(a + d) − λ_K(a)) ≤ d` (`log(1 + d/a) ≤ d/a`), from `LogElementary.log_upper`;
* `divisor_upper`: `D(y) − yλ_K(y) − (2c − 1)y ≤ 8m`;
* `divisor_lower`: `D(y) − yλ_K(y) − (2c − 1)y ≥ −11m` for `y ≤ K`;

so `|D(y) − yλ_K(y) − (2c − 1)y| ≤ 11m ≤ 11√y`. The inputs are `DivisorHarmonic.divisor_harmonic`
(`D(y) = 2yH_m − m² + e`), `superadd`/`subadd` at `(m, m)`, and `m⌊F/m⌋ ≤ F`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (log_refine)
open LeanProofs.IPRA.AnalyticNumberTheory.LogElementary (log_upper)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono superadd)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (subadd le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (divisor_harmonic)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (pos_of_lt_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.HurwitzLoop (quo_mul_le)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `0 ≤ η_m ≤ 1/m`: `S(X) + S(Km) ≤ S(KX) + S(m)` and `S(KX) + S(m) ≤ S(Km) + S(X) + ⌊F/m⌋`. -/
theorem eta_bounds {m X K L : PTm n} (hm : Γ ⊢[PRAAx] le one m) (hmX : Γ ⊢[PRAAx] le m X)
    (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * X) L) :
    Γ ⊢[PRAAx] le (S X (fact L) + S (K * m) (fact L)) (S (K * X) (fact L) + S m (fact L)) ⋏
      le (S (K * X) (fact L) + S m (fact L)) (S (K * m) (fact L) + S X (fact L) + quo (fact L) m) := by
  have hmp := pos_of_lt_zero hm
  have q1 : Γ ⊢[PRAAx] K * (succ (pred m) + monus X m) ≐ K * X := by
    ipra_lc -(𝔞 K) * natEq hmp - 𝔞 K * natEq (eq_add_of_le hmX)
  have r := log_refine (c₁ := pred m) (T := monus X m) (pos_of_lt_zero hK) (le_congr q1.eqSymm (.eqRefl _) hL)
  have qa : Γ ⊢[PRAAx] succ (pred m) + monus X m ≐ X := by
    ipra_lc -natEq hmp - natEq (eq_add_of_le hmX)
  have qb : Γ ⊢[PRAAx] K * succ (pred m) ≐ K * m := by
    ipra_lc -(𝔞 K) * natEq hmp
  have qc : Γ ⊢[PRAAx] X ≐ succ (pred m + monus X m) := by
    ipra_lc natEq (eq_add_of_le hmX) + natEq hmp
  have e1 := natEq (congrAp2 (Γ := Γ) (sumF hB) qa (.eqRefl (fact L)))
  have e2 := natEq (congrAp2 (Γ := Γ) (sumF hB) qb (.eqRefl (fact L)))
  have e3 := natEq (congrAp2 (Γ := Γ) (sumF hB) q1 (.eqRefl (fact L)))
  have e4 := natEq (congrAp2 (Γ := Γ) (sumF hB) hmp.eqSymm (.eqRefl (fact L)))
  have sM : Γ ⊢[PRAAx] S m (fact L) ≐ S (pred m) (fact L) + quo (fact L) (succ (pred m)) := by
    refine (congrAp2 (sumF hB) hmp (.eqRefl _)).eqTrans ?_
    have s := sum_succ' (Γ := Γ) hB (pred m) (fact L)
    rw [inst2_h] at s
    exact s
  have sX : Γ ⊢[PRAAx] S X (fact L) ≐ S (pred m + monus X m) (fact L) + quo (fact L) (succ (pred m + monus X m)) := by
    refine (congrAp2 (sumF hB) qc (.eqRefl _)).eqTrans ?_
    have s := sum_succ' (Γ := Γ) hB (pred m + monus X m) (fact L)
    rw [inst2_h] at s
    exact s
  have eSm := natEq sM
  have eSX := natEq sX
  have eq := natEq (congrAp2 (Γ := Γ) quoF (.eqRefl (fact L)) hmp)
  refine .andI ?_ ?_
  · ipra_le sl (Prf.andE₁ r) with e3 + e4 - e1 - e2
  · ipra_le sl (Prf.andE₂ r) + 𝔞 (quo (fact L) (succ (pred m + monus X m))) with e2 - e3 + eSm - eSX - eq

/-- `log(1 + d/a) ≤ d/a`: `a S(K(a + d)) ≤ a S(Ka) + dF`. -/
theorem lam_upper {K : PTm n} (a d F : PTm n) (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) :
    Γ ⊢[PRAAx] le (a * S (K * (a + d)) F) (a * S (K * a) F + d * F) := by
  have lu := log_upper (Γ := Γ) (K * a) (K * d) F
  have q : Γ ⊢[PRAAx] K * (a + d) ≐ K * a + K * d := by ipra_ring
  have e := natEq (congrAp2 (Γ := Γ) (sumF hB) q (.eqRefl F))
  have mono := S_mono (Γ := Γ) F (le_of_eq_add q : Γ ⊢[PRAAx] le (K * a) (K * (a + d)))
  refine mul_le_cancel (d' := pred K) ?_
  have c : Γ ⊢[PRAAx] le (K * (a * S (K * (a + d)) F)) (K * (a * S (K * a) F + d * F)) := by
    ipra_le sl lu + sl mono with (𝔞 K * 𝔞 a + 1) * e
  exact le_congr (congrMul hK (.eqRefl _)) (congrMul hK (.eqRefl _)) c

/-- `y ≤ m² + 2m` from `y < (m + 1)²`. -/
theorem y_le {y m : PTm n} (h2 : Γ ⊢[PRAAx] lt y (succ m * succ m)) : Γ ⊢[PRAAx] le y (m * m + two * m) := by
  refine le_of_eq_add (d := monus (succ m * succ m) (succ y)) ?_
  ipra_lc natEq (eq_add_of_le h2)

/-- `sb:divisor-bound`, upper half: `D(y) − yλ_K(y) − (2c − 1)y ≤ 8m` with `c = H_X − λ_K(X)`, i.e.
`F D(y) + 2y S(KX) + Fy ≤ y S(Ky) + y S(K) + 2y S(X) + 8mF`. -/
theorem divisor_upper {y m X K L : PTm n} (hm : Γ ⊢[PRAAx] le one m) (h1 : Γ ⊢[PRAAx] le (m * m) y)
    (h2 : Γ ⊢[PRAAx] lt y (succ m * succ m)) (hmX : Γ ⊢[PRAAx] le m X) (hK : Γ ⊢[PRAAx] le one K)
    (hLX : Γ ⊢[PRAAx] le (K * X) L) (hLy : Γ ⊢[PRAAx] le (K * y) L) (hmL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] le (fact L * S y y + two * (y * S (K * X) (fact L)) + fact L * y)
      (y * S (K * y) (fact L) + y * S K (fact L) + two * (y * S X (fact L)) +
        two * (two * (two * (m * fact L)))) := by
  have hmp := pos_of_lt_zero hm
  have hKp := pos_of_lt_zero hK
  have lo := Prf.andE₁ (divisor_harmonic h1 h2 hmL)
  have eu := le_scale (two * y) (Prf.andE₂ (eta_bounds hm hmX hK hLX))
  have kmm := le_scale K h1
  have sa := le_scale y (superadd hKp hmp hmp (le_trans kmm hLy))
  have mono := le_scale y (S_mono (fact L) kmm)
  have hy2 := y_le h2
  have fy := le_scale (fact L) hy2
  have qy := le_scale (two * quo (fact L) m) hy2
  have mq := quo_mul_le (x := fact L) hmp
  have mq2 := le_scale (two * m) mq
  have mq4 := le_scale (two * two) mq
  have f4 := le_scale (two * (two * fact L)) hm
  ipra_le sl lo + sl eu + sl sa + sl mono + sl fy + sl qy + sl mq2 + sl mq4 + sl f4

/-- `sb:divisor-bound`, lower half: `D(y) − yλ_K(y) − (2c − 1)y ≥ −11m` for `y ≤ K`, i.e.
`y S(Ky) + y S(K) + 2y S(X) ≤ F D(y) + 2y S(KX) + Fy + 11mF`. -/
theorem divisor_lower {y m X K L : PTm n} (hm : Γ ⊢[PRAAx] le one m) (h1 : Γ ⊢[PRAAx] le (m * m) y)
    (h2 : Γ ⊢[PRAAx] lt y (succ m * succ m)) (hmX : Γ ⊢[PRAAx] le m X) (hK : Γ ⊢[PRAAx] le one K)
    (hyK : Γ ⊢[PRAAx] le y K) (hLX : Γ ⊢[PRAAx] le (K * X) L) (hLy : Γ ⊢[PRAAx] le (K * y) L)
    (hmL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] le (y * S (K * y) (fact L) + y * S K (fact L) + two * (y * S X (fact L)))
      (fact L * S y y + two * (y * S (K * X) (fact L)) + fact L * y +
        (two * (two * (two * (m * fact L))) + two * (m * fact L) + m * fact L)) := by
  have hmp := pos_of_lt_zero hm
  have hKp := pos_of_lt_zero hK
  have hi := Prf.andE₂ (divisor_harmonic h1 h2 hmL)
  have el := le_scale (two * y) (Prf.andE₁ (eta_bounds hm hmX hK hLX))
  have kmm := le_scale K h1
  have sb := le_scale y (subadd hKp hmp hmp (le_trans kmm hLy))
  have hy2 := y_le h2
  have wy := natEq (eq_add_of_le h1)
  have hd2 : Γ ⊢[PRAAx] le (monus y (m * m)) (two * m) := by
    ipra_le sl hy2 with -wy
  have t2 := le_scale (two * m) hm
  have h4 : Γ ⊢[PRAAx] le y (two * (two * (m * m))) := by
    ipra_le sl hy2 + sl t2 + 𝔞 m * 𝔞 m
  have monoK := S_mono (fact L) kmm
  have eD := natEq (eq_add_of_le monoK)
  have D1 := le_scale (monus (S (K * y) (fact L)) (S (K * (m * m)) (fact L))) h4
  have lu := le_scale (two * two) (lam_upper (m * m) (monus y (m * m)) (fact L) hKp)
  have qy : Γ ⊢[PRAAx] m * m + monus y (m * m) ≐ y := (eq_add_of_le h1).eqSymm
  have eS := natEq (congrAp2 (Γ := Γ) (sumF hB) (congrMul (.eqRefl K) qy) (.eqRefl (fact L)))
  have d4 := le_scale (two * (two * fact L)) hd2
  have qK1 := le_scale (quo (fact L) K) hyK
  have qK2 := quo_mul_le (x := fact L) hKp
  have fm := le_scale (fact L) hm
  have fmm := le_scale (fact L) h1
  ipra_le sl hi + sl el + sl sb + sl D1 + sl lu + sl d4 + sl qK1 + sl qK2 + sl fm + sl fmm with
    (𝔞 y - 4 * 𝔞 m * 𝔞 m) * eD - 4 * 𝔞 m * 𝔞 m * eS

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorBound
