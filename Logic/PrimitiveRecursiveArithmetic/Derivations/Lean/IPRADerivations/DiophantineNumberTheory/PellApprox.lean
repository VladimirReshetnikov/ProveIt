import IPRADerivations.DiophantineNumberTheory.PellDirichlet
import IPRADerivations.DiophantineNumberTheory.IrrationalSqrt
import IPRADerivations.AnalyticNumberTheory.SquareReciprocal
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.AnalyticNumberTheory.Smooth

/-!
# Bounded norm with a prescribed lower denominator

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, `dio:pell-approx`:

  "Let `D ≥ 2` be nonsquare and `Y ≥ 0`. Set `B = 4(D+1)`, `Q = B(Y+1)`, `C = 4D+2`. There are positive integers
  `p, q` with `Y < q ≤ Q`, `p ≤ DQ + 1`, `0 < |p² − Dq²| < C`. The pair can be obtained by bounded search using
  integer arithmetic."

The pair is the one of the finite Dirichlet construction `PellDirichlet.dirichlet` (a primitive recursive function of
`D` and `Q`): `1 ≤ q ≤ Q`, `1 ≤ p ≤ D q` and, cleared, `(Qp − 1)² < Q² q² D < (Qp + 1)²`. With `X = Qp`:

* `sq_lower`, `sq_upper`: `X² + 2 ≤ Q²q²D + 2X` and `Q²q²D ≤ X² + 2X`;
* `norm_upper`, `norm_lower`: `p² < Dq² + C` and `Dq² < p² + C` (multiply by `Q²`, use `p ≤ DQ`, cancel);
* `norm_ne`: `p² ≠ Dq²` (`IrrationalSqrt.square_of_rational_root`);
* `q_large`: `Y < q`. If `q ≤ Y`, a nonzero norm forces `Q² ≤ 2Qp + 1`, hence `Q ≤ 2p ≤ 2DY + 1`, contradicting
  `Q = 4(D+1)(Y+1)`;
* **`pell_approx`**: all the assertions together.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellApprox

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.PellDirichlet (dirichlet dp dq)
open LeanProofs.IPRA.DiophantineNumberTheory.IrrationalSqrt (square_of_rational_root)
open LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal (cancel_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (one_le_of_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `Q = 4(D + 1)(Y + 1)`. -/
abbrev Qv (D Y : PTm n) : PTm n := num 4 * (succ D * succ Y)

/-- `C = 4D + 2`. -/
abbrev Cv (D : PTm n) : PTm n := num 4 * D + two

abbrev pv (D Y : PTm n) : PTm n := dp D (Qv D Y)
abbrev qv (D Y : PTm n) : PTm n := dq D (Qv D Y)

theorem Q_pos (D Y : PTm n) : Γ ⊢[PRAAx] Qv D Y ≐ succ (pred (Qv D Y)) :=
  AnalyticNumberTheory.Primes.eq_succ_pred (y := num 3 + num 4 * (D + Y + D * Y))
    (by ipra_ring)

theorem one_pos (x : PTm n) : Γ ⊢[PRAAx] le one (succ x) := (succ_monus_succ _ _).eqTrans (zero_le x)

/-! ## The two squared comparisons -/

theorem sq_lower {Q p S : PTm n} (hX : Γ ⊢[PRAAx] le one (Q * p))
    (h : Γ ⊢[PRAAx] lt (monus (Q * p) one * monus (Q * p) one) S) :
    Γ ⊢[PRAAx] le (Q * p * (Q * p) + two) (S + two * (Q * p)) := by
  have e := natEq (eq_add_of_le hX)
  ipra_le sl h with (𝔞 Q * 𝔞 p + 𝔞 (monus (Q * p) one) - 1) * e

theorem sq_upper {Q p S : PTm n} (h : Γ ⊢[PRAAx] lt S ((Q * p + one) * (Q * p + one))) :
    Γ ⊢[PRAAx] le S (Q * p * (Q * p) + two * (Q * p)) := by
  ipra_le sl h

/-! ## The norm bounds -/

theorem norm_upper {Q p q D : PTm n} (hQ : Γ ⊢[PRAAx] Q ≐ succ (pred Q)) (hp : Γ ⊢[PRAAx] le p (D * Q))
    (h : Γ ⊢[PRAAx] le (Q * p * (Q * p) + two) (Q * q * (Q * q) * D + two * (Q * p))) :
    Γ ⊢[PRAAx] lt (p * p) (D * (q * q) + (num 4 * D + two)) := by
  refine cancel_le (pos_mul hQ hQ) ?_
  ipra_le sl h + 2 * 𝔞 Q * sl hp + 𝔞 Q * 𝔞 Q * (2 * 𝔞 D + 1) + 2

theorem norm_lower {Q p q D : PTm n} (hQ : Γ ⊢[PRAAx] Q ≐ succ (pred Q)) (hp : Γ ⊢[PRAAx] le p (D * Q))
    (h : Γ ⊢[PRAAx] le (Q * q * (Q * q) * D) (Q * p * (Q * p) + two * (Q * p))) :
    Γ ⊢[PRAAx] lt (D * (q * q)) (p * p + (num 4 * D + two)) := by
  refine cancel_le (pos_mul hQ hQ) ?_
  ipra_le sl h + 2 * 𝔞 Q * sl hp + 𝔞 Q * 𝔞 Q * (2 * 𝔞 D + 1)

/-! ## The lower bound on the denominator -/

/-- `Q² ≤ 2Qp + 1`, `p ≤ DY` and `Q = 4(D+1)(Y+1)` are incompatible. -/
theorem absurd_alg {D Y p : PTm n} (h : Γ ⊢[PRAAx] le (Qv D Y * Qv D Y) (two * (Qv D Y * p) + one))
    (hp : Γ ⊢[PRAAx] le p (D * Y)) : Γ ⊢[PRAAx] le one zero := by
  have hQ := Q_pos (Γ := Γ) D Y
  have h' : Γ ⊢[PRAAx] le (Qv D Y * Qv D Y) (Qv D Y * (two * (D * Y) + one)) := by
    have eQ := natEq hQ
    ipra_le sl h + 2 * 𝔞 (Qv D Y) * sl hp + 𝔞 (pred (Qv D Y)) with eQ
  exact absurd2 (cancel_le hQ h')
where
  absurd2 {D Y : PTm n} (h : Γ ⊢[PRAAx] le (Qv D Y) (two * (D * Y) + one)) : Γ ⊢[PRAAx] le one zero := by
    ipra_le sl h + 2 * 𝔞 D * 𝔞 Y + 4 * 𝔞 D + 4 * 𝔞 Y + 2

/-- **`Y < q`**: a nonzero norm with `q ≤ Y` is impossible. -/
theorem q_large {D Y p q : PTm n} (hp : Γ ⊢[PRAAx] le p (D * q))
    (hl : Γ ⊢[PRAAx] le (Qv D Y * p * (Qv D Y * p) + two) (Qv D Y * q * (Qv D Y * q) * D + two * (Qv D Y * p)))
    (hu : Γ ⊢[PRAAx] le (Qv D Y * q * (Qv D Y * q) * D) (Qv D Y * p * (Qv D Y * p) + two * (Qv D Y * p)))
    (hne : Γ ⊢[PRAAx] neg (p * p ≐ D * (q * q))) : Γ ⊢[PRAAx] lt Y q := by
  refine .orE (lt_or_le Y q) Prf.hyp0 ?_
  let C : List (Fm PTm n) := le q Y :: Γ
  have hqY : C ⊢[PRAAx] le q Y := Prf.hyp0
  have hpY : C ⊢[PRAAx] le p (D * Y) := le_trans hp.wk (le_mul_mono (le_refl D) hqY)
  refine .orE (lt_or_le (p * p) (D * (q * q))) ?_ ?_
  · -- `p² < Dq²`
    have hlt : (lt (p * p) (D * (q * q)) :: C) ⊢[PRAAx] le (p * p + one) (D * (q * q)) :=
      le_congr (succ_eq_add_one _) (.eqRefl _) Prf.hyp0
    have hu' : (lt (p * p) (D * (q * q)) :: C) ⊢[PRAAx]
        le (Qv D Y * q * (Qv D Y * q) * D) (Qv D Y * p * (Qv D Y * p) + two * (Qv D Y * p)) := hu.wk.wk
    have k : (lt (p * p) (D * (q * q)) :: C) ⊢[PRAAx]
        le (Qv D Y * Qv D Y) (two * (Qv D Y * p) + one) := by
      ipra_le 𝔞 (Qv D Y) * 𝔞 (Qv D Y) * sl hlt + sl hu' + 1
    exact .botE _ (lt_zero_absurd _ (absurd_alg k hpY.wk))
  · -- `Dq² ≤ p²`, hence `Dq² < p²`
    refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · have hlt : (lt (D * (q * q)) (p * p) :: le (D * (q * q)) (p * p) :: C) ⊢[PRAAx]
          le (D * (q * q) + one) (p * p) := le_congr (succ_eq_add_one _) (.eqRefl _) Prf.hyp0
      have hl' : (lt (D * (q * q)) (p * p) :: le (D * (q * q)) (p * p) :: C) ⊢[PRAAx]
          le (Qv D Y * p * (Qv D Y * p) + two) (Qv D Y * q * (Qv D Y * q) * D + two * (Qv D Y * p)) :=
        hl.wk.wk.wk
      have k : (lt (D * (q * q)) (p * p) :: le (D * (q * q)) (p * p) :: C) ⊢[PRAAx]
          le (Qv D Y * Qv D Y) (two * (Qv D Y * p) + one) := by
        ipra_le 𝔞 (Qv D Y) * 𝔞 (Qv D Y) * sl hlt + sl hl' + 3
      exact .botE _ (lt_zero_absurd _ (absurd_alg k hpY.wk.wk))
    · exact .botE _ (.impE hne.wk.wk.wk Prf.hyp0.eqSymm)

/-! ## The lemma -/

/-- **`dio:pell-approx`**: for `D ≥ 2` nonsquare and every `Y`, the Dirichlet pair `p = pv D Y`, `q = qv D Y`
for `Q = 4(D+1)(Y+1)` has `Y < q ≤ Q`, `1 ≤ p ≤ DQ + 1`, `p² < Dq² + C`, `Dq² < p² + C` (`C = 4D + 2`) and
`p² ≠ Dq²`, i.e. `0 < |p² − Dq²| < C`. -/
theorem pell_approx {D Y : PTm n} (hD : Γ ⊢[PRAAx] le two D) (hns : Γ ⊢[PRAAx] neg (D ≐ isqrt D * isqrt D)) :
    Γ ⊢[PRAAx] (lt Y (qv D Y) ⋏ le (qv D Y) (Qv D Y)) ⋏
      ((le one (pv D Y) ⋏ le (pv D Y) (D * Qv D Y + one)) ⋏
        ((lt (pv D Y * pv D Y) (D * (qv D Y * qv D Y) + Cv D) ⋏ lt (D * (qv D Y * qv D Y)) (pv D Y * pv D Y + Cv D)) ⋏
          neg (pv D Y * pv D Y ≐ D * (qv D Y * qv D Y)))) := by
  have hDp : Γ ⊢[PRAAx] D ≐ succ (pred D) := AnalyticNumberTheory.Primes.eq_succ_pred (AnalyticNumberTheory.Smooth.K_eq hD)
  have hQ := Q_pos (Γ := Γ) D Y
  have dr := dirichlet hDp hQ
  have q1 := Prf.andE₁ dr
  have qQ := Prf.andE₁ (Prf.andE₂ dr)
  have p1 := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ dr))
  have pDq := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ dr)))
  have up := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ dr))))
  have lo := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ dr))))
  have hpDQ : Γ ⊢[PRAAx] le (pv D Y) (D * Qv D Y) := le_trans pDq (le_mul_mono (le_refl D) qQ)
  have hX : Γ ⊢[PRAAx] le one (Qv D Y * pv D Y) := le_trans p1 (le_congr (one_mul _) (.eqRefl _)
    (le_mul_mono (one_le_of_pos hQ) (le_refl _)))
  have hl := sq_lower hX lo
  have hu := sq_upper up
  have hqp : Γ ⊢[PRAAx] qv D Y ≐ succ (pred (qv D Y)) := AnalyticNumberTheory.Primes.eq_succ_pred
    ((eq_add_of_le q1).eqTrans (by ipra_ring : Γ ⊢[PRAAx] one + monus (qv D Y) one ≐ succ (monus (qv D Y) one)))
  have hne : Γ ⊢[PRAAx] neg (pv D Y * pv D Y ≐ D * (qv D Y * qv D Y)) :=
    .impI (.impE hns.wk (square_of_rational_root hqp.wk Prf.hyp0))
  exact .andI (.andI (q_large pDq hl hu hne) qQ)
    (.andI (.andI p1 (le_trans hpDQ (le_add_right _ one)))
      (.andI (.andI (norm_upper hQ hpDQ hl) (norm_lower hQ hpDQ hu)) hne))

end LeanProofs.IPRA.DiophantineNumberTheory.PellApprox
