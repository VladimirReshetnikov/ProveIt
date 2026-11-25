import IPRADerivations.Analysis.ReciprocalSquareTail
import IPRADerivations.Core.Powers
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# A checked cutoff for the Barnes canonical-factor tail

The packet `analysis/barnes_g_ipra_2026-11-16`, `eq:product-cutoff`, prints
`ceil(2^(p+5) R³ / 3)` and then claims `2 R³ / (3 N) ≤ 2^(-p-5)`.
That implication has a factor-two error. The corrected cutoff here uses
`N = max(2R, ceil(2^(p+6) R³ / 3))`. The ceiling is the actual primitive
recursive quotient `(s + 2) div 3`, and the maximum uses truncated subtraction.

The exact denominator-cleared tail budget is conditional on the pointwise
canonical-factor majorant. The zero-radius case is included.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BarnesCutoff

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ReciprocalSquareTail (majorant tailSum tailSum_zero tailSum_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

abbrev three : PTm n := num 3

/-- The exact integer ceiling of `s / 3`. -/
def ceilThird (s : PTm n) : PTm n := quo (s + two) (succ two)

/-- The primitive recursive maximum. -/
def maximum (a b : PTm n) : PTm n := a + monus b a

/-- The requested denominator multiplier `2^(p+5)`. -/
def budget (p : PTm n) : PTm n := pw two (p + num 5)

/-- The corrected numerator in the ceiling. -/
def scale (R p : PTm n) : PTm n := pw two (p + num 6) * R * R * R

/-- The corrected source cutoff. -/
def cutoff (R p : PTm n) : PTm n := maximum (two * R) (ceilThird (scale R p))

@[simp] theorem subst_ceilThird {m : ℕ} (σ : Fin n → PTm m) (s : PTm n) :
    Syn.subst σ (ceilThird s) = ceilThird (Syn.subst σ s) := by
  simp [ceilThird]

@[simp] theorem subst_maximum {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (maximum a b) = maximum (Syn.subst σ a) (Syn.subst σ b) := by
  simp [maximum]

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (budget p) = budget (Syn.subst σ p) := by
  simp [budget]

@[simp] theorem subst_scale {m : ℕ} (σ : Fin n → PTm m) (R p : PTm n) :
    Syn.subst σ (scale R p) = scale (Syn.subst σ R) (Syn.subst σ p) := by
  simp [scale]

@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (R p : PTm n) :
    Syn.subst σ (cutoff R p) = cutoff (Syn.subst σ R) (Syn.subst σ p) := by
  simp [cutoff]

/-- The ceiling never rounds down. -/
theorem ceil_lower (s : PTm n) : Γ ⊢[PRAAx] le s (three * ceilThird s) := by
  have d := Prf.andE₁ (div_mod (Γ := Γ) (s + two) two)
  have r := Prf.andE₂ (div_mod (Γ := Γ) (s + two) two)
  have hr : Γ ⊢[PRAAx] le (rem (s + two) (succ two)) two :=
    (succ_monus_succ _ _).eqSymm.eqTrans r
  refine le_of_eq_add (d := monus two (rem (s + two) (succ two))) ?_
  unfold ceilThird
  ipra_lc -natEq d + natEq (eq_add_of_le hr)

/-- The ceiling rounds upward by at most two numerator units. -/
theorem ceil_upper (s : PTm n) : Γ ⊢[PRAAx] le (three * ceilThird s) (s + two) :=
  le_of_eq_add (Prf.andE₁ (div_mod (s + two) two))

/-- Every integer upper bound on `s / 3` is above the computed ceiling. -/
theorem ceil_least {s q : PTm n} (h : Γ ⊢[PRAAx] le s (three * q)) :
    Γ ⊢[PRAAx] le (ceilThird s) q := by
  refine .orE (lt_or_le q (ceilThird s)) ?_ Prf.hyp0
  refine succ_ne_zero' _ (a := monus (three * q) s +
    three * monus (ceilThird s) (succ q) + monus (s + two) (three * ceilThird s)) ?_
  ipra_lc -natEq (eq_add_of_le ((ceil_upper (Γ := Γ) s).wk (ψ := lt q (ceilThird s)))) -
    3 * natEq (eq_add_of_le (Prf.hyp0 : (lt q (ceilThird s) :: Γ) ⊢[PRAAx] _)) -
    natEq (eq_add_of_le (h.wk (ψ := lt q (ceilThird s))))

theorem ceil_zero : Γ ⊢[PRAAx] ceilThird (zero : PTm n) ≐ zero := by
  have h : Γ ⊢[PRAAx] quo two (succ two) ≐ zero :=
    Prf.andE₁ (div_mod_unique (K' := two) (z := two) (q := zero) (r := two)
      (by ipra_ring) (le_refl (succ two)))
  exact (congrAp2 quoF (zero_add two) (.eqRefl _)).eqTrans h

theorem maximum_left (a b : PTm n) : Γ ⊢[PRAAx] le a (maximum a b) := le_add_right _ _

theorem maximum_right (a b : PTm n) : Γ ⊢[PRAAx] le b (maximum a b) := by
  have e : Γ ⊢[PRAAx] maximum a b ≐ monus a b + b :=
    (add_comm _ _).eqTrans (monus_max b a)
  exact le_congr (.eqRefl _) e.eqSymm (le_add_left b (monus a b))

theorem maximum_of_left {a b : PTm n} (h : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] maximum a b ≐ a :=
  (congrAdd (.eqRefl _) h).eqTrans (add_zero _)

theorem maximum_of_right {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] maximum a b ≐ b :=
  ((add_comm _ _).eqTrans (monus_max b a)).eqTrans
    ((congrAdd h (.eqRefl _)).eqTrans (zero_add _))

theorem maximum_least {a b c : PTm n} (ha : Γ ⊢[PRAAx] le a c) (hb : Γ ⊢[PRAAx] le b c) :
    Γ ⊢[PRAAx] le (maximum a b) c := by
  refine .orE (le_total a b) ?_ ?_
  · exact le_congr (maximum_of_right Prf.hyp0).eqSymm (.eqRefl _) hb.wk
  · exact le_congr (maximum_of_left Prf.hyp0).eqSymm (.eqRefl _) ha.wk

/-- Both source guards are satisfied by the computed cutoff. -/
theorem cutoff_guards (R p : PTm n) :
    Γ ⊢[PRAAx] le (two * R) (cutoff R p) ⋏ le (scale R p) (three * cutoff R p) := by
  refine .andI (maximum_left _ _) (le_trans (ceil_lower _) ?_)
  exact le_congr (mul_comm _ _) (mul_comm _ _)
    (mul_le_mul_right three (maximum_right (two * R) (ceilThird (scale R p))))

/-- The computed maximum is the least natural cutoff satisfying both guards. -/
theorem cutoff_least {R p N : PTm n} (radius : Γ ⊢[PRAAx] le (two * R) N)
    (precision : Γ ⊢[PRAAx] le (scale R p) (three * N)) :
    Γ ⊢[PRAAx] le (cutoff R p) N :=
  maximum_least radius (ceil_least precision)

/-- The corrected power is twice the requested tail denominator. -/
theorem scale_budget (R p : PTm n) :
    Γ ⊢[PRAAx] scale R p ≐ two * budget p * R * R * R := by
  have ee : Γ ⊢[PRAAx] p + num 6 ≐ succ (p + num 5) := by ipra_ring
  unfold scale budget
  ipra_lc 𝔞(R) ^ 3 * natEq ((congrAp2 (Γ := Γ) powF ee (.eqRefl two)).eqTrans (pw_succ two (p + num 5)))

theorem scale_zero (p : PTm n) : Γ ⊢[PRAAx] scale zero p ≐ zero := by
  unfold scale
  ipra_ring

/-- At zero radius the displayed maximum is exactly zero. -/
theorem cutoff_zero (p : PTm n) : Γ ⊢[PRAAx] cutoff zero p ≐ zero := by
  have ce : Γ ⊢[PRAAx] ceilThird (scale zero p) ≐ zero :=
    (congrAp2 quoF (congrAdd (scale_zero p) (.eqRefl _)) (.eqRefl _)).eqTrans ceil_zero
  have m : Γ ⊢[PRAAx] maximum (two * zero) (ceilThird (scale zero p)) ≐ maximum zero zero := by
    exact (congrAdd (mul_zero two) (congrMonus ce (mul_zero two)))
  exact m.eqTrans ((congrAdd (.eqRefl _) (monus_self _)).eqTrans (add_zero _))

theorem cutoff_positive {R : PTm n} (p : PTm n) (hR : Γ ⊢[PRAAx] le one R) :
    Γ ⊢[PRAAx] le one (cutoff R p) := by
  have h2 : Γ ⊢[PRAAx] le R (two * R) := le_of_eq_add (d := R) (by ipra_ring)
  exact le_trans (le_trans hR h2) (Prf.andE₁ (cutoff_guards R p))

private alias cancel_positive := Common.mul_cancel_le

private theorem zero_point {k E : PTm n}
    (h : Γ ⊢[PRAAx] le (three * succ k * succ k * E) zero) :
    Γ ⊢[PRAAx] E ≐ zero := by
  have regrouped : Γ ⊢[PRAAx] le (three * (succ k * (succ k * E)))
      (three * (succ k * (succ k * zero))) :=
    le_congr (by ipra_ring) (by ipra_ring) h
  exact le_antisymm (mul_le_cancel (mul_le_cancel (mul_le_cancel regrouped))) (zero_le _)

/-- A zero canonical-factor majorant makes every positive-index tail sum zero. -/
theorem zero_majorant (e : PR 2) (N r C x : PTm n)
    (hm : Γ ⊢[PRAAx] majorant e three N C x) (hC : Γ ⊢[PRAAx] C ≐ zero) :
    Γ ⊢[PRAAx] tailSum e N r x ≐ zero := by
  have all : Γ ⊢[PRAAx] .all (tailSum e (Syn.shift N) (var 0) (Syn.shift x) ≐ zero) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [Fm.subst_eq, ReciprocalSquareTail.subst_tailSum, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] using tailSum_zero e N x
    · simp only [Fm.subst_eq, ReciprocalSquareTail.subst_tailSum, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      have shifted : Γ.map Fm.shift ⊢[PRAAx]
          majorant e three (Syn.shift N) (Syn.shift C) (Syn.shift x) := by
        simpa [ReciprocalSquareTail.shift_majorant, Syn.shift] using hm.shift
      have point := Prf.allE (var 0) shifted
      have cz : Γ.map Fm.shift ⊢[PRAAx] Syn.shift C ≐ zero := by
        simpa [Fm.shift, Syn.shift] using hC.shift
      have point0 : (tailSum e (Syn.shift N) (var 0) (Syn.shift x) ≐ zero) ::
          Γ.map Fm.shift ⊢[PRAAx]
          le (three * succ (Syn.shift N + var 0) * succ (Syn.shift N + var 0) *
            ap2 e (succ (Syn.shift N + var 0)) (Syn.shift x)) zero := by
        apply le_congr (.eqRefl _) cz.wk
        simpa [majorant] using point.wk
      exact (tailSum_succ e _ _ _).eqTrans
        ((congrAdd Prf.hyp0 (zero_point point0)).eqTrans (add_zero _))
  simpa only [Fm.subst_eq, ReciprocalSquareTail.subst_tailSum, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] using Prf.allE r all

private theorem positive_budget (e : PR 2) (R p r D x : PTm n)
    (hR : Γ ⊢[PRAAx] le one R)
    (hm : Γ ⊢[PRAAx] majorant e three (cutoff R p) (two * R * R * R * D) x) :
    Γ ⊢[PRAAx] le (budget p * tailSum e (cutoff R p) r x) D := by
  let S := tailSum e (cutoff R p) r x
  have tail := ReciprocalSquareTail.barnes_qtail e (cutoff R p) r R D x (cutoff_positive p hR) hm
  have guard := Prf.andE₂ (cutoff_guards (Γ := Γ) R p)
  have multiplied := mul_le_mul_right S guard
  have whole : Γ ⊢[PRAAx] le (two * (R * (R * (R * (budget p * S)))))
      (two * (R * (R * (R * D)))) := by
    refine le_congr ?_ (by ipra_ring) (le_trans multiplied tail)
    ipra_lc 𝔞(S) * natEq (scale_budget (Γ := Γ) R p)
  exact cancel_positive hR (cancel_positive hR (cancel_positive hR (mul_le_cancel whole)))

/-- The corrected cutoff supplies the stated `2^(-p-5)` tail budget,
including radius zero, from the pointwise canonical-factor certificate. -/
theorem tail_budget (e : PR 2) (R p r D x : PTm n)
    (hm : Γ ⊢[PRAAx] majorant e three (cutoff R p) (two * R * R * R * D) x) :
    Γ ⊢[PRAAx] le (budget p * tailSum e (cutoff R p) r x) D := by
  refine .orE (zero_or_succ R) ?_ ?_
  · have cz : ((R ≐ zero) :: Γ) ⊢[PRAAx] two * R * R * R * D ≐ zero := by
      ipra_lc 2 * 𝔞(R) ^ 2 * 𝔞(D) * natEq (Prf.hyp0 : ((R ≐ zero) :: Γ) ⊢[PRAAx] _)
    have z := zero_majorant e (cutoff R p) r _ x hm.wk cz
    exact le_congr ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqSymm (.eqRefl _) (zero_le D)
  · have positive : ((R ≐ succ (PTm.pred R)) :: Γ) ⊢[PRAAx] le one R := by
      refine le_of_eq_add (d := PTm.pred R) (Prf.hyp0.eqTrans ?_)
      ipra_ring
    exact positive_budget e R p r D x positive hm.wk

/-- Variables `0 = R`, `1 = p`. -/
abbrev guardsFormula : Fm PTm 2 :=
  le (two * var 0) (cutoff (var 0) (var 1)) ⋏
    le (scale (var 0) (var 1)) (three * cutoff (var 0) (var 1))

theorem cutoff_guards_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 guardsFormula :=
  closeUniv 2 (cutoff_guards _ _)

/-- Variables `0 = s`, `1 = q`. -/
abbrev ceilingFormula : Fm PTm 2 :=
  le (var 0) (three * ceilThird (var 0)) ⋏
    (le (three * ceilThird (var 0)) (var 0 + two) ⋏
      (le (var 0) (three * var 1) ⟶ le (ceilThird (var 0)) (var 1)))

theorem ceiling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 ceilingFormula :=
  closeUniv 2 (.andI (ceil_lower _) (.andI (ceil_upper _) (.impI (ceil_least Prf.hyp0))))

/-- Variables `0 = R`, `1 = p`, `2 = r`, `3 = D`, `4 = x`. -/
abbrev tailBudgetFormula (e : PR 2) : Fm PTm 5 :=
  majorant e three (cutoff (var 0) (var 1)) (two * var 0 * var 0 * var 0 * var 3) (var 4) ⟶
    le (budget (var 1) * tailSum e (cutoff (var 0) (var 1)) (var 2) (var 4)) (var 3)

theorem canonical_tail_cutoff (e : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (tailBudgetFormula e) :=
  closeUniv 5 (.impI (tail_budget e _ _ _ _ _ Prf.hyp0))

#print axioms ceil_lower
#print axioms ceil_upper
#print axioms ceiling_closed
#print axioms cutoff_guards_closed
#print axioms canonical_tail_cutoff

end LeanProofs.IPRA.Analysis.BarnesCutoff
