import IPRADerivations.Foundations.ApproximateWitness
import IPRADerivations.Core.Signum
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Finite minimization over admissible candidates

Packet: `foundations/ipra_certified_finitary_framework_2026-11-15`, `paper/sections/03_boolean_kernel.tex`,
Lemma `lem:minimize` ("Finite minimization"): "If some candidate below `C(p)` is admissible, iPRA proves
that the scan returns an admissible index below `C(p)` whose cost is no larger than that of any
admissible candidate; among equal minima it returns the least index."

The candidates are `i ≤ K`, with an admissibility body `a(i, x)` (admissible when `a = 0`) and a cost body
`c(i, x)`. The scan is the bounded `argmin` of `Foundations/ApproximateWitness` applied to the penalized
score `c + sg(a) · m`, where the penalty body `m(i, x) = M` exceeds every cost:

* `pB c a m`: the score `c + sg(a) m`; `fmin`: the selected index;
* `filtered_min`: if `m(i) = M` and `c(i) < M` for `i ≤ K`, and the candidate `j ≤ K` is admissible, then
  `fmin ≤ K`, `fmin` is admissible and `c(fmin) ≤ c(j)`;
* `filtered_tie`: if moreover `c(j) = c(fmin)`, then `fmin ≤ j` (the least index among equal minima).

The hypotheses on `m` and `c` are families of derivations (one for each index `i ≤ K`), so the theorems
are schemas; the scan itself is one primitive-recursive term.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FilteredMinimization

open_ipra
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Foundations.ApproximateWitness (argmin argmin_spec argmin_minimal argmin_tie)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Filter

variable (c a m : PTm 2)

/-- The penalized score `c + sg(a) · m`. -/
def pB : PTm 2 := c + sg a * m

theorem inst2_pB (i x : PTm n) :
    inst2 (pB c a m) i x = inst2 c i x + sg (inst2 a i x) * inst2 m i x := by
  simp [inst2, pB]

/-- The selected index. -/
abbrev fmin (K x : PTm n) : PTm n := argmin (pB c a m) K x

/-- The score of an admissible candidate is its cost. -/
theorem score_adm {i x : PTm n} (h : Γ ⊢[PRAAx] inst2 a i x ≐ zero) :
    Γ ⊢[PRAAx] inst2 (pB c a m) i x ≐ inst2 c i x := by
  rw [inst2_pB]
  ipra_lc 𝔟(inst2 m i x) * natEq ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans (sg_zero (Γ := Γ)))

variable {c a m}

/-- `lem:minimize`: the scan returns an admissible index whose cost is at most that of any admissible
candidate. -/
theorem filtered_min {K x M j : PTm n}
    (hm : ∀ {i : PTm n}, (Γ ⊢[PRAAx] le i K) → (Γ ⊢[PRAAx] inst2 m i x ≐ M))
    (hc : ∀ {i : PTm n}, (Γ ⊢[PRAAx] le i K) → (Γ ⊢[PRAAx] lt (inst2 c i x) M))
    (hj : Γ ⊢[PRAAx] le j K) (haj : Γ ⊢[PRAAx] inst2 a j x ≐ zero) :
    Γ ⊢[PRAAx] le (fmin c a m K x) K ⋏
      ((inst2 a (fmin c a m K x) x ≐ zero) ⋏ le (inst2 c (fmin c a m K x) x) (inst2 c j x)) := by
  have sp := argmin_spec (Γ := Γ) (pB c a m) K x
  have hK : Γ ⊢[PRAAx] le (fmin c a m K x) K := Prf.andE₁ sp
  have hmin := argmin_minimal (Γ := Γ) (pB c a m) (x := x) hj
  have sj := score_adm c a m haj
  have hmin' := le_congr (.eqRefl _) sj hmin
  have adm : Γ ⊢[PRAAx] inst2 a (fmin c a m K x) x ≐ zero := by
    refine .orE (zero_or_succ (inst2 a (fmin c a m K x) x)) Prf.hyp0 ?_
    have hs : ((inst2 a (fmin c a m K x) x ≐ succ (pred (inst2 a (fmin c a m K x) x))) :: Γ) ⊢[PRAAx]
        inst2 a (fmin c a m K x) x ≐ succ (pred (inst2 a (fmin c a m K x) x)) := Prf.hyp0
    have e₁ := natEq ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hs)).eqTrans
      (sg_succ (Γ := _) (pred (inst2 a (fmin c a m K x) x))))
    have e₂ := natEq ((hm hK).wk (ψ := inst2 a (fmin c a m K x) x ≐ succ (pred (inst2 a (fmin c a m K x) x))))
    have hm' := hmin'.wk (ψ := inst2 a (fmin c a m K x) x ≐ succ (pred (inst2 a (fmin c a m K x) x)))
    have hcj := (hc hj).wk (ψ := inst2 a (fmin c a m K x) x ≐ succ (pred (inst2 a (fmin c a m K x) x)))
    rw [inst2_pB] at hm'
    have abs : ((inst2 a (fmin c a m K x) x ≐ succ (pred (inst2 a (fmin c a m K x) x))) :: Γ) ⊢[PRAAx]
        le (succ (inst2 c j x)) (inst2 c j x) := by
      ipra_le sl hm' + sl hcj + 𝔟(inst2 c (fmin c a m K x) x) using
        linear_combination 𝔟(inst2 m (fmin c a m K x) x) * e₁ + e₂
    exact not_succ_le_self _ _ abs
  exact .andI hK (.andI adm (le_congr (score_adm c a m adm) (.eqRefl _) hmin'))

/-- `lem:minimize`: among admissible candidates of equal minimal cost, the scan returns the least index. -/
theorem filtered_tie {K x M j : PTm n}
    (hm : ∀ {i : PTm n}, (Γ ⊢[PRAAx] le i K) → (Γ ⊢[PRAAx] inst2 m i x ≐ M))
    (hc : ∀ {i : PTm n}, (Γ ⊢[PRAAx] le i K) → (Γ ⊢[PRAAx] lt (inst2 c i x) M))
    (hj : Γ ⊢[PRAAx] le j K) (haj : Γ ⊢[PRAAx] inst2 a j x ≐ zero)
    (htie : Γ ⊢[PRAAx] inst2 c j x ≐ inst2 c (fmin c a m K x) x) :
    Γ ⊢[PRAAx] le (fmin c a m K x) j := by
  have f := filtered_min hm hc hj haj
  have adm := Prf.andE₁ (Prf.andE₂ f)
  exact argmin_tie (pB c a m) hj
    (((score_adm c a m haj).eqTrans htie).eqTrans (score_adm c a m adm).eqSymm)

end Filter

end LeanProofs.IPRA.Foundations.FilteredMinimization
