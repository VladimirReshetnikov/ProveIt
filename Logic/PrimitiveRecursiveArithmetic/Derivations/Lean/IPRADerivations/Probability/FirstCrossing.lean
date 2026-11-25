import IPRADerivations.Foundations.MixedRadix
import IPRADerivations.Core.LinearCombination

/-!
# First-crossing indicators

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/08_samples_lln.tex`, proof of
`thm:kolmogorov`: "Let `A_k` be the event that `k` is the first index with `|S_k| ≥ a`. The `A_k` are disjoint
and their union is the maximal event", and "first-crossing events are decidable by bounded search".

For a level body `D(l, y)` and a threshold body `c(l, y)` (natural numbers; for Kolmogorov `D_l = S_l²` and
`c = a²`, cleared):

* `ge c d = 1 ∸ (c ∸ d)` is the indicator `[c ≤ d]`: `ge_of_le`, `ge_of_lt`; with `nb = 1 ∸ ge`,
  `ge_add_nb`: `[c ≤ d] + [d < c] = 1`; `ge_mul`: `[c ≤ d] c ≤ [c ≤ d] d`;
* the first-crossing indicator `I_k = [c_k ≤ D_k] ∏_{l<k} [D_l < c_l]` (`Ib`);
* `cover`: `∑_{k<K} I_k + ∏_{l<K} [D_l < c_l] = 1`, so the events are disjoint and their union is the
  complement of "no crossing before `K`";
* `disjoint`: `∑_{k<K} I_k ≤ 1`;
* `crossing_bound`: `I_k c_k ≤ I_k D_k`, the crossing condition on `A_k`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.FirstCrossing

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MixedRadix (prod_succ')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The indicator `[c ≤ d] = 1 ∸ (c ∸ d)`. -/
abbrev ge (c d : PTm n) : PTm n := monus one (monus c d)

theorem ge_of_le {c d : PTm n} (h : Γ ⊢[PRAAx] le c d) : Γ ⊢[PRAAx] ge c d ≐ one :=
  (congrMonus (.eqRefl one) h).eqTrans (monus_zero one)

theorem ge_of_lt {c d : PTm n} (h : Γ ⊢[PRAAx] lt d c) : Γ ⊢[PRAAx] ge c d ≐ zero := by
  have e := eq_add_of_le h
  have e' : Γ ⊢[PRAAx] c ≐ succ (monus c (succ d)) + d := by
    ipra_lc natEq e
  have m : Γ ⊢[PRAAx] monus c d ≐ succ (monus c (succ d)) :=
    (congrMonus e' (.eqRefl d)).eqTrans (add_monus _ _)
  have h₁ : Γ ⊢[PRAAx] le one (succ (monus c (succ d))) := by ipra_le 𝔟 (monus c (succ d))
  exact (congrMonus (.eqRefl one) m).eqTrans h₁

/-- `[c ≤ d] + [d < c] = 1`. -/
theorem ge_add_nb (c d : PTm n) : Γ ⊢[PRAAx] ge c d + monus one (ge c d) ≐ one := by
  refine .orE (lt_or_le d c) ?_ ?_
  · have g := ge_of_lt (Γ := lt d c :: Γ) Prf.hyp0
    have e₁ := natEq g
    have e₂ := natEq ((congrMonus (.eqRefl one) g).eqTrans (monus_zero (Γ := lt d c :: Γ) one))
    apply deriveNat; ipra_simps; linear_combination e₁ + e₂
  · have g := ge_of_le (Γ := le c d :: Γ) Prf.hyp0
    have e₁ := natEq g
    have e₂ := natEq ((congrMonus (.eqRefl one) g).eqTrans (monus_self (Γ := le c d :: Γ) one))
    apply deriveNat; ipra_simps; linear_combination e₁ + e₂

/-- `[c ≤ d] c ≤ [c ≤ d] d`. -/
theorem ge_mul (c d : PTm n) : Γ ⊢[PRAAx] le (ge c d * c) (ge c d * d) := by
  refine .orE (lt_or_le d c) ?_ ?_
  · have e := natEq (ge_of_lt (Γ := lt d c :: Γ) Prf.hyp0)
    ipra_le 0 using rw [e]; ring
  · have h : (le c d :: Γ) ⊢[PRAAx] le c d := Prf.hyp0
    have e := natEq (ge_of_le h)
    ipra_le sl h using rw [e]; ring

section Bodies

variable (c D : PTm 2)

/-- `[c_l ≤ D_l]` as a body. -/
abbrev geB : PTm 2 := monus one (monus c D)
/-- `[D_l < c_l]` as a body. -/
abbrev nbB : PTm 2 := monus one (geB c D)
/-- The first-crossing indicator `I_k = [c_k ≤ D_k] ∏_{l<k} [D_l < c_l]`. -/
abbrev Ib : PTm 2 := geB c D * ap2 (prodF (nbB c D)) (var 0) (var 1)

theorem inst2_Ib (k y : PTm n) :
    inst2 (Ib c D) k y = ge (inst2 c k y) (inst2 D k y) * ap2 (prodF (nbB c D)) k y := by
  simp [inst2]

theorem inst2_nbB (k y : PTm n) : inst2 (nbB c D) k y = monus one (ge (inst2 c k y) (inst2 D k y)) := by
  simp [inst2]

theorem cover_base (y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (Ib c D)) zero y + ap2 (prodF (nbB c D)) zero y ≐ one := by
  have s := natEq (sum_zero (Γ := Γ) (Ib c D) y)
  have p := natEq (prod_zero (Γ := Γ) (nbB c D) y)
  apply deriveNat; ipra_simps; rw [s, p]; ring

theorem cover_step {K y : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF (Ib c D)) K y + ap2 (prodF (nbB c D)) K y ≐ one) :
    Γ ⊢[PRAAx] ap2 (sumF (Ib c D)) (succ K) y + ap2 (prodF (nbB c D)) (succ K) y ≐ one := by
  have s' := sum_succ' (Γ := Γ) (Ib c D) K y
  rw [inst2_Ib] at s'
  have s := natEq s'
  have p' := prod_succ' (Γ := Γ) (nbB c D) K y
  rw [inst2_nbB] at p'
  have p := natEq p'
  have g := natEq (ge_add_nb (Γ := Γ) (inst2 c K y) (inst2 D K y))
  have i := natEq ih
  apply deriveNat; ipra_simps
  linear_combination s + p + 𝔟 (ap2 (prodF (nbB c D)) K y) * g + i

/-- Variables: `0 = K`, `1 = y`. -/
private abbrev coverF : Fm PTm 2 :=
  ap2 (sumF (Ib c D)) (var 0) (var 1) + ap2 (prodF (nbB c D)) (var 0) (var 1) ≐ one

private theorem cover₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] coverF c D := by
  refine ind _ trivial ?_ ?_
  · simp only [coverF, Fm.subst_eq, PTm.subst_add, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact cover_base c D _
  · simp only [coverF, Fm.subst_eq, PTm.subst_add, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact cover_step c D Prf.hyp0

/-- `cover`: `∑_{k<K} I_k + ∏_{l<K} [D_l < c_l] = 1`. -/
theorem cover (K y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (Ib c D)) K y + ap2 (prodF (nbB c D)) K y ≐ one := by
  have h := inst (Γ := Γ) (cover₀ c D) (![K, y] : Fin 2 → PTm n)
  simpa using h

/-- The first-crossing events are disjoint: `∑_{k<K} I_k ≤ 1`. -/
theorem disjoint (K y : PTm n) : Γ ⊢[PRAAx] le (ap2 (sumF (Ib c D)) K y) one := by
  have e := natEq (cover (Γ := Γ) c D K y)
  ipra_le 𝔟 (ap2 (prodF (nbB c D)) K y) using linear_combination -e

/-- On `A_k` the level has crossed the threshold: `I_k c_k ≤ I_k D_k`. -/
theorem crossing_bound (k y : PTm n) :
    Γ ⊢[PRAAx] le (inst2 (Ib c D) k y * inst2 c k y) (inst2 (Ib c D) k y * inst2 D k y) := by
  rw [inst2_Ib]
  have h := ge_mul (Γ := Γ) (inst2 c k y) (inst2 D k y)
  ipra_le sl h * 𝔟 (ap2 (prodF (nbB c D)) k y)

end Bodies

end LeanProofs.IPRA.Probability.FirstCrossing
