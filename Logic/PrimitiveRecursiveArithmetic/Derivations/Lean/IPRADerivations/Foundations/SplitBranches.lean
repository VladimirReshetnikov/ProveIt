import IPRADerivations.DiophantineNumberTheory.FLTMultiples
import IPRADerivations.Foundations.FrontierSoundness

/-!
# Polynomial estimates for separated branches

Packet: `foundations/ipra_local_global`, `paper/05_split_branches.tex`, Lemma `lem:split-poly-estimates`
("Polynomial estimates", `eq:split-dominance` and its consequence) and Lemma `lem:split-factor` ("Size of an
integer factor"). Integers enter through their absolute values, which are natural numbers.

`lem:split-factor`: if `u v = w` and `w ≠ 0`, then `u ≠ 0`, `v ≠ 0` and `|u| ≤ |w|`:

* `factor_pos_left`, `factor_pos_right`: `u v = w + 1` gives `u ≥ 1` and `v ≥ 1`;
* `factor_le`: `u v = w` with `v ≥ 1` gives `u ≤ w`.

`lem:split-poly-estimates`, for coefficient magnitudes `c_k = |q_k|` (a body `c(k, x)`) and `M = |x| ≥ 1`:

* `tmB c`, `tm_at`: the body of the lower terms, `c_k M^k`, with the pair `⟨M, x⟩` as parameter;
* `lower_terms`: `M · ∑_{k<s} c_k M^k ≤ (∑_{k<s} c_k) · M^s`, i.e.
  `∑_{k<s} |q_k| M^k ≤ (∑_{k<s} |q_k|) M^{s−1}`;
* `dominance` (`eq:split-dominance`, multiplied by `M`): from the isolated leading term
  `M^s ≤ V + ∑_{k<s} c_k M^k` (with `V = |Q(x)|`; this is the triangle inequality and `|q_s| ≥ 1`, taken as
  a hypothesis), `M · M^s ≤ M V + (∑_{k<s} c_k) M^s`;
* `no_large_root`: if moreover `V = 0`, then `M ≤ ∑_{k<s} c_k`: a polynomial with nonzero integer leading
  coefficient has no integer root of absolute value above the sum of its lower coefficient magnitudes.

The first estimate `|Q(x)| ≤ E_Q(H)`, the degree bookkeeping and Theorem `thm:split-bound` are not derived
here.
-/

namespace LeanProofs.IPRA.Foundations.SplitBranches

open_ipra exports

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The size of a factor -/

/-- `u v = w + 1` gives `u ≥ 1`. -/
theorem factor_pos_left {u v w' : PTm n} (h : Γ ⊢[PRAAx] u * v ≐ succ w') :
    Γ ⊢[PRAAx] u ≐ succ (pred u) := by
  refine .orE (zero_or_succ u) ?_ Prf.hyp0
  exact succ_ne_zero' _ (Prf.eqTrans (Prf.eqSymm h.wk)
    (Prf.eqTrans (congrMul Prf.hyp0 (.eqRefl v)) (zero_mul v)))

/-- `u v = w + 1` gives `v ≥ 1`. -/
theorem factor_pos_right {u v w' : PTm n} (h : Γ ⊢[PRAAx] u * v ≐ succ w') :
    Γ ⊢[PRAAx] v ≐ succ (pred v) := by
  refine .orE (zero_or_succ v) ?_ Prf.hyp0
  exact succ_ne_zero' _ (Prf.eqTrans (Prf.eqSymm h.wk)
    (Prf.eqTrans (congrMul (.eqRefl u) Prf.hyp0) (mul_zero u)))

/-- `u v = w` with `v ≥ 1` gives `u ≤ w`. -/
theorem factor_le {u v w : PTm n} (h : Γ ⊢[PRAAx] u * v ≐ w) (hv : Γ ⊢[PRAAx] v ≐ succ (pred v)) :
    Γ ⊢[PRAAx] le u w := by
  have e₁ := natEq h
  have e₂ := natEq hv
  ipra_le 𝔟 u * 𝔟 (pred v) using linear_combination 𝔟 u * e₂ - e₁

/-! ## The lower terms -/

/-- `c(k, snd y) · (fst y)^k`: the term `c_k M^k` with the parameter `y = ⟨M, x⟩`. -/
def tmB (c : PTm 2) : PTm 2 := rdB c * pw (fstT (var 1)) (var 0)

theorem inst2_tmB (c : PTm 2) (k y : PTm n) :
    inst2 (tmB c) k y = inst2 (rdB c) k y * pw (fstT y) k := by
  simp [inst2, tmB]

theorem tm_at (c : PTm 2) (k M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (tmB c) k (pairT M x) ≐ inst2 c k x * pw M k := by
  rw [inst2_tmB, inst2_rdB]
  exact congrMul (congrInst2 c (.eqRefl k) (snd_pair M x)) (congrAp2 powF (.eqRefl k) (fst_pair M x))

/-- The invariant of `lower_terms` at length `s`. -/
abbrev LowerInv (c : PTm 2) (M' x s : PTm n) : Fm PTm n :=
  le (succ M' * ap2 (sumF (tmB c)) s (pairT (succ M') x)) (ap2 (sumF c) s x * pw (succ M') s)

theorem lower_base (c : PTm 2) (M' x : PTm n) : Γ ⊢[PRAAx] LowerInv c M' x zero := by
  have z₁ := natEq (sum_zero (Γ := Γ) (tmB c) (pairT (succ M') x))
  have z₂ := natEq (sum_zero (Γ := Γ) c x)
  ipra_le 0 using rw [z₁, z₂]; ring

theorem lower_step {c : PTm 2} {M' x s : PTm n} (ih : Γ ⊢[PRAAx] LowerInv c M' x s) :
    Γ ⊢[PRAAx] LowerInv c M' x (succ s) := by
  have es₁ := natEq ((sum_succ' (Γ := Γ) (tmB c) s (pairT (succ M') x)).eqTrans
    (congrAdd (.eqRefl _) (tm_at c s (succ M') x)))
  have es₂ := natEq (sum_succ' (Γ := Γ) c s x)
  have ep := natEq (pw_succ (Γ := Γ) (succ M') s)
  ipra_le sl ih + 𝔟 (ap2 (sumF c) s x) * 𝔟 (pw (succ M') s) * 𝔟 M' using rw [es₁, es₂, ep]; ring

theorem lower_all (c : PTm 2) (M' x : PTm n) :
    Γ ⊢[PRAAx] Fm.all (LowerInv c (Syn.shift M') (Syn.shift x) (var 0)) := by
  refine PRA.qfInd _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact lower_base c M' x
  · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
      subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact lower_step Prf.hyp0

/-- `M · ∑_{k<s} c_k M^k ≤ (∑_{k<s} c_k) · M^s` for `M = M′ + 1`. -/
theorem lower_terms (c : PTm 2) (M' x s : PTm n) : Γ ⊢[PRAAx] LowerInv c M' x s := by
  have a := Prf.allE s (lower_all (Γ := Γ) c M' x)
  simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact a

/-! ## Dominance of the leading term -/

/-- `eq:split-dominance`, multiplied by `M`: `M · M^s ≤ M V + (∑_{k<s} c_k) M^s`. -/
theorem dominance {c : PTm 2} {M' x s V : PTm n}
    (hl : Γ ⊢[PRAAx] le (pw (succ M') s) (V + ap2 (sumF (tmB c)) s (pairT (succ M') x))) :
    Γ ⊢[PRAAx] le (succ M' * pw (succ M') s) (succ M' * V + ap2 (sumF c) s x * pw (succ M') s) := by
  have lt := lower_terms (Γ := Γ) c M' x s
  ipra_le (𝔟 M' + 1) * sl hl + sl lt

/-- No large root: if `V = 0`, then `M ≤ ∑_{k<s} c_k`. -/
theorem no_large_root {c : PTm 2} {M' x s V : PTm n}
    (hl : Γ ⊢[PRAAx] le (pw (succ M') s) (V + ap2 (sumF (tmB c)) s (pairT (succ M') x)))
    (hV : Γ ⊢[PRAAx] V ≐ zero) : Γ ⊢[PRAAx] le (succ M') (ap2 (sumF c) s x) := by
  have hd := dominance hl
  have e := natEq (pw_pos (Γ := Γ) M' s)
  have k := natEq hV
  have h : Γ ⊢[PRAAx] le (succ (pred (pw (succ M') s)) * succ M')
      (succ (pred (pw (succ M') s)) * ap2 (sumF c) s x) := by
    ipra_le sl hd using
      linear_combination (-(𝔟 (ap2 (sumF c) s x) - (𝔟 M' + 1))) * e - (𝔟 M' + 1) * k
  exact mul_le_cancel h

end LeanProofs.IPRA.Foundations.SplitBranches
