import IPRADerivations.Algebra.DescentPigeonhole
import IPRADerivations.Probability.Lotus
import IPRADerivations.Core.SumPalindrome
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.Core.ProdLemmas

/-!
# Geometric domination of the other terms

Packet: `algebra/FTA_iPRA` (`lem:descent`, `eq:other-terms`): if the term of index `k` dominates at
three consecutive scales, then `|b_i| r^i ≤ 4^{−(k−i)} V` for `i < k` and `≤ 4^{−(i−k)} V` for
`i > k`, so the other terms total at most `(2/3) V`, "each of the two finite geometric sums [being]
at most `1/3`". Cleared of the powers of `4`, for natural-number terms `T_i`:

* `geom4`: `3 ∑_{i<K} 4^i + 1 = 4^K`;
* `geo_dom`: if `4^{K−i} T_i ≤ V` for `i < K`, then `3 ∑_{i<K} T_i ≤ V` (the terms below `k`);
* `geo_dom_up`: if `4^{j+1} T_j ≤ V` for `j < K`, then `3 ∑_{j<K} T_j ≤ V` (the terms above `k`,
  indexed by `j = i − k − 1`), by reflecting the sum;
* `other_terms`: both together, `3 (∑ below + ∑ above) ≤ 2V`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.DescentDomination

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

abbrev four {n : ℕ} : PTm n := two * two

/-- `4^i`. -/
abbrev p4B : PTm 2 := pw four (var 0)

theorem inst2_p4 (i x : PTm n) : inst2 p4B i x = pw four i := by simp [inst2]

/-! ## The geometric sum -/

theorem geom4_step {K x : PTm n}
    (ih : Γ ⊢[PRAAx] (two + one) * ap2 (sumF p4B) K x + one ≐ pw four K) :
    Γ ⊢[PRAAx] (two + one) * ap2 (sumF p4B) (succ K) x + one ≐ pw four (succ K) := by
  have s := sum_succ' (Γ := Γ) p4B K x
  rw [inst2_p4] at s
  have a := natEq s; have i := natEq ih; have p := natEq (pw_succ (Γ := Γ) four K)
  apply deriveNat; ipra_simps
  linear_combination 3 * a + 4 * i - p - 3 * i

/-- Variables: `0 = K` (induction), `1 = x`. -/
private abbrev g4F : Fm PTm 2 := (two + one) * ap2 (sumF p4B) (var 0) (var 1) + one ≐ pw four (var 0)

private theorem g4₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] g4F := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have z := natEq (sum_zero (Γ := []) p4B (var 0 : PTm 1))
    have p := natEq (pw_zero (Γ := []) (four : PTm 1))
    apply deriveNat; ipra_simps; linear_combination 3 * z - p
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact geom4_step Prf.hyp0

/-- `3 ∑_{i<K} 4^i + 1 = 4^K`. -/
theorem geom4 (K x : PTm n) : Γ ⊢[PRAAx] (two + one) * ap2 (sumF p4B) K x + one ≐ pw four K := by
  have h := inst (Γ := Γ) g4₀ (![K, x] : Fin 2 → PTm n)
  simpa using h

/-! ## Domination below -/

theorem four_pos : Γ ⊢[PRAAx] (four : PTm n) ≐ succ (pred four) :=
  pos_of_eq_succ (c := succ (succ (succ zero))) (by apply deriveNat; ipra_simps; ring)

theorem dom_pt {i K V t : PTm n} (hi : Γ ⊢[PRAAx] lt i K) (hh : Γ ⊢[PRAAx] le (pw four (monus K i) * t) V) :
    Γ ⊢[PRAAx] le (pw four K * t) (V * pw four i) := by
  have eK : Γ ⊢[PRAAx] K ≐ monus K i + i := (eq_add_of_le (le_of_lt hi)).eqTrans (add_comm _ _)
  have e : Γ ⊢[PRAAx] pw four K * t ≐ (pw four (monus K i) * t) * pw four i := by
    have a := natEq ((congrAp2 powF eK (.eqRefl four)).eqTrans (pw_add (Γ := Γ) four (monus K i) i))
    apply deriveNat; ipra_simps; linear_combination 𝔞(t) * a
  exact le_congr e.eqSymm (.eqRefl _) (mul_le_mul_right (pw four i) hh)

/-- If `4^{K−i} T_i ≤ V` for `i < K`, then `3 ∑_{i<K} T_i ≤ V`. -/
theorem geo_dom (T : PTm 2) (K V x : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift K) ⟶
      le (pw four (monus (Syn.shift K) (var 0)) * inst2 T (var 0) (Syn.shift x)) (Syn.shift V))) :
    Γ ⊢[PRAAx] le ((two + one) * ap2 (sumF T) K x) V := by
  have P : Γ ⊢[PRAAx] le (ap2 (sumF (cmB T)) K (pairT (pw four K) x)) (ap2 (sumF (cmB p4B)) K (pairT V x)) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    have e₁ : Syn.shift (pairT (pw four K) x) = pairT (pw four (Syn.shift K)) (Syn.shift x) := by simp [Syn.shift]
    have e₂ : Syn.shift (pairT V x) = pairT (Syn.shift V) (Syn.shift x) := by simp [Syn.shift]
    rw [e₁, e₂, inst2_cmB, inst2_cmB, inst2_p4]
    have hh := Prf.impE h.allOpen.wk Prf.hyp0
    refine le_congr (congrMul (fst_pair _ _).eqSymm (congrInst2 T (.eqRefl _) (snd_pair _ _)).eqSymm)
      (congrMul (fst_pair _ _).eqSymm (.eqRefl _)) ?_
    exact dom_pt Prf.hyp0 hh
  have L := le_congr (sum_const_mul T K (pw four K) x) (sum_const_mul p4B K V x) P
  have L₂ := mul_le_mul_right (two + one) L
  have g := natEq (geom4 (Γ := Γ) K x)
  have e : Γ ⊢[PRAAx] V * ap2 (sumF p4B) K x * (two + one) + V ≐ pw four K * V := by
    apply deriveNat; ipra_simps; linear_combination 𝔞(V) * g
  have L₃ := le_trans L₂ (le_congr (.eqRefl _) e (le_add_right _ _))
  have pp := pw_pos' (four_pos (Γ := Γ)) K
  refine mul_le_cancel (d' := pred (pw four K)) (le_congr ?_ ?_ L₃)
  · have a := natEq pp
    apply deriveNat; ipra_simps; linear_combination (3 * 𝔞(ap2 (sumF T) K x)) * a
  · have a := natEq pp
    apply deriveNat; ipra_simps; linear_combination 𝔞(V) * a

/-! ## Domination above -/

theorem monus_pred {v K : PTm n} (hv : Γ ⊢[PRAAx] lt v K) : Γ ⊢[PRAAx] monus K v ≐ succ (monus K (succ v)) := by
  have e := natEq (eq_add_of_le hv)
  have a : Γ ⊢[PRAAx] K ≐ succ (monus K (succ v)) + v := by apply deriveNat; ipra_simps; linear_combination e
  exact (congrMonus a (.eqRefl _)).eqTrans (add_monus _ _)

theorem lt_rfl {v K : PTm n} (hv : Γ ⊢[PRAAx] lt v K) : Γ ⊢[PRAAx] lt (monus K (succ v)) K := by
  have e := natEq (eq_add_of_le hv)
  refine le_of_eq_add (d := v) ?_
  apply deriveNat; ipra_simps; linear_combination e

/-- If `4^{j+1} T_j ≤ V` for `j < K`, then `3 ∑_{j<K} T_j ≤ V`. -/
theorem geo_dom_up (T : PTm 2) (K V x : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift K) ⟶
      le (pw four (succ (var 0)) * inst2 T (var 0) (Syn.shift x)) (Syn.shift V))) :
    Γ ⊢[PRAAx] le ((two + one) * ap2 (sumF T) K x) V := by
  refine le_congr (congrMul (.eqRefl _) (sum_reflect T K x)).eqSymm (.eqRefl _) (geo_dom (rflBody T) K V (pairT K x) ?_)
  refine .allI (.impI ?_)
  have e₁ : Syn.shift (pairT K x) = pairT (Syn.shift K) (Syn.shift x) := by simp [Syn.shift]
  rw [e₁, inst2_rflBody]
  have hv : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift K) := Prf.hyp0
  have a := Prf.allE (monus (Syn.shift K) (succ (var 0))) h.shift
  simp only [Fm.shift, Fm.subst_all, Fm.subst_imp, Fm.subst_eq, subst_le, subst_lt, subst_inst2, subst_ap2,
    PTm.subst_mul, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Syn.up_zero, Syn.inst_zero, subst_up_shift_pal, Syn.subst_inst_shift] at a
  have hh := Prf.impE a.wk (lt_rfl hv)
  refine le_congr (congrMul (congrAp2 powF (monus_pred hv).eqSymm (.eqRefl four))
    (congrInst2 T (congrMonus (fst_pair _ _) (.eqRefl _)).eqSymm (snd_pair _ _).eqSymm)) (.eqRefl _) hh

/-- `eq:other-terms`, cleared: the terms below and above the dominant index contribute
`3 (∑ below + ∑ above) ≤ 2V`. -/
theorem other_terms (L U : PTm 2) (k m V x : PTm n)
    (hlo : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift k) ⟶
      le (pw four (monus (Syn.shift k) (var 0)) * inst2 L (var 0) (Syn.shift x)) (Syn.shift V)))
    (hup : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      le (pw four (succ (var 0)) * inst2 U (var 0) (Syn.shift x)) (Syn.shift V))) :
    Γ ⊢[PRAAx] le ((two + one) * (ap2 (sumF L) k x + ap2 (sumF U) m x)) (V + V) :=
  le_congr (by apply deriveNat; ipra_simps; ring) (.eqRefl _)
    (add_le_add₂ (geo_dom L k V x hlo) (geo_dom_up U m V x hup))

end LeanProofs.IPRA.Algebra.DescentDomination
