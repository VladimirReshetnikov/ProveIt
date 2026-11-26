import IPRADerivations.Algebra.DescentPigeonhole
import IPRADerivations.Probability.Lotus
import IPRADerivations.Core.SumPalindrome
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Core.IntOrder

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
* `decrease`, `decrease_factor`: the final decrease, cleared by `12`: `|u| ≤ 12A − 11V`,
  `|v| ≤ 8V` give `|u + v| ≤ 12A − 3V`, and with `D V ≥ A`, `D (12A − 3V) ≤ 3A (4D − 1)`, i.e.
  `|P(z + Δ)| ≤ A − V/4 ≤ (1 − 1/(4D)) A`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.DescentDomination

open_ipra
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')

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
  ipra_lc 3 * natEq s + 4 * natEq ih - natEq (pw_succ (Γ := Γ) four K) - 3 * natEq ih

/-- Variables: `0 = K` (induction), `1 = x`. -/
private abbrev g4F : Fm PTm 2 := (two + one) * ap2 (sumF p4B) (var 0) (var 1) + one ≐ pw four (var 0)

private theorem g4₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] g4F := by
  refine ind _ trivial ?_ ?_
  · ipra_lc [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] 3 * natEq (sum_zero (Γ := []) p4B (var 0 : PTm 1)) -
      natEq (pw_zero (Γ := []) (four : PTm 1))
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact geom4_step Prf.hyp0

/-- `3 ∑_{i<K} 4^i + 1 = 4^K`. -/
theorem geom4 (K x : PTm n) : Γ ⊢[PRAAx] (two + one) * ap2 (sumF p4B) K x + one ≐ pw four K := by
  have h := inst (Γ := Γ) g4₀ (![K, x] : Fin 2 → PTm n)
  simpa using h

/-! ## Domination below -/

theorem four_pos : Γ ⊢[PRAAx] (four : PTm n) ≐ succ (pred four) :=
  pos_of_eq_succ (c := succ (succ (succ zero))) (by ipra_ring)

theorem dom_pt {i K V t : PTm n} (hi : Γ ⊢[PRAAx] lt i K) (hh : Γ ⊢[PRAAx] le (pw four (monus K i) * t) V) :
    Γ ⊢[PRAAx] le (pw four K * t) (V * pw four i) := by
  have eK : Γ ⊢[PRAAx] K ≐ monus K i + i := (eq_add_of_le (le_of_lt hi)).eqTrans (add_comm _ _)
  have e : Γ ⊢[PRAAx] pw four K * t ≐ (pw four (monus K i) * t) * pw four i := by
    ipra_lc 𝔞(t) * natEq ((congrAp2 powF eK (.eqRefl four)).eqTrans (pw_add (Γ := Γ) four (monus K i) i))
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
  have e : Γ ⊢[PRAAx] V * ap2 (sumF p4B) K x * (two + one) + V ≐ pw four K * V := by
    ipra_lc 𝔞(V) * natEq (geom4 (Γ := Γ) K x)
  have L₃ := le_trans L₂ (le_congr (.eqRefl _) e (le_add_right _ _))
  have pp := pw_pos' (four_pos (Γ := Γ)) K
  refine mul_le_cancel (d' := pred (pw four K)) (le_congr ?_ ?_ L₃)
  · have a := natEq pp
    apply deriveNat; ipra_simps; linear_combination (3 * 𝔞(ap2 (sumF T) K x)) * a
  · have a := natEq pp
    apply deriveNat; ipra_simps; linear_combination 𝔞(V) * a

/-! ## Domination above -/

alias monus_pred := Common.monus_succ_of_lt

theorem lt_rfl {v K : PTm n} (hv : Γ ⊢[PRAAx] lt v K) : Γ ⊢[PRAAx] lt (monus K (succ v)) K := by
  refine le_of_eq_add (d := v) ?_
  ipra_lc natEq (eq_add_of_le hv)

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
  le_congr (by ipra_ring) (.eqRefl _)
    (add_le_add₂ (geo_dom L k V x hlo) (geo_dom_up U m V x hup))

/-! ## The decrease -/

section Decrease

variable {A V Dd : PTm n} {x₁ y₁ x₂ y₂ : ZT n}

abbrev twelve {n : ℕ} : PTm n := num 12
abbrev eleven {n : ℕ} : PTm n := num 11
abbrev eight {n : ℕ} : PTm n := num 8
abbrev three {n : ℕ} : PTm n := num 3

/-- The decrease of the residual, cleared by `12`: with `u = 12 (b₀ + b_k Δ^k)` and `v` twelve
times the other terms, `|u| ≤ 12A − 11V` and `|v| ≤ 8V` give `|u + v| ≤ 12A − 3V`, i.e.
`|P(z + Δ)| ≤ A − V/4`, for `V ≤ A`. -/
theorem decrease (hVA : Γ ⊢[PRAAx] le V A)
    (h₁ : Γ ⊢[PRAAx] zle (ZT.sq x₁ + ZT.sq y₁) (ZT.ofNat (monus (twelve * A) (eleven * V) * monus (twelve * A) (eleven * V))))
    (h₂ : Γ ⊢[PRAAx] zle (ZT.sq x₂ + ZT.sq y₂) (ZT.ofNat ((eight * V) * (eight * V)))) :
    Γ ⊢[PRAAx] zle (ZT.sq (x₁ + x₂) + ZT.sq (y₁ + y₂))
      (ZT.ofNat (monus (twelve * A) (three * V) * monus (twelve * A) (three * V))) := by
  have t := triangle h₁ h₂
  have m₁ : Γ ⊢[PRAAx] monus (twelve * A) (eleven * V) ≐ V + twelve * monus A V := by
    have a : Γ ⊢[PRAAx] twelve * A ≐ (V + twelve * monus A V) + eleven * V := by
      ipra_lc 12 * natEq (eq_add_of_le hVA)
    exact (congrMonus a (.eqRefl _)).eqTrans (add_monus _ _)
  have m₃ : Γ ⊢[PRAAx] monus (twelve * A) (three * V) ≐ num 9 * V + twelve * monus A V := by
    have a : Γ ⊢[PRAAx] twelve * A ≐ (num 9 * V + twelve * monus A V) + three * V := by
      ipra_lc 12 * natEq (eq_add_of_le hVA)
    exact (congrMonus a (.eqRefl _)).eqTrans (add_monus _ _)
  have ab : Γ ⊢[PRAAx] monus (twelve * A) (eleven * V) + eight * V ≐ monus (twelve * A) (three * V) := by
    have a := natEq m₁; have b := natEq m₃
    apply deriveNat; ipra_simps; linear_combination a - b
  refine le_congr (.eqRefl _) ?_ t
  simp only [zle, ZT.ofNat]
  exact congrAdd (congrMul ab ab) (.eqRefl _)

/-- With `D V ≥ A` (`eq:dominant-lower`): `D (12A − 3V) ≤ 3A (4D − 1)`, i.e.
`A − V/4 ≤ (1 − 1/(4D)) A`. -/
theorem decrease_factor (hVA : Γ ⊢[PRAAx] le V A) (hD : Γ ⊢[PRAAx] le A (Dd * V)) :
    Γ ⊢[PRAAx] le (Dd * monus (twelve * A) (three * V)) (three * A * monus (num 4 * Dd) one + zero) := by
  have m : Γ ⊢[PRAAx] monus (twelve * A) (three * V) ≐ num 9 * V + twelve * monus A V := by
    have a : Γ ⊢[PRAAx] twelve * A ≐ (num 9 * V + twelve * monus A V) + three * V := by
      ipra_lc 12 * natEq (eq_add_of_le hVA)
    exact (congrMonus a (.eqRefl _)).eqTrans (add_monus _ _)
  -- `D ≥ 1` since `A ≤ D V` and, if `D = 0`, then `A = 0 = V` and both sides vanish.
  refine .orE (zero_or_succ Dd) ?_ ?_
  · have z : ((Dd ≐ zero) :: Γ) ⊢[PRAAx] Dd ≐ zero := Prf.hyp0
    exact le_trans (le_congr ((zero_mul _).eqSymm.eqTrans (congrMul z.eqSymm (.eqRefl _))) (.eqRefl _) (le_refl zero))
      (zero_le _)
  · have s : ((Dd ≐ succ (pred Dd)) :: Γ) ⊢[PRAAx] Dd ≐ succ (pred Dd) := Prf.hyp0
    have m4 : ((Dd ≐ succ (pred Dd)) :: Γ) ⊢[PRAAx] monus (num 4 * Dd) one ≐ num 3 * Dd + pred Dd := by
      have a := natEq s
      have b : ((Dd ≐ succ (pred Dd)) :: Γ) ⊢[PRAAx] num 4 * Dd ≐ (num 3 * Dd + pred Dd) + one := by
        ipra_lc 4 * a - 3 * a
      exact (congrMonus b (.eqRefl _)).eqTrans (add_monus _ _)
    have e₂ := natEq (eq_add_of_le (hD.wk (ψ := Dd ≐ succ (pred Dd))))
    have e₁ := natEq (eq_add_of_le (hVA.wk (ψ := Dd ≐ succ (pred Dd))))
    refine le_of_eq_add (d := three * monus (Dd * V) A) ?_
    have mm := natEq (m.wk (ψ := Dd ≐ succ (pred Dd))); have m4' := natEq m4; have a := natEq s
    apply deriveNat; ipra_simps
    linear_combination 3 * 𝔞(A) * m4' - 3 * 𝔞(A) * a + 12 * 𝔞(Dd) * e₁ - 𝔞(Dd) * mm + 3 * e₂

end Decrease

end LeanProofs.IPRA.Algebra.DescentDomination
