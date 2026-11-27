import IPRADerivations.AnalyticNumberTheory.SymmetricProduct
import IPRADerivations.Topology.CollisionScales
import IPRADerivations.AnalyticNumberTheory.BlockChain

/-!
# The harmonic budget and the logarithm absorption (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "The sum of the absolute values up to `2^j` is at most `(j+1)X` … In each subsequent block
`2^j < d ≤ 2^{j+1}`, every term satisfies `2^j|t_d| ≤ X` and there are `2^j` terms. Add those inequalities and
cancel the positive factor `2^j`." and "write `ℓ = kz + s` with `s < k`. Since `z + 1 ≤ 2^z`, we have
`ℓ + 2 ≤ 2k(z+1) ≤ 2k 2^z`. Raising to the `k`th power and using `kz ≤ ℓ` yields `(ℓ+2)^k ≤ (2k)^k N`."

For a body `v(i, z)` with `(i+1) v(i, z) ≤ X` for every `i` (`Budget`):

* `block_tail`: `M · Σ_{i<M} v(M + i) ≤ M · X` (every term of the block has weight `≥ M`);
* `dyadic_budget`: `Σ_{i<2^e} v(i) ≤ (e+1) X`, by quantifier-free induction on `e`, splitting `2^{e+1} = 2^e + 2^e`
  and cancelling `2^e ≥ 1` in `block_tail` (`mul_le_cancel`);
* `budget_below`: the cut-off form used by the theorem: if `(i+1) u(i, y) ≤ X` only for `i < N` and `N ≤ 2^e`, then
  `Σ_{i<N} u(i, y) ≤ (e+1) X` (the masked body `u(i, y)·sg(N ∸ i)` satisfies `Budget`);
* `log_absorb`: `(e+2)^k ≤ (2k)^k 2^e` for `k ≥ 1`, through `e = kz + s` (`div_mod_at`), `z + 1 ≤ 2^z`
  (`lt_pw_two`), `(ab)^k = a^k b^k` (`pw_mul_base`), `(2^z)^k = 2^{zk}` (`pw_mul`) and `zk ≤ e` (`pw_le_exp`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerBudget

open_ipra exports
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.Foundations.IntervalPacking (sg_one_of_lt)
open LeanProofs.IPRA.Topology.CollisionScales (lt_pw_two)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Signum (sg sg_zero)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias mul_one' := Common.mul_one_right

/-! ## The dyadic budget -/

section Dyadic

variable (v : PTm 2)

/-- The hypothesis `(i+1) v(i, z) ≤ X` for every `i`. -/
abbrev Budget (z X : PTm n) : Fm PTm n :=
  Fm.all (le (succ (var 0) * inst2 v (var 0) (Syn.shift z)) (Syn.shift X))

theorem budget_shift (z X : PTm n) : Fm.shift (Budget v z X) = Budget v (Syn.shift z) (Syn.shift X) := by
  ipra_ind_simp [Budget, Fm.shift, Fm.subst_all, subst_le, Syn.up_zero, subst_inst2, subst_up_shift_pal]
  rfl

theorem budget_at {z X : PTm n} (hv : Γ ⊢[PRAAx] Budget v z X) (t : PTm n) :
    Γ ⊢[PRAAx] le (succ t * inst2 v t z) X := by
  have h := Prf.allE t hv
  simpa [Budget, subst_le, Syn.subst_inst_shift] using h

/-- Every term of the block `[M, 2M)` has weight at least `M`: `M · Σ_{i<M} v(M + i) ≤ M · X`. -/
theorem block_tail {z X : PTm n} (hv : Γ ⊢[PRAAx] Budget v z X) (M : PTm n) :
    Γ ⊢[PRAAx] le (M * ap2 (sumF (offB v)) M (pairT M z)) (M * X) := by
  have c := sum_const_mul (Γ := Γ) (offB v) M M (pairT M z)
  refine le_congr c (.eqRefl _) (sum_le_const (cmB (offB v)) (.allI (.impI ?_)))
  have hv' : (Γ.map Fm.shift) ⊢[PRAAx] Budget v (Syn.shift z) (Syn.shift X) := by
    have a := hv.shift
    rw [budget_shift] at a
    exact a
  rw [show Syn.shift (pairT M (pairT M z)) = pairT (Syn.shift M) (pairT (Syn.shift M) (Syn.shift z)) by
    simp [Syn.shift], inst2_cmB, inst2_offB]
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
  have e1 : Θ ⊢[PRAAx] fstT (pairT (Syn.shift M) (pairT (Syn.shift M) (Syn.shift z))) ≐ Syn.shift M := fst_pair _ _
  have e2 : Θ ⊢[PRAAx] inst2 v (fstT (sndT (pairT (Syn.shift M) (pairT (Syn.shift M) (Syn.shift z)))) + var 0)
      (sndT (sndT (pairT (Syn.shift M) (pairT (Syn.shift M) (Syn.shift z))))) ≐
      inst2 v (Syn.shift M + var 0) (Syn.shift z) :=
    congrInst2 v (congrAdd ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) (.eqRefl _))
      ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  have hb := budget_at (Γ := Θ) v (hv'.wk : Θ ⊢[PRAAx] _) (Syn.shift M + var 0)
  have hw : Θ ⊢[PRAAx] le (Syn.shift M * inst2 v (Syn.shift M + var 0) (Syn.shift z))
      (succ (Syn.shift M + var 0) * inst2 v (Syn.shift M + var 0) (Syn.shift z)) :=
    mul_le_mul_right _ (by ipra_le 𝔞 (var 0) + 1)
  exact le_congr (congrMul e1 e2).eqSymm (.eqRefl _) (le_trans hw hb)

/-- `Σ_{i<2^e} v(i, z) ≤ (e+1) X`. -/
theorem dyadic_budget {z X : PTm n} (hv : Γ ⊢[PRAAx] Budget v z X) (e : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF v) (pw two e) z) (succ e * X) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (ap2 (sumF v) (pw two (var 0)) (Syn.shift z)) (succ (var 0) * Syn.shift X)) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_ap2]
    · have s1 : Γ ⊢[PRAAx] ap2 (sumF v) (pw two zero) z ≐ ap2 (sumF v) one z :=
        congrAp2 (sumF v) (pw_zero two) (.eqRefl _)
      have s2 : Γ ⊢[PRAAx] ap2 (sumF v) one z ≐ ap2 (sumF v) zero z + inst2 v zero z := sum_succ v zero z
      have s3 : Γ ⊢[PRAAx] ap2 (sumF v) zero z ≐ zero := sum_zero v z
      have h0 := budget_at v hv zero
      have f1 := natEq s1
      have f2 := natEq s2
      have f3 := natEq s3
      ipra_le sl h0 with -f1 - f2 - f3
    · let φ : Fm PTm (n + 1) := le (ap2 (sumF v) (pw two (var 0)) (Syn.shift z)) (succ (var 0) * Syn.shift X)
      let Δ : List (Fm PTm (n + 1)) := φ :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] φ := Prf.hyp0
      have hv' : Δ ⊢[PRAAx] Budget v (Syn.shift z) (Syn.shift X) := by
        have a := hv.shift
        rw [budget_shift] at a
        exact a.wk
      have hP : Δ ⊢[PRAAx] (pw two (var 0)) ≐ succ (pred (pw two (var 0))) := pos_of_one_le (one_le_pw' (by ipra_le 1) _)
      have hsplit : Δ ⊢[PRAAx] pw two (succ (var 0)) ≐ (pw two (var 0)) + (pw two (var 0)) :=
        (pw_succ two (var 0)).eqTrans (by ipra_ring)
      have sp : Δ ⊢[PRAAx] ap2 (sumF v) (pw two (succ (var 0))) (Syn.shift z) ≐
          ap2 (sumF v) (pw two (var 0)) (Syn.shift z) + ap2 (sumF (offB v)) (pw two (var 0)) (pairT (pw two (var 0)) (Syn.shift z)) :=
        (congrAp2 (sumF v) hsplit (.eqRefl _)).eqTrans (sum_split v (pw two (var 0)) (pw two (var 0)) (Syn.shift z))
      have bt := block_tail v hv' (pw two (var 0))
      have bt' : Δ ⊢[PRAAx] le (succ (pred (pw two (var 0))) * ap2 (sumF (offB v)) (pw two (var 0)) (pairT (pw two (var 0)) (Syn.shift z)))
          (succ (pred (pw two (var 0))) * Syn.shift X) :=
        le_congr (congrMul hP (.eqRefl _)) (congrMul hP (.eqRefl _)) bt
      have tl := mul_le_cancel bt'
      have f := natEq sp
      ipra_le sl ih + sl tl with -f
  have h := Prf.allE e hall
  simpa [subst_le, Syn.subst_inst_shift] using h

end Dyadic

/-! ## The cut-off budget -/

section Cutoff

variable (u : PTm 2)

/-- The masked body `u(i, y) · sg(N ∸ i)` over `0 = i`, `1 = ⟨N, y⟩`. -/
def maskB : PTm 2 := Syn.subst ![var 0, sndT (var 1)] u * sg (monus (fstT (var 1)) (var 0))

theorem inst2_maskB (i P : PTm n) : inst2 (maskB u) i P = inst2 u i (sndT P) * sg (monus (fstT P) i) := by
  simp only [inst2, maskB, PTm.subst_mul, PTm.subst_monus, subst_reindex2]
  simp

theorem maskB_at (i N y : PTm n) :
    Γ ⊢[PRAAx] inst2 (maskB u) i (pairT N y) ≐ inst2 u i y * sg (monus N i) := by
  rw [inst2_maskB]
  exact congrMul (congrInst2 u (.eqRefl _) (snd_pair _ _)) (congrSg (congrMonus (fst_pair _ _) (.eqRefl _)))

/-- The hypothesis `(i+1) u(i, y) ≤ X` for every `i < N`. -/
abbrev BudgetBelow (N y X : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ le (succ (var 0) * inst2 u (var 0) (Syn.shift y)) (Syn.shift X))

theorem mask_budget {N y X : PTm n} (hu : Γ ⊢[PRAAx] BudgetBelow u N y X) :
    Γ ⊢[PRAAx] Budget (maskB u) (pairT N y) X := by
  refine .allI ?_
  rw [show Syn.shift (pairT N y) = pairT (Syn.shift N) (Syn.shift y) by simp [Syn.shift]]
  have hm := maskB_at (Γ := Γ.map Fm.shift) u (var 0) (Syn.shift N) (Syn.shift y)
  refine .orE (lt_or_le (var 0) (Syn.shift N)) ?_ ?_
  · let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have hlt : Θ ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
    have hb : Θ ⊢[PRAAx] le (succ (var 0) * inst2 u (var 0) (Syn.shift y)) (Syn.shift X) :=
      Prf.impE hu.allOpen.wk hlt
    have e : Θ ⊢[PRAAx] inst2 (maskB u) (var 0) (pairT (Syn.shift N) (Syn.shift y)) ≐
        inst2 u (var 0) (Syn.shift y) :=
      hm.wk.eqTrans ((congrMul (.eqRefl _) (sg_one_of_lt hlt)).eqTrans (mul_one' _))
    exact le_congr (congrMul (.eqRefl _) e).eqSymm (.eqRefl _) hb
  · let Θ : List (Fm PTm (n + 1)) := le (Syn.shift N) (var 0) :: Γ.map Fm.shift
    have hle : Θ ⊢[PRAAx] monus (Syn.shift N) (var 0) ≐ zero := Prf.hyp0
    have e : Θ ⊢[PRAAx] inst2 (maskB u) (var 0) (pairT (Syn.shift N) (Syn.shift y)) ≐ zero :=
      hm.wk.eqTrans ((congrMul (.eqRefl _) ((congrSg hle).eqTrans sg_zero)).eqTrans (mul_zero _))
    have z : Θ ⊢[PRAAx] succ (var 0) * inst2 (maskB u) (var 0) (pairT (Syn.shift N) (Syn.shift y)) ≐ zero :=
      (congrMul (.eqRefl _) e).eqTrans (mul_zero _)
    exact le_congr z.eqSymm (.eqRefl _) (by ipra_le 𝔞 (Syn.shift X))

/-- `Σ_{i<N} u(i, y) ≤ (e+1) X` when `(i+1) u(i, y) ≤ X` for `i < N` and `N ≤ 2^e`. -/
theorem budget_below {N y X e : PTm n} (hu : Γ ⊢[PRAAx] BudgetBelow u N y X) (hN : Γ ⊢[PRAAx] le N (pw two e)) :
    Γ ⊢[PRAAx] le (ap2 (sumF u) N y) (succ e * X) := by
  have eq : Γ ⊢[PRAAx] ap2 (sumF u) N y ≐ ap2 (sumF (maskB u)) N (pairT N y) := by
    refine sum_congr_bounded u (maskB u) y (pairT N y) N (.allI (.impI ?_))
    rw [show Syn.shift (pairT N y) = pairT (Syn.shift N) (Syn.shift y) by simp [Syn.shift]]
    have hlt : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
    exact ((maskB_at u (var 0) (Syn.shift N) (Syn.shift y)).eqTrans
      ((congrMul (.eqRefl _) (sg_one_of_lt hlt)).eqTrans (mul_one' _))).eqSymm
  have sp := natEq ((congrAp2 (sumF (maskB u)) (eq_add_of_le hN) (.eqRefl (pairT N y))).eqTrans
    (sum_split (Γ := Γ) (maskB u) N (monus (pw two e) N) (pairT N y)))
  have db := dyadic_budget (maskB u) (mask_budget u hu) e
  have f := natEq eq
  ipra_le sl db + 𝔞 (ap2 (sumF (offB (maskB u))) (monus (pw two e) N) (pairT N (pairT N y))) with sp - f

end Cutoff

/-! ## Absorbing the logarithm -/

/-- `(e+2)^k ≤ (2k)^k 2^e` for `k ≥ 1`. -/
theorem log_absorb {k : PTm n} (hk : Γ ⊢[PRAAx] le one k) (e : PTm n) :
    Γ ⊢[PRAAx] le (pw (e + two) k) (pw (two * k) k * pw two e) := by
  have d := div_mod_at (Γ := Γ) (x := e) (y := k) (c := pred k) (pos_of_one_le hk)
  have e1 := natEq (Prf.andE₁ d)
  have r1 := Prf.andE₂ d
  have hz : Γ ⊢[PRAAx] lt (quo e k) (pw two (quo e k)) := lt_pw_two (quo e k)
  -- `e + 2 ≤ (2k)((quo e k)+1)`
  have b1 : Γ ⊢[PRAAx] le (e + two) (two * k * succ (quo e k)) := by
    ipra_le sl r1 + sl hk + 𝔞 (k * quo e k) with -e1
  have p1 := pw_le_pw k b1
  have m1 : Γ ⊢[PRAAx] pw (two * k * succ (quo e k)) k ≐ pw (two * k) k * pw (succ (quo e k)) k := pw_mul_base _ _ _
  -- `((quo e k)+1)^k ≤ (2^(quo e k))^k = 2^{zk} ≤ 2^e`
  have p2 := pw_le_pw k hz
  have m2 : Γ ⊢[PRAAx] pw (pw two (quo e k)) k ≐ pw two ((quo e k) * k) := pw_mul _ _ _
  have hzk : Γ ⊢[PRAAx] le ((quo e k) * k) e := by ipra_le 𝔞 (rem e k) with e1
  have p3 := pw_le_exp (c := two) (pos_of_one_le (by ipra_le 1)) hzk
  have p4 : Γ ⊢[PRAAx] le (pw (succ (quo e k)) k) (pw two e) := le_trans p2 (le_congr m2.eqSymm (.eqRefl _) p3)
  have p5 : Γ ⊢[PRAAx] le (pw (succ (quo e k)) k * pw (two * k) k) (pw two e * pw (two * k) k) := mul_le_mul_right _ p4
  refine le_trans p1 (le_congr (m1.eqTrans (mul_comm _ _)).eqSymm (mul_comm _ _) p5)

end LeanProofs.IPRA.AnalyticNumberTheory.PowerBudget
