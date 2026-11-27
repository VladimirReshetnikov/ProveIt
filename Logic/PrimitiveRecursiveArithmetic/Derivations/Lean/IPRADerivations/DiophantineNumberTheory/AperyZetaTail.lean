import IPRADerivations.Core.OrderCertificates
import IPRADerivations.AnalyticNumberTheory.PhiLower

/-!
# Finite zeta tails

Packet: `diophantine-number-theory/apery_ipra`, `apery_ipra.tex`, Lemma `lem:zeta-tail` ("Finite zeta tails"):
for `T ≥ M ≥ 1`, `0 ≤ Z_T − Z_M ≤ 1/(2M²)`, where `Z_N = ∑_{t ≤ N} 1/t³`. "For `t ≥ 2`,
`1/t³ ≤ ½ (1/(t−1)² − 1/t²)`. After multiplication by `2t³(t−1)²`, the difference of the right numerator and
the left numerator is `3t − 2 ≥ 0`. Sum from `t = M+1` to `T`; the right side telescopes."

Denominators are cleared by a common multiple `F` with exact quotients (the convention of
`Analysis/BaselAverages`): `u(i) = F/(M+1+i)³` and `v(i) = F/(2(M+i)²)`, given by the equations
`(M+1+i)³ u(i) = F` and `2 (M+i)² v(i) = F`.

* `term_le`: from `t³ q = F`, `2t² p = F`, `2s² p' = F` with `t = s + 1`, `s ≥ 1`: `q + p ≤ p'`
  (the slack after multiplying by `W = 2t³s²` is `F (3s + 1)`, the paper's `3t − 2`; then `W` is cancelled);
* `telescope` (generic): if `u(i) + v(i+1) ≤ v(i)` for `i < r`, then `∑_{i<r} u(i) + v(r) ≤ v(0)`;
* `zeta_tail` (`eq:zeta-tail`, with `T = M + r`): `2M² ∑_{i<r} u(i) ≤ F`, i.e.
  `Z_T − Z_M ≤ 1/(2M²)`; nonnegativity is that of natural numbers.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyZetaTail

open_ipra exports

variable {k : ℕ} {Γ : List (Fm PTm k)}

set_option hygiene false in
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

@[simp] theorem subst_two' {m : ℕ} (σ : Fin k → PTm m) : Syn.subst σ (two : PTm k) = two := by
  simp only [two, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- One term: `t³ q = F`, `2t² p = F`, `2s² p' = F` with `t = s + 1` and `s ≥ 1` give `q + p ≤ p'`. -/
theorem term_le {s q p p' F : PTm k} (hs : Γ ⊢[PRAAx] le one s)
    (hq : Γ ⊢[PRAAx] succ s * succ s * succ s * q ≐ F) (hp : Γ ⊢[PRAAx] two * succ s * succ s * p ≐ F)
    (hp' : Γ ⊢[PRAAx] two * s * s * p' ≐ F) : Γ ⊢[PRAAx] le (q + p) p' := by
  -- `W = 2 t³ s² ≥ 1`
  have ht : Γ ⊢[PRAAx] le one (succ s) := by ipra_le 𝔞 s
  have hW : Γ ⊢[PRAAx] le one (two * (succ s * succ s * succ s) * (s * s)) := by
    have a := le_mul_mono (le_mul_mono ht ht) ht
    have b := le_mul_mono hs hs
    have c := le_mul_mono a b
    ipra_le 2 * sl c + 1
  refine .orE (zero_or_succ (two * (succ s * succ s * succ s) * (s * s))) ?_ ?_
  · have h0 : ((two * (succ s * succ s * succ s) * (s * s) ≐ zero) :: Γ) ⊢[PRAAx]
        two * (succ s * succ s * succ s) * (s * s) ≐ zero := Prf.hyp0
    exact not_succ_le_self zero _ (le_congr (.eqRefl _) h0 hW.wk)
  · have hw : ((two * (succ s * succ s * succ s) * (s * s) ≐
        succ (pred (two * (succ s * succ s * succ s) * (s * s)))) :: Γ) ⊢[PRAAx]
        two * (succ s * succ s * succ s) * (s * s) ≐ succ (pred (two * (succ s * succ s * succ s) * (s * s))) :=
      Prf.hyp0
    refine mul_le_cancel (d' := pred (two * (succ s * succ s * succ s) * (s * s))) ?_
    refine le_of_eq_add (d := F * (num 3 * s + one)) ?_
    have ew := natEq hw
    have eq := natEq (hq.wk : ((two * (succ s * succ s * succ s) * (s * s) ≐
        succ (pred (two * (succ s * succ s * succ s) * (s * s)))) :: Γ) ⊢[PRAAx] _)
    have ep := natEq (hp.wk : ((two * (succ s * succ s * succ s) * (s * s) ≐
        succ (pred (two * (succ s * succ s * succ s) * (s * s)))) :: Γ) ⊢[PRAAx] _)
    have ep' := natEq (hp'.wk : ((two * (succ s * succ s * succ s) * (s * s) ≐
        succ (pred (two * (succ s * succ s * succ s) * (s * s)))) :: Γ) ⊢[PRAAx] _)
    apply deriveNat; ipra_simps
    linear_combination (𝔟 p - 𝔟 p' + 𝔟 q) * ew - (2 * 𝔟 s * 𝔟 s) * eq - (𝔟 s * 𝔟 s * 𝔟 s + 𝔟 s * 𝔟 s) * ep +
      ((𝔟 s + 1) * (𝔟 s + 1) * (𝔟 s + 1)) * ep'

/-- Generic telescoping: `u(i) + v(i+1) ≤ v(i)` for `i < r` gives `∑_{i<r} u(i) + v(r) ≤ v(0)`. -/
theorem telescope (u v : PTm 2) {x r : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (Syn.var 0) (Syn.shift r) ⟶
      le (inst2 u (Syn.var 0) (Syn.shift x) + inst2 v (succ (Syn.var 0)) (Syn.shift x))
        (inst2 v (Syn.var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF u) r x + inst2 v r x) (inst2 v zero x) := by
  let invariant := le (ap2 (sumF u) (Syn.var 0) (Syn.shift x) + inst2 v (Syn.var 0) (Syn.shift x))
    (inst2 v zero (Syn.shift x))
  suffices result : Γ ⊢[PRAAx] invariant.subst (Syn.inst r) by simpa [invariant] using result
  refine qfIndUpTo r (le_QF _ _) ?_ ?_
  · simpa [invariant] using le_congr
      ((congrAdd (sum_zero (Γ := Γ) u x) (.eqRefl _)).eqTrans (zero_add _)).eqSymm (.eqRefl _) (le_refl (inst2 v zero x))
  · simp [invariant]
    refine .impI ?_
    let Δ := lt (Syn.var 0) (Syn.shift r) :: invariant :: Γ.map Fm.shift
    have ih : Δ ⊢[PRAAx] invariant := Prf.hyp1
    have st := Prf.impE h.allOpen.wk.wk (Prf.hyp0 : Δ ⊢[PRAAx] lt (Syn.var 0) (Syn.shift r))
    have es := natEq (sum_succ' (Γ := Δ) u (Syn.var 0) (Syn.shift x))
    ipra_le sl ih + sl st using rw [es]; ring

/-- `eq:zeta-tail` with `M = M' + 1`, `T = M + r`: if `(M+1+i)³ u(i) = F` for `i < r` and
`2 (M+i)² v(i) = F` for `i ≤ r`, then `2M² ∑_{i<r} u(i) ≤ F`, i.e. `Z_T − Z_M ≤ 1/(2M²)`. -/
theorem zeta_tail (u v : PTm 2) {x r M' F : PTm k}
    (hu : Γ ⊢[PRAAx] Fm.all (lt (Syn.var 0) (Syn.shift r) ⟶
      succ (succ (Syn.shift M') + Syn.var 0) * succ (succ (Syn.shift M') + Syn.var 0) *
        succ (succ (Syn.shift M') + Syn.var 0) * inst2 u (Syn.var 0) (Syn.shift x) ≐ Syn.shift F))
    (hv : Γ ⊢[PRAAx] Fm.all (le (Syn.var 0) (Syn.shift r) ⟶
      two * (succ (Syn.shift M') + Syn.var 0) * (succ (Syn.shift M') + Syn.var 0) *
        inst2 v (Syn.var 0) (Syn.shift x) ≐ Syn.shift F)) :
    Γ ⊢[PRAAx] le (two * succ M' * succ M' * ap2 (sumF u) r x) F := by
  have step : Γ ⊢[PRAAx] Fm.all (lt (Syn.var 0) (Syn.shift r) ⟶
      le (inst2 u (Syn.var 0) (Syn.shift x) + inst2 v (succ (Syn.var 0)) (Syn.shift x))
        (inst2 v (Syn.var 0) (Syn.shift x))) := by
    refine .allI (.impI ?_)
    let Δ : List (Fm PTm (k + 1)) := lt (Syn.var 0) (Syn.shift r) :: Γ.map Fm.shift
    have hl : Δ ⊢[PRAAx] lt (Syn.var 0) (Syn.shift r) := Prf.hyp0
    have hl' : Δ ⊢[PRAAx] le (succ (Syn.var 0)) (Syn.shift r) := hl
    have hs : Δ ⊢[PRAAx] le one (succ (Syn.shift M') + Syn.var 0) := by
      ipra_le 𝔟 (Syn.shift M') + 𝔟 (Syn.var 0)
    have hq := Prf.impE hu.allOpen.wk hl
    have hp' := Prf.impE hv.allOpen.wk (le_trans (le_succ_self _) hl')
    have hv1 : Γ.map Fm.shift ⊢[PRAAx] (le (succ (Syn.var 0)) (Syn.shift r) ⟶
        two * (succ (Syn.shift M') + succ (Syn.var 0)) * (succ (Syn.shift M') + succ (Syn.var 0)) *
          inst2 v (succ (Syn.var 0)) (Syn.shift x) ≐ Syn.shift F) := by
      have a := Prf.allE (succ (Syn.var 0)) hv.shift
      simp [Fm.shift, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst, subst_le,
        subst_inst2] at a
      exact a
    have hp0 := Prf.impE hv1.wk hl'
    have e : Δ ⊢[PRAAx] succ (succ (Syn.shift M') + Syn.var 0) ≐ succ (Syn.shift M') + succ (Syn.var 0) :=
      (add_succ _ _).eqSymm
    have hp : Δ ⊢[PRAAx] two * succ (succ (Syn.shift M') + Syn.var 0) * succ (succ (Syn.shift M') + Syn.var 0) *
        inst2 v (succ (Syn.var 0)) (Syn.shift x) ≐ Syn.shift F :=
      (congrMul (congrMul (congrMul (.eqRefl _) e) e) (.eqRefl _)).eqTrans hp0
    exact term_le hs hq hp hp'
  have t := telescope u v step
  have h0 := Prf.allE zero hv
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_inst2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, subst_two'] at h0
  have e0 := natEq (Prf.impE h0 (zero_le r))
  ipra_le 2 * (𝔞 M' + 1) * (𝔞 M' + 1) * sl t + 2 * (𝔞 M' + 1) * (𝔞 M' + 1) * 𝔞 (inst2 v r x) using
    linear_combination -e0

end LeanProofs.IPRA.DiophantineNumberTheory.AperyZetaTail
