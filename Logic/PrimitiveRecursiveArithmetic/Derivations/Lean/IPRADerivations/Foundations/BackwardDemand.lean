import IPRADerivations.Foundations.MasterCertificate
import IPRADerivations.Foundations.BoundedFormulas
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# Backward schedules for nonmonotone finite observations

Packet `foundations/ipra_finite_demand`, `sections/02_backward_induction.tex`,
`thm:backward-transfer` and `cor:observational-induction`.

For a fixed `D : PR 3`, the actual primitive-recursive backward array starts
at terminal demand `K` and applies `D(N ∸ (j+1), previous, x)`. Its horizon
at stage `t` is the array entry `N ∸ t`. The schedule equations are object
equalities, including arbitrary internal endpoint and parameter values.

The observation is an arbitrary fixed bounded formula interpreted at packed
`(stage,demand,x)`. Transfer uses QF induction on the reflected observation
bit guarded by `stage ≤ N`. The local-step premise remains an external
quantified contract. No monotonicity of the demands or observations occurs.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.BackwardDemand

open_ipra
open LeanProofs.IPRA.Foundations.BoundedFormulas
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (split_lt monus_succ_of_lt)

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] private theorem subst_one {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (one : PTm n) = one := by
  simp only [one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

private alias pair_congr := Common.congrPairT

/-- Step variables are backward offset, previous demand and packed `(N,K,x)`. -/
def backwardStep (D : PR 3) : PTm 3 :=
  ap3 D (monus (fstT (var 2)) (succ (var 0))) (var 1) (sndT (sndT (var 2)))

def backwardF (D : PR 3) : PR 2 := rec2 (fstT (sndT (var 0))) (backwardStep D)

/-- The actual backward array, total also beyond the terminal horizon. -/
def backward (D : PR 3) (N K j x : PTm n) : PTm n :=
  ap2 (backwardF D) j (pairT N (pairT K x))

def horizon (D : PR 3) (N K t x : PTm n) : PTm n :=
  backward D N K (monus N t) x

@[simp] theorem subst_backward {m : ℕ} (σ : Fin n → PTm m)
    (D : PR 3) (N K j x : PTm n) :
    Syn.subst σ (backward D N K j x) =
      backward D (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ j) (Syn.subst σ x) := by
  simp only [backward, subst_ap2, subst_pairT]

@[simp] theorem subst_horizon {m : ℕ} (σ : Fin n → PTm m)
    (D : PR 3) (N K t x : PTm n) :
    Syn.subst σ (horizon D N K t x) =
      horizon D (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ t) (Syn.subst σ x) := by
  simp only [horizon, subst_backward, PTm.subst_monus]

theorem backward_zero (D : PR 3) (N K x : PTm n) :
    Γ ⊢[PRAAx] backward D N K zero x ≐ K := by
  have equation := rec2_zero (Γ := Γ) (fstT (sndT (var 0))) (backwardStep D) (pairT N (pairT K x))
  simp only [subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero] at equation
  exact equation.eqTrans ((congrFst (snd_pair N (pairT K x))).eqTrans (fst_pair K x))

theorem backward_succ (D : PR 3) (N K j x : PTm n) :
    Γ ⊢[PRAAx] backward D N K (succ j) x ≐
      ap3 D (monus N (succ j)) (backward D N K j x) x := by
  have equation := rec2_succ (Γ := Γ) (fstT (sndT (var 0))) (backwardStep D) j (pairT N (pairT K x))
  simp only [backwardStep, subst_ap3, PTm.subst_monus, ConciseIPRA.PTm.subst_succ,
    subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at equation
  exact equation.eqTrans (congrAp3 D (congrMonus (fst_pair _ _) (.eqRefl _)) (.eqRefl _)
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair K x)))

theorem backward_index_congr (D : PR 3) (N K x : PTm n) {j j' : PTm n}
    (h : Γ ⊢[PRAAx] j ≐ j') :
    Γ ⊢[PRAAx] backward D N K j x ≐ backward D N K j' x :=
  congrAp2 (backwardF D) h (.eqRefl _)

/-- The final observation has exactly the demanded terminal precision. -/
theorem horizon_final (D : PR 3) (N K x : PTm n) :
    Γ ⊢[PRAAx] horizon D N K N x ≐ K :=
  (backward_index_congr D N K x (monus_self N)).eqTrans (backward_zero D N K x)

private theorem recover_stage {t N : PTm n} (h : Γ ⊢[PRAAx] lt t N) :
    Γ ⊢[PRAAx] monus N (succ (monus N (succ t))) ≐ t :=
  (congrMonus (split_lt h) (.eqRefl _)).eqTrans (add_monus' _ _)

/-- Every in-range forward stage asks precisely the computed predecessor demand. -/
theorem horizon_step (D : PR 3) (N K t x : PTm n) (ht : Γ ⊢[PRAAx] lt t N) :
    Γ ⊢[PRAAx] horizon D N K t x ≐ ap3 D t (horizon D N K (succ t) x) x :=
  (backward_index_congr D N K x (monus_succ_of_lt ht)).eqTrans
    ((backward_succ D N K (monus N (succ t)) x).eqTrans
      (congrAp3 D (recover_stage ht) (.eqRefl _) (.eqRefl _)))

def observation (A : BF) (t k x : PTm n) : Fm PTm n :=
  fmAt A n (pairT t (pairT k x))

def observationBit (A : BF) (t k x : PTm n) : PTm n :=
  bitAt A n (pairT t (pairT k x))

@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m)
    (A : BF) (t k x : PTm n) :
    (observation A t k x).subst σ =
      observation A (Syn.subst σ t) (Syn.subst σ k) (Syn.subst σ x) := by
  simp only [observation, fmAt_subst, subst_pairT]

@[simp] theorem subst_observationBit {m : ℕ} (σ : Fin n → PTm m)
    (A : BF) (t k x : PTm n) :
    Syn.subst σ (observationBit A t k x) =
      observationBit A (Syn.subst σ t) (Syn.subst σ k) (Syn.subst σ x) := by
  simp only [observationBit, bitAt_subst, subst_pairT]

theorem bit_of_observation (A : BF) (t k x : PTm n)
    (h : Γ ⊢[PRAAx] observation A t k x) :
    Γ ⊢[PRAAx] observationBit A t k x ≐ one :=
  Prf.impE (reflect A (pairT t (pairT k x))).1 h

theorem observation_of_bit (A : BF) (t k x : PTm n)
    (h : Γ ⊢[PRAAx] observationBit A t k x ≐ one) :
    Γ ⊢[PRAAx] observation A t k x :=
  Prf.impE (reflect A (pairT t (pairT k x))).2.1 h

theorem observation_demand_congr (A : BF) (t x : PTm n) {k k' : PTm n}
    (hk : Γ ⊢[PRAAx] k ≐ k') (h : Γ ⊢[PRAAx] observation A t k x) :
    Γ ⊢[PRAAx] observation A t k' x := by
  have source : Γ ⊢[PRAAx] (fmAt A 1 (var 0)).subst ![pairT t (pairT k x)] := by
    simpa only [observation, fmAt_subst, Syn.subst_var, Matrix.cons_val_zero] using h
  have target := Prf.eqSubst (fmAt A 1 (var 0)) ![pairT t (pairT k x)] ![pairT t (pairT k' x)]
    (fun i => by fin_cases i; exact pair_congr (.eqRefl _) (pair_congr hk (.eqRefl _))) source
  simpa only [observation, fmAt_subst, Syn.subst_var, Matrix.cons_val_zero] using target

/-- The local transfer contract contains only a single predecessor observation. -/
def localStep (A : BF) (D : PR 3) (N x : PTm n) : Fm PTm n :=
  .all (.all (lt (var 1) (Syn.shift (Syn.shift N)) ⟶
    observation A (var 1) (ap3 D (var 1) (var 0) (Syn.shift (Syn.shift x))) (Syn.shift (Syn.shift x)) ⟶
    observation A (succ (var 1)) (var 0) (Syn.shift (Syn.shift x))))

@[simp] theorem subst_localStep {m : ℕ} (σ : Fin n → PTm m)
    (A : BF) (D : PR 3) (N x : PTm n) :
    (localStep A D N x).subst σ = localStep A D (Syn.subst σ N) (Syn.subst σ x) := by
  simp only [localStep, Fm.subst_all, Fm.subst_imp, subst_lt, subst_observation,
    subst_ap3, ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.up_zero, Syn.up_succ,
    Syn.subst_shift, Syn.shift_subst, Syn.up_one, Syn.shift_var, Fin.succ_zero_eq_one]

theorem localStep_at (A : BF) (D : PR 3) {N x : PTm n}
    (h : Γ ⊢[PRAAx] localStep A D N x) (t k : PTm n)
    (ht : Γ ⊢[PRAAx] lt t N)
    (hp : Γ ⊢[PRAAx] observation A t (ap3 D t k x) x) :
    Γ ⊢[PRAAx] observation A (succ t) k x := by
  have instantiated := Prf.allE k (Prf.allE t h)
  have contract : Γ ⊢[PRAAx] lt t N ⟶
      observation A t (ap3 D t k x) x ⟶ observation A (succ t) k x := by
    simpa [localStep, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst] using instantiated
  exact Prf.impE (Prf.impE contract ht) hp

/-- `thm:backward-transfer`: a single correctly budgeted initial observation
propagates through arbitrary nonstationary, nonmonotone demand transformers. -/
theorem transfer (A : BF) (D : PR 3) (N K x : PTm n)
    (hbase : Γ ⊢[PRAAx] observation A zero (horizon D N K zero x) x)
    (hstep : Γ ⊢[PRAAx] localStep A D N x) :
    Γ ⊢[PRAAx] observation A N K x := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      observationBit A (var 0)
        (horizon D (Syn.shift N) (Syn.shift K) (var 0) (Syn.shift x)) (Syn.shift x) ≐ one) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, Fm.subst_eq, subst_observationBit,
        subst_horizon, subst_one, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, PTm.subst_monus]
      exact .impI (bit_of_observation A _ _ _ hbase.wk)
    · simp only [Fm.subst_imp, subst_le, Fm.subst_eq, subst_observationBit,
        subst_horizon, subst_one, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, PTm.subst_monus]
      refine .impI ?_
      let Δ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶ observationBit A (var 0)
          (horizon D (Syn.shift N) (Syn.shift K) (var 0) (Syn.shift x)) (Syn.shift x) ≐ one) ::
        Γ.map Fm.shift
      have range : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
      have previous : Δ ⊢[PRAAx] observation A (var 0)
          (horizon D (Syn.shift N) (Syn.shift K) (var 0) (Syn.shift x)) (Syn.shift x) :=
        observation_of_bit A _ _ _
          (Prf.impE Prf.hyp1 (le_trans (le_succ_self (var 0)) Prf.hyp0))
      have scheduled : Δ ⊢[PRAAx] observation A (var 0)
          (ap3 D (var 0) (horizon D (Syn.shift N) (Syn.shift K) (succ (var 0)) (Syn.shift x))
            (Syn.shift x)) (Syn.shift x) :=
        observation_demand_congr A _ _ (horizon_step D _ _ _ _ range) previous
      have shifted : Γ.map Fm.shift ⊢[PRAAx] localStep A D (Syn.shift N) (Syn.shift x) := by
        simpa only [Fm.shift, subst_localStep, Syn.shift] using hstep.shift
      exact bit_of_observation A _ _ _ (localStep_at A D shifted.wk.wk
        (var 0) (horizon D (Syn.shift N) (Syn.shift K) (succ (var 0)) (Syn.shift x)) range scheduled)
  have endpoint := Prf.allE N all
  have terminal : Γ ⊢[PRAAx] observationBit A N (horizon D N K N x) x ≐ one := by
    have guarded : Γ ⊢[PRAAx] le N N ⟶ observationBit A N (horizon D N K N x) x ≐ one := by
      simpa only [Fm.subst_imp, subst_le, Fm.subst_eq, subst_observationBit,
        subst_horizon, subst_one, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        PTm.subst_monus] using endpoint
    exact Prf.impE guarded (le_refl N)
  exact observation_demand_congr A N x (horizon_final D N K x)
    (observation_of_bit A _ _ _ terminal)

/-- Variables are terminal stage `N`, terminal demand `K`, and data `x`. -/
def transferFormula (A : BF) (D : PR 3) : Fm PTm 3 :=
  localStep A D (var 0) (var 2) ⟶
    observation A zero (horizon D (var 0) (var 1) zero (var 2)) (var 2) ⟶
    observation A (var 0) (var 1) (var 2)

theorem backward_transfer (A : BF) (D : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (transferFormula A D) :=
  closeUniv 3 (.impI (.impI (transfer A D _ _ _ Prf.hyp0 Prf.hyp1)))

def allBase (A : BF) (x : PTm n) : Fm PTm n :=
  .all (observation A zero (var 0) (Syn.shift x))

def globalStep (A : BF) (D : PR 3) (x : PTm n) : Fm PTm n :=
  .all (.all (observation A (var 1) (ap3 D (var 1) (var 0) (Syn.shift (Syn.shift x)))
      (Syn.shift (Syn.shift x)) ⟶
    observation A (succ (var 1)) (var 0) (Syn.shift (Syn.shift x))))

@[simp] theorem subst_allBase {m : ℕ} (σ : Fin n → PTm m) (A : BF) (x : PTm n) :
    (allBase A x).subst σ = allBase A (Syn.subst σ x) := by
  simp only [allBase, Fm.subst_all, subst_observation, ConciseIPRA.PTm.subst_zero,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

@[simp] theorem subst_globalStep {m : ℕ} (σ : Fin n → PTm m) (A : BF) (D : PR 3) (x : PTm n) :
    (globalStep A D x).subst σ = globalStep A D (Syn.subst σ x) := by
  simp only [globalStep, Fm.subst_all, Fm.subst_imp, subst_observation, subst_ap3,
    ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.up_zero, Syn.up_succ,
    Syn.subst_shift, Syn.shift_subst, Syn.up_one, Syn.shift_var, Fin.succ_zero_eq_one]

theorem allBase_at (A : BF) {x : PTm n} (h : Γ ⊢[PRAAx] allBase A x) (k : PTm n) :
    Γ ⊢[PRAAx] observation A zero k x := by
  simpa only [allBase, subst_observation, ConciseIPRA.PTm.subst_zero,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE k h

theorem localStep_of_global (A : BF) (D : PR 3) (N x : PTm n)
    (h : Γ ⊢[PRAAx] globalStep A D x) : Γ ⊢[PRAAx] localStep A D N x :=
  .allI (.allI (.impI h.allOpen.allOpen.wk))

/-- `cor:observational-induction`: global closure is introduced after finite
transfer, never used as the induction predicate. -/
theorem observational_induction (A : BF) (D : PR 3) (x : PTm n)
    (hbase : Γ ⊢[PRAAx] allBase A x) (hstep : Γ ⊢[PRAAx] globalStep A D x) :
    Γ ⊢[PRAAx] .all (.all (observation A (var 1) (var 0) (Syn.shift (Syn.shift x)))) := by
  refine .allI (.allI ?_)
  have bases : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] allBase A (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift, subst_allBase, Syn.shift] using hbase.shift.shift
  have steps : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] globalStep A D (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift, subst_globalStep, Syn.shift] using hstep.shift.shift
  exact transfer A D (var 1) (var 0) (Syn.shift (Syn.shift x))
    (allBase_at A bases (horizon D (var 1) (var 0) zero (Syn.shift (Syn.shift x))))
    (localStep_of_global A D (var 1) (Syn.shift (Syn.shift x)) steps)

def inductionFormula (A : BF) (D : PR 3) : Fm PTm 1 :=
  allBase A (var 0) ⟶ globalStep A D (var 0) ⟶
    .all (.all (observation A (var 1) (var 0) (Syn.shift (Syn.shift (var 0)))))

theorem observational_induction_closed (A : BF) (D : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (inductionFormula A D) :=
  closeUniv 1 (.impI (.impI (observational_induction A D (var 0) Prf.hyp1 Prf.hyp0)))

#print axioms backward_zero
#print axioms backward_succ
#print axioms horizon_final
#print axioms horizon_step
#print axioms backward_transfer
#print axioms observational_induction_closed

end LeanProofs.IPRA.Foundations.BackwardDemand
