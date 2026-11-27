import IPRADerivations.Foundations.BackwardDemand
import IPRADerivations.Core.BoundedSums

/-!
# Compile predetermined parameter-changing recursion

Packet `foundations/ipra_finite_demand`, `sections/02_backward_induction.tex`,
`thm:parameter-changing-recursion`.

For fixed symbols `b : PR 2`, `D : PR 3` and `F : PR 4`, the actual PR
program constructs `X(N,K,x)` by composing the backward demand schedule
with an ordinary forward recursion whose parameters `(N,K,x)` stay fixed.
The program's defining equations are proved in the object theory:

* `X(0,K,x)=b(K,x)`;
* `X(N+1,K,x)=F(N,K,X(N,D(N,K,x),x),x)`.

The schedule coherence and equality of the forward traces are derived
by QF induction. No changing-parameter recurrence or schedule-equivalence
contract is supplied as a premise. Bounds `t≤N` are retained exactly where
the truncated-subtraction schedule comparison requires them.
-/

namespace LeanProofs.IPRA.Foundations.ParameterChangingRecursion

open_ipra exports
open LeanProofs.IPRA.Foundations.BackwardDemand

variable {n : ℕ} {Γ : List (Fm PTm n)}

def apply4 (F : PR 4) (a b c d : PTm n) : PTm n := app F ![a, b, c, d]

@[simp] theorem subst_apply4 {m : ℕ} (σ : Fin n → PTm m) (F : PR 4) (a b c d : PTm n) :
    Syn.subst σ (apply4 F a b c d) = apply4 F (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ c) (Syn.subst σ d) := by
  show app _ _ = app _ _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem congrApply4 (F : PR 4) {a a' b b' c c' d d' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (hc : Γ ⊢[PRAAx] c ≐ c') (hd : Γ ⊢[PRAAx] d ≐ d') :
    Γ ⊢[PRAAx] apply4 F a b c d ≐ apply4 F a' b' c' d' :=
  congrApp F (fun i => by fin_cases i <;> assumption)

theorem horizon_congr (D : PR 3) {N N' K K' t t' x x' : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ N') (hK : Γ ⊢[PRAAx] K ≐ K')
    (ht : Γ ⊢[PRAAx] t ≐ t') (hx : Γ ⊢[PRAAx] x ≐ x') :
    Γ ⊢[PRAAx] horizon D N K t x ≐ horizon D N' K' t' x' := by
  have equation := Prf.eqCongr (horizon D (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![N, K, t, x]) (σ' := ![N', K', t', x']) (fun i => by fin_cases i <;> assumption)
  simpa only [subst_horizon, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using equation

/-- The two backward arrays coincide after the first predecessor demand.
This equality is total, including offsets outside the useful horizon. -/
theorem backward_coherence (D : PR 3) (N K j x : PTm n) :
    Γ ⊢[PRAAx] backward D (succ N) K (succ j) x ≐ backward D N (ap3 D N K x) j x := by
  have all : Γ ⊢[PRAAx] .all
      (backward D (succ (Syn.shift N)) (Syn.shift K) (succ (var 0)) (Syn.shift x) ≐
        backward D (Syn.shift N) (ap3 D (Syn.shift N) (Syn.shift K) (Syn.shift x))
          (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_backward, subst_ap3, ConciseIPRA.PTm.subst_succ,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact (backward_succ D (succ N) K zero x).eqTrans
        ((congrAp3 D ((succ_monus_succ N zero).eqTrans (monus_zero N))
          (backward_zero D (succ N) K x) (.eqRefl x)).eqTrans
            (backward_zero D N (ap3 D N K x) x).eqSymm)
    · simp only [Fm.subst_eq, subst_backward, subst_ap3, ConciseIPRA.PTm.subst_succ,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact (backward_succ D (succ (Syn.shift N)) (Syn.shift K) (succ (var 0)) (Syn.shift x)).eqTrans
        ((congrAp3 D (succ_monus_succ (Syn.shift N) (succ (var 0))) Prf.hyp0 (.eqRefl _)).eqTrans
          (backward_succ D (Syn.shift N) (ap3 D (Syn.shift N) (Syn.shift K) (Syn.shift x))
            (var 0) (Syn.shift x)).eqSymm)
  simpa only [Fm.subst_eq, subst_backward, subst_ap3, ConciseIPRA.PTm.subst_succ,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE j all

private theorem successor_monus {N t : PTm n} (h : Γ ⊢[PRAAx] le t N) :
    Γ ⊢[PRAAx] monus (succ N) t ≐ succ (monus N t) := by
  have split : Γ ⊢[PRAAx] succ N ≐ succ (monus N t) + t :=
    (congrSucc (eq_add_of_le h)).eqTrans (by ipra_ring)
  exact (congrMonus split (.eqRefl _)).eqTrans (add_monus _ _)

/-- Equality of the two complete demand schedules on exactly their common
useful range. No monotonicity property of `D` is needed. -/
theorem horizon_coherence (D : PR 3) (N K t x : PTm n) (ht : Γ ⊢[PRAAx] le t N) :
    Γ ⊢[PRAAx] horizon D (succ N) K t x ≐ horizon D N (ap3 D N K x) t x :=
  (backward_index_congr D (succ N) K x (successor_monus ht)).eqTrans
    (backward_coherence D N K (monus N t) x)

/-- The fixed data passed to the ordinary forward recursion. -/
def parameters (N K x : PTm n) : PTm n := pairT N (pairT K x)

def forwardBase (b : PR 2) (D : PR 3) : PTm 1 :=
  ap2 b (horizon D (fstT (var 0)) (fstT (sndT (var 0))) zero (sndT (sndT (var 0))))
    (sndT (sndT (var 0)))

/-- Step variables are forward stage, previous value and unchanged parameters. -/
def forwardStep (D : PR 3) (F : PR 4) : PTm 3 :=
  apply4 F (var 0)
    (horizon D (fstT (var 2)) (fstT (sndT (var 2))) (succ (var 0)) (sndT (sndT (var 2))))
    (var 1) (sndT (sndT (var 2)))

def forwardF (b : PR 2) (D : PR 3) (F : PR 4) : PR 2 := rec2 (forwardBase b D) (forwardStep D F)

/-- Actual ordinary forward recursion with a precomputed PR demand schedule. -/
def forward (b : PR 2) (D : PR 3) (F : PR 4) (N K t x : PTm n) : PTm n :=
  ap2 (forwardF b D F) t (parameters N K x)

@[simp] theorem subst_parameters {m : ℕ} (σ : Fin n → PTm m) (N K x : PTm n) :
    Syn.subst σ (parameters N K x) = parameters (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ x) := by
  simp only [parameters, subst_pairT]

@[simp] theorem subst_forward {m : ℕ} (σ : Fin n → PTm m)
    (b : PR 2) (D : PR 3) (F : PR 4) (N K t x : PTm n) :
    Syn.subst σ (forward b D F N K t x) = forward b D F
      (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ t) (Syn.subst σ x) := by
  simp only [forward, subst_ap2, subst_parameters]

private theorem parameters_stage (N K x : PTm n) : Γ ⊢[PRAAx] fstT (parameters N K x) ≐ N :=
  fst_pair _ _

private theorem parameters_demand (N K x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (parameters N K x)) ≐ K :=
  (congrFst (snd_pair N (pairT K x))).eqTrans (fst_pair K x)

private theorem parameters_data (N K x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (parameters N K x)) ≐ x :=
  (congrSnd (snd_pair N (pairT K x))).eqTrans (snd_pair K x)

theorem forward_zero (b : PR 2) (D : PR 3) (F : PR 4) (N K x : PTm n) :
    Γ ⊢[PRAAx] forward b D F N K zero x ≐ ap2 b (horizon D N K zero x) x := by
  have equation := rec2_zero (Γ := Γ) (forwardBase b D) (forwardStep D F) (parameters N K x)
  simp only [forwardBase, subst_ap2, subst_horizon, subst_fstT, subst_sndT,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Matrix.cons_val_zero] at equation
  exact equation.eqTrans (congrAp2 b
    (horizon_congr D (parameters_stage N K x) (parameters_demand N K x) (.eqRefl _) (parameters_data N K x))
    (parameters_data N K x))

theorem forward_succ (b : PR 2) (D : PR 3) (F : PR 4) (N K t x : PTm n) :
    Γ ⊢[PRAAx] forward b D F N K (succ t) x ≐
      apply4 F t (horizon D N K (succ t) x) (forward b D F N K t x) x := by
  have equation := rec2_succ (Γ := Γ) (forwardBase b D) (forwardStep D F) t (parameters N K x)
  simp only [forwardStep, subst_apply4, subst_horizon, subst_fstT, subst_sndT,
    ConciseIPRA.PTm.subst_succ, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at equation
  exact equation.eqTrans (congrApply4 F (.eqRefl _)
    (horizon_congr D (parameters_stage N K x) (parameters_demand N K x) (.eqRefl _) (parameters_data N K x))
    (.eqRefl _) (parameters_data N K x))

/-- The two actual forward computations agree on their common schedule.
The guard is part of the QF induction invariant, not a global schedule premise. -/
theorem forward_coherence (b : PR 2) (D : PR 3) (F : PR 4) (N K t x : PTm n)
    (ht : Γ ⊢[PRAAx] le t N) :
    Γ ⊢[PRAAx] forward b D F (succ N) K t x ≐ forward b D F N (ap3 D N K x) t x := by
  let P : Fm PTm (n + 1) :=
    forward b D F (succ (Syn.shift N)) (Syn.shift K) (var 0) (Syn.shift x) ≐
      forward b D F (Syn.shift N) (ap3 D (Syn.shift N) (Syn.shift K) (Syn.shift x)) (var 0) (Syn.shift x)
  have atIndex : Γ ⊢[PRAAx] P.subst (Syn.inst t) := by
    refine qfIndAtMost ht trivial ?_ ?_
    · simp only [P, Fm.subst_eq, subst_forward, subst_ap3, ConciseIPRA.PTm.subst_succ,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact (forward_zero b D F (succ N) K x).eqTrans
        ((congrAp2 b (horizon_coherence D N K zero x (zero_le N)) (.eqRefl _)).eqTrans
          (forward_zero b D F N (ap3 D N K x) x).eqSymm)
    · simp only [P, Fm.subst_eq, subst_forward, subst_ap3, ConciseIPRA.PTm.subst_succ,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let Δ := lt (var 0) (Syn.shift N) :: P :: Γ.map Fm.shift
      have range : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
      have schedule := horizon_coherence D (Syn.shift N) (Syn.shift K) (succ (var 0)) (Syn.shift x) range
      exact (forward_succ b D F (succ (Syn.shift N)) (Syn.shift K) (var 0) (Syn.shift x)).eqTrans
        ((congrApply4 F (.eqRefl _) schedule Prf.hyp1 (.eqRefl _)).eqTrans
          (forward_succ b D F (Syn.shift N) (ap3 D (Syn.shift N) (Syn.shift K) (Syn.shift x))
            (var 0) (Syn.shift x)).eqSymm)
  simpa only [P, Fm.subst_eq, subst_forward, subst_ap3, ConciseIPRA.PTm.subst_succ,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using atIndex

/-- The constructed changing-parameter value is the final forward value. -/
def compiledRecursion (b : PR 2) (D : PR 3) (F : PR 4) (N K x : PTm n) : PTm n :=
  forward b D F N K N x

@[simp] theorem subst_compiledRecursion {m : ℕ} (σ : Fin n → PTm m)
    (b : PR 2) (D : PR 3) (F : PR 4) (N K x : PTm n) :
    Syn.subst σ (compiledRecursion b D F N K x) = compiledRecursion b D F
      (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ x) := by
  simp only [compiledRecursion, subst_forward]

theorem compiled_zero (b : PR 2) (D : PR 3) (F : PR 4) (K x : PTm n) :
    Γ ⊢[PRAAx] compiledRecursion b D F zero K x ≐ ap2 b K x :=
  (forward_zero b D F zero K x).eqTrans
    (congrAp2 b (horizon_final D zero K x) (.eqRefl _))

/-- The parameter-changing equation is a conclusion about the actual program. -/
theorem compiled_succ (b : PR 2) (D : PR 3) (F : PR 4) (N K x : PTm n) :
    Γ ⊢[PRAAx] compiledRecursion b D F (succ N) K x ≐
      apply4 F N K (compiledRecursion b D F N (ap3 D N K x) x) x :=
  (forward_succ b D F (succ N) K N x).eqTrans
    (congrApply4 F (.eqRefl _) (horizon_final D (succ N) K x)
      (forward_coherence b D F N K N x (le_refl N)) (.eqRefl _))

/-- Explicit ternary primitive-recursive symbol for the constructed program. -/
def compiledF (b : PR 2) (D : PR 3) (F : PR 4) : PR 3 :=
  PTm.toPR (compiledRecursion b D F (var 0) (var 1) (var 2))

theorem compiled_at (b : PR 2) (D : PR 3) (F : PR 4) (N K x : PTm n) :
    Γ ⊢[PRAAx] ap3 (compiledF b D F) N K x ≐ compiledRecursion b D F N K x := by
  have equation := toPR_eq (Γ := Γ) (compiledRecursion b D F (var 0) (var 1) (var 2)) ![N, K, x]
  simpa only [compiledF, ap3, subst_compiledRecursion, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using equation

theorem compiled_program_zero (b : PR 2) (D : PR 3) (F : PR 4) (K x : PTm n) :
    Γ ⊢[PRAAx] ap3 (compiledF b D F) zero K x ≐ ap2 b K x :=
  (compiled_at b D F zero K x).eqTrans (compiled_zero b D F K x)

theorem compiled_program_succ (b : PR 2) (D : PR 3) (F : PR 4) (N K x : PTm n) :
    Γ ⊢[PRAAx] ap3 (compiledF b D F) (succ N) K x ≐
      apply4 F N K (ap3 (compiledF b D F) N (ap3 D N K x) x) x :=
  (compiled_at b D F (succ N) K x).eqTrans ((compiled_succ b D F N K x).eqTrans
    (congrApply4 F (.eqRefl _) (.eqRefl _) (compiled_at b D F N (ap3 D N K x) x).eqSymm (.eqRefl _)))

/-- Closed zero equation of the actual generated PR symbol, variables `K,x`. -/
theorem zero_equation (b : PR 2) (D : PR 3) (F : PR 4) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (ap3 (compiledF b D F) zero (var 0) (var 1) ≐ ap2 b (var 0) (var 1)) :=
  closeUniv 2 (compiled_program_zero b D F _ _)

/-- `thm:parameter-changing-recursion`, closed at runtime variables `N,K,x`.
No schedule or recursion-correctness formula occurs among the premises. -/
theorem successor_equation (b : PR 2) (D : PR 3) (F : PR 4) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap3 (compiledF b D F) (succ (var 0)) (var 1) (var 2) ≐
        apply4 F (var 0) (var 1)
          (ap3 (compiledF b D F) (var 0) (ap3 D (var 0) (var 1) (var 2)) (var 2)) (var 2)) :=
  closeUniv 3 (compiled_program_succ b D F _ _ _)

#print axioms backward_coherence
#print axioms horizon_coherence
#print axioms forward_zero
#print axioms forward_succ
#print axioms forward_coherence
#print axioms compiled_program_zero
#print axioms compiled_program_succ
#print axioms zero_equation
#print axioms successor_equation

end LeanProofs.IPRA.Foundations.ParameterChangingRecursion
