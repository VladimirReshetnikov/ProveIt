import IPRADerivations.Foundations.BackwardDemand
import IPRADerivations.Foundations.BoundedSyntax
import IPRADerivations.Foundations.DemandClosure
import IPRADerivations.Core.Header

/-!
# Observational induction with variable finite query families

Packet `foundations/ipra_finite_demand`, `sections/02_backward_induction.tex`,
`cor:finite-query-induction`. The actual runtime demand envelope is
`max_{j≤H} max_{r<m(n,j,x)} q(n,j,r,x)`, with empty maximum zero.
Both maxima are primitive-recursive folds, and their indexing inequalities
are proved by QF induction. No monotonicity of query indices is assumed.

The source observation uses arity-indexed bounded syntax at `(stage,index,x)`.
Its bounded-prefix syntax and the packed adapter for `BackwardDemand` are
constructed here, including a proved equivalence to the literal source
formula. The local prefix transfer is derived from the multiple-query
contract and actual envelope inequalities.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteQueryDemand

open_ipra
open LeanProofs.IPRA.Foundations.DemandClosure
  (maximum subst_maximum maximum_left maximum_right maximum_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def apply4 (q : PR 4) (a b c d : PTm n) : PTm n := app q ![a, b, c, d]

@[simp] theorem subst_apply4 {m : ℕ} (σ : Fin n → PTm m) (q : PR 4) (a b c d : PTm n) :
    Syn.subst σ (apply4 q a b c d) = apply4 q (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ c) (Syn.subst σ d) := by
  show app _ _ = app _ _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem congrApply4 (q : PR 4) {a a' b b' c c' d d' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (hc : Γ ⊢[PRAAx] c ≐ c') (hd : Γ ⊢[PRAAx] d ≐ d') :
    Γ ⊢[PRAAx] apply4 q a b c d ≐ apply4 q a' b' c' d' :=
  congrApp q (fun i => by fin_cases i <;> assumption)

def maximumStep (body : PTm 2) : PTm 3 := maximum (var 1) (inst2 body (var 0) (var 2))
def maximumF (body : PTm 2) : PR 2 := rec2 zero (maximumStep body)
def finiteMaximum (body : PTm 2) (N x : PTm n) : PTm n := ap2 (maximumF body) N x

@[simp] theorem subst_finiteMaximum {m : ℕ} (σ : Fin n → PTm m)
    (body : PTm 2) (N x : PTm n) :
    Syn.subst σ (finiteMaximum body N x) = finiteMaximum body (Syn.subst σ N) (Syn.subst σ x) :=
  subst_ap2 _ _ _ _

theorem finiteMaximum_zero (body : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] finiteMaximum body zero x ≐ zero := by
  simpa only [finiteMaximum, maximumF, ConciseIPRA.PTm.subst_zero] using
    rec2_zero (Γ := Γ) zero (maximumStep body) x

theorem finiteMaximum_succ (body : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] finiteMaximum body (succ N) x ≐ maximum (finiteMaximum body N x) (inst2 body N x) := by
  simpa only [finiteMaximum, maximumF, maximumStep, subst_maximum, subst_inst2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using rec2_succ (Γ := Γ) zero (maximumStep body) N x

theorem finiteMaximum_increasing (body : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] le (finiteMaximum body N x) (finiteMaximum body (succ N) x) :=
  le_congr (.eqRefl _) (finiteMaximum_succ body N x).eqSymm (maximum_left _ _)

/-- Every in-range body value is bounded by the actual maximum fold. -/
theorem finiteMaximum_at (body : PTm 2) {N i x : PTm n}
    (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] le (inst2 body i x) (finiteMaximum body N x) := by
  have all : Γ ⊢[PRAAx] .all (lt (Syn.shift i) (var 0) ⟶
      le (inst2 body (Syn.shift i) (Syn.shift x)) (finiteMaximum body (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨lt_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_lt, subst_le, subst_inst2, subst_finiteMaximum,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      exact .impI (lt_zero_absurd _ Prf.hyp0)
    · simp only [Fm.subst_imp, subst_lt, subst_le, subst_inst2, subst_finiteMaximum,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      have small : (lt (Syn.shift i) (succ (var 0)) ::
          (lt (Syn.shift i) (var 0) ⟶
            le (inst2 body (Syn.shift i) (Syn.shift x)) (finiteMaximum body (var 0) (Syn.shift x))) ::
              Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift i) (var 0) :=
        (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      refine .orE (lt_or_eq_of_le small) ?_ ?_
      · exact le_trans (Prf.impE Prf.hyp1.wk Prf.hyp0) (finiteMaximum_increasing body _ _)
      · exact le_congr (congrInst2 body Prf.hyp0 (.eqRefl _)).eqSymm
          (finiteMaximum_succ body _ _).eqSymm (maximum_right _ _)
  have one := Prf.allE N all
  have guarded : Γ ⊢[PRAAx] lt i N ⟶ le (inst2 body i x) (finiteMaximum body N x) := by
    simpa only [Fm.subst_imp, subst_lt, subst_le, subst_inst2, subst_finiteMaximum,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using one
  exact Prf.impE guarded hi

private theorem le_iff_lt_succ {i H : PTm n} :
    Γ ⊢[PRAAx] Fm.iff (le i H) (lt i (succ H)) :=
  .iffI (.impI ((succ_monus_succ _ _).eqTrans Prf.hyp0))
    (.impI ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0))

/-- Body of the inner query maximum; its data are packed `(stage,index,x)`. -/
def queryBody (q : PR 4) : PTm 2 :=
  apply4 q (fstT (var 1)) (fstT (sndT (var 1))) (var 0) (sndT (sndT (var 1)))

def innerMaximum (m : PR 3) (q : PR 4) (stage index x : PTm n) : PTm n :=
  finiteMaximum (queryBody q) (ap3 m stage index x) (pairT stage (pairT index x))

@[simp] theorem subst_innerMaximum {k : ℕ} (σ : Fin n → PTm k)
    (m : PR 3) (q : PR 4) (stage index x : PTm n) :
    Syn.subst σ (innerMaximum m q stage index x) =
      innerMaximum m q (Syn.subst σ stage) (Syn.subst σ index) (Syn.subst σ x) := by
  simp only [innerMaximum, subst_finiteMaximum, subst_ap3, subst_pairT]

private theorem innerMaximum_congr (m : PR 3) (q : PR 4) {a a' b b' c c' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') (hc : Γ ⊢[PRAAx] c ≐ c') :
    Γ ⊢[PRAAx] innerMaximum m q a b c ≐ innerMaximum m q a' b' c' := by
  have equation := Prf.eqCongr (innerMaximum m q (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![a, b, c]) (σ' := ![a', b', c']) (fun i => by fin_cases i <;> assumption)
  simpa only [subst_innerMaximum, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using equation

theorem queryBody_at (q : PR 4) (stage index r x : PTm n) :
    Γ ⊢[PRAAx] inst2 (queryBody q) r (pairT stage (pairT index x)) ≐ apply4 q stage index r x := by
  simp only [queryBody, inst2, subst_apply4, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact congrApply4 q (fst_pair _ _)
    ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) (.eqRefl _)
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

theorem query_le_inner (m : PR 3) (q : PR 4) (stage index r x : PTm n)
    (hr : Γ ⊢[PRAAx] lt r (ap3 m stage index x)) :
    Γ ⊢[PRAAx] le (apply4 q stage index r x) (innerMaximum m q stage index x) :=
  le_congr (queryBody_at q stage index r x) (.eqRefl _) (finiteMaximum_at (queryBody q) hr)

def outerBody (m : PR 3) (q : PR 4) : PTm 2 :=
  innerMaximum m q (fstT (var 1)) (var 0) (sndT (var 1))

/-- Actual nested maximum over output indices `0≤j≤H` and their query lists. -/
def envelope (m : PR 3) (q : PR 4) (stage H x : PTm n) : PTm n :=
  finiteMaximum (outerBody m q) (succ H) (pairT stage x)

@[simp] theorem subst_envelope {k : ℕ} (σ : Fin n → PTm k)
    (m : PR 3) (q : PR 4) (stage H x : PTm n) :
    Syn.subst σ (envelope m q stage H x) =
      envelope m q (Syn.subst σ stage) (Syn.subst σ H) (Syn.subst σ x) := by
  simp only [envelope, subst_finiteMaximum, ConciseIPRA.PTm.subst_succ, subst_pairT]

theorem outerBody_at (m : PR 3) (q : PR 4) (stage index x : PTm n) :
    Γ ⊢[PRAAx] inst2 (outerBody m q) index (pairT stage x) ≐ innerMaximum m q stage index x := by
  simp only [outerBody, inst2, subst_innerMaximum, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact innerMaximum_congr m q (fst_pair _ _) (.eqRefl _) (snd_pair _ _)

/-- The genuine runtime envelope covers every requested predecessor index. -/
theorem query_le_envelope (m : PR 3) (q : PR 4) (stage H index r x : PTm n)
    (hj : Γ ⊢[PRAAx] le index H) (hr : Γ ⊢[PRAAx] lt r (ap3 m stage index x)) :
    Γ ⊢[PRAAx] le (apply4 q stage index r x) (envelope m q stage H x) := by
  have outer : Γ ⊢[PRAAx] le (innerMaximum m q stage index x) (envelope m q stage H x) :=
    le_congr (outerBody_at m q stage index x) (.eqRefl _)
      (finiteMaximum_at (outerBody m q) (Prf.iffMp le_iff_lt_succ hj))
  exact le_trans (query_le_inner m q stage index r x hr) outer

def envelopeF (m : PR 3) (q : PR 4) : PR 3 :=
  PTm.toPR (envelope m q (var 0) (var 1) (var 2))

theorem envelope_at (m : PR 3) (q : PR 4) (stage H x : PTm n) :
    Γ ⊢[PRAAx] ap3 (envelopeF m q) stage H x ≐ envelope m q stage H x := by
  have equation := toPR_eq (Γ := Γ) (envelope m q (var 0) (var 1) (var 2)) ![stage, H, x]
  simpa only [envelopeF, ap3, subst_envelope, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using equation

/-! ## The literal source observation and its internally constructed prefix -/

def observe (A : BoundedSyntax.BFm 3) (stage index x : PTm n) : Fm PTm n :=
  (BoundedSyntax.formula A).subst ![stage, index, x]

@[simp] theorem subst_observe {k : ℕ} (σ : Fin n → PTm k)
    (A : BoundedSyntax.BFm 3) (stage index x : PTm n) :
    (observe A stage index x).subst σ = observe A (Syn.subst σ stage) (Syn.subst σ index) (Syn.subst σ x) := by
  simp only [observe, Fm.subst_subst]
  congr 1
  funext i
  fin_cases i <;> rfl

def prefixAt (A : BoundedSyntax.BFm 3) (stage H x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (succ (Syn.shift H)) ⟶ observe A (Syn.shift stage) (var 0) (Syn.shift x))

@[simp] theorem subst_prefixAt {k : ℕ} (σ : Fin n → PTm k)
    (A : BoundedSyntax.BFm 3) (stage H x : PTm n) :
    (prefixAt A stage H x).subst σ =
      prefixAt A (Syn.subst σ stage) (Syn.subst σ H) (Syn.subst σ x) := by
  simp only [prefixAt, Fm.subst_all, Fm.subst_imp, subst_lt, subst_observe,
    ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.up_zero,
    Syn.subst_shift, Syn.shift_subst, Syn.up_succ]

/-- Original variables are stage, horizon and data; a fresh bounded variable
becomes the observation index, while stage and data are shifted correctly. -/
def prefixSyntax (A : BoundedSyntax.BFm 3) : BoundedSyntax.BFm 3 :=
  .all (succ (var 1)) (A.subst ![var 1, var 0, var 3])

theorem prefixSyntax_at (A : BoundedSyntax.BFm 3) (stage H x : PTm n) :
    (BoundedSyntax.formula (prefixSyntax A)).subst ![stage, H, x] = prefixAt A stage H x := by
  have compose : (fun i : Fin 3 =>
      Syn.subst (Syn.up (![stage, H, x] : Fin 3 → PTm n)) ((![var 1, var 0, var 3] : Fin 3 → PTm 4) i)) =
      (![Syn.shift stage, var 0, Syn.shift x] : Fin 3 → PTm (n + 1)) := by
    funext i
    fin_cases i <;> rfl
  simp only [prefixSyntax, BoundedSyntax.formula, BoundedSyntax.formula_subst,
    Fm.subst_all, Fm.subst_imp, subst_lt, ConciseIPRA.PTm.subst_succ,
    Syn.subst_var, Syn.up_zero, BoundedFormulas.subst_up_shift', Fm.subst_subst]
  rw [compose]
  rfl

def prefixEmbedding : Fin 3 → PTm 1 :=
  ![fstT (var 0), fstT (sndT (var 0)), sndT (sndT (var 0))]

def prefixCode (A : BoundedSyntax.BFm 3) : BoundedFormulas.BF :=
  BoundedSyntax.compile (prefixSyntax A) prefixEmbedding

private theorem prefix_embedding_at (stage H x : PTm n) (i : Fin 3) :
    Γ ⊢[PRAAx] BoundedFormulas.at1 (prefixEmbedding i) (pairT stage (pairT H x)) ≐
      (![stage, H, x] : Fin 3 → PTm n) i := by
  fin_cases i
  · simpa [prefixEmbedding, BoundedFormulas.at1] using fst_pair (Γ := Γ) stage (pairT H x)
  · simpa [prefixEmbedding, BoundedFormulas.at1] using
      (congrFst (snd_pair (Γ := Γ) stage (pairT H x))).eqTrans (fst_pair H x)
  · simpa [prefixEmbedding, BoundedFormulas.at1] using
      (congrSnd (snd_pair (Γ := Γ) stage (pairT H x))).eqTrans (snd_pair H x)

/-- No source-prefix equivalence is supplied by a client. It follows from
the checked frontend compiler and the actual three coordinate projections. -/
theorem prefix_correct (A : BoundedSyntax.BFm 3) (stage H x : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (BackwardDemand.observation (prefixCode A) stage H x) (prefixAt A stage H x) := by
  have checked := BoundedSyntax.compile_correct (Γ := Γ) (prefixSyntax A) prefixEmbedding
    (pairT stage (pairT H x)) ![stage, H, x] (prefix_embedding_at stage H x)
  simpa only [prefixCode, BackwardDemand.observation, prefixSyntax_at] using checked

theorem prefix_to (A : BoundedSyntax.BFm 3) (stage H x : PTm n)
    (h : Γ ⊢[PRAAx] BackwardDemand.observation (prefixCode A) stage H x) :
    Γ ⊢[PRAAx] prefixAt A stage H x := Prf.iffMp (prefix_correct A stage H x) h

theorem prefix_from (A : BoundedSyntax.BFm 3) (stage H x : PTm n)
    (h : Γ ⊢[PRAAx] prefixAt A stage H x) :
    Γ ⊢[PRAAx] BackwardDemand.observation (prefixCode A) stage H x := Prf.iffMpr (prefix_correct A stage H x) h

theorem prefix_at (A : BoundedSyntax.BFm 3) {stage H x : PTm n}
    (h : Γ ⊢[PRAAx] prefixAt A stage H x) (j : PTm n) (hj : Γ ⊢[PRAAx] le j H) :
    Γ ⊢[PRAAx] observe A stage j x := by
  have instantiated := Prf.allE j h
  have guarded : Γ ⊢[PRAAx] lt j (succ H) ⟶ observe A stage j x := by
    simpa only [prefixAt, Fm.subst_imp, subst_lt, subst_observe, ConciseIPRA.PTm.subst_succ,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using instantiated
  exact Prf.impE guarded (Prf.iffMp le_iff_lt_succ hj)

/-! ## Multiple queries imply the internally computed prefix transfer -/

def allBase (A : BoundedSyntax.BFm 3) (x : PTm n) : Fm PTm n :=
  .all (observe A zero (var 0) (Syn.shift x))

def queries (A : BoundedSyntax.BFm 3) (m : PR 3) (q : PR 4) (stage index x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (ap3 m (Syn.shift stage) (Syn.shift index) (Syn.shift x)) ⟶
    observe A (Syn.shift stage) (apply4 q (Syn.shift stage) (Syn.shift index) (var 0) (Syn.shift x))
      (Syn.shift x))

def multipleStep (A : BoundedSyntax.BFm 3) (m : PR 3) (q : PR 4) (x : PTm n) : Fm PTm n :=
  .all (.all (queries A m q (var 1) (var 0) (Syn.shift (Syn.shift x)) ⟶
    observe A (succ (var 1)) (var 0) (Syn.shift (Syn.shift x))))

@[simp] theorem subst_allBase {k : ℕ} (σ : Fin n → PTm k) (A : BoundedSyntax.BFm 3) (x : PTm n) :
    (allBase A x).subst σ = allBase A (Syn.subst σ x) := by
  simp only [allBase, Fm.subst_all, subst_observe, ConciseIPRA.PTm.subst_zero,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

@[simp] theorem subst_queries {k : ℕ} (σ : Fin n → PTm k)
    (A : BoundedSyntax.BFm 3) (m : PR 3) (q : PR 4) (stage index x : PTm n) :
    (queries A m q stage index x).subst σ =
      queries A m q (Syn.subst σ stage) (Syn.subst σ index) (Syn.subst σ x) := by
  simp only [queries, Fm.subst_all, Fm.subst_imp, subst_lt, subst_observe,
    subst_ap3, subst_apply4, Syn.subst_var, Syn.up_zero, Syn.up_succ,
    Syn.subst_shift, Syn.shift_subst]

@[simp] theorem subst_multipleStep {k : ℕ} (σ : Fin n → PTm k)
    (A : BoundedSyntax.BFm 3) (m : PR 3) (q : PR 4) (x : PTm n) :
    (multipleStep A m q x).subst σ = multipleStep A m q (Syn.subst σ x) := by
  simp only [multipleStep, Fm.subst_all, Fm.subst_imp, subst_queries, subst_observe,
    ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.up_zero, Syn.up_succ,
    Syn.subst_shift, Syn.shift_subst, Syn.up_one, Syn.shift_var, Fin.succ_zero_eq_one]

theorem multipleStep_at (A : BoundedSyntax.BFm 3) (m : PR 3) (q : PR 4) {x : PTm n}
    (h : Γ ⊢[PRAAx] multipleStep A m q x) (stage index : PTm n)
    (hp : Γ ⊢[PRAAx] queries A m q stage index x) :
    Γ ⊢[PRAAx] observe A (succ stage) index x := by
  have instantiated := Prf.allE index (Prf.allE stage h)
  have contract : Γ ⊢[PRAAx] queries A m q stage index x ⟶ observe A (succ stage) index x := by
    simpa [multipleStep, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst] using instantiated
  exact Prf.impE contract hp

theorem prefix_base_at (A : BoundedSyntax.BFm 3) (H x : PTm n)
    (h : Γ ⊢[PRAAx] allBase A x) : Γ ⊢[PRAAx] prefixAt A zero H x := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift, ConciseIPRA.PTm.subst_zero] using h.allOpen.wk

/-- Every requested predecessor observation is obtained from the true
computed envelope and the prefix observation. -/
theorem queries_from_prefix (A : BoundedSyntax.BFm 3) (m : PR 3) (q : PR 4)
    (stage H index x : PTm n)
    (hp : Γ ⊢[PRAAx] prefixAt A stage (ap3 (envelopeF m q) stage H x) x)
    (hj : Γ ⊢[PRAAx] le index H) : Γ ⊢[PRAAx] queries A m q stage index x := by
  refine .allI (.impI ?_)
  have pref : Γ.map Fm.shift ⊢[PRAAx]
      prefixAt A (Syn.shift stage) (ap3 (envelopeF m q) (Syn.shift stage) (Syn.shift H) (Syn.shift x)) (Syn.shift x) := by
    simpa only [Fm.shift, subst_prefixAt, subst_ap3, Syn.shift] using hp.shift
  have range : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift index) (Syn.shift H) := by
    simpa only [Fm.shift, subst_le, Syn.shift] using hj.shift
  have bound : (lt (var 0) (ap3 m (Syn.shift stage) (Syn.shift index) (Syn.shift x)) :: Γ.map Fm.shift)
      ⊢[PRAAx] le (apply4 q (Syn.shift stage) (Syn.shift index) (var 0) (Syn.shift x))
        (ap3 (envelopeF m q) (Syn.shift stage) (Syn.shift H) (Syn.shift x)) :=
    le_congr (.eqRefl _) (envelope_at m q _ _ _).eqSymm
      (query_le_envelope m q _ _ _ _ _ range.wk Prf.hyp0)
  exact prefix_at A pref.wk _ bound

/-- The source multiple-query contract yields the prefix local step;
its validity is not an assumption about the envelope program. -/
theorem prefix_local_step (A : BoundedSyntax.BFm 3) (m : PR 3) (q : PR 4)
    (stage H x : PTm n) (hs : Γ ⊢[PRAAx] multipleStep A m q x)
    (hp : Γ ⊢[PRAAx] prefixAt A stage (ap3 (envelopeF m q) stage H x) x) :
    Γ ⊢[PRAAx] prefixAt A (succ stage) H x := by
  refine .allI (.impI ?_)
  have steps : Γ.map Fm.shift ⊢[PRAAx] multipleStep A m q (Syn.shift x) := by
    simpa only [Fm.shift, subst_multipleStep, Syn.shift] using hs.shift
  have pref : Γ.map Fm.shift ⊢[PRAAx]
      prefixAt A (Syn.shift stage) (ap3 (envelopeF m q) (Syn.shift stage) (Syn.shift H) (Syn.shift x)) (Syn.shift x) := by
    simpa only [Fm.shift, subst_prefixAt, subst_ap3, Syn.shift] using hp.shift
  have range : (lt (var 0) (succ (Syn.shift H)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift H) :=
    Prf.iffMpr le_iff_lt_succ Prf.hyp0
  exact multipleStep_at A m q steps.wk (Syn.shift stage) (var 0)
    (queries_from_prefix A m q (Syn.shift stage) (Syn.shift H) (var 0) (Syn.shift x) pref.wk range)

theorem prefix_allBase (A : BoundedSyntax.BFm 3) (x : PTm n)
    (h : Γ ⊢[PRAAx] allBase A x) : Γ ⊢[PRAAx] BackwardDemand.allBase (prefixCode A) x := by
  refine .allI ?_
  have shifted : Γ.map Fm.shift ⊢[PRAAx] allBase A (Syn.shift x) := by
    simpa only [Fm.shift, subst_allBase, Syn.shift] using h.shift
  exact prefix_from A zero (var 0) (Syn.shift x) (prefix_base_at A (var 0) (Syn.shift x) shifted)

theorem prefix_globalStep (A : BoundedSyntax.BFm 3) (m : PR 3) (q : PR 4) (x : PTm n)
    (h : Γ ⊢[PRAAx] multipleStep A m q x) :
    Γ ⊢[PRAAx] BackwardDemand.globalStep (prefixCode A) (envelopeF m q) x := by
  refine .allI (.allI (.impI ?_))
  have shifted : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] multipleStep A m q (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift, subst_multipleStep, Syn.shift] using h.shift.shift
  exact prefix_from A (succ (var 1)) (var 0) (Syn.shift (Syn.shift x))
    (prefix_local_step A m q (var 1) (var 0) (Syn.shift (Syn.shift x)) shifted.wk
      (prefix_to A (var 1) (ap3 (envelopeF m q) (var 1) (var 0) (Syn.shift (Syn.shift x)))
        (Syn.shift (Syn.shift x)) Prf.hyp0))

/-- `cor:finite-query-induction`: arbitrary input-dependent finite query
families yield every observation, using only the genuine local contract. -/
theorem finite_query_induction (A : BoundedSyntax.BFm 3) (m : PR 3) (q : PR 4) (x : PTm n)
    (hbase : Γ ⊢[PRAAx] allBase A x) (hstep : Γ ⊢[PRAAx] multipleStep A m q x) :
    Γ ⊢[PRAAx] .all (.all (observe A (var 1) (var 0) (Syn.shift (Syn.shift x)))) := by
  have prefixes := BackwardDemand.observational_induction (prefixCode A) (envelopeF m q) x
    (prefix_allBase A x hbase) (prefix_globalStep A m q x hstep)
  refine .allI (.allI ?_)
  exact prefix_at A (prefix_to A (var 1) (var 0) (Syn.shift (Syn.shift x)) prefixes.allOpen.allOpen)
    (var 0) (le_refl _)

def inductionFormula (A : BoundedSyntax.BFm 3) (m : PR 3) (q : PR 4) : Fm PTm 1 :=
  allBase A (var 0) ⟶ multipleStep A m q (var 0) ⟶
    .all (.all (observe A (var 1) (var 0) (Syn.shift (Syn.shift (var 0)))))

theorem finite_query_induction_closed (A : BoundedSyntax.BFm 3) (m : PR 3) (q : PR 4) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (inductionFormula A m q) :=
  closeUniv 1 (.impI (.impI (finite_query_induction A m q (var 0) Prf.hyp1 Prf.hyp0)))

/-- Variables are stage, horizon, requested output index, subquery and data. -/
theorem finite_query_envelope (m : PR 3) (q : PR 4) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le (var 2) (var 1) ⟶ lt (var 3) (ap3 m (var 0) (var 2) (var 4)) ⟶
        le (apply4 q (var 0) (var 2) (var 3) (var 4))
          (ap3 (envelopeF m q) (var 0) (var 1) (var 4))) :=
  closeUniv 5 (.impI (.impI
    (le_congr (.eqRefl _) (envelope_at m q _ _ _).eqSymm
      (query_le_envelope m q _ _ _ _ _ Prf.hyp1 Prf.hyp0))))

#print axioms finiteMaximum_at
#print axioms query_le_envelope
#print axioms prefix_correct
#print axioms queries_from_prefix
#print axioms prefix_local_step
#print axioms prefix_globalStep
#print axioms finite_query_induction_closed
#print axioms finite_query_envelope

end LeanProofs.IPRA.Foundations.FiniteQueryDemand
