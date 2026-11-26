import IPRADerivations.Foundations.RealizerGraph
import IPRADerivations.Foundations.FiberCompiler
import IPRADerivations.Core.SubstCommand

/-!
# A bounded runtime fold with actual finite-query metadata

FIBER `thm:compilation`, the bounded `map`/`fold` case. A fixed loop computes
its runtime fuel and one input query at each stage from the output query and
persistent parameter. Its transformer folds the actual master entries by
primitive recursion. Arbitrary quantifier-free state and paired-state
invariants have only local base, one-step and final extraction contracts.

The demand list, canonical master cap, verifier, transformer and observation
are actual fixed PR programs. Global and stage-specialized producer formulas
remain explicit outside induction. Adaptive state-dependent demands and
variable blocks of demands per stage are not implemented here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RealizerLoop

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.RealizerComposition
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.ClockedDescent (subst_QF')
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Fixed source data, independent of proof compilation. The step's third
argument is the actual tuple `(input certificate, query, parameter)`. -/
structure Code where
  fuel : PR 2
  query : PR 3
  initial : PR 2
  step : PR 3
  guard : Fm PTm 2
  residuals : List (Fm PTm 2)
  stageResiduals : List (Fm PTm 3)
  invariant : Fm PTm 4
  stabilityInvariant : Fm PTm 5

def stageAt (A : Fm PTm 3) (i q p : PTm n) : Fm PTm n := A.subst ![i, q, p]
def invAt (D : Code) (i s q p : PTm n) : Fm PTm n := D.invariant.subst ![i, s, q, p]
def relAt (D : Code) (i s s' q p : PTm n) : Fm PTm n := D.stabilityInvariant.subst ![i, s, s', q, p]
def stepAt (D : Code) (i s c q p : PTm n) : PTm n := ap3 D.step i s (pairT c (pairT q p))

@[simp] theorem subst_stageAt {k : ℕ} (σ : Fin n → PTm k) (A : Fm PTm 3) (i q p : PTm n) :
    (stageAt A i q p).subst σ = stageAt A (Syn.subst σ i) (Syn.subst σ q) (Syn.subst σ p) := by
  simp only [stageAt, Fm.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

@[simp] theorem subst_invAt {k : ℕ} (σ : Fin n → PTm k) (D : Code) (i s q p : PTm n) :
    (invAt D i s q p).subst σ = invAt D (Syn.subst σ i) (Syn.subst σ s) (Syn.subst σ q) (Syn.subst σ p) := by
  simp only [invAt, Fm.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

@[simp] theorem subst_relAt {k : ℕ} (σ : Fin n → PTm k) (D : Code) (i s s' q p : PTm n) :
    (relAt D i s s' q p).subst σ = relAt D (Syn.subst σ i) (Syn.subst σ s)
      (Syn.subst σ s') (Syn.subst σ q) (Syn.subst σ p) := by
  simp only [relAt, Fm.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

@[simp] theorem subst_stepAt {k : ℕ} (σ : Fin n → PTm k) (D : Code) (i s c q p : PTm n) :
    Syn.subst σ (stepAt D i s c q p) = stepAt D (Syn.subst σ i) (Syn.subst σ s)
      (Syn.subst σ c) (Syn.subst σ q) (Syn.subst σ p) := by simp [stepAt]

theorem invAt_congr (D : Code) (i q p : PTm n) {s t : PTm n}
    (hst : Γ ⊢[PRAAx] s ≐ t) (h : Γ ⊢[PRAAx] invAt D i s q p) : Γ ⊢[PRAAx] invAt D i t q p :=
  Prf.eqSubst D.invariant ![i, s, q, p] ![i, t, q, p]
    (fun j => by fin_cases j <;> first | exact hst | exact .eqRefl _) h

theorem relAt_congr (D : Code) (i q p : PTm n) {s s' t t' : PTm n}
    (hst : Γ ⊢[PRAAx] s ≐ t) (hst' : Γ ⊢[PRAAx] s' ≐ t')
    (h : Γ ⊢[PRAAx] relAt D i s s' q p) : Γ ⊢[PRAAx] relAt D i t t' q p :=
  Prf.eqSubst D.stabilityInvariant ![i, s, s', q, p] ![i, t, t', q, p]
    (fun j => by fin_cases j <;> first | exact hst | exact hst' | exact .eqRefl _) h

/-- These are local contracts. In particular `final` sees an arbitrary state
and its declared QF invariant, never an asserted correctness of the run. -/
structure Laws (X Y : Interface) (D : Code) : Prop where
  qf : D.invariant.QF
  relQf : D.stabilityInvariant.QF
  base : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    D.guard ⟶ allOf D.residuals ⟶ invAt D zero (ap2 D.initial (var 0) (var 1)) (var 0) (var 1)
  step : ([] : List (Fm PTm 5)) ⊢[PRAAx]
    queryAt D.guard (var 3) (var 4) ⟶ queryAt (allOf D.residuals) (var 3) (var 4) ⟶
    stageAt (allOf D.stageResiduals) (var 0) (var 3) (var 4) ⟶
    lt (var 0) (ap2 D.fuel (var 3) (var 4)) ⟶ invAt D (var 0) (var 1) (var 3) (var 4) ⟶
    valid X (var 2) (ap3 D.query (var 0) (var 3) (var 4)) (var 4) ⟶
      invAt D (succ (var 0)) (stepAt D (var 0) (var 1) (var 2) (var 3) (var 4)) (var 3) (var 4)
  final : ([] : List (Fm PTm 3)) ⊢[PRAAx]
    queryAt D.guard (var 1) (var 2) ⟶ queryAt (allOf D.residuals) (var 1) (var 2) ⟶
    invAt D (ap2 D.fuel (var 1) (var 2)) (var 0) (var 1) (var 2) ⟶ valid Y (var 0) (var 1) (var 2)
  relBase : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    D.guard ⟶ allOf D.residuals ⟶ relAt D zero
      (ap2 D.initial (var 0) (var 1)) (ap2 D.initial (var 0) (var 1)) (var 0) (var 1)
  relStep : ([] : List (Fm PTm 7)) ⊢[PRAAx]
    queryAt D.guard (var 5) (var 6) ⟶ queryAt (allOf D.residuals) (var 5) (var 6) ⟶
    stageAt (allOf D.stageResiduals) (var 0) (var 5) (var 6) ⟶
    lt (var 0) (ap2 D.fuel (var 5) (var 6)) ⟶
    invAt D (var 0) (var 1) (var 5) (var 6) ⟶ invAt D (var 0) (var 2) (var 5) (var 6) ⟶
    relAt D (var 0) (var 1) (var 2) (var 5) (var 6) ⟶
    valid X (var 3) (ap3 D.query (var 0) (var 5) (var 6)) (var 6) ⟶
    valid X (var 4) (ap3 D.query (var 0) (var 5) (var 6)) (var 6) ⟶
    related X (var 3) (var 4) (ap3 D.query (var 0) (var 5) (var 6)) (var 6) ⟶
      relAt D (succ (var 0)) (stepAt D (var 0) (var 1) (var 3) (var 5) (var 6))
        (stepAt D (var 0) (var 2) (var 4) (var 5) (var 6)) (var 5) (var 6)
  relFinal : ([] : List (Fm PTm 4)) ⊢[PRAAx]
    queryAt D.guard (var 2) (var 3) ⟶ queryAt (allOf D.residuals) (var 2) (var 3) ⟶
    invAt D (ap2 D.fuel (var 2) (var 3)) (var 0) (var 2) (var 3) ⟶
    invAt D (ap2 D.fuel (var 2) (var 3)) (var 1) (var 2) (var 3) ⟶
    relAt D (ap2 D.fuel (var 2) (var 3)) (var 0) (var 1) (var 2) (var 3) ⟶
      related Y (var 0) (var 1) (var 2) (var 3)

theorem Laws.base_at {X Y : Interface} {D : Code} (h : Laws X Y D) (q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p) :
    Γ ⊢[PRAAx] invAt D zero (ap2 D.initial q p) q p := by
  have law := inst (Γ := Γ) h.base ![q, p]
  have specialized : Γ ⊢[PRAAx] queryAt D.guard q p ⟶ queryAt (allOf D.residuals) q p ⟶
      invAt D zero (ap2 D.initial q p) q p := by simpa [queryAt] using law
  exact .impE (.impE specialized hg) hr

theorem Laws.step_at {X Y : Interface} {D : Code} (h : Laws X Y D) (i s c q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p)
    (hs : Γ ⊢[PRAAx] stageAt (allOf D.stageResiduals) i q p)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) (hinv : Γ ⊢[PRAAx] invAt D i s q p)
    (hc : Γ ⊢[PRAAx] valid X c (ap3 D.query i q p) p) :
    Γ ⊢[PRAAx] invAt D (succ i) (stepAt D i s c q p) q p := by
  have law := inst (Γ := Γ) h.step ![i, s, c, q, p]
  have specialized : Γ ⊢[PRAAx] queryAt D.guard q p ⟶ queryAt (allOf D.residuals) q p ⟶
      stageAt (allOf D.stageResiduals) i q p ⟶ lt i (ap2 D.fuel q p) ⟶ invAt D i s q p ⟶
      valid X c (ap3 D.query i q p) p ⟶ invAt D (succ i) (stepAt D i s c q p) q p := by simpa using law
  exact .impE (.impE (.impE (.impE (.impE (.impE specialized hg) hr) hs) hi) hinv) hc

theorem Laws.final_at {X Y : Interface} {D : Code} (h : Laws X Y D) (s q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p)
    (hi : Γ ⊢[PRAAx] invAt D (ap2 D.fuel q p) s q p) : Γ ⊢[PRAAx] valid Y s q p := by
  have law := inst (Γ := Γ) h.final ![s, q, p]
  have specialized : Γ ⊢[PRAAx] queryAt D.guard q p ⟶ queryAt (allOf D.residuals) q p ⟶
      invAt D (ap2 D.fuel q p) s q p ⟶ valid Y s q p := by simpa using law
  exact .impE (.impE (.impE specialized hg) hr) hi

/-! ## Actual demand and primitive-recursive accumulator programs -/

def queryBody (D : Code) : PTm 2 := ap3 D.query (var 0) (fstT (var 1)) (sndT (var 1))
def demands (D : Code) (q p : PTm n) : PTm n := sequence (queryBody D) (ap2 D.fuel q p) (pairT q p)
def demandF (D : Code) : PR 2 := PTm.toPR (demands D (var 0) (var 1))

ipra_subst demands

theorem demands_length (D : Code) (q p : PTm n) : Γ ⊢[PRAAx] length (demands D q p) ≐ ap2 D.fuel q p :=
  MasterCertificate.sequence_length _ _ _

theorem queryBody_at (D : Code) (i q p : PTm n) :
    Γ ⊢[PRAAx] inst2 (queryBody D) i (pairT q p) ≐ ap3 D.query i q p := by
  simp only [inst2, queryBody, subst_ap3, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact congrAp3 D.query (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

theorem demands_lookup (D : Code) (i q p : PTm n) (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) :
    Γ ⊢[PRAAx] entry (demands D q p) i ≐ ap3 D.query i q p :=
  (sequence_decode (queryBody D) hi).eqTrans (queryBody_at D i q p)

theorem demand_at (D : Code) (q p : PTm n) : Γ ⊢[PRAAx] ap2 (demandF D) q p ≐ demands D q p := by
  have h := toPR_eq (Γ := Γ) (demands D (var 0) (var 1)) ![q, p]
  simpa [demandF, ap2] using h

def initTerm (D : Code) : PTm 1 := ap2 D.initial (fstT (sndT (var 0))) (sndT (sndT (var 0)))
def stepTerm (D : Code) : PTm 3 := stepAt D (var 0) (var 1) (entry (fstT (var 2)) (var 0))
  (fstT (sndT (var 2))) (sndT (sndT (var 2)))
def run (D : Code) (j C q p : PTm n) : PTm n :=
  TraceReflection.Run (initTerm D) (stepTerm D) j (pairT C (pairT q p))
def transformTerm (D : Code) (C q p : PTm n) : PTm n := run D (ap2 D.fuel q p) C q p
def transformF (D : Code) : PR 3 := PTm.toPR (transformTerm D (var 0) (var 1) (var 2))

ipra_subst run
ipra_subst transformTerm

theorem run_zero (D : Code) (C q p : PTm n) : Γ ⊢[PRAAx] run D zero C q p ≐ ap2 D.initial q p := by
  have h := TraceReflection.run_zero (Δ := Γ) (init := initTerm D) (step := stepTerm D) (pairT C (pairT q p))
  simp only [initTerm, subst_ap2, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero] at h
  exact h.eqTrans (congrAp2 D.initial ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))

theorem run_succ (D : Code) (j C q p : PTm n) :
    Γ ⊢[PRAAx] run D (succ j) C q p ≐ stepAt D j (run D j C q p) (entry C j) q p := by
  have h := TraceReflection.run_succ (Δ := Γ) (init := initTerm D) (step := stepTerm D) j (pairT C (pairT q p))
  simp only [stepTerm, subst_stepAt, MasterCertificate.subst_entry, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  exact h.eqTrans (congrAp3 D.step (.eqRefl _) (.eqRefl _)
    (pair_congr (SequenceComposition.entry_congr (fst_pair _ _) (.eqRefl _))
      (pair_congr ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
        ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))))

theorem transform_at (D : Code) (C q p : PTm n) :
    Γ ⊢[PRAAx] ap3 (transformF D) C q p ≐ transformTerm D C q p := by
  have h := toPR_eq (Γ := Γ) (transformTerm D (var 0) (var 1) (var 2)) ![C, q, p]
  simpa [transformF, ap3] using h

#print axioms demands_lookup
#print axioms run_zero
#print axioms run_succ

/-! ## Named producers, specialized at every actually executed stage -/

def stageTemplate (D : Code) (A : Fm PTm 3) : Fm PTm 2 :=
  .all (lt (var 0) (ap2 D.fuel (var 1) (var 2)) ⟶ A)

def residuals (D : Code) : List (Fm PTm 2) := D.residuals ++ D.stageResiduals.map (stageTemplate D)

theorem stageTemplate_subst (D : Code) (A : Fm PTm 3) (q p : PTm n) :
    queryAt (stageTemplate D A) q p = .all
      (lt (var 0) (ap2 D.fuel (Syn.shift q) (Syn.shift p)) ⟶ stageAt A (var 0) (Syn.shift q) (Syn.shift p)) := by
  have upEq : Syn.up ![q, p] = ![var 0, Syn.shift q, Syn.shift p] := by
    funext j; fin_cases j <;> rfl
  simp only [queryAt, stageTemplate, Fm.subst_all, upEq, Fm.subst_imp, subst_lt, subst_ap2,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, stageAt]

theorem stageTemplate_at (D : Code) (A : Fm PTm 3) (i q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (stageTemplate D A) q p) (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) :
    Γ ⊢[PRAAx] stageAt A i q p := by
  have rule : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p) ⟶ stageAt A i q p := by
    rw [stageTemplate_subst] at h
    have e := Prf.allE i h
    simpa only [Fm.subst_imp, subst_lt, subst_ap2, subst_stageAt, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift] using e
  exact .impE rule hi

theorem global_residuals_at (D : Code) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (allOf (residuals D)) q p) :
    Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p := by
  apply allOf_at_intro D.residuals ![q, p]
  intro A hA
  exact allOf_at_elim (residuals D) ![q, p] h (List.mem_append_left _ hA)

theorem stage_residuals_at (D : Code) (i q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (allOf (residuals D)) q p) (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) :
    Γ ⊢[PRAAx] stageAt (allOf D.stageResiduals) i q p := by
  apply allOf_at_intro D.stageResiduals ![i, q, p]
  intro A hA
  exact stageTemplate_at D A i q p
    (allOf_at_elim (residuals D) ![q, p] h (List.mem_append_right _ (List.mem_map.mpr ⟨A, hA, rfl⟩))) hi

theorem master_input_at (X : Interface) (D : Code) (C i q p : PTm n)
    (h : Γ ⊢[PRAAx] masterValid X (demands D q p) C p) (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) :
    Γ ⊢[PRAAx] valid X (entry C i) (ap3 D.query i q p) p :=
  valid_congr X (.eqRefl _) (demands_lookup D i q p hi) (.eqRefl _)
    (master_values_at X (Prf.andE₂ (Prf.andE₂ h))
      (lt_congr (.eqRefl _) (demands_length D q p).eqSymm hi))

theorem master_input_related_at (X : Interface) (D : Code) (C C' i q p : PTm n)
    (h : Γ ⊢[PRAAx] masterRelated X (demands D q p) C C' p) (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) :
    Γ ⊢[PRAAx] related X (entry C i) (entry C' i) (ap3 D.query i q p) p :=
  related_congr X (.eqRefl _) (.eqRefl _) (demands_lookup D i q p hi) (.eqRefl _)
    (master_related_at X h (lt_congr (.eqRefl _) (demands_length D q p).eqSymm hi))

/-! ## The source fold really supplies the checked guarded-loop obligations -/

def masterOf (u : PTm n) : PTm n := fstT u
def queryOf (u : PTm n) : PTm n := fstT (sndT u)
def parameterOf (u : PTm n) : PTm n := sndT (sndT u)

ipra_subst masterOf
ipra_subst queryOf
ipra_subst parameterOf

def external (X : Interface) (D : Code) (C q p : PTm n) : Fm PTm n :=
  queryAt D.guard q p ⋏ queryAt (allOf (residuals D)) q p ⋏ masterValid X (demands D q p) C p

@[simp] theorem subst_external {k : ℕ} (σ : Fin n → PTm k) (X : Interface) (D : Code) (C q p : PTm n) :
    (external X D C q p).subst σ = external X D (Syn.subst σ C) (Syn.subst σ q) (Syn.subst σ p) := by
  simp only [external, Fm.subst_and, subst_queryAt, subst_masterValid, subst_demands]

def sourceGuard (X : Interface) (D : Code) : Fm PTm 1 :=
  external X D (masterOf (var 0)) (queryOf (var 0)) (parameterOf (var 0))
def sourceInvariant (D : Code) : Fm PTm 3 := invAt D (var 0) (var 1) (queryOf (var 2)) (parameterOf (var 2))
def sourceFuel (D : Code) : PTm 1 := ap2 D.fuel (queryOf (var 0)) (parameterOf (var 0))
def sourceOutput (Y : Interface) : Fm PTm 2 := valid Y (var 0) (queryOf (var 1)) (parameterOf (var 1))

theorem sourceGuard_at (X : Interface) (D : Code) (u : PTm n) :
    ClockedDescent.Pat (sourceGuard X D) u = external X D (masterOf u) (queryOf u) (parameterOf u) := by
  simp [ClockedDescent.Pat, sourceGuard]

theorem sourceInvariant_at (D : Code) (i s u : PTm n) :
    TraceReflection.I3 (sourceInvariant D) i s u = invAt D i s (queryOf u) (parameterOf u) := by
  simp [TraceReflection.I3, sourceInvariant]

theorem sourceFuel_at (D : Code) (u : PTm n) :
    Syn.subst ![u] (sourceFuel D) = ap2 D.fuel (queryOf u) (parameterOf u) := by simp [sourceFuel]

theorem sourceOutput_at (Y : Interface) (s u : PTm n) :
    TraceReflection.A2 (sourceOutput Y) s u = valid Y s (queryOf u) (parameterOf u) := by
  simp [TraceReflection.A2, sourceOutput]

theorem checked_source_loop {X Y : Interface} {D : Code} (h : Laws X Y D) :
    GuardedLoop.Loop (initTerm D) (stepTerm D) (sourceFuel D) (sourceInvariant D)
      (sourceGuard X D) (sourceOutput Y) where
  qf := subst_QF' h.qf _
  base := by
    refine .impI ?_
    have ext : [sourceGuard X D] ⊢[PRAAx]
        external X D (masterOf (var 0)) (queryOf (var 0)) (parameterOf (var 0)) := Prf.hyp0
    have first := h.base_at (queryOf (var 0)) (parameterOf (var 0))
      (Prf.andE₁ ext) (global_residuals_at D _ _ (Prf.andE₁ (Prf.andE₂ ext)))
    simpa [sourceInvariant_at, initTerm, queryOf, parameterOf] using first
  step := by
    rw [sourceGuard_at, sourceFuel_at, sourceInvariant_at, sourceInvariant_at]
    refine .impI (.impI (.impI ?_))
    have ext : [invAt D (var 0 : PTm 3) (var 1) (queryOf (var 2)) (parameterOf (var 2)),
        lt (var 0) (ap2 D.fuel (queryOf (var 2)) (parameterOf (var 2))),
        external X D (masterOf (var 2)) (queryOf (var 2)) (parameterOf (var 2))] ⊢[PRAAx]
        external X D (masterOf (var 2)) (queryOf (var 2)) (parameterOf (var 2)) := hyp2
    have next := h.step_at (var 0) (var 1) (entry (masterOf (var 2)) (var 0))
      (queryOf (var 2)) (parameterOf (var 2)) (Prf.andE₁ ext)
      (global_residuals_at D _ _ (Prf.andE₁ (Prf.andE₂ ext)))
      (stage_residuals_at D _ _ _ (Prf.andE₁ (Prf.andE₂ ext)) Prf.hyp1) Prf.hyp1 Prf.hyp0
      (master_input_at X D _ _ _ _ (Prf.andE₂ (Prf.andE₂ ext)) Prf.hyp1)
    exact next
  final := by
    rw [sourceGuard_at, sourceInvariant_at, sourceFuel_at, sourceOutput_at]
    refine .impI (.impI ?_)
    have ext : [invAt D (ap2 D.fuel (queryOf (var 1 : PTm 2)) (parameterOf (var 1)))
        (var 0) (queryOf (var 1)) (parameterOf (var 1)),
        external X D (masterOf (var 1)) (queryOf (var 1)) (parameterOf (var 1))] ⊢[PRAAx]
        external X D (masterOf (var 1)) (queryOf (var 1)) (parameterOf (var 1)) := Prf.hyp1
    exact h.final_at (var 0) (queryOf (var 1)) (parameterOf (var 1)) (Prf.andE₁ ext)
      (global_residuals_at D _ _ (Prf.andE₁ (Prf.andE₂ ext))) Prf.hyp0

#print axioms checked_source_loop

theorem external_congr (X : Interface) (D : Code) {C C' q q' p p' : PTm n}
    (hC : Γ ⊢[PRAAx] C ≐ C') (hq : Γ ⊢[PRAAx] q ≐ q') (hp : Γ ⊢[PRAAx] p ≐ p')
    (h : Γ ⊢[PRAAx] external X D C q p) : Γ ⊢[PRAAx] external X D C' q' p' := by
  have source : Γ ⊢[PRAAx] (external X D (var 0) (var 1) (var 2)).subst ![C, q, p] := by simpa using h
  have out := Prf.eqSubst (external X D (var 0) (var 1) (var 2)) ![C, q, p] ![C', q', p']
    (fun j => by fin_cases j <;> assumption) source
  simpa using out

/-- Source guarded-loop elimination yields actual bounded-fold soundness. -/
theorem fold_sound {X Y : Interface} {D : Code} (h : Laws X Y D) (C q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf (residuals D)) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p) :
    Γ ⊢[PRAAx] valid Y (transformTerm D C q p) q p := by
  let u := pairT C (pairT q p)
  have ec : Γ ⊢[PRAAx] masterOf u ≐ C := fst_pair _ _
  have eq : Γ ⊢[PRAAx] queryOf u ≐ q := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have ep : Γ ⊢[PRAAx] parameterOf u ≐ p := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  have hext := external_congr X D ec.eqSymm eq.eqSymm ep.eqSymm (.andI hg (.andI hr hC))
  have g : Γ ⊢[PRAAx] ClockedDescent.Pat (sourceGuard X D) u := by rw [sourceGuard_at]; exact hext
  have result := GuardedLoop.loop_at (checked_source_loop h) u g
  rw [sourceOutput_at, sourceFuel_at] at result
  have state : Γ ⊢[PRAAx] TraceReflection.Run (initTerm D) (stepTerm D)
      (ap2 D.fuel (queryOf u) (parameterOf u)) u ≐ transformTerm D C q p :=
    congrAp2 (rec2 (initTerm D) (stepTerm D)) (congrAp2 D.fuel eq ep) (.eqRefl _)
  exact valid_congr Y state eq ep result

theorem Laws.relBase_at {X Y : Interface} {D : Code} (h : Laws X Y D) (q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p) :
    Γ ⊢[PRAAx] relAt D zero (ap2 D.initial q p) (ap2 D.initial q p) q p := by
  have law := inst (Γ := Γ) h.relBase ![q, p]
  have specialized : Γ ⊢[PRAAx] queryAt D.guard q p ⟶ queryAt (allOf D.residuals) q p ⟶
      relAt D zero (ap2 D.initial q p) (ap2 D.initial q p) q p := by simpa [queryAt] using law
  exact .impE (.impE specialized hg) hr

theorem Laws.relStep_at {X Y : Interface} {D : Code} (h : Laws X Y D) (i s s' c c' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p)
    (hs : Γ ⊢[PRAAx] stageAt (allOf D.stageResiduals) i q p)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p))
    (hinv : Γ ⊢[PRAAx] invAt D i s q p) (hinv' : Γ ⊢[PRAAx] invAt D i s' q p)
    (hrel : Γ ⊢[PRAAx] relAt D i s s' q p)
    (hc : Γ ⊢[PRAAx] valid X c (ap3 D.query i q p) p)
    (hc' : Γ ⊢[PRAAx] valid X c' (ap3 D.query i q p) p)
    (hcc : Γ ⊢[PRAAx] related X c c' (ap3 D.query i q p) p) :
    Γ ⊢[PRAAx] relAt D (succ i) (stepAt D i s c q p) (stepAt D i s' c' q p) q p := by
  have law := inst (Γ := Γ) h.relStep ![i, s, s', c, c', q, p]
  have specialized : Γ ⊢[PRAAx] queryAt D.guard q p ⟶ queryAt (allOf D.residuals) q p ⟶
      stageAt (allOf D.stageResiduals) i q p ⟶ lt i (ap2 D.fuel q p) ⟶
      invAt D i s q p ⟶ invAt D i s' q p ⟶ relAt D i s s' q p ⟶
      valid X c (ap3 D.query i q p) p ⟶ valid X c' (ap3 D.query i q p) p ⟶
      related X c c' (ap3 D.query i q p) p ⟶
      relAt D (succ i) (stepAt D i s c q p) (stepAt D i s' c' q p) q p := by simpa using law
  exact .impE (.impE (.impE (.impE (.impE (.impE (.impE (.impE (.impE (.impE
    specialized hg) hr) hs) hi) hinv) hinv') hrel) hc) hc') hcc

theorem Laws.relFinal_at {X Y : Interface} {D : Code} (h : Laws X Y D) (s s' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p)
    (hi : Γ ⊢[PRAAx] invAt D (ap2 D.fuel q p) s q p) (hi' : Γ ⊢[PRAAx] invAt D (ap2 D.fuel q p) s' q p)
    (hrel : Γ ⊢[PRAAx] relAt D (ap2 D.fuel q p) s s' q p) : Γ ⊢[PRAAx] related Y s s' q p := by
  have law := inst (Γ := Γ) h.relFinal ![s, s', q, p]
  have specialized : Γ ⊢[PRAAx] queryAt D.guard q p ⟶ queryAt (allOf D.residuals) q p ⟶
      invAt D (ap2 D.fuel q p) s q p ⟶ invAt D (ap2 D.fuel q p) s' q p ⟶
      relAt D (ap2 D.fuel q p) s s' q p ⟶ related Y s s' q p := by simpa using law
  exact .impE (.impE (.impE (.impE (.impE specialized hg) hr) hi) hi') hrel

/-- Only this declared QF conjunction is used for stability induction. -/
def pairedInvariant (D : Code) (i C C' q p : PTm n) : Fm PTm n :=
  invAt D i (run D i C q p) q p ⋏ invAt D i (run D i C' q p) q p ⋏
    relAt D i (run D i C q p) (run D i C' q p) q p

@[simp] theorem subst_pairedInvariant {k : ℕ} (σ : Fin n → PTm k) (D : Code) (i C C' q p : PTm n) :
    (pairedInvariant D i C C' q p).subst σ = pairedInvariant D (Syn.subst σ i) (Syn.subst σ C)
      (Syn.subst σ C') (Syn.subst σ q) (Syn.subst σ p) := by
  simp only [pairedInvariant, Fm.subst_and, subst_invAt, subst_relAt, subst_run]

theorem pairedInvariant_qf {X Y : Interface} {D : Code} (h : Laws X Y D) (i C C' q p : PTm n) :
    (pairedInvariant D i C C' q p).QF :=
  ⟨subst_QF' h.qf _, ⟨subst_QF' h.qf _, subst_QF' h.relQf _⟩⟩

theorem paired_step {X Y : Interface} {D : Code} (h : Laws X Y D) (i C C' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf (residuals D)) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (demands D q p) C' p)
    (hrel : Γ ⊢[PRAAx] masterRelated X (demands D q p) C C' p)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p))
    (previous : Γ ⊢[PRAAx] pairedInvariant D i C C' q p) :
    Γ ⊢[PRAAx] pairedInvariant D (succ i) C C' q p := by
  have global := global_residuals_at D q p hr
  have stage := stage_residuals_at D i q p hr hi
  have input := master_input_at X D C i q p hC hi
  have input' := master_input_at X D C' i q p hC' hi
  have inputsRelated := master_input_related_at X D C C' i q p hrel hi
  have left := h.step_at i (run D i C q p) (entry C i) q p hg global stage hi (Prf.andE₁ previous) input
  have right := h.step_at i (run D i C' q p) (entry C' i) q p hg global stage hi
    (Prf.andE₁ (Prf.andE₂ previous)) input'
  have relation := h.relStep_at i (run D i C q p) (run D i C' q p) (entry C i) (entry C' i) q p
    hg global stage hi (Prf.andE₁ previous) (Prf.andE₁ (Prf.andE₂ previous))
    (Prf.andE₂ (Prf.andE₂ previous)) input input' inputsRelated
  exact .andI (invAt_congr D _ _ _ (run_succ D i C q p).eqSymm left)
    (.andI (invAt_congr D _ _ _ (run_succ D i C' q p).eqSymm right)
      (relAt_congr D _ _ _ (run_succ D i C q p).eqSymm (run_succ D i C' q p).eqSymm relation))

theorem fold_stable {X Y : Interface} {D : Code} (h : Laws X Y D) (C C' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf (residuals D)) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (demands D q p) C' p)
    (hrel : Γ ⊢[PRAAx] masterRelated X (demands D q p) C C' p) :
    Γ ⊢[PRAAx] related Y (transformTerm D C q p) (transformTerm D C' q p) q p := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (ap2 D.fuel (Syn.shift q) (Syn.shift p)) ⟶
      pairedInvariant D (var 0) (Syn.shift C) (Syn.shift C') (Syn.shift q) (Syn.shift p)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, pairedInvariant_qf h _ _ _ _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairedInvariant, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift]
      refine .impI ?_
      have base := h.base_at (Γ := le zero (ap2 D.fuel q p) :: Γ) q p hg.wk (global_residuals_at D q p hr.wk)
      have relation := h.relBase_at (Γ := le zero (ap2 D.fuel q p) :: Γ) q p hg.wk (global_residuals_at D q p hr.wk)
      exact .andI (invAt_congr D _ _ _ (run_zero D C q p).eqSymm base)
        (.andI (invAt_congr D _ _ _ (run_zero D C' q p).eqSymm base)
          (relAt_congr D _ _ _ (run_zero D C q p).eqSymm (run_zero D C' q p).eqSymm relation))
    · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairedInvariant, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let Δ : List (Fm PTm (n + 1)) :=
        le (succ (var 0)) (ap2 D.fuel (Syn.shift q) (Syn.shift p)) ::
        (le (var 0) (ap2 D.fuel (Syn.shift q) (Syn.shift p)) ⟶
          pairedInvariant D (var 0) (Syn.shift C) (Syn.shift C') (Syn.shift q) (Syn.shift p)) :: Γ.map Fm.shift
      have guard : Γ.map Fm.shift ⊢[PRAAx] queryAt D.guard (Syn.shift q) (Syn.shift p) := by
        simpa only [Fm.shift, subst_queryAt, Syn.shift] using hg.shift
      have producers : Γ.map Fm.shift ⊢[PRAAx] queryAt (allOf (residuals D)) (Syn.shift q) (Syn.shift p) := by
        simpa only [Fm.shift, subst_queryAt, Syn.shift] using hr.shift
      have input : Γ.map Fm.shift ⊢[PRAAx] masterValid X (demands D (Syn.shift q) (Syn.shift p)) (Syn.shift C) (Syn.shift p) := by
        simpa only [Fm.shift, subst_masterValid, subst_demands, Syn.shift] using hC.shift
      have input' : Γ.map Fm.shift ⊢[PRAAx] masterValid X (demands D (Syn.shift q) (Syn.shift p)) (Syn.shift C') (Syn.shift p) := by
        simpa only [Fm.shift, subst_masterValid, subst_demands, Syn.shift] using hC'.shift
      have relation : Γ.map Fm.shift ⊢[PRAAx] masterRelated X (demands D (Syn.shift q) (Syn.shift p))
          (Syn.shift C) (Syn.shift C') (Syn.shift p) := by
        simpa only [Fm.shift, subst_masterRelated, subst_demands, Syn.shift] using hrel.shift
      have previous : Δ ⊢[PRAAx] pairedInvariant D (var 0) (Syn.shift C) (Syn.shift C') (Syn.shift q) (Syn.shift p) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact paired_step h (var 0) (Syn.shift C) (Syn.shift C') (Syn.shift q) (Syn.shift p)
        guard.wk.wk producers.wk.wk input.wk.wk input'.wk.wk relation.wk.wk Prf.hyp0 previous
  have endpoint : Γ ⊢[PRAAx] pairedInvariant D (ap2 D.fuel q p) C C' q p := by
    have e := Prf.allE (ap2 D.fuel q p) all
    have rule : Γ ⊢[PRAAx] le (ap2 D.fuel q p) (ap2 D.fuel q p) ⟶
        pairedInvariant D (ap2 D.fuel q p) C C' q p := by
      simpa only [Fm.subst_imp, subst_le, subst_ap2, subst_pairedInvariant, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift] using e
    exact .impE rule (le_refl _)
  exact h.relFinal_at _ _ q p hg (global_residuals_at D q p hr) (Prf.andE₁ endpoint)
    (Prf.andE₁ (Prf.andE₂ endpoint)) (Prf.andE₂ (Prf.andE₂ endpoint))

#print axioms fold_sound
#print axioms paired_step
#print axioms fold_stable

/-! ## Construct the bounded realizer and expose its actual source programs -/

def realizer {X Y : Interface} {D : Code} (h : Laws X Y D) : Realizer X Y where
  demand := demandF D
  transform := transformF D
  guard := D.guard
  residuals := residuals D
  sound := by
    let Δ : List (Fm PTm 3) := [D.guard.shift, (allOf (residuals D)).shift,
      masterValid X (ap2 (demandF D) (var 1) (var 2)) (var 0) (var 2)]
    have guard : Δ ⊢[PRAAx] queryAt D.guard (var 1) (var 2) := by rw [queryAt_shift3]; exact Prf.hyp0
    have producers : Δ ⊢[PRAAx] queryAt (allOf (residuals D)) (var 1) (var 2) := by
      rw [queryAt_shift3]; exact Prf.hyp1
    have input := masterValid_congr X (demand_at D (var 1) (var 2)) (.eqRefl _) (.eqRefl _)
      (hyp2 : Δ ⊢[PRAAx] _)
    exact valid_congr Y (transform_at D (var 0) (var 1) (var 2)).eqSymm (.eqRefl _) (.eqRefl _)
      (fold_sound h _ _ _ guard producers input)
  stable := by
    let Δ : List (Fm PTm 4) := [D.guard.shift.shift, (allOf (residuals D)).shift.shift,
      masterValid X (ap2 (demandF D) (var 2) (var 3)) (var 0) (var 3),
      masterValid X (ap2 (demandF D) (var 2) (var 3)) (var 1) (var 3),
      masterRelated X (ap2 (demandF D) (var 2) (var 3)) (var 0) (var 1) (var 3)]
    have guard : Δ ⊢[PRAAx] queryAt D.guard (var 2) (var 3) := by rw [queryAt_shift4]; exact Prf.hyp0
    have producers : Δ ⊢[PRAAx] queryAt (allOf (residuals D)) (var 2) (var 3) := by
      rw [queryAt_shift4]; exact Prf.hyp1
    have input := masterValid_congr X (demand_at D (var 2) (var 3)) (.eqRefl _) (.eqRefl _)
      (hyp2 : Δ ⊢[PRAAx] _)
    have input' := masterValid_congr X (demand_at D (var 2) (var 3)) (.eqRefl _) (.eqRefl _)
      (hyp2.wk : Δ ⊢[PRAAx] _)
    have relation := masterRelated_congr X (demand_at D (var 2) (var 3)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (hyp2.wk.wk : Δ ⊢[PRAAx] _)
    exact related_congr Y (transform_at D (var 0) (var 2) (var 3)).eqSymm
      (transform_at D (var 1) (var 2) (var 3)).eqSymm (.eqRefl _) (.eqRefl _)
      (fold_stable h _ _ _ _ guard producers input input' relation)

/-- Independent source metadata; none of these definitions reads a compiled
proof or takes a final target realizer as an input. -/
def Code.boundF (X : Interface) (D : Code) : PR 2 :=
  PTm.toPR (masterBound X (ap2 (demandF D) (var 0) (var 1)) (var 1))
def Code.verifierF (X : Interface) (D : Code) : PR 3 :=
  PTm.toPR (masterBit X (ap2 (demandF D) (var 1) (var 2)) (var 0) (var 2))
def Code.observationF (Y : Interface) (D : Code) : PR 3 :=
  PTm.toPR (ap3 Y.observe (ap3 (transformF D) (var 0) (var 1) (var 2)) (var 1) (var 2))

theorem compile_bound {X Y : Interface} {D : Code} (h : Laws X Y D) :
    (realizer h).inputBoundF = D.boundF X := rfl
theorem compile_verifier {X Y : Interface} {D : Code} (h : Laws X Y D) :
    (realizer h).inputVerifierF = D.verifierF X := rfl
theorem compile_observation {X Y : Interface} {D : Code} (h : Laws X Y D) :
    (realizer h).outputObservationF = D.observationF Y := rfl

/-- Adapter to the earlier proof-producing frontend's genuine `fold` node. -/
def sourceProgram {X Y : Interface} {D : Code} (h : Laws X Y D) (u : PTm n) :
    FiberCompiler.Program [ClockedDescent.Pat (sourceGuard X D) u]
      (TraceReflection.A2 (sourceOutput Y)
        (TraceReflection.Run (initTerm D) (stepTerm D) (Syn.subst ![u] (sourceFuel D)) u) u) :=
  .fold (checked_source_loop h) u (.input List.mem_cons_self)

theorem source_program_emits {X Y : Interface} {D : Code} (h : Laws X Y D) (u : PTm n) :
    [ClockedDescent.Pat (sourceGuard X D) u] ⊢[PRAAx]
      TraceReflection.A2 (sourceOutput Y)
        (TraceReflection.Run (initTerm D) (stepTerm D) (Syn.subst ![u] (sourceFuel D)) u) u :=
  (sourceProgram h u).compile

/-- The acyclic bounded-realizer frontend can use this derived operation.
Its local proofs were constructed from the source loop's base/step laws. -/
def primitive {X Y : Interface} {D : Code} (h : Laws X Y D) : RealizerGraph.Primitive X Y where
  code := ⟨demandF D, transformF D, D.guard, residuals D⟩
  sound := (realizer h).sound
  stable := (realizer h).stable

def program {X Y : Interface} {D : Code} (h : Laws X Y D) : RealizerGraph.Program X Y := .primitive (primitive h)

theorem program_metadata {X Y : Interface} {D : Code} (h : Laws X Y D) :
    (program h).code = (⟨demandF D, transformF D, D.guard, residuals D⟩ : RealizerGraph.Code) := rfl

/-- Runtime zero fuel returns the actual initial accumulator. -/
theorem zero_fuel (D : Code) (C q p : PTm n) (hN : Γ ⊢[PRAAx] ap2 D.fuel q p ≐ zero) :
    Γ ⊢[PRAAx] ap3 (transformF D) C q p ≐ ap2 D.initial q p :=
  (transform_at D C q p).eqTrans
    ((congrAp2 (rec2 (initTerm D) (stepTerm D)) hN (.eqRefl _)).eqTrans (run_zero D C q p))

/-! ## Closed runtime endpoints and exact literal producer sequents -/

def programsFormula (X Y : Interface) (D : Code) : Fm PTm 3 :=
  (ap2 (demandF D) (var 1) (var 2) ≐ demands D (var 1) (var 2)) ⋏
  ((length (demands D (var 1) (var 2)) ≐ ap2 D.fuel (var 1) (var 2)) ⋏
  ((ap3 (transformF D) (var 0) (var 1) (var 2) ≐ transformTerm D (var 0) (var 1) (var 2)) ⋏
  ((ap2 (D.boundF X) (var 1) (var 2) ≐ masterBound X (ap2 (demandF D) (var 1) (var 2)) (var 2)) ⋏
  ((ap3 (D.verifierF X) (var 0) (var 1) (var 2) ≐
    masterBit X (ap2 (demandF D) (var 1) (var 2)) (var 0) (var 2)) ⋏
    (ap3 (D.observationF Y) (var 0) (var 1) (var 2) ≐
      ap3 Y.observe (ap3 (transformF D) (var 0) (var 1) (var 2)) (var 1) (var 2))))))

theorem bounded_fold_programs {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (programsFormula X Y D) :=
  closeUniv 3 (.andI (demand_at D _ _) (.andI (demands_length D _ _)
    (.andI (transform_at D _ _ _) (.andI ((realizer h).inputBound_at _ _)
      (.andI ((realizer h).inputVerifier_at _ _ _) ((realizer h).outputObservation_at _ _ _))))))

/-- The actual compiled demand list supplies exactly the stage query.
The stage, output query and persistent parameter are all internal. -/
theorem bounded_fold_query (D : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (lt (var 0) (ap2 D.fuel (var 1) (var 2)) ⟶
        (entry (ap2 (demandF D) (var 1) (var 2)) (var 0) ≐ ap3 D.query (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI
    ((SequenceComposition.entry_congr (demand_at D _ _) (.eqRefl _)).eqTrans
      (demands_lookup D _ _ _ Prf.hyp0)))

/-- Actual recursion equations, without any local soundness hypothesis. -/
theorem bounded_fold_recurrence (D : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((run D zero (var 1) (var 2) (var 3) ≐ ap2 D.initial (var 2) (var 3)) ⋏
        (run D (succ (var 0)) (var 1) (var 2) (var 3) ≐
          stepAt D (var 0) (run D (var 0) (var 1) (var 2) (var 3))
            (entry (var 1) (var 0)) (var 2) (var 3))) :=
  closeUniv 4 (.andI (run_zero D _ _ _) (run_succ D _ _ _ _))

/-- The exact residual family suffices for each reached stage, including
empty stage ranges. No state-dependent producer is silently dropped. -/
theorem bounded_fold_producers (D : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (queryAt (allOf (residuals D)) (var 1) (var 2) ⟶
        lt (var 0) (ap2 D.fuel (var 1) (var 2)) ⟶
        (queryAt (allOf D.residuals) (var 1) (var 2) ⋏
          stageAt (allOf D.stageResiduals) (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.andI (global_residuals_at D _ _ Prf.hyp1)
    (stage_residuals_at D _ _ _ Prf.hyp1 Prf.hyp0))))

theorem bounded_fold_verifier {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (verifierFormula (realizer h)) :=
  bounded_master_verifier (realizer h)

theorem bounded_fold_soundness {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (soundFormula (realizer h)) :=
  bounded_realizer_soundness (realizer h)

theorem bounded_fold_stability {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (stabilityFormula (realizer h)) :=
  bounded_realizer_stability (realizer h)

theorem bounded_fold_sealed {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (sealedFormula (realizer h)) :=
  bounded_realizer_sealed (realizer h)

/-- Finite internal stage, output query and persistent parameter are retained
in every stage-specific producer, including under further frontend composition. -/
def residualContext (D : Code) (q p : PTm n) : List (Fm PTm n) :=
  (residuals D).map (fun A => queryAt A q p)

theorem fold_sequent {X Y : Interface} {D : Code} (h : Laws X Y D) (C q p : PTm n) :
    (residualContext D q p ++ [queryAt D.guard q p, ap3 (D.verifierF X) C q p ≐ one]) ⊢[PRAAx]
      valid Y (ap3 (transformF D) C q p) q p := by
  apply (realizer h).applySound C q p
  · exact .hyp (List.mem_append_right _ (List.mem_cons_self))
  · apply allOf_at_intro (residuals D) ![q, p]
    intro A hA
    exact .hyp (List.mem_append_left _ (List.mem_map.mpr ⟨A, hA, rfl⟩))
  · apply (realizer h).verifier_sound C q p
    exact .hyp (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem fold_sealed_sequent {X Y : Interface} {D : Code} (h : Laws X Y D) (q p : PTm n) :
    (residualContext D q p ++ [queryAt D.guard q p, inputTotal (realizer h) q p]) ⊢[PRAAx]
      outputTotal Y q p := by
  apply (realizer h).seal q p
  · exact .hyp (List.mem_append_right _ (List.mem_cons_self))
  · apply allOf_at_intro (residuals D) ![q, p]
    intro A hA
    exact .hyp (List.mem_append_left _ (List.mem_map.mpr ⟨A, hA, rfl⟩))
  · exact .hyp (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

#print axioms realizer
#print axioms source_program_emits
#print axioms primitive
#print axioms program_metadata
#print axioms zero_fuel
#print axioms bounded_fold_programs
#print axioms bounded_fold_query
#print axioms bounded_fold_recurrence
#print axioms bounded_fold_producers
#print axioms bounded_fold_verifier
#print axioms bounded_fold_soundness
#print axioms bounded_fold_stability
#print axioms bounded_fold_sealed
#print axioms fold_sequent
#print axioms fold_sealed_sequent

end LeanProofs.IPRA.Foundations.RealizerLoop
