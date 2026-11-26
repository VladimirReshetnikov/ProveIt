import IPRADerivations.Foundations.RealizerMasterInterface
import IPRADerivations.Foundations.RealizerLoop
import IPRADerivations.Core.SubstCommand

/-!
# A source bounded fold with variable blocks of input queries

Each actual PR3 blocks(i,q,p) returns a runtime list of arbitrary length.
The compiler flattens these lists and extracts the actual canonical submaster
for each stage. The original source-local QF state/paired invariants suffice
to construct the loop realizer. No global run or target realizer correctness
is supplied. Queries remain independent of the certificate/state; adaptive
queries and certificate-dependent producer scopes remain separate extensions.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RealizerBlockLoop

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.RealizerComposition
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length flatMap block prefixSum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

structure Code where
  fuel : PR 2
  blocks : PR 3
  initial : PR 2
  step : PR 3
  guard : Fm PTm 2
  residuals : List (Fm PTm 2)
  stageResiduals : List (Fm PTm 3)
  invariant : Fm PTm 4
  stabilityInvariant : Fm PTm 5

def stageQuery : PR 3 := PTm.toPR (pairT (var 0) (var 1) : PTm 3)
def inner (D : Code) : PR 2 := PTm.toPR
  (ap3 D.blocks (fstT (var 0)) (sndT (var 0)) (var 1) : PTm 2)
def loopCode (D : Code) : RealizerLoop.Code where
  fuel := D.fuel
  query := stageQuery
  initial := D.initial
  step := D.step
  guard := D.guard
  residuals := D.residuals
  stageResiduals := D.stageResiduals
  invariant := D.invariant
  stabilityInvariant := D.stabilityInvariant

def invAt (D : Code) (i s q p : PTm n) : Fm PTm n := RealizerLoop.invAt (loopCode D) i s q p
def relAt (D : Code) (i s s' q p : PTm n) : Fm PTm n := RealizerLoop.relAt (loopCode D) i s s' q p
def stepAt (D : Code) (i s c q p : PTm n) : PTm n := RealizerLoop.stepAt (loopCode D) i s c q p
def stageAt (A : Fm PTm 3) (i q p : PTm n) : Fm PTm n := RealizerLoop.stageAt A i q p

theorem stage_query_at (i q p : PTm n) : Γ ⊢[PRAAx] ap3 stageQuery i q p ≐ pairT i q := by
  simpa [stageQuery,ap3] using toPR_eq (Γ := Γ) (pairT (var 0) (var 1) : PTm 3) ![i,q,p]
theorem inner_at (D : Code) (r p : PTm n) : Γ ⊢[PRAAx]
    ap2 (inner D) r p ≐ ap3 D.blocks (fstT r) (sndT r) p := by
  simpa [inner,ap2] using toPR_eq (Γ := Γ)
    (ap3 D.blocks (fstT (var 0)) (sndT (var 0)) (var 1) : PTm 2) ![r,p]
theorem inner_stage (D : Code) (i q p : PTm n) : Γ ⊢[PRAAx]
    ap2 (inner D) (ap3 stageQuery i q p) p ≐ ap3 D.blocks i q p :=
  (congrAp2 (inner D) (stage_query_at i q p) (.eqRefl _)).eqTrans
    ((inner_at D (pairT i q) p).eqTrans (congrAp3 D.blocks (fst_pair i q) (snd_pair i q) (.eqRefl _)))

theorem valid_stage (X : Interface) (D : Code) (c i q p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (valid (RealizerMasterInterface.bundle X (inner D)) c (ap3 stageQuery i q p) p)
      (masterValid X (ap3 D.blocks i q p) c p) := by
  have original := RealizerMasterInterface.validity (Γ := Γ) X (inner D) c (ap3 stageQuery i q p) p
  exact .andI (.impI (masterValid_congr X (inner_stage D i q p) (.eqRefl _) (.eqRefl _) (original.wk.iffMp Prf.hyp0)))
    (.impI (original.wk.iffMpr (masterValid_congr X (inner_stage D i q p).eqSymm (.eqRefl _) (.eqRefl _) Prf.hyp0)))

theorem related_stage (X : Interface) (D : Code) (c c' i q p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (related (RealizerMasterInterface.bundle X (inner D)) c c' (ap3 stageQuery i q p) p)
      (masterRelated X (ap3 D.blocks i q p) c c' p) := by
  have original := RealizerMasterInterface.relatedness (Γ := Γ) X (inner D) c c' (ap3 stageQuery i q p) p
  exact .andI (.impI (masterRelated_congr X (inner_stage D i q p) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (original.wk.iffMp Prf.hyp0)))
    (.impI (original.wk.iffMpr (masterRelated_congr X (inner_stage D i q p).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0)))

/-- Only the local invariant contracts explicitly authorized by source C1. -/
structure Laws (X Y : Interface) (D : Code) : Prop where
  qf : D.invariant.QF
  relQf : D.stabilityInvariant.QF
  base : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    D.guard ⟶ allOf D.residuals ⟶ invAt D zero (ap2 D.initial (var 0) (var 1)) (var 0) (var 1)
  step : ([] : List (Fm PTm 5)) ⊢[PRAAx]
    queryAt D.guard (var 3) (var 4) ⟶ queryAt (allOf D.residuals) (var 3) (var 4) ⟶
    stageAt (allOf D.stageResiduals) (var 0) (var 3) (var 4) ⟶
    lt (var 0) (ap2 D.fuel (var 3) (var 4)) ⟶ invAt D (var 0) (var 1) (var 3) (var 4) ⟶
    masterValid X (ap3 D.blocks (var 0) (var 3) (var 4)) (var 2) (var 4) ⟶
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
    masterValid X (ap3 D.blocks (var 0) (var 5) (var 6)) (var 3) (var 6) ⟶
    masterValid X (ap3 D.blocks (var 0) (var 5) (var 6)) (var 4) (var 6) ⟶
    masterRelated X (ap3 D.blocks (var 0) (var 5) (var 6)) (var 3) (var 4) (var 6) ⟶
      relAt D (succ (var 0)) (stepAt D (var 0) (var 1) (var 3) (var 5) (var 6))
        (stepAt D (var 0) (var 2) (var 4) (var 5) (var 6)) (var 5) (var 6)
  relFinal : ([] : List (Fm PTm 4)) ⊢[PRAAx]
    queryAt D.guard (var 2) (var 3) ⟶ queryAt (allOf D.residuals) (var 2) (var 3) ⟶
    invAt D (ap2 D.fuel (var 2) (var 3)) (var 0) (var 2) (var 3) ⟶
    invAt D (ap2 D.fuel (var 2) (var 3)) (var 1) (var 2) (var 3) ⟶
    relAt D (ap2 D.fuel (var 2) (var 3)) (var 0) (var 1) (var 2) (var 3) ⟶
      related Y (var 0) (var 1) (var 2) (var 3)

theorem loop_laws {X Y : Interface} {D : Code} (h : Laws X Y D) :
    RealizerLoop.Laws (RealizerMasterInterface.bundle X (inner D)) Y (loopCode D) where
  qf := h.qf
  relQf := h.relQf
  base := h.base
  final := h.final
  relBase := h.relBase
  relFinal := h.relFinal
  step := by
    refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
    apply Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.ofNil h.step) ?_) ?_) ?_) ?_) ?_)
    · exact (valid_stage X D (var 2) (var 0) (var 3) (var 4)).iffMp (.hyp (by simp [loopCode]))
    · exact .hyp (by simp [loopCode])
    · exact .hyp (by simp [loopCode])
    · exact .hyp (by simp [loopCode,stageAt])
    · exact .hyp (by simp [loopCode])
    · exact .hyp (by simp [invAt])
  relStep := by
    refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))))
    apply Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.ofNil h.relStep) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_)
    · exact (related_stage X D (var 3) (var 4) (var 0) (var 5) (var 6)).iffMp (.hyp (by simp [loopCode]))
    · exact .hyp (by simp [loopCode])
    · exact .hyp (by simp [loopCode])
    · exact .hyp (by simp [loopCode,stageAt])
    · exact .hyp (by simp [loopCode])
    · exact .hyp (by simp [invAt])
    · exact .hyp (by simp [invAt])
    · exact .hyp (by simp [relAt])
    · exact (valid_stage X D (var 3) (var 0) (var 5) (var 6)).iffMp (.hyp (by simp [loopCode]))
    · exact (valid_stage X D (var 4) (var 0) (var 5) (var 6)).iffMp (.hyp (by simp [loopCode]))

def loopRawCode (D : Code) : RealizerGraph.Code :=
  ⟨RealizerLoop.demandF (loopCode D),RealizerLoop.transformF (loopCode D),D.guard,RealizerLoop.residuals (loopCode D)⟩
def code (D : Code) : RealizerGraph.Code := (RealizerMasterInterface.code (inner D)).seq (loopRawCode D)
def realizer {X Y : Interface} {D : Code} (h : Laws X Y D) : Realizer X Y :=
  compose (RealizerMasterInterface.realizer X (inner D)) (RealizerLoop.realizer (loop_laws h))
theorem realizer_code {X Y : Interface} {D : Code} (h : Laws X Y D) :
    RealizerGraph.Code.ofRealizer (realizer h) = code D := rfl

def outer (D : Code) (q p : PTm n) : PTm n := ap2 (RealizerLoop.demandF (loopCode D)) q p
def demands (D : Code) (q p : PTm n) : PTm n := flatMap (inner D) (outer D q p) p
def demandF (D : Code) : PR 2 := (code D).demand
def transformF (D : Code) : PR 3 := (code D).transform
def residuals (D : Code) : List (Fm PTm 2) := (code D).residuals
def masters (D : Code) (C q p : PTm n) : PTm n :=
  (RealizerMasterInterface.code (inner D)).bundle C (outer D q p) p
def submaster (D : Code) (C i q p : PTm n) : PTm n :=
  slice C (prefixSum (inner D) (outer D q p) p i) (length (block (inner D) (outer D q p) p i))
def run (D : Code) (i C q p : PTm n) : PTm n := RealizerLoop.run (loopCode D) i (masters D C q p) q p

ipra_subst outer
ipra_subst demands
ipra_subst submaster

theorem demand_at (D : Code) (q p : PTm n) : Γ ⊢[PRAAx] ap2 (demandF D) q p ≐ demands D q p :=
  RealizerGraph.Code.seqDemand_at (RealizerMasterInterface.code (inner D)) (loopRawCode D) q p

theorem outer_length (D : Code) (q p : PTm n) : Γ ⊢[PRAAx] length (outer D q p) ≐ ap2 D.fuel q p :=
  (congrFst (RealizerLoop.demand_at (loopCode D) q p)).eqTrans
    (RealizerLoop.demands_length (loopCode D) q p)

theorem outer_lookup (D : Code) (i q p : PTm n) (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) : Γ ⊢[PRAAx]
    entry (outer D q p) i ≐ pairT i q :=
  (SequenceComposition.entry_congr (RealizerLoop.demand_at (loopCode D) q p) (.eqRefl _)).eqTrans
    ((RealizerLoop.demands_lookup (loopCode D) i q p hi).eqTrans (stage_query_at i q p))

theorem block_at (D : Code) (i q p : PTm n) (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) : Γ ⊢[PRAAx]
    block (inner D) (outer D q p) p i ≐ ap3 D.blocks i q p :=
  (congrAp2 (inner D) (outer_lookup D i q p hi) (.eqRefl _)).eqTrans
    ((inner_at D (pairT i q) p).eqTrans (congrAp3 D.blocks (fst_pair i q) (snd_pair i q) (.eqRefl _)))

/-- The exact flattened length is the actual prefix sum of variable block lengths. -/
theorem demand_length (D : Code) (q p : PTm n) : Γ ⊢[PRAAx]
    length (demands D q p) ≐ prefixSum (inner D) (outer D q p) p (ap2 D.fuel q p) :=
  (SequenceComposition.flatMap_length (inner D) (outer D q p) p).eqTrans
    (congrAp3 (sum2F (SequenceComposition.lengthBody (inner D))) (outer_length D q p) (.eqRefl _) (.eqRefl _))

theorem flat_lookup (D : Code) (i j q p : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p))
    (hj : Γ ⊢[PRAAx] lt j (length (ap3 D.blocks i q p))) : Γ ⊢[PRAAx]
    entry (demands D q p) (prefixSum (inner D) (outer D q p) p i+j) ≐ entry (ap3 D.blocks i q p) j := by
  have range := lt_congr (.eqRefl _) (outer_length D q p).eqSymm hi
  have localRange := lt_congr (.eqRefl _) (congrFst (block_at D i q p hi)).eqSymm hj
  exact (SequenceComposition.flatMap_lookup (inner D) (outer D q p) p i j range localRange).eqTrans
    (SequenceComposition.entry_congr (block_at D i q p hi) (.eqRefl _))

theorem submaster_valid (X : Interface) (D : Code) (C i q p : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p) : Γ ⊢[PRAAx]
    masterValid X (ap3 D.blocks i q p) (submaster D C i q p) p :=
  masterValid_congr X (block_at D i q p hi) (.eqRefl _) (.eqRefl _)
    (extracted_master_valid X (inner D) (outer D q p) C p i
      (lt_congr (.eqRefl _) (outer_length D q p).eqSymm hi) hC)

theorem submaster_related (X : Interface) (D : Code) (C C' i q p : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p))
    (hC : Γ ⊢[PRAAx] masterRelated X (demands D q p) C C' p) : Γ ⊢[PRAAx]
    masterRelated X (ap3 D.blocks i q p) (submaster D C i q p) (submaster D C' i q p) p :=
  masterRelated_congr X (block_at D i q p hi) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (extracted_master_related X (inner D) (outer D q p) C C' p i
      (lt_congr (.eqRefl _) (outer_length D q p).eqSymm hi) hC)

theorem masters_lookup (X : Interface) (D : Code) (C i q p : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) : Γ ⊢[PRAAx]
    entry (masters D C q p) i ≐ submaster D C i q p :=
  (bundle_lookup (RealizerMasterInterface.realizer X (inner D)) C (outer D q p) p i
    (lt_congr (.eqRefl _) (outer_length D q p).eqSymm hi)).eqTrans
    (RealizerMasterInterface.transform_at _ _ _)

theorem transform_at (D : Code) (C q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (transformF D) C q p ≐ run D (ap2 D.fuel q p) C q p :=
  (RealizerGraph.Code.seqTransform_at (RealizerMasterInterface.code (inner D)) (loopRawCode D) C q p).eqTrans
    (RealizerLoop.transform_at (loopCode D) (masters D C q p) q p)

theorem run_zero (D : Code) (C q p : PTm n) : Γ ⊢[PRAAx] run D zero C q p ≐ ap2 D.initial q p :=
  RealizerLoop.run_zero (loopCode D) (masters D C q p) q p
theorem run_succ (X : Interface) (D : Code) (i C q p : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) : Γ ⊢[PRAAx]
    run D (succ i) C q p ≐ stepAt D i (run D i C q p) (submaster D C i q p) q p :=
  (RealizerLoop.run_succ (loopCode D) i (masters D C q p) q p).eqTrans
    (congrAp3 D.step (.eqRefl _) (.eqRefl _)
      (pair_congr (masters_lookup X D C i q p hi) (.eqRefl _)))

theorem residuals_eq (D : Code) : residuals D = RealizerLoop.residuals (loopCode D) := by
  simp [residuals,code,RealizerGraph.Code.seq,RealizerMasterInterface.code,loopRawCode]

theorem compiled_guard (D : Code) (q p : PTm n) (hg : Γ ⊢[PRAAx] queryAt D.guard q p) : Γ ⊢[PRAAx]
    queryAt (code D).guard q p := by
  have total : Γ ⊢[PRAAx] specializeAll (zero ≐ zero) (outer D q p) p := .allI (.impI (.eqRefl _))
  simpa only [code,RealizerGraph.Code.seq,RealizerMasterInterface.code,loopRawCode,queryAt,Fm.subst_and,
    subst_specializeAll,subst_ap2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,outer] using .andI hg total

theorem sound {X Y : Interface} {D : Code} (h : Laws X Y D) (C q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf (residuals D)) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p) : Γ ⊢[PRAAx]
    valid Y (ap3 (transformF D) C q p) q p :=
  (realizer h).applySound C q p (compiled_guard D q p hg) hr
    (masterValid_congr X (demand_at D q p).eqSymm (.eqRefl _) (.eqRefl _) hC)

theorem stable {X Y : Interface} {D : Code} (h : Laws X Y D) (C C' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf (residuals D)) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (demands D q p) C' p)
    (hrel : Γ ⊢[PRAAx] masterRelated X (demands D q p) C C' p) : Γ ⊢[PRAAx]
    related Y (ap3 (transformF D) C q p) (ap3 (transformF D) C' q p) q p :=
  (realizer h).applyStable C C' q p (compiled_guard D q p hg) hr
    (masterValid_congr X (demand_at D q p).eqSymm (.eqRefl _) (.eqRefl _) hC)
    (masterValid_congr X (demand_at D q p).eqSymm (.eqRefl _) (.eqRefl _) hC')
    (masterRelated_congr X (demand_at D q p).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) hrel)

def boundF (X : Interface) (D : Code) : PR 2 := (code D).boundF X
def verifierF (X : Interface) (D : Code) : PR 3 := (code D).verifierF X
def observationF (Y : Interface) (D : Code) : PR 3 := (code D).observationF Y

theorem bound_at {X Y : Interface} {D : Code} (h : Laws X Y D) (q p : PTm n) : Γ ⊢[PRAAx]
    ap2 (boundF X D) q p ≐ masterBound X (ap2 (demandF D) q p) p := (realizer h).inputBound_at q p
theorem verifier_at {X Y : Interface} {D : Code} (h : Laws X Y D) (C q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (verifierF X D) C q p ≐ masterBit X (ap2 (demandF D) q p) C p := (realizer h).inputVerifier_at C q p
theorem observation_at {X Y : Interface} {D : Code} (h : Laws X Y D) (C q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (observationF Y D) C q p ≐ ap3 Y.observe (ap3 (transformF D) C q p) q p :=
  (realizer h).outputObservation_at C q p

theorem verifier_sound {X Y : Interface} {D : Code} (h : Laws X Y D) (C q p : PTm n)
    (hc : Γ ⊢[PRAAx] ap3 (verifierF X D) C q p ≐ one) : Γ ⊢[PRAAx]
    masterValid X (demands D q p) C p :=
  masterValid_congr X (demand_at D q p) (.eqRefl _) (.eqRefl _) ((realizer h).verifier_sound C q p hc)

theorem zero_fuel (D : Code) (C q p : PTm n) (h0 : Γ ⊢[PRAAx] ap2 D.fuel q p ≐ zero) : Γ ⊢[PRAAx]
    ap3 (transformF D) C q p ≐ ap2 D.initial q p :=
  (RealizerGraph.Code.seqTransform_at (RealizerMasterInterface.code (inner D)) (loopRawCode D) C q p).eqTrans
    (RealizerLoop.zero_fuel (loopCode D) (masters D C q p) q p h0)

theorem global_producers (D : Code) (q p : PTm n)
    (hr : Γ ⊢[PRAAx] queryAt (allOf (residuals D)) q p) : Γ ⊢[PRAAx]
    queryAt (allOf D.residuals) q p :=
  RealizerLoop.global_residuals_at (loopCode D) q p (by simpa only [residuals_eq] using hr)
theorem stage_producers (D : Code) (i q p : PTm n)
    (hr : Γ ⊢[PRAAx] queryAt (allOf (residuals D)) q p) (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) : Γ ⊢[PRAAx]
    stageAt (allOf D.stageResiduals) i q p :=
  RealizerLoop.stage_residuals_at (loopCode D) i q p (by simpa only [residuals_eq] using hr) hi

def primitive {X Y : Interface} {D : Code} (h : Laws X Y D) : RealizerGraph.Primitive X Y where
  code := code D
  sound := (realizer h).sound
  stable := (realizer h).stable
def program {X Y : Interface} {D : Code} (h : Laws X Y D) : RealizerGraph.Program X Y := .primitive (primitive h)
theorem program_code {X Y : Interface} {D : Code} (h : Laws X Y D) : (program h).code = code D := rfl

theorem block_fold_programs {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap2 (demandF D) (var 1) (var 2) ≐ demands D (var 1) (var 2) ⋏
      (ap3 (transformF D) (var 0) (var 1) (var 2) ≐ run D (ap2 D.fuel (var 1) (var 2)) (var 0) (var 1) (var 2) ⋏
      (ap2 (boundF X D) (var 1) (var 2) ≐ masterBound X (ap2 (demandF D) (var 1) (var 2)) (var 2) ⋏
      (ap3 (verifierF X D) (var 0) (var 1) (var 2) ≐ masterBit X (ap2 (demandF D) (var 1) (var 2)) (var 0) (var 2) ⋏
        ap3 (observationF Y D) (var 0) (var 1) (var 2) ≐
          ap3 Y.observe (ap3 (transformF D) (var 0) (var 1) (var 2)) (var 1) (var 2))))) :=
  closeUniv 3 (.andI (demand_at D _ _) (.andI (transform_at D _ _ _)
    (.andI (bound_at h _ _) (.andI (verifier_at h _ _ _) (observation_at h _ _ _)))))

theorem block_fold_lookup (D : Code) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 0) (ap2 D.fuel (var 2) (var 3)) ⟶ lt (var 1) (length (ap3 D.blocks (var 0) (var 2) (var 3))) ⟶
      entry (demands D (var 2) (var 3))
        (prefixSum (inner D) (outer D (var 2) (var 3)) (var 3) (var 0)+(var 1)) ≐
          entry (ap3 D.blocks (var 0) (var 2) (var 3)) (var 1)) :=
  closeUniv 4 (.impI (.impI (flat_lookup D _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem block_fold_length (D : Code) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (demands D (var 0) (var 1)) ≐
      prefixSum (inner D) (outer D (var 0) (var 1)) (var 1) (ap2 D.fuel (var 0) (var 1))) :=
  closeUniv 2 (demand_length D _ _)
theorem block_fold_submaster (X : Interface) (D : Code) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (masterValid X (demands D (var 2) (var 3)) (var 0) (var 3) ⟶
      lt (var 1) (ap2 D.fuel (var 2) (var 3)) ⟶
        masterValid X (ap3 D.blocks (var 1) (var 2) (var 3))
          (submaster D (var 0) (var 1) (var 2) (var 3)) (var 3)) :=
  closeUniv 4 (.impI (.impI (submaster_valid X D _ _ _ _ Prf.hyp0 Prf.hyp1)))
theorem block_fold_recurrence (X : Interface) (D : Code) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run D zero (var 1) (var 2) (var 3) ≐ ap2 D.initial (var 2) (var 3) ⋏
      (lt (var 0) (ap2 D.fuel (var 2) (var 3)) ⟶
        run D (succ (var 0)) (var 1) (var 2) (var 3) ≐ stepAt D (var 0)
          (run D (var 0) (var 1) (var 2) (var 3)) (submaster D (var 1) (var 0) (var 2) (var 3)) (var 2) (var 3))) :=
  closeUniv 4 (.andI (run_zero D _ _ _) (.impI (run_succ X D _ _ _ _ Prf.hyp0)))
theorem block_fold_producers (D : Code) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (queryAt (allOf (residuals D)) (var 1) (var 2) ⟶ lt (var 0) (ap2 D.fuel (var 1) (var 2)) ⟶
      queryAt (allOf D.residuals) (var 1) (var 2) ⋏ stageAt (allOf D.stageResiduals) (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.andI (global_producers D _ _ Prf.hyp1) (stage_producers D _ _ _ Prf.hyp1 Prf.hyp0))))

theorem block_fold_soundness {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (queryAt D.guard (var 1) (var 2) ⟶ queryAt (allOf (residuals D)) (var 1) (var 2) ⟶
        masterValid X (demands D (var 1) (var 2)) (var 0) (var 2) ⟶
          valid Y (ap3 (transformF D) (var 0) (var 1) (var 2)) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (sound h _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem block_fold_stability {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (stabilityFormula (realizer h)) := bounded_realizer_stability (realizer h)
theorem block_fold_verifier {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (verifierFormula (realizer h)) := bounded_master_verifier (realizer h)
theorem block_fold_sealed {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (queryAt D.guard (var 0) (var 1) ⟶ queryAt (allOf (residuals D)) (var 0) (var 1) ⟶
        inputTotal (realizer h) (var 0) (var 1) ⟶ outputTotal Y (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (.impI ((realizer h).seal _ _ (compiled_guard D _ _ hyp2) Prf.hyp1 Prf.hyp0))))

theorem block_fold_source_stability {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (queryAt D.guard (var 2) (var 3) ⟶ queryAt (allOf (residuals D)) (var 2) (var 3) ⟶
        masterValid X (demands D (var 2) (var 3)) (var 0) (var 3) ⟶
        masterValid X (demands D (var 2) (var 3)) (var 1) (var 3) ⟶
        masterRelated X (demands D (var 2) (var 3)) (var 0) (var 1) (var 3) ⟶
          related Y (ap3 (transformF D) (var 0) (var 2) (var 3))
            (ap3 (transformF D) (var 1) (var 2) (var 3)) (var 2) (var 3)) := by
  apply closeUniv 4
  refine .impI (.impI (.impI (.impI (.impI ?_))))
  exact stable h _ _ _ _ (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))

def residualContext (D : Code) (q p : PTm n) : List (Fm PTm n) :=
  (residuals D).map (fun A => queryAt A q p)

theorem block_fold_sequent {X Y : Interface} {D : Code} (h : Laws X Y D) (C q p : PTm n) :
    (residualContext D q p ++ [queryAt D.guard q p,ap3 (verifierF X D) C q p ≐ one]) ⊢[PRAAx]
      valid Y (ap3 (transformF D) C q p) q p := by
  apply sound h C q p
  · exact .hyp (List.mem_append_right _ List.mem_cons_self)
  · apply allOf_at_intro (residuals D) ![q,p]
    intro A ha
    exact .hyp (List.mem_append_left _ (List.mem_map.mpr ⟨A,ha,rfl⟩))
  · exact verifier_sound h C q p (.hyp (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem block_fold_sealed_sequent {X Y : Interface} {D : Code} (h : Laws X Y D) (q p : PTm n) :
    (residualContext D q p ++ [queryAt D.guard q p,inputTotal (realizer h) q p]) ⊢[PRAAx]
      outputTotal Y q p := by
  apply (realizer h).seal q p
  · exact compiled_guard D q p (.hyp (List.mem_append_right _ List.mem_cons_self))
  · apply allOf_at_intro (residuals D) ![q,p]
    intro A ha
    exact .hyp (List.mem_append_left _ (List.mem_map.mpr ⟨A,ha,rfl⟩))
  · exact .hyp (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

end LeanProofs.IPRA.Foundations.RealizerBlockLoop
