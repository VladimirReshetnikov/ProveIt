import IPRADerivations.Foundations.RealizerBlockLoop

/-!
# Finite-candidate state-adaptive interface calls

FIBER C1's bounded fold/call constructor. Each stage prefetches its actual
finite candidate table, then the current state selects the certificate read
by the actual next step. The full variable-block loop contracts are derived
from one-certificate local source contracts. Paired selector alignment is an
explicit local observation contract; no cross-query relation is inferred.

The final section supplies a genuine parity-adaptive accumulator, discharging
all local arithmetic and paired contracts. State-dependent producer scopes,
unbounded candidate sets and cyclic certificate execution remain separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.RealizerStateAdaptive

open_ipra exports
open LeanProofs.IPRA.Foundations.RealizerComposition
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

structure Code where
  fuel : PR 2
  cap : PR 3
  candidate : PR 4
  slot : PR 4
  initial : PR 2
  step : PR 5
  guard : Fm PTm 2
  residuals : List (Fm PTm 2)
  stageResiduals : List (Fm PTm 3)
  invariant : Fm PTm 4
  stabilityInvariant : Fm PTm 5

def selectedSlot (D : Code) (i s q p : PTm n) : PTm n := ap4 D.slot i s q p
def candidate (D : Code) (i t q p : PTm n) : PTm n := ap4 D.candidate i t q p
def localStep (D : Code) (i s c q p : PTm n) : PTm n := app D.step ![i,s,c,q,p]
def queryAtState (D : Code) (i s q p : PTm n) : PTm n := candidate D i (selectedSlot D i s q p) q p
def invAt (D : Code) (i s q p : PTm n) : Fm PTm n := D.invariant.subst ![i,s,q,p]
def relAt (D : Code) (i s s' q p : PTm n) : Fm PTm n := D.stabilityInvariant.subst ![i,s,s',q,p]
def stageAt (D : Code) (i q p : PTm n) : Fm PTm n := RealizerBlockLoop.stageAt (allOf D.stageResiduals) i q p
def candidateData (i q p : PTm n) : PTm n := pairT i (pairT q p)
def candidateBody (D : Code) : PTm 2 := candidate D (fstT (var 1)) (var 0)
  (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def candidateBlock (D : Code) (i q p : PTm n) : PTm n :=
  sequence (candidateBody D) (ap3 D.cap i q p) (candidateData i q p)
def blocksF (D : Code) : PR 3 := PTm.toPR (candidateBlock D (var 0) (var 1) (var 2))
def adaptiveStep (D : Code) (i s C q p : PTm n) : PTm n :=
  localStep D i s (entry C (selectedSlot D i s q p)) q p
def adapterBody (D : Code) : PTm 3 := adaptiveStep D (var 0) (var 1) (fstT (var 2))
  (fstT (sndT (var 2))) (sndT (sndT (var 2)))
def adapterF (D : Code) : PR 3 := PTm.toPR (adapterBody D)
def blockCode (D : Code) : RealizerBlockLoop.Code where
  fuel := D.fuel
  blocks := blocksF D
  initial := D.initial
  step := adapterF D
  guard := D.guard
  residuals := D.residuals
  stageResiduals := D.stageResiduals
  invariant := D.invariant
  stabilityInvariant := D.stabilityInvariant

ipra_subst selectedSlot
ipra_subst candidate
@[simp] theorem subst_localStep {m : ℕ} (σ : Fin n → PTm m) (D : Code) (i s c q p : PTm n) :
    Syn.subst σ (localStep D i s c q p) = localStep D (Syn.subst σ i) (Syn.subst σ s) (Syn.subst σ c) (Syn.subst σ q) (Syn.subst σ p) := by
  simp only [localStep,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl
@[simp] theorem subst_candidateData {m : ℕ} (σ : Fin n → PTm m) (i q p : PTm n) :
    Syn.subst σ (candidateData i q p) = candidateData (Syn.subst σ i) (Syn.subst σ q) (Syn.subst σ p) := by simp [candidateData]
ipra_subst candidateBlock
ipra_subst adaptiveStep

theorem candidate_body_at (D : Code) (i t q p : PTm n) : Γ ⊢[PRAAx]
    inst2 (candidateBody D) t (candidateData i q p) ≐ candidate D i t q p := by
  simp only [candidateBody,inst2,subst_candidate,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have e := snd_pair (Γ := Γ) i (pairT q p)
  apply congrApp D.candidate
  intro j
  fin_cases j
  · exact fst_pair _ _
  · exact .eqRefl t
  · exact (congrFst e).eqTrans (fst_pair _ _)
  · exact (congrSnd e).eqTrans (snd_pair _ _)
theorem candidate_length (D : Code) (i q p : PTm n) : Γ ⊢[PRAAx]
    length (candidateBlock D i q p) ≐ ap3 D.cap i q p := MasterCertificate.sequence_length _ _ _
theorem candidate_lookup (D : Code) (i t q p : PTm n)
    (ht : Γ ⊢[PRAAx] lt t (ap3 D.cap i q p)) : Γ ⊢[PRAAx]
    entry (candidateBlock D i q p) t ≐ candidate D i t q p :=
  (MasterCertificate.sequence_decode (candidateBody D) ht).eqTrans (candidate_body_at D i t q p)
theorem blocks_at (D : Code) (i q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (blocksF D) i q p ≐ candidateBlock D i q p := by
  simpa [blocksF,ap3] using toPR_eq (Γ := Γ) (candidateBlock D (var 0) (var 1) (var 2)) ![i,q,p]
theorem adapter_at (D : Code) (i s C q p : PTm n) : Γ ⊢[PRAAx]
    RealizerBlockLoop.stepAt (blockCode D) i s C q p ≐ adaptiveStep D i s C q p := by
  have start := toPR_eq (Γ := Γ) (adapterBody D) ![i,s,pairT C (pairT q p)]
  have eqs : Γ ⊢[PRAAx]
      adaptiveStep D i s (fstT (pairT C (pairT q p)))
        (fstT (sndT (pairT C (pairT q p)))) (sndT (sndT (pairT C (pairT q p)))) ≐
      adaptiveStep D i s C q p := by
    have hc := fst_pair (Γ := Γ) C (pairT q p)
    have e := snd_pair (Γ := Γ) C (pairT q p)
    have hq := (congrFst e).eqTrans (fst_pair q p)
    have hp := (congrSnd e).eqTrans (snd_pair q p)
    have hs : Γ ⊢[PRAAx] selectedSlot D i s (fstT (sndT (pairT C (pairT q p))))
        (sndT (sndT (pairT C (pairT q p)))) ≐ selectedSlot D i s q p := by
      apply congrApp D.slot
      intro j
      fin_cases j; exact .eqRefl _; exact .eqRefl _; exact hq; exact hp
    apply congrApp D.step
    intro j
    fin_cases j
    · exact .eqRefl i
    · exact .eqRefl s
    · exact entry_congr hc hs
    · exact hq
    · exact hp
  have e : Γ ⊢[PRAAx] RealizerBlockLoop.stepAt (blockCode D) i s C q p ≐
      adaptiveStep D i s (fstT (pairT C (pairT q p)))
        (fstT (sndT (pairT C (pairT q p)))) (sndT (sndT (pairT C (pairT q p)))) := by
    simpa [RealizerBlockLoop.stepAt,RealizerLoop.stepAt,RealizerBlockLoop.loopCode,blockCode,adapterF,adapterBody,ap3] using start
  exact e.eqTrans eqs

/-- Only source-local contracts; no actual run or global output premise. -/
structure Laws (X Y : Interface) (D : Code) : Prop where
  qf : D.invariant.QF
  relQf : D.stabilityInvariant.QF
  base : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (q p : PTm n),
    (Γ ⊢[PRAAx] queryAt D.guard q p) → (Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p) →
    (Γ ⊢[PRAAx] invAt D zero (ap2 D.initial q p) q p)
  slot_bound : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (i s q p : PTm n),
    (Γ ⊢[PRAAx] queryAt D.guard q p) → (Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p) →
    (Γ ⊢[PRAAx] stageAt D i q p) → (Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) →
    (Γ ⊢[PRAAx] invAt D i s q p) → (Γ ⊢[PRAAx] lt (selectedSlot D i s q p) (ap3 D.cap i q p))
  step : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (i s c q p : PTm n),
    (Γ ⊢[PRAAx] queryAt D.guard q p) → (Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p) →
    (Γ ⊢[PRAAx] stageAt D i q p) → (Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) →
    (Γ ⊢[PRAAx] invAt D i s q p) → (Γ ⊢[PRAAx] valid X c (queryAtState D i s q p) p) →
    (Γ ⊢[PRAAx] invAt D (succ i) (localStep D i s c q p) q p)
  final : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (s q p : PTm n),
    (Γ ⊢[PRAAx] queryAt D.guard q p) → (Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p) →
    (Γ ⊢[PRAAx] invAt D (ap2 D.fuel q p) s q p) → (Γ ⊢[PRAAx] valid Y s q p)
  relBase : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (q p : PTm n),
    (Γ ⊢[PRAAx] queryAt D.guard q p) → (Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p) →
    (Γ ⊢[PRAAx] relAt D zero (ap2 D.initial q p) (ap2 D.initial q p) q p)
  slot_equal : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (i s s' q p : PTm n),
    (Γ ⊢[PRAAx] queryAt D.guard q p) → (Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p) →
    (Γ ⊢[PRAAx] stageAt D i q p) → (Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) →
    (Γ ⊢[PRAAx] invAt D i s q p) → (Γ ⊢[PRAAx] invAt D i s' q p) →
    (Γ ⊢[PRAAx] relAt D i s s' q p) →
    (Γ ⊢[PRAAx] selectedSlot D i s q p ≐ selectedSlot D i s' q p)
  relStep : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (i s s' c c' q p : PTm n),
    (Γ ⊢[PRAAx] queryAt D.guard q p) → (Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p) →
    (Γ ⊢[PRAAx] stageAt D i q p) → (Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) →
    (Γ ⊢[PRAAx] invAt D i s q p) → (Γ ⊢[PRAAx] invAt D i s' q p) →
    (Γ ⊢[PRAAx] relAt D i s s' q p) →
    (Γ ⊢[PRAAx] valid X c (queryAtState D i s q p) p) →
    (Γ ⊢[PRAAx] valid X c' (queryAtState D i s' q p) p) →
    (Γ ⊢[PRAAx] related X c c' (queryAtState D i s q p) p) →
    (Γ ⊢[PRAAx] relAt D (succ i) (localStep D i s c q p) (localStep D i s' c' q p) q p)
  relFinal : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (s s' q p : PTm n),
    (Γ ⊢[PRAAx] queryAt D.guard q p) → (Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p) →
    (Γ ⊢[PRAAx] invAt D (ap2 D.fuel q p) s q p) →
    (Γ ⊢[PRAAx] invAt D (ap2 D.fuel q p) s' q p) →
    (Γ ⊢[PRAAx] relAt D (ap2 D.fuel q p) s s' q p) → (Γ ⊢[PRAAx] related Y s s' q p)

theorem selected_valid (X : Interface) (D : Code) (i s C q p : PTm n)
    (hs : Γ ⊢[PRAAx] lt (selectedSlot D i s q p) (ap3 D.cap i q p))
    (hC : Γ ⊢[PRAAx] masterValid X (ap3 (blocksF D) i q p) C p) : Γ ⊢[PRAAx]
    valid X (entry C (selectedSlot D i s q p)) (queryAtState D i s q p) p := by
  have hc := masterValid_congr X (blocks_at D i q p) (.eqRefl _) (.eqRefl _) hC
  have bound := lt_congr (.eqRefl _) (candidate_length D i q p).eqSymm hs
  exact valid_congr X (.eqRefl _) (candidate_lookup D i _ q p hs) (.eqRefl _)
    (master_values_at X (.andE₂ (.andE₂ hc)) bound)

theorem selected_related (X : Interface) (D : Code) (i s s' C C' q p : PTm n)
    (hs : Γ ⊢[PRAAx] lt (selectedSlot D i s q p) (ap3 D.cap i q p))
    (he : Γ ⊢[PRAAx] selectedSlot D i s q p ≐ selectedSlot D i s' q p)
    (hr : Γ ⊢[PRAAx] masterRelated X (ap3 (blocksF D) i q p) C C' p) : Γ ⊢[PRAAx]
    related X (entry C (selectedSlot D i s q p)) (entry C' (selectedSlot D i s' q p))
      (queryAtState D i s q p) p := by
  have hc := masterRelated_congr X (blocks_at D i q p) (.eqRefl _) (.eqRefl _) (.eqRefl _) hr
  have bound := lt_congr (.eqRefl _) (candidate_length D i q p).eqSymm hs
  exact related_congr X (.eqRefl _) (entry_congr (.eqRefl _) he)
    (candidate_lookup D i _ q p hs) (.eqRefl _) (master_related_at X hc bound)

theorem block_step {X Y : Interface} {D : Code} (h : Laws X Y D) (i s C q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p)
    (hp : Γ ⊢[PRAAx] stageAt D i q p) (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p))
    (hI : Γ ⊢[PRAAx] invAt D i s q p)
    (hC : Γ ⊢[PRAAx] masterValid X (ap3 (blocksF D) i q p) C p) : Γ ⊢[PRAAx]
    invAt D (succ i) (RealizerBlockLoop.stepAt (blockCode D) i s C q p) q p := by
  have hs := h.slot_bound i s q p hg hr hp hi hI
  have next := h.step i s _ q p hg hr hp hi hI (selected_valid X D i s C q p hs hC)
  exact RealizerLoop.invAt_congr (RealizerBlockLoop.loopCode (blockCode D)) (succ i) q p
    (adapter_at D i s C q p).eqSymm next

theorem block_rel_step {X Y : Interface} {D : Code} (h : Laws X Y D) (i s s' C C' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf D.residuals) q p)
    (hp : Γ ⊢[PRAAx] stageAt D i q p) (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p))
    (hI : Γ ⊢[PRAAx] invAt D i s q p) (hI' : Γ ⊢[PRAAx] invAt D i s' q p)
    (hR : Γ ⊢[PRAAx] relAt D i s s' q p)
    (hC : Γ ⊢[PRAAx] masterValid X (ap3 (blocksF D) i q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (ap3 (blocksF D) i q p) C' p)
    (hrel : Γ ⊢[PRAAx] masterRelated X (ap3 (blocksF D) i q p) C C' p) : Γ ⊢[PRAAx]
    relAt D (succ i) (RealizerBlockLoop.stepAt (blockCode D) i s C q p)
      (RealizerBlockLoop.stepAt (blockCode D) i s' C' q p) q p := by
  have hs := h.slot_bound i s q p hg hr hp hi hI
  have hs' := h.slot_bound i s' q p hg hr hp hi hI'
  have he := h.slot_equal i s s' q p hg hr hp hi hI hI' hR
  have next := h.relStep i s s' _ _ q p hg hr hp hi hI hI' hR
    (selected_valid X D i s C q p hs hC) (selected_valid X D i s' C' q p hs' hC')
    (selected_related X D i s s' C C' q p hs he hrel)
  exact RealizerLoop.relAt_congr (RealizerBlockLoop.loopCode (blockCode D)) (succ i) q p
    (adapter_at D i s C q p).eqSymm (adapter_at D i s' C' q p).eqSymm next

@[simp] theorem block_invAt (D : Code) (i s q p : PTm n) :
    RealizerBlockLoop.invAt (blockCode D) i s q p = invAt D i s q p := rfl
@[simp] theorem block_relAt (D : Code) (i s s' q p : PTm n) :
    RealizerBlockLoop.relAt (blockCode D) i s s' q p = relAt D i s s' q p := rfl

theorem queryAt_variables (A : Fm PTm 2) : queryAt A (var 0) (var 1) = A := by
  have h : (![var 0,var 1] : Fin 2 → PTm 2) = var := by
    funext i
    fin_cases i <;> rfl
  simp only [queryAt,h,Fm.subst_id]

theorem block_laws {X Y : Interface} {D : Code} (h : Laws X Y D) :
    RealizerBlockLoop.Laws X Y (blockCode D) where
  qf := h.qf
  relQf := h.relQf
  base := by
    simp only [block_invAt]
    dsimp only [blockCode]
    refine .impI (.impI ?_)
    exact h.base _ _ (by simpa only [queryAt_variables] using (Prf.hyp (Ax := PRAAx) (Γ := [allOf D.residuals,D.guard]) (φ := D.guard) (by simp))) (by simpa only [queryAt_variables] using (Prf.hyp0 (Ax := PRAAx) (Γ := [D.guard]) (φ := allOf D.residuals)))
  step := by
    simp only [block_invAt]
    dsimp only [blockCode]
    refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
    exact block_step h _ _ _ _ _ (.hyp (by simp)) (.hyp (by simp))
      (.hyp (by simp [stageAt])) (.hyp (by simp))
      (.hyp (by simp)) (.hyp (by simp))
  final := by
    simp only [block_invAt]
    dsimp only [blockCode]
    refine .impI (.impI (.impI ?_))
    exact h.final _ _ _ (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
  relBase := by
    simp only [block_relAt]
    dsimp only [blockCode]
    refine .impI (.impI ?_)
    exact h.relBase _ _ (by simpa only [queryAt_variables] using (Prf.hyp (Ax := PRAAx) (Γ := [allOf D.residuals,D.guard]) (φ := D.guard) (by simp))) (by simpa only [queryAt_variables] using (Prf.hyp0 (Ax := PRAAx) (Γ := [D.guard]) (φ := allOf D.residuals)))
  relStep := by
    simp only [block_invAt,block_relAt]
    dsimp only [blockCode]
    refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))))
    exact block_rel_step h _ _ _ _ _ _ _ (.hyp (by simp)) (.hyp (by simp))
      (.hyp (by simp [stageAt])) (.hyp (by simp))
      (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
      (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
  relFinal := by
    simp only [block_invAt,block_relAt]
    dsimp only [blockCode]
    refine .impI (.impI (.impI (.impI (.impI ?_))))
    exact h.relFinal _ _ _ _ (.hyp (by simp)) (.hyp (by simp))
      (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))

def realizer {X Y : Interface} {D : Code} (h : Laws X Y D) : Realizer X Y := RealizerBlockLoop.realizer (block_laws h)
def code (D : Code) : RealizerGraph.Code := RealizerBlockLoop.code (blockCode D)
def demands (D : Code) (q p : PTm n) : PTm n := RealizerBlockLoop.demands (blockCode D) q p
def demandF (D : Code) : PR 2 := RealizerBlockLoop.demandF (blockCode D)
def transformF (D : Code) : PR 3 := RealizerBlockLoop.transformF (blockCode D)
def residuals (D : Code) : List (Fm PTm 2) := RealizerBlockLoop.residuals (blockCode D)
def submaster (D : Code) (C i q p : PTm n) : PTm n := RealizerBlockLoop.submaster (blockCode D) C i q p
def run (D : Code) (i C q p : PTm n) : PTm n := RealizerBlockLoop.run (blockCode D) i C q p
def offset (D : Code) (i q p : PTm n) : PTm n :=
  SequenceComposition.prefixSum (RealizerBlockLoop.inner (blockCode D)) (RealizerBlockLoop.outer (blockCode D) q p) p i
def selectedCertificate (D : Code) (i C q p : PTm n) : PTm n :=
  entry (submaster D C i q p) (selectedSlot D i (run D i C q p) q p)
theorem realizer_code {X Y : Interface} {D : Code} (h : Laws X Y D) :
    RealizerGraph.Code.ofRealizer (realizer h) = code D := rfl
theorem demand_at (D : Code) (q p : PTm n) : Γ ⊢[PRAAx] ap2 (demandF D) q p ≐ demands D q p :=
  RealizerBlockLoop.demand_at _ _ _
theorem transform_at (D : Code) (C q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (transformF D) C q p ≐ run D (ap2 D.fuel q p) C q p := RealizerBlockLoop.transform_at _ _ _ _
theorem run_zero (D : Code) (C q p : PTm n) : Γ ⊢[PRAAx] run D zero C q p ≐ ap2 D.initial q p :=
  RealizerBlockLoop.run_zero _ _ _ _
theorem run_succ (X : Interface) (D : Code) (i C q p : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) : Γ ⊢[PRAAx]
    run D (succ i) C q p ≐ localStep D i (run D i C q p) (selectedCertificate D i C q p) q p :=
  (RealizerBlockLoop.run_succ X (blockCode D) i C q p hi).eqTrans (adapter_at D i _ _ q p)
theorem flat_candidate (D : Code) (i t q p : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.fuel q p)) (ht : Γ ⊢[PRAAx] lt t (ap3 D.cap i q p)) : Γ ⊢[PRAAx]
    entry (demands D q p) (offset D i q p+t) ≐ candidate D i t q p := by
  have hb := lt_congr (.eqRefl _) ((congrFst (blocks_at D i q p)).eqTrans (candidate_length D i q p)).eqSymm ht
  exact (RealizerBlockLoop.flat_lookup (blockCode D) i t q p hi hb).eqTrans
    ((entry_congr (blocks_at D i q p) (.eqRefl _)).eqTrans (candidate_lookup D i t q p ht))
theorem sound {X Y : Interface} {D : Code} (h : Laws X Y D) (C q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf (residuals D)) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p) : Γ ⊢[PRAAx]
    valid Y (ap3 (transformF D) C q p) q p := RealizerBlockLoop.sound (block_laws h) _ _ _ hg hr hC
theorem stable {X Y : Interface} {D : Code} (h : Laws X Y D) (C C' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt D.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf (residuals D)) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (demands D q p) C' p)
    (he : Γ ⊢[PRAAx] masterRelated X (demands D q p) C C' p) : Γ ⊢[PRAAx]
    related Y (ap3 (transformF D) C q p) (ap3 (transformF D) C' q p) q p :=
  RealizerBlockLoop.stable (block_laws h) _ _ _ _ hg hr hC hC' he

/-! ## A concrete state-adaptive parity accumulator -/

def parityState (i s p : PTm n) : Fm PTm n :=
  (s ≐ pairT (fstT s) (sndT s)) ⋏ (le (fstT s) (i*p) ⋏ le (sndT s) one)
def parityRelation (s s' : PTm n) : Fm PTm n := (fstT s ≐ fstT s') ⋏ (sndT s ≐ sndT s')
def parityOutputFormula : BoundedSyntax.BFm 3 :=
  .and (.eq (var 0) (pairT (fstT (var 0)) (sndT (var 0))))
    (.and (.le (fstT (var 0)) (var 1*var 2)) (.le (sndT (var 0)) one))
def parityInput : Interface where
  query := PTm.toPR (one : PTm 2)
  bound := PTm.toPR (succ (var 1) : PTm 2)
  verify := PTm.toPR (one : PTm 3)
  observe := PTm.toPR (var 0 : PTm 3)
  related := PTm.toPR (eqb (var 0) (var 1) : PTm 4)
def parityOutput : Interface where
  query := PTm.toPR (one : PTm 2)
  bound := PTm.toPR (succ (pairT (var 0*var 1) one) : PTm 2)
  verify := BoundedSyntax.bitF parityOutputFormula
  observe := PTm.toPR (fstT (var 0) : PTm 3)
  related := PTm.toPR (eqb (var 0) (var 1) : PTm 4)
def parityCode : Code where
  fuel := PTm.toPR (var 0 : PTm 2)
  cap := PTm.toPR (two : PTm 3)
  candidate := PTm.toPR (pairT (var 0) (var 1) : PTm 4)
  slot := PTm.toPR (sndT (var 1) : PTm 4)
  initial := PTm.toPR (pairT zero zero : PTm 2)
  step := PTm.toPR (pairT (fstT (var 1)+var 2) (par (var 2)) : PTm 5)
  guard := zero ≐ zero
  residuals := []
  stageResiduals := []
  invariant := parityState (var 0) (var 1) (var 3)
  stabilityInvariant := parityRelation (var 1) (var 2)

@[simp] theorem parity_inv_at (i s q p : PTm n) : invAt parityCode i s q p = parityState i s p := by
  simp [invAt,parityCode,parityState]
@[simp] theorem parity_rel_at (i s s' q p : PTm n) : relAt parityCode i s s' q p = parityRelation s s' := by
  simp [relAt,parityCode,parityRelation]
theorem parity_fuel_at (q p : PTm n) : Γ ⊢[PRAAx] ap2 parityCode.fuel q p ≐ q := by
  simpa [parityCode,ap2] using toPR_eq (Γ := Γ) (var 0 : PTm 2) ![q,p]
theorem parity_cap_at (i q p : PTm n) : Γ ⊢[PRAAx] ap3 parityCode.cap i q p ≐ two := by
  simpa [parityCode,ap3] using toPR_eq (Γ := Γ) (two : PTm 3) ![i,q,p]
theorem parity_candidate_at (i t q p : PTm n) : Γ ⊢[PRAAx] candidate parityCode i t q p ≐ pairT i t := by
  simpa [candidate,parityCode,ap4] using toPR_eq (Γ := Γ) (pairT (var 0) (var 1) : PTm 4) ![i,t,q,p]
theorem parity_slot_at (i s q p : PTm n) : Γ ⊢[PRAAx] selectedSlot parityCode i s q p ≐ sndT s := by
  simpa [selectedSlot,parityCode,ap4] using toPR_eq (Γ := Γ) (sndT (var 1) : PTm 4) ![i,s,q,p]
theorem parity_initial_at (q p : PTm n) : Γ ⊢[PRAAx] ap2 parityCode.initial q p ≐ pairT zero zero := by
  simpa [parityCode,ap2] using toPR_eq (Γ := Γ) (pairT zero zero : PTm 2) ![q,p]
theorem parity_step_at (i s c q p : PTm n) : Γ ⊢[PRAAx]
    localStep parityCode i s c q p ≐ pairT (fstT s+c) (par c) := by
  have es : Syn.subst ![i,s,c,q,p] (pairT (fstT (var 1)+var 2) (par (var 2)) : PTm 5) =
      pairT (fstT s+c) (par c) := by
    simp only [subst_pairT,LeanProofs.IPRA.PTm.subst_add,subst_fstT,subst_ap1,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  have start := toPR_eq (Γ := Γ) (pairT (fstT (var 1)+var 2) (par (var 2)) : PTm 5) ![i,s,c,q,p]
  rw [es] at start
  exact start

theorem parity_input_bound (r p : PTm n) : Γ ⊢[PRAAx] ap2 parityInput.bound r p ≐ succ p := by
  simpa [parityInput,ap2] using toPR_eq (Γ := Γ) (succ (var 1) : PTm 2) ![r,p]
theorem parity_input_observation (c r p : PTm n) : Γ ⊢[PRAAx] ap3 parityInput.observe c r p ≐ c := by
  simpa [parityInput,ap3] using toPR_eq (Γ := Γ) (var 0 : PTm 3) ![c,r,p]
theorem parity_certificate_bound (c r p : PTm n) (h : Γ ⊢[PRAAx] valid parityInput c r p) : Γ ⊢[PRAAx] le c p :=
  (succ_monus_succ c p).eqSymm.eqTrans (lt_congr (.eqRefl _) (parity_input_bound r p) (.andE₁ h))
theorem parity_input_equal (c c' r p : PTm n) (h : Γ ⊢[PRAAx] related parityInput c c' r p) : Γ ⊢[PRAAx] c ≐ c' := by
  have e : Γ ⊢[PRAAx] ap4 parityInput.related (ap3 parityInput.observe c r p)
      (ap3 parityInput.observe c' r p) r p ≐ eqb (ap3 parityInput.observe c r p) (ap3 parityInput.observe c' r p) := by
    simpa [parityInput,ap4] using toPR_eq (Γ := Γ) (eqb (var 0) (var 1) : PTm 4)
      ![ap3 parityInput.observe c r p,ap3 parityInput.observe c' r p,r,p]
  have a := BoundedReflection.eq_of_eqb (e.eqSymm.eqTrans h)
  exact (parity_input_observation c r p).eqSymm.eqTrans (a.eqTrans (parity_input_observation c' r p))

theorem parity_bit_bound (c : PTm n) : Γ ⊢[PRAAx] le (par c) one := by
  refine .orE (par_cases c) ?_ ?_
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le one)
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (le_refl one)
theorem parity_pair_state (i a b p : PTm n) (ha : Γ ⊢[PRAAx] le a (i*p)) (hb : Γ ⊢[PRAAx] le b one) :
    Γ ⊢[PRAAx] parityState i (pairT a b) p :=
  .andI (pair_congr (fst_pair a b).eqSymm (snd_pair a b).eqSymm)
    (.andI (le_congr (fst_pair a b).eqSymm (.eqRefl _) ha) (le_congr (snd_pair a b).eqSymm (.eqRefl _) hb))
theorem parity_state_congr {i s t p : PTm n} (e : Γ ⊢[PRAAx] s ≐ t)
    (h : Γ ⊢[PRAAx] parityState i s p) : Γ ⊢[PRAAx] parityState i t p := by
  have out := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (parityState (var 0) (var 1) (var 2)) ![i,s,p] ![i,t,p]
    (fun j => by fin_cases j; exact .eqRefl _; exact e; exact .eqRefl _) (by simpa [parityState] using h)
  simpa [parityState] using out

theorem parity_output_valid (s N p : PTm n) (h : Γ ⊢[PRAAx] parityState N s p) :
    Γ ⊢[PRAAx] valid parityOutput s N p := by
  have cap := pair_mono (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h))
  have bound : Γ ⊢[PRAAx] lt s (succ (pairT (N*p) one)) :=
    lt_congr (Prf.andE₁ h).eqSymm (.eqRefl _) ((succ_monus_succ _ _).eqTrans cap)
  have eb : Γ ⊢[PRAAx] ap2 parityOutput.bound N p ≐ succ (pairT (N*p) one) := by
    simpa [parityOutput,ap2] using toPR_eq (Γ := Γ) (succ (pairT (var 0*var 1) one) : PTm 2) ![N,p]
  refine .andI (lt_congr (.eqRefl _) eb.eqSymm bound) ?_
  have e := BoundedSyntax.program_correct parityOutputFormula ![s,N,p] (Γ := Γ)
  have accepted : Γ ⊢[PRAAx] (BoundedSyntax.formula parityOutputFormula).subst ![s,N,p] := by
    simpa [parityOutputFormula,BoundedSyntax.formula,BoundedSyntax.BFm.le,parityState,le] using h
  exact e.eqTrans ((BoundedSyntax.bounded_reflection parityOutputFormula ![s,N,p]).iffMpr accepted)
theorem parity_output_related (s s' N p : PTm n) (h : Γ ⊢[PRAAx] parityRelation s s') :
    Γ ⊢[PRAAx] related parityOutput s s' N p := by
  have ol : Γ ⊢[PRAAx] ap3 parityOutput.observe s N p ≐ fstT s := by
    simpa [parityOutput,ap3] using toPR_eq (Γ := Γ) (fstT (var 0) : PTm 3) ![s,N,p]
  have or : Γ ⊢[PRAAx] ap3 parityOutput.observe s' N p ≐ fstT s' := by
    simpa [parityOutput,ap3] using toPR_eq (Γ := Γ) (fstT (var 0) : PTm 3) ![s',N,p]
  have e : Γ ⊢[PRAAx] ap4 parityOutput.related (ap3 parityOutput.observe s N p)
      (ap3 parityOutput.observe s' N p) N p ≐ eqb (ap3 parityOutput.observe s N p) (ap3 parityOutput.observe s' N p) := by
    simpa [parityOutput,ap4] using toPR_eq (Γ := Γ) (eqb (var 0) (var 1) : PTm 4)
      ![ap3 parityOutput.observe s N p,ap3 parityOutput.observe s' N p,N,p]
  exact e.eqTrans (eqb_of_eq (ol.eqTrans ((Prf.andE₁ h).eqTrans or.eqSymm)))

theorem parity_base (q p : PTm n) : Γ ⊢[PRAAx] invAt parityCode zero (ap2 parityCode.initial q p) q p := by
  rw [parity_inv_at]
  exact parity_state_congr (parity_initial_at q p).eqSymm
    (parity_pair_state zero zero zero p (zero_le _) (zero_le _))
theorem parity_slot_bound (i s q p : PTm n) (hI : Γ ⊢[PRAAx] invAt parityCode i s q p) : Γ ⊢[PRAAx]
    lt (selectedSlot parityCode i s q p) (ap3 parityCode.cap i q p) := by
  have h : Γ ⊢[PRAAx] parityState i s p := by simpa only [parity_inv_at] using hI
  exact lt_congr (parity_slot_at i s q p).eqSymm (parity_cap_at i q p).eqSymm
    ((succ_monus_succ _ _).eqTrans (Prf.andE₂ (Prf.andE₂ h)))
theorem parity_step (i s c q p : PTm n) (hI : Γ ⊢[PRAAx] invAt parityCode i s q p)
    (hc : Γ ⊢[PRAAx] valid parityInput c (queryAtState parityCode i s q p) p) :
    Γ ⊢[PRAAx] invAt parityCode (succ i) (localStep parityCode i s c q p) q p := by
  have h : Γ ⊢[PRAAx] parityState i s p := by simpa only [parity_inv_at] using hI
  have cBound := parity_certificate_bound c _ p hc
  have old := Prf.andE₁ (Prf.andE₂ h)
  have sumBound : Γ ⊢[PRAAx] le (fstT s+c) (succ i*p) := by
    have a := add_le_add_right c old
    have b := le_congr (add_comm c (i*p)) (add_comm p (i*p)) (add_le_add_right (i*p) cBound)
    have e : Γ ⊢[PRAAx] succ i*p ≐ i*p+p :=
      (mul_comm (succ i) p).eqTrans ((mul_succ p i).eqTrans (congrAdd (mul_comm p i) (.eqRefl _)))
    exact le_congr (.eqRefl _) e.eqSymm (le_trans a b)
  rw [parity_inv_at]
  exact parity_state_congr (parity_step_at i s c q p).eqSymm
    (parity_pair_state (succ i) (fstT s+c) (par c) p sumBound (parity_bit_bound c))
theorem parity_final (s N p : PTm n) (hI : Γ ⊢[PRAAx] invAt parityCode (ap2 parityCode.fuel N p) s N p) :
    Γ ⊢[PRAAx] valid parityOutput s N p := by
  have h : Γ ⊢[PRAAx] parityState (ap2 parityCode.fuel N p) s p := by simpa only [parity_inv_at] using hI
  exact parity_output_valid s N p (.andI (.andE₁ h) (.andI
    (le_congr (.eqRefl _) (congrMul (parity_fuel_at N p) (.eqRefl _)) (.andE₁ (.andE₂ h))) (.andE₂ (.andE₂ h))))
theorem parity_rel_base (q p : PTm n) : Γ ⊢[PRAAx]
    relAt parityCode zero (ap2 parityCode.initial q p) (ap2 parityCode.initial q p) q p := by
  rw [parity_rel_at]
  exact .andI (.eqRefl _) (.eqRefl _)
theorem parity_slot_equal (i s s' q p : PTm n) (hR : Γ ⊢[PRAAx] relAt parityCode i s s' q p) :
    Γ ⊢[PRAAx] selectedSlot parityCode i s q p ≐ selectedSlot parityCode i s' q p := by
  have r : Γ ⊢[PRAAx] parityRelation s s' := by simpa only [parity_rel_at] using hR
  exact (parity_slot_at i s q p).eqTrans ((Prf.andE₂ r).eqTrans (parity_slot_at i s' q p).eqSymm)
theorem parity_rel_step (i s s' c c' q p : PTm n) (hR : Γ ⊢[PRAAx] relAt parityCode i s s' q p)
    (hc : Γ ⊢[PRAAx] related parityInput c c' (queryAtState parityCode i s q p) p) :
    Γ ⊢[PRAAx] relAt parityCode (succ i) (localStep parityCode i s c q p) (localStep parityCode i s' c' q p) q p := by
  have e := parity_input_equal c c' _ p hc
  have r : Γ ⊢[PRAAx] parityRelation s s' := by simpa only [parity_rel_at] using hR
  rw [parity_rel_at]
  have leftF := (congrFst (parity_step_at (Γ := Γ) i s c q p)).eqTrans (fst_pair _ _)
  have rightF := (congrFst (parity_step_at (Γ := Γ) i s' c' q p)).eqTrans (fst_pair _ _)
  have leftS := (congrSnd (parity_step_at (Γ := Γ) i s c q p)).eqTrans (snd_pair _ _)
  have rightS := (congrSnd (parity_step_at (Γ := Γ) i s' c' q p)).eqTrans (snd_pair _ _)
  exact .andI (leftF.eqTrans ((congrAdd (.andE₁ r) e).eqTrans rightF.eqSymm))
    (leftS.eqTrans ((congrAp1 parF e).eqTrans rightS.eqSymm))

/-- Every local source contract of this adaptive example is discharged. -/
theorem parity_laws : Laws parityInput parityOutput parityCode where
  qf := ⟨trivial,⟨trivial,trivial⟩⟩
  relQf := ⟨trivial,trivial⟩
  base := fun q p _ _ => parity_base q p
  slot_bound := fun i s q p _ _ _ _ hI => parity_slot_bound i s q p hI
  step := fun i s c q p _ _ _ _ hI hc => parity_step i s c q p hI hc
  final := fun s q p _ _ hI => parity_final s q p hI
  relBase := fun q p _ _ => parity_rel_base q p
  slot_equal := fun i s s' q p _ _ _ _ _ _ hR => parity_slot_equal i s s' q p hR
  relStep := fun i s s' c c' q p _ _ _ _ _ _ hR _ _ hc => parity_rel_step i s s' c c' q p hR hc
  relFinal := fun s s' q p _ _ _ _ hR => parity_output_related s s' q p (by simpa only [parity_rel_at] using hR)

theorem parity_producers (N p : PTm n) : Γ ⊢[PRAAx] queryAt (allOf (residuals parityCode)) N p := by
  simpa [residuals,RealizerBlockLoop.residuals_eq,RealizerLoop.residuals,RealizerBlockLoop.loopCode,
    blockCode,parityCode,allOf,queryAt] using Prf.eqRefl (Ax := PRAAx) (Γ := Γ) (zero : PTm n)
theorem parity_accumulator (C N p : PTm n) (hC : Γ ⊢[PRAAx] masterValid parityInput (demands parityCode N p) C p) :
    Γ ⊢[PRAAx] valid parityOutput (ap3 (transformF parityCode) C N p) N p :=
  sound parity_laws C N p (.eqRefl _) (parity_producers N p) hC
theorem parity_accumulator_stable (C C' N p : PTm n)
    (hC : Γ ⊢[PRAAx] masterValid parityInput (demands parityCode N p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid parityInput (demands parityCode N p) C' p)
    (he : Γ ⊢[PRAAx] masterRelated parityInput (demands parityCode N p) C C' p) : Γ ⊢[PRAAx]
    related parityOutput (ap3 (transformF parityCode) C N p) (ap3 (transformF parityCode) C' N p) N p :=
  stable parity_laws C C' N p (.eqRefl _) (parity_producers N p) hC hC' he
theorem parity_actual_query (i C N p : PTm n) : Γ ⊢[PRAAx]
    queryAtState parityCode i (run parityCode i C N p) N p ≐ pairT i (sndT (run parityCode i C N p)) :=
  (parity_candidate_at i _ N p).eqTrans (pair_congr (.eqRefl _) (parity_slot_at i _ N p))
theorem parity_recurrence (i C N p : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    run parityCode (succ i) C N p ≐
      pairT (fstT (run parityCode i C N p)+selectedCertificate parityCode i C N p)
        (par (selectedCertificate parityCode i C N p)) :=
  (run_succ parityInput parityCode i C N p (lt_congr (.eqRefl _) (parity_fuel_at N p).eqSymm hi)).eqTrans
    (parity_step_at i _ _ N p)

theorem parity_output_state (s N p : PTm n) (h : Γ ⊢[PRAAx] valid parityOutput s N p) :
    Γ ⊢[PRAAx] parityState N s p := by
  have v : Γ ⊢[PRAAx] app (BoundedSyntax.bitF parityOutputFormula) ![s,N,p] ≐ one := by
    simpa only [parityOutput,ap3] using Prf.andE₂ h
  have e := BoundedSyntax.program_correct parityOutputFormula ![s,N,p] (Γ := Γ)
  have accepted := (BoundedSyntax.bounded_reflection parityOutputFormula ![s,N,p]).iffMp (e.eqSymm.eqTrans v)
  simpa [parityOutputFormula,BoundedSyntax.formula,BoundedSyntax.BFm.le,parityState,le] using accepted
theorem parity_accumulated_bound (C N p : PTm n)
    (hC : Γ ⊢[PRAAx] masterValid parityInput (demands parityCode N p) C p) : Γ ⊢[PRAAx]
    le (fstT (ap3 (transformF parityCode) C N p)) (N*p) :=
  .andE₁ (.andE₂ (parity_output_state _ _ _ (parity_accumulator C N p hC)))
theorem parity_zero_cap (C N : PTm n)
    (hC : Γ ⊢[PRAAx] masterValid parityInput (demands parityCode N zero) C zero) : Γ ⊢[PRAAx]
    fstT (ap3 (transformF parityCode) C N zero) ≐ zero :=
  le_antisymm (le_congr (.eqRefl _) (mul_zero N) (parity_accumulated_bound C N zero hC)) (zero_le _)
theorem parity_zero_fuel (C p : PTm n) : Γ ⊢[PRAAx]
    ap3 (transformF parityCode) C zero p ≐ pairT zero zero :=
  (RealizerBlockLoop.zero_fuel (blockCode parityCode) C zero p (parity_fuel_at zero p)).eqTrans (parity_initial_at zero p)

/-! ## Actual generated metadata and closed source endpoints -/

def boundF (X : Interface) (D : Code) : PR 2 := RealizerBlockLoop.boundF X (blockCode D)
def verifierF (X : Interface) (D : Code) : PR 3 := RealizerBlockLoop.verifierF X (blockCode D)
def observationF (Y : Interface) (D : Code) : PR 3 := RealizerBlockLoop.observationF Y (blockCode D)
def primitive {X Y : Interface} {D : Code} (h : Laws X Y D) : RealizerGraph.Primitive X Y :=
  RealizerBlockLoop.primitive (block_laws h)
def program {X Y : Interface} {D : Code} (h : Laws X Y D) : RealizerGraph.Program X Y :=
  .primitive (primitive h)
theorem program_code {X Y : Interface} {D : Code} (h : Laws X Y D) : (program h).code = code D := rfl
theorem verifier_sound {X Y : Interface} {D : Code} (h : Laws X Y D) (C q p : PTm n)
    (hc : Γ ⊢[PRAAx] ap3 (verifierF X D) C q p ≐ one) : Γ ⊢[PRAAx]
    masterValid X (demands D q p) C p := RealizerBlockLoop.verifier_sound (block_laws h) _ _ _ hc

theorem state_adaptive_table_closed (D : Code) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 (blocksF D) (var 0) (var 1) (var 2) ≐ candidateBlock D (var 0) (var 1) (var 2) ⋏
      length (candidateBlock D (var 0) (var 1) (var 2)) ≐ ap3 D.cap (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.andI (blocks_at D _ _ _) (candidate_length D _ _ _))
theorem state_adaptive_lookup_closed (D : Code) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 0) (ap2 D.fuel (var 2) (var 3)) ⟶ lt (var 1) (ap3 D.cap (var 0) (var 2) (var 3)) ⟶
      entry (demands D (var 2) (var 3)) (offset D (var 0) (var 2) (var 3)+var 1) ≐
        candidate D (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (flat_candidate D _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem state_adaptive_recurrence_closed (X : Interface) (D : Code) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run D zero (var 1) (var 2) (var 3) ≐ ap2 D.initial (var 2) (var 3) ⋏
      (lt (var 0) (ap2 D.fuel (var 2) (var 3)) ⟶
        run D (succ (var 0)) (var 1) (var 2) (var 3) ≐
          localStep D (var 0) (run D (var 0) (var 1) (var 2) (var 3))
            (selectedCertificate D (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3))) :=
  closeUniv 4 (.andI (run_zero D _ _ _) (.impI (run_succ X D _ _ _ _ Prf.hyp0)))
theorem state_adaptive_programs_closed {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap2 (demandF D) (var 1) (var 2) ≐ demands D (var 1) (var 2) ⋏
        (ap3 (transformF D) (var 0) (var 1) (var 2) ≐ run D (ap2 D.fuel (var 1) (var 2)) (var 0) (var 1) (var 2) ⋏
          (ap2 (boundF X D) (var 1) (var 2) ≐ masterBound X (ap2 (demandF D) (var 1) (var 2)) (var 2) ⋏
            (ap3 (verifierF X D) (var 0) (var 1) (var 2) ≐ masterBit X (ap2 (demandF D) (var 1) (var 2)) (var 0) (var 2) ⋏
              ap3 (observationF Y D) (var 0) (var 1) (var 2) ≐
                ap3 Y.observe (ap3 (transformF D) (var 0) (var 1) (var 2)) (var 1) (var 2))))) :=
  RealizerBlockLoop.block_fold_programs (block_laws h)
theorem state_adaptive_producers_closed (D : Code) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (queryAt (allOf (residuals D)) (var 1) (var 2) ⟶ lt (var 0) (ap2 D.fuel (var 1) (var 2)) ⟶
      queryAt (allOf D.residuals) (var 1) (var 2) ⋏ stageAt D (var 0) (var 1) (var 2)) :=
  RealizerBlockLoop.block_fold_producers (blockCode D)
theorem state_adaptive_soundness {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (soundFormula (realizer h)) := bounded_realizer_soundness (realizer h)
theorem state_adaptive_stability {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (stabilityFormula (realizer h)) := bounded_realizer_stability (realizer h)
theorem state_adaptive_sealed {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (sealedFormula (realizer h)) := bounded_realizer_sealed (realizer h)
theorem state_adaptive_verifier_closed {X Y : Interface} {D : Code} (h : Laws X Y D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap3 (verifierF X D) (var 0) (var 1) (var 2) ≐ one ⟶
        masterValid X (demands D (var 1) (var 2)) (var 0) (var 2)) :=
  closeUniv 3 (.impI (verifier_sound h _ _ _ Prf.hyp0))

theorem parity_adaptive_accumulator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (masterValid parityInput (demands parityCode (var 1) (var 2)) (var 0) (var 2) ⟶
      valid parityOutput (ap3 (transformF parityCode) (var 0) (var 1) (var 2)) (var 1) (var 2)) :=
  closeUniv 3 (.impI (parity_accumulator _ _ _ Prf.hyp0))
theorem parity_adaptive_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (masterValid parityInput (demands parityCode (var 1) (var 2)) (var 0) (var 2) ⟶
      le (fstT (ap3 (transformF parityCode) (var 0) (var 1) (var 2))) (var 1*var 2)) :=
  closeUniv 3 (.impI (parity_accumulated_bound _ _ _ Prf.hyp0))
theorem parity_adaptive_queries_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (queryAtState parityCode (var 0) (run parityCode (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3) ≐
      pairT (var 0) (sndT (run parityCode (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (parity_actual_query _ _ _ _)
theorem parity_adaptive_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 0) (var 2) ⟶ run parityCode (succ (var 0)) (var 1) (var 2) (var 3) ≐
      pairT (fstT (run parityCode (var 0) (var 1) (var 2) (var 3))+
          selectedCertificate parityCode (var 0) (var 1) (var 2) (var 3))
        (par (selectedCertificate parityCode (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (parity_recurrence _ _ _ _ Prf.hyp0))
theorem parity_adaptive_zero_fuel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap3 (transformF parityCode) (var 0) zero (var 1) ≐ pairT zero zero) := closeUniv 2 (parity_zero_fuel _ _)
theorem parity_adaptive_zero_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (masterValid parityInput (demands parityCode (var 1) zero) (var 0) zero ⟶
      fstT (ap3 (transformF parityCode) (var 0) (var 1) zero) ≐ zero) :=
  closeUniv 2 (.impI (parity_zero_cap _ _ Prf.hyp0))
theorem parity_adaptive_stability_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (masterValid parityInput (demands parityCode (var 2) (var 3)) (var 0) (var 3) ⟶
      masterValid parityInput (demands parityCode (var 2) (var 3)) (var 1) (var 3) ⟶
        masterRelated parityInput (demands parityCode (var 2) (var 3)) (var 0) (var 1) (var 3) ⟶
          related parityOutput (ap3 (transformF parityCode) (var 0) (var 2) (var 3))
            (ap3 (transformF parityCode) (var 1) (var 2) (var 3)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (parity_accumulator_stable _ _ _ _ (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))

theorem demand_length (D : Code) (q p : PTm n) : Γ ⊢[PRAAx]
    length (demands D q p) ≐ offset D (ap2 D.fuel q p) q p :=
  RealizerBlockLoop.demand_length (blockCode D) q p
theorem state_adaptive_length_closed (D : Code) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (demands D (var 0) (var 1)) ≐ offset D (ap2 D.fuel (var 0) (var 1)) (var 0) (var 1)) :=
  closeUniv 2 (demand_length D _ _)
theorem state_adaptive_zero_fuel_closed (D : Code) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 D.fuel (var 1) (var 2) ≐ zero ⟶
      ap3 (transformF D) (var 0) (var 1) (var 2) ≐ ap2 D.initial (var 1) (var 2)) :=
  closeUniv 3 (.impI (RealizerBlockLoop.zero_fuel (blockCode D) _ _ _ Prf.hyp0))
theorem parity_seal (N p : PTm n) (ht : Γ ⊢[PRAAx] inputTotal (realizer parity_laws) N p) :
    Γ ⊢[PRAAx] outputTotal parityOutput N p :=
  (realizer parity_laws).seal N p
    (RealizerBlockLoop.compiled_guard (blockCode parityCode) N p (.eqRefl _)) (parity_producers N p) ht
theorem parity_adaptive_sealed_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (inputTotal (realizer parity_laws) (var 0) (var 1) ⟶ outputTotal parityOutput (var 0) (var 1)) :=
  closeUniv 2 (.impI (parity_seal _ _ Prf.hyp0))

end LeanProofs.IPRA.Foundations.RealizerStateAdaptive
