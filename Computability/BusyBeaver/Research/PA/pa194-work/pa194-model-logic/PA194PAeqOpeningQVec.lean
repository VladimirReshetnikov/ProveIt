import PA194PAeqReopenConditional
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.OpeningQVec
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Iteration of the actual relational-source qVec over model-internal depths. -/
def sourceQVecZeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out seed. out = seed”
noncomputable def sourceQVecSuccDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index seed. !(qVecGraph PA194PAeq.language) out previous”
noncomputable def sourceQVecBlueprint : PR.Blueprint 1 where
  zero := sourceQVecZeroDef
  succ := sourceQVecSuccDef
noncomputable def sourceQVecConstruction : PR.Construction M sourceQVecBlueprint where
  zero p := p 0
  succ _ _ previous := qVec PA194PAeq.language previous
  zero_defined := .mk fun e => by simp [sourceQVecBlueprint,sourceQVecZeroDef]
  succ_defined := .mk fun e => by simp [sourceQVecBlueprint,sourceQVecSuccDef]

theorem sourceQVec_exists_trace (seed limit : M) :
    ∃ s : M, (sourceQVecConstruction (M := M)).CSeq ![seed] s ∧ limit + 1 = lh s :=
  PR.Construction.CSeq.exists _ _ _

theorem sourceQVec_trace_start (seed s : M) (h : (sourceQVecConstruction (M := M)).CSeq ![seed] s) :
    znth s 0 = seed := by
  have hm := h.zero
  have hm' : ⟪(0 : M), seed⟫ ∈ s := by simpa [sourceQVecConstruction] using hm
  exact h.seq.znth_eq_of_mem hm'

theorem sourceQVec_trace_step (seed limit s i : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![seed] s)
    (hl : limit + 1 = lh s) (hi : i < limit) :
    znth s (i + 1) = qVec PA194PAeq.language (znth s i) := by
  have hlt : i < lh s := by rw [← hl]; exact lt_trans hi (by simp)
  have hm := h.succ i (by simp [← hl, hi]) (znth s i) (h.seq.znth hlt)
  have hm' : ⟪i + 1, qVec PA194PAeq.language (znth s i)⟫ ∈ s := by simpa [sourceQVecConstruction] using hm
  exact h.seq.znth_eq_of_mem hm'


/-- Every lifted singleton substitution has one slot per crossed binder plus its free slot. -/
theorem sourceQVec_trace_typed (limit s : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) :
    ∀ i ≤ limit, IsSemitermVec PA194PAeq.language (i+1) i (znth s i) := by
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero =>
    intro hi
    rw [sourceQVec_trace_start _ s h]
    simp
  | succ i ih =>
    intro hi
    have hlt : i < limit := lt_iff_succ_le.mpr hi
    have hi' : i ≤ limit := le_trans le_self_add hi
    rw [sourceQVec_trace_step _ limit s i h hl hlt]
    simpa only [add_assoc] using (ih hi').qVec

/-- The lifted substitution fixes all inner bound variables and frees the original one. -/
theorem sourceQVec_trace_entries (limit s : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) :
    ∀ i ≤ limit, (∀ j < i, (znth s i).[j] = ^#j) ∧ (znth s i).[i] = ^&(0 : M) := by
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    rw [sourceQVec_trace_start _ s h]
    simp
  | succ i ih =>
    intro hi
    have hlt : i < limit := lt_iff_succ_le.mpr hi
    have hi' : i ≤ limit := le_trans le_self_add hi
    have hp := ih hi'
    have hty := sourceQVec_trace_typed limit s h hl i hi'
    rw [sourceQVec_trace_step _ limit s i h hl hlt]
    constructor
    · intro j hj
      rcases zero_or_succ j with (rfl | ⟨j,rfl⟩)
      · simp [qVec]
      · have hj' : j < i := by simpa using hj
        have hj'' : j < i+1 := lt_trans hj' (lt_add_one i)
        simp [qVec, hty.lh, nth_termBShiftVec hty.isUTerm hj'', hp.1 j hj']
    · have hj : i < i+1 := lt_add_one i
      simp [qVec, hty.lh, nth_termBShiftVec hty.isUTerm hj, hp.2]


#print axioms sourceQVec_trace_entries
end PA194PAeq.OpeningQVec
