import PA194PAeqOpeningTerm
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.OpeningQVec
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def openingFormula (s k p : M) : M :=
  subst language (znth s k) (shift language p)

theorem opening_bindTermVec (limit s k ar v : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit)
    (hv : IsSemitermVec language ar k v) :
    termSubstVec language ar (znth s k) (termShiftVec language ar (bindTermVec k ar v)) = v := by
  have hvb := bindTermVec_uterm (k := k) hv.isUTerm
  apply nth_ext' ar (by simp [hvb]) hv.lh
  intro i hi
  rw [nth_termSubstVec hvb.termShiftVec hi,nth_termShiftVec hvb hi,bindTermVec_nth hv.isUTerm hi]
  exact opening_bindTerm limit s h hl (hv.nth hi).isUTerm k hk (hv.nth hi)

theorem opening_bind_positiveAtom (limit s k ar r v : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit) (hr : language.IsRel ar r)
    (hv : IsSemitermVec language ar k v) :
    openingFormula s k (bindFormula k (^rel ar r v)) = ^rel ar r v := by
  have hvb := bindTermVec_uterm (k := k) hv.isUTerm
  rw [bindFormula_rel hr hv.isUTerm]
  unfold openingFormula
  rw [shift_rel hr hvb,substs_rel hr hvb.termShiftVec,opening_bindTermVec limit s k ar v h hl hk hv]

theorem opening_bind_negativeAtom (limit s k ar r v : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit) (hr : language.IsRel ar r)
    (hv : IsSemitermVec language ar k v) :
    openingFormula s k (bindFormula k (^nrel ar r v)) = ^nrel ar r v := by
  have hvb := bindTermVec_uterm (k := k) hv.isUTerm
  rw [bindFormula_nrel hr hv.isUTerm]
  unfold openingFormula
  rw [shift_nrel hr hvb,substs_nrel hr hvb.termShiftVec,opening_bindTermVec limit s k ar v h hl hk hv]

theorem openingFormula_and (s k a b : M) (ha : IsUFormula language a) (hb : IsUFormula language b) :
    openingFormula s k (a ^⋏ b) = openingFormula s k a ^⋏ openingFormula s k b := by
  simp only [openingFormula,shift_and ha hb,substs_and ha.shift hb.shift]
theorem openingFormula_or (s k a b : M) (ha : IsUFormula language a) (hb : IsUFormula language b) :
    openingFormula s k (a ^⋎ b) = openingFormula s k a ^⋎ openingFormula s k b := by
  simp only [openingFormula,shift_or ha hb,substs_or ha.shift hb.shift]
theorem openingFormula_all (limit s k a : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k < limit) (ha : IsUFormula language a) :
    openingFormula s k (^∀ a) = ^∀ (openingFormula s (k+1) a) := by
  rw [openingFormula,shift_all ha,substs_all ha.shift,← sourceQVec_trace_step _ limit s k h hl hk]
  rfl
theorem openingFormula_ex (limit s k a : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k < limit) (ha : IsUFormula language a) :
    openingFormula s k (^∃ a) = ^∃ (openingFormula s (k+1) a) := by
  rw [openingFormula,shift_exs ha,substs_ex ha.shift,← sourceQVec_trace_step _ limit s k h hl hk]
  rfl
#print axioms opening_bindTermVec
#print axioms opening_bind_positiveAtom
#print axioms opening_bind_negativeAtom
end PA194PAeq.OpeningQVec
