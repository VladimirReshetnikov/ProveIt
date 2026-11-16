import PA194PAeqBindQVec
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termVecBindSubst {ar n k ts v w : V}
    (ht : IsSemitermVec PA194PAeq.language ar n ts)
    (hv : IsSemitermVec PA194PAeq.language n k v)
    (hw : ∀ i < n, bindTerm k v.[i] = w.[i])
    (hz : atomFreeBound ar ts = 0) :
    bindTermVec k ar (termSubstVec PA194PAeq.language ar v ts) =
      termSubstVec PA194PAeq.language ar w ts := by
  have hts := (hv.termSubstVec ht).isUTerm
  apply nth_ext' ar (by simpa [bindTermVec] using (termConstruction.resultVec_lh PA194PAeq.language ![k] hts)) (by simp [ht.isUTerm])
  intro i hi
  rw [bindTermVec_nth hts hi,nth_termSubstVec ht.isUTerm hi,nth_termSubstVec ht.isUTerm hi]
  apply termBindSubst (ht.nth hi).isUTerm n k v w (ht.nth hi) hv hw
  apply le_antisymm _ zero_le
  have hle : (termFreeBoundVec ar ts).[i] ≤ listMax (termFreeBoundVec ar ts) :=
    nth_le_listMax (by simpa [termFreeBoundVec_len ht.isUTerm] using hi)
  have hz' : listMax (termFreeBoundVec ar ts) = 0 := by simpa [atomFreeBound] using hz
  simpa [termFreeBoundVec_nth ht.isUTerm hi,hz'] using hle

def FormulaBindSubst (p : V) : Prop := ∀ n k v w : V,
  IsSemiformula PA194PAeq.language n p →
  IsSemitermVec PA194PAeq.language n k v →
  IsSemitermVec PA194PAeq.language n (k+1) w →
  (∀ i < n, bindTerm k v.[i] = w.[i]) → formulaFreeBound p = 0 →
  bindFormula k (subst PA194PAeq.language v p) = subst PA194PAeq.language w p

theorem formulaBindSubst_definable : 𝚷₁-Predicate (FormulaBindSubst : V → Prop) := by
  haveI : 𝚺₁-Function₁ (formulaFreeBound : V → V) := formulaFreeBound_defined.to_definable
  haveI : 𝚺₁-Function₂ (bindTerm : V → V → V) := bindTerm_defined.to_definable
  haveI : 𝚺₁-Function₂ (bindFormula : V → V → V) := bindFormula_defined.to_definable
  unfold FormulaBindSubst
  definability

theorem formulaBindSubst {p : V} (hp : IsUFormula PA194PAeq.language p) : FormulaBindSubst p := by
  apply IsUFormula.ISigma1.pi1_succ_induction formulaBindSubst_definable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro ar r ts hr ht n k v w hs hv hw h hz
    have ht' := (IsSemiformula.rel.mp hs).2
    have hsvec := (hv.termSubstVec ht').isUTerm
    have hz' : atomFreeBound ar ts = 0 := by simpa [formulaFreeBound_rel hr ht] using hz
    rw [substs_rel hr ht,bindFormula_rel hr hsvec,substs_rel hr ht,termVecBindSubst ht' hv h hz']
  · intro ar r ts hr ht n k v w hs hv hw h hz
    have ht' := (IsSemiformula.nrel.mp hs).2
    have hsvec := (hv.termSubstVec ht').isUTerm
    have hz' : atomFreeBound ar ts = 0 := by simpa [formulaFreeBound_nrel hr ht] using hz
    rw [substs_nrel hr ht,bindFormula_nrel hr hsvec,substs_nrel hr ht,termVecBindSubst ht' hv h hz']
  · intro n k v w hs hv hw h hz; simp
  · intro n k v w hs hv hw h hz; simp
  · intro a b ha hb iha ihb n k v w hs hv hw h hz
    have hab := (IsSemiformula.and.mp hs)
    have hmax : max (formulaFreeBound a) (formulaFreeBound b) = 0 := by simpa [formulaFreeBound_and ha hb] using hz
    have hza : formulaFreeBound a = 0 := le_antisymm (by simpa [hmax] using le_max_left (formulaFreeBound a) (formulaFreeBound b)) zero_le
    have hzb : formulaFreeBound b = 0 := le_antisymm (by simpa [hmax] using le_max_right (formulaFreeBound a) (formulaFreeBound b)) zero_le
    rw [substs_and ha hb, bindFormula_and (hab.1.subst hv).isUFormula (hab.2.subst hv).isUFormula,
      substs_and ha hb,iha n k v w hab.1 hv hw h hza,ihb n k v w hab.2 hv hw h hzb]
  · intro a b ha hb iha ihb n k v w hs hv hw h hz
    have hab := (IsSemiformula.or.mp hs)
    have hmax : max (formulaFreeBound a) (formulaFreeBound b) = 0 := by simpa [formulaFreeBound_or ha hb] using hz
    have hza : formulaFreeBound a = 0 := le_antisymm (by simpa [hmax] using le_max_left (formulaFreeBound a) (formulaFreeBound b)) zero_le
    have hzb : formulaFreeBound b = 0 := le_antisymm (by simpa [hmax] using le_max_right (formulaFreeBound a) (formulaFreeBound b)) zero_le
    rw [substs_or ha hb, bindFormula_or (hab.1.subst hv).isUFormula (hab.2.subst hv).isUFormula,
      substs_or ha hb,iha n k v w hab.1 hv hw h hza,ihb n k v w hab.2 hv hw h hzb]
  · intro a ha ih n k v w hs hv hw h hz
    have ha' := IsSemiformula.all.mp hs
    have hz' : formulaFreeBound a = 0 := by simpa [formulaFreeBound_all ha] using hz
    rw [substs_all ha, bindFormula_all (ha'.subst hv.qVec).isUFormula,substs_all ha]
    congr 1
    exact ih (n+1) (k+1) _ _ ha' hv.qVec (by simpa [add_assoc] using hw.qVec) (bindQVec hv hw h) hz'
  · intro a ha ih n k v w hs hv hw h hz
    have ha' := IsSemiformula.exs.mp hs
    have hz' : formulaFreeBound a = 0 := by simpa [formulaFreeBound_exs ha] using hz
    rw [substs_ex ha, bindFormula_exs (ha'.subst hv.qVec).isUFormula,substs_ex ha]
    congr 1
    exact ih (n+1) (k+1) _ _ ha' hv.qVec (by simpa [add_assoc] using hw.qVec) (bindQVec hv hw h) hz'
#print axioms termVecBindSubst
#print axioms formulaBindSubst
end PA194PAeqBind
