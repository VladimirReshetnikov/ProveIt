import PA194TermDispatcher
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TermDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194PAeqTermFormulaTree
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def ref (param p : V) : V := (termConstruction (V := V)).result SourceL param p

theorem sourceRel : SourceL.IsRel (2 : V) (0 : V) := by
  change (“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : V), 0]
  simp

theorem ref_all (param p : V) (hp : IsUFormula SourceL p) :
    ref param (^∀ p) = ref (childParameters param) p := by
  simpa [ref,termConstruction] using (termConstruction (V := V)).result_all (param := param) hp

theorem ref_exs (param p : V) (hp : IsUFormula SourceL p) :
    ref param (^∃ p) = ref (shiftParameters param 1) p := by
  simpa [ref,termConstruction] using (termConstruction (V := V)).result_exs (param := param) hp

theorem ref_verum (param : V) : ref param ^⊤ = zeroValue (nth param 2) := by
  simpa [ref,termConstruction,verumValue] using (termConstruction (V := V)).result_verum (param := param) (L := SourceL)

theorem ref_and (param p q : V) (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q) :
    ref param (p ^⋏ q) = andValue param p (ref param p) (ref param q) := by
  simpa [ref,termConstruction] using (termConstruction (V := V)).result_and (param := param) hp hq

theorem ref_or (param p q : V) (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q) :
    ref param (p ^⋎ q) = orValue param (ref param p) (ref param q) := by
  simpa [ref,termConstruction] using (termConstruction (V := V)).result_or (param := param) hp hq

theorem translate_bound (param i : V) :
    translate param (^#i) = variableValue (nth param 2) (nth (nth param 0) i) := by
  rw [translate,termTree_bvar]
  have hv : IsUTermVec SourceL (2 : V) (?[ ^#i, ^#i] : V) := by simp
  rw [show boundLeaf i = ^rel (2 : V) 0 (?[ ^#i, ^#i] : V) by rfl,
    (termConstruction (V := V)).result_rel sourceRel hv]
  simp [termConstruction,atomValue,qqBvar]

theorem translate_free (param i : V) :
    translate param (^&i) = variableValue (nth param 2) (nth (nth param 1) i) := by
  rw [translate,termTree_fvar]
  have hv : IsUTermVec SourceL (2 : V) (?[ ^&i, ^&i] : V) := by simp
  rw [show freeLeaf i = ^nrel (2 : V) 0 (?[ ^&i, ^&i] : V) by rfl,
    (termConstruction (V := V)).result_nrel sourceRel hv]
  simp [termConstruction,atomValue,qqFvar]
theorem translate_zero (param : V) :
    translate param (^func (0 : V) 0 0) = zeroValue (nth param 2) := by
  have hf : PA194PAeq.language.IsFunc (0 : V) 0 := by simp
  have hv : IsUTermVec PA194PAeq.language (0 : V) 0 := by simp
  rw [translate,termTree_func hf hv]
  simpa [functionNode,ref,termConstruction,verumValue] using (ref_verum param)

theorem translate_succ (param t : V) (ht : IsUTerm PA194PAeq.language t) :
    translate param (^func (1 : V) 1 (?[t] : V)) =
      successorValue (nth param 2) (translate (childParameters param) t) := by
  have hf : PA194PAeq.language.IsFunc (1 : V) 1 := by simp
  have hv : IsUTermVec PA194PAeq.language (1 : V) (?[t] : V) := by simp [ht]
  have ht0 : nth (termTreeVec 1 (?[t] : V)) 0 = termTree t := by
    rw [termTreeVec_nth hv (by simp)]
    simp
  have htree := termTree_valid t ht
  rw [translate,termTree_func hf hv]
  simp only [functionNode,Arithmetic.one_ne_zero,if_false,if_true,ht0]
  change ref param (^⊤ ^⋏ (^∀ (termTree t))) = _
  rw [ref_and param _ _ (by simp [IsUFormula.verum]) (by simpa [IsUFormula.all] using htree)]
  rw [ref_all param _ htree]
  simp [andValue,translate,ref]

theorem leftMarker_ne_verum (p : V) : leftMarker p ≠ (^⊤ : V) := by
  simp [leftMarker,qqAll,qqVerum]

theorem ref_leftMarker (param p : V) (hp : IsUFormula SourceL p) :
    ref param (leftMarker p) = ref (binaryParameters param 1) p := by
  have he : IsUFormula SourceL (^∃ p) := by simpa [IsUFormula.ex] using hp
  rw [leftMarker,ref_all param _ he,ref_exs _ _ hp,shiftParameters_child]

theorem ref_rightMarker (param p : V) (hp : IsUFormula SourceL p) :
    ref param (rightMarker p) = ref (binaryParameters param 0) p := by
  have ha : IsUFormula SourceL (^∀ p) := by simpa [IsUFormula.all] using hp
  rw [rightMarker,ref_all param _ ha,ref_all _ _ hp,← shiftParameters_zero,shiftParameters_child]

theorem translate_add (param s t : V) (hs : IsUTerm PA194PAeq.language s)
    (ht : IsUTerm PA194PAeq.language t) :
    translate param (^func (2 : V) 2 (?[s,t] : V)) =
      binaryValue additionTemplate (nth param 2)
        (translate (binaryParameters param 1) s) (translate (binaryParameters param 0) t) := by
  have hf : PA194PAeq.language.IsFunc (2 : V) 2 := by simp
  have hv : IsUTermVec PA194PAeq.language (2 : V) (?[s,t] : V) := by simp [hs,ht]
  have h0 : nth (termTreeVec 2 (?[s,t] : V)) 0 = termTree s := by
    rw [termTreeVec_nth hv (by simp)]; simp
  have h1 : nth (termTreeVec 2 (?[s,t] : V)) 1 = termTree t := by
    rw [termTreeVec_nth hv (by simp)]; simp
  have hts := termTree_valid s hs
  have htt := termTree_valid t ht
  have hl : IsUFormula SourceL (leftMarker (termTree s)) := by
    simpa [leftMarker,IsUFormula.all,IsUFormula.ex] using hts
  have hr : IsUFormula SourceL (rightMarker (termTree t)) := by
    simpa [rightMarker,IsUFormula.all] using htt
  rw [translate,termTree_func hf hv]
  simp only [functionNode,show (2 : V) ≠ 0 by simp,show (2 : V) ≠ 1 by simp,if_false,if_true,h0,h1]
  change ref param (leftMarker (termTree s) ^⋏ rightMarker (termTree t)) = _
  rw [ref_and param _ _ hl hr,ref_leftMarker param _ hts,ref_rightMarker param _ htt]
  simp [andValue,leftMarker_ne_verum,translate,ref]

theorem translate_mul (param s t : V) (hs : IsUTerm PA194PAeq.language s)
    (ht : IsUTerm PA194PAeq.language t) :
    translate param (^func (2 : V) 3 (?[s,t] : V)) =
      binaryValue multiplicationTemplate (nth param 2)
        (translate (binaryParameters param 1) s) (translate (binaryParameters param 0) t) := by
  have hf : PA194PAeq.language.IsFunc (2 : V) 3 := by simp
  have hv : IsUTermVec PA194PAeq.language (2 : V) (?[s,t] : V) := by simp [hs,ht]
  have h0 : nth (termTreeVec 2 (?[s,t] : V)) 0 = termTree s := by
    rw [termTreeVec_nth hv (by simp)]; simp
  have h1 : nth (termTreeVec 2 (?[s,t] : V)) 1 = termTree t := by
    rw [termTreeVec_nth hv (by simp)]; simp
  have hts := termTree_valid s hs
  have htt := termTree_valid t ht
  have hl : IsUFormula SourceL (leftMarker (termTree s)) := by
    simpa [leftMarker,IsUFormula.all,IsUFormula.ex] using hts
  have hr : IsUFormula SourceL (rightMarker (termTree t)) := by
    simpa [rightMarker,IsUFormula.all] using htt
  rw [translate,termTree_func hf hv]
  simp only [functionNode,show (2 : V) ≠ 0 by simp,show (2 : V) ≠ 1 by simp,
    show (3 : V) ≠ 2 by simp,if_false,h0,h1]
  change ref param (leftMarker (termTree s) ^⋎ rightMarker (termTree t)) = _
  rw [ref_or param _ _ hl hr,ref_leftMarker param _ hts,ref_rightMarker param _ htt]
  rfl
#print axioms translate_add
#print axioms translate_mul
#print axioms leftMarker_ne_verum
#print axioms ref_leftMarker
#print axioms ref_rightMarker
#print axioms translate_zero
#print axioms translate_succ
#print axioms translate_bound
#print axioms translate_free
#print axioms ref_all
#print axioms ref_exs
end generic
end PA194TermDispatcher
