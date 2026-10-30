import DiophantineConsistency.PRAFormulaSetUHistoryBound
import DiophantineConsistency.PRABVGraphHistoryBound
/-! Exact positive formula-set graph with both recursively defined syntax histories explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAFormulaSetTwoHistoriesBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem inline_bv_bound (p w : V) (h : (bnd (bvGraph L).val).Evalb ![0,p,w]) :
    (bnd (PRASemiFormulaSigmaBound.bvInside (L := L))).Evalb ![0,0,p,w] := by
  let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#2]
  have hn := PRABndRewriting.natural (bvGraph L).val ω ![0,0,p] w
  have hv : (fun j => (ω #j).val ![0,0,p] Empty.elim) = ![0,p] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs : Fin.snoc ![0,0,p] w = ![0,0,p,w] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs' : Fin.snoc ![0,p] w = ![0,p,w] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hv,hs,hs'] at hn
  have heq : PRASemiFormulaSigmaBound.bvInside (L := L) = ω ▹ (bvGraph L).val := by
    simp [PRASemiFormulaSigmaBound.bvInside, ω]
  rw [heq]
  exact hn.mpr h

theorem formulaSet_bound_of_two_histories (s w : V)
    (hw : 0 < w) (hneg : PRANegBitFullWitnessBound.negBitMajorant s ≤ w)
    (hU : ∀ p, p < s → (isSemiformula L).sigma.val.Evalb ![0,p] →
      ∃ t, t < w ∧ PRABitFullWitnessBound.bitMajorant t ≤ w ∧ bitDef.val.Evalb ![p,t] ∧
        (bnd (PRAFixBitUFormulaBound.limInsideBody (L := L))).Evalb ![t,p,w])
    (hBV : ∀ p, p < s → (isSemiformula L).sigma.val.Evalb ![0,p] →
      ∃ pr v t, pr < w ∧ pr+1 ≤ w ∧ pair₃Def.val.Evalb ![pr,0,p,0] ∧ v < w ∧ t < w ∧
        PRABitFullWitnessBound.bitMajorant v ≤ w ∧ bitDef.val.Evalb ![pr,v] ∧
        (bnd (PRABVFixpointBound.limInsideBody (L := L))).Evalb ![v,t,pr,w]) :
    (isFormulaSet L).sigma.val.Evalb ![s] → (bnd (isFormulaSet L).sigma.val).Evalb ![s,w] := by
  apply PRAFormulaSetUHistoryBound.formulaSet_bound_of_histories s w hw hneg hU
  intro p hp hsemi
  obtain ⟨pr,v,t,hpr,hpairsize,hpair,hv,ht,hsize,hbit,hlim⟩ := hBV p hp hsemi
  apply inline_bv_bound
  exact PRABVGraphHistoryBound.bvGraph_zero_bound_of_history p pr v t w hpr hpairsize hpair hv ht hsize hbit hlim
noncomputable def semiSigma0 : ArithmeticSemisentence 1 := PRAFormulaSetSyntaxBound.semiSigma0 (L := L)
noncomputable def boundedULim : ArithmeticSemisentence 3 := PRAFixBitUFormulaBound.boundedLim (L := L)
noncomputable def boundedBVLim : ArithmeticSemisentence 4 := PRABVFixpointBound.boundedLim (L := L)
noncomputable def formulaSet : ArithmeticSemisentence 1 := (isFormulaSet L).sigma.val
noncomputable def boundedFormulaSet : ArithmeticSemisentence 2 := bnd (formulaSet (L := L))
noncomputable def formulaSetTwoHistoriesBody : ArithmeticSemisentence 2 :=
  “s w. 0 < w ∧ (((2*s+1)+(2*s²+1))+s+1) ≤ w ∧
    (∀ p < s, !((semiSigma0 (L := L))) p → ∃ t < w,
      (((t⁴+1)+(t²+1)+(2*t²+1)+(t⁴+t⁴+2*t+1))+t+1) ≤ w ∧ !bitDef p t ∧ !((boundedULim (L := L))) t p w) ∧
    (∀ p < s, !((semiSigma0 (L := L))) p → ∃ pr, ∃ v, ∃ t,
      pr < w ∧ pr+1 ≤ w ∧ !pair₃Def pr 0 p 0 ∧ v < w ∧ t < w ∧
      (((v⁴+1)+(v²+1)+(2*v²+1)+(v⁴+v⁴+2*v+1))+v+1) ≤ w ∧ !bitDef pr v ∧ !((boundedBVLim (L := L))) v t pr w) ∧
    !((formulaSet (L := L))) s → !((boundedFormulaSet (L := L))) s w”
theorem formulaSetTwoHistoriesBody_model (e : Fin 2 → V) : (formulaSetTwoHistoriesBody (L := L)).Eval e Empty.elim := by
  simp [formulaSetTwoHistoriesBody,boundedULim,PRAFixBitUFormulaBound.boundedLim,
    boundedBVLim,PRABVFixpointBound.boundedLim,boundedFormulaSet,semiSigma0,
    PRAFormulaSetSyntaxBound.semiSigma0,PRAFormulaSetWitnessBound.semiformulaSigma0,Semiformula.eval_substs]
  intro hw hn hu hbv hf
  have hb : ∀ p, p < e 0 → (isSemiformula L).sigma.val.Evalb ![0,p] →
      ∃ pr v t, pr < e 1 ∧ pr+1 ≤ e 1 ∧ pair₃Def.val.Evalb ![pr,0,p,0] ∧ v < e 1 ∧ t < e 1 ∧
        PRABitFullWitnessBound.bitMajorant v ≤ e 1 ∧ bitDef.val.Evalb ![pr,v] ∧
        (bnd (PRABVFixpointBound.limInsideBody (L := L))).Evalb ![v,t,pr,e 1] := by
    intro p hp hsemi
    obtain ⟨hpr,hps,v,hv,t,ht,hsize,hbit,hlim⟩ := hbv p hp hsemi
    refine ⟨⟪0,⟪p,0⟫⟫,v,t,hpr,hps,?_,hv,ht,hsize,hbit,hlim⟩
    simp
  exact formulaSet_bound_of_two_histories (e 0) (e 1) hw hn hu hb hf
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def formulaSetTwoHistoriesSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (formulaSetTwoHistoriesBody (L := L))
theorem candidate_proves_formulaSet_two_histories_bound : PRA ⊢ formulaSetTwoHistoriesSentence (L := L) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, formulaSetTwoHistoriesSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact formulaSetTwoHistoriesBody_model e
end DiophantineConsistency.PRAFormulaSetTwoHistoriesBound
