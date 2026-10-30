import DiophantineConsistency.PRAFormulaSetExplicitPairBound
import DiophantineConsistency.PRABVPairFamilyBound
/-! A single explicit BV pair-code bound for all relevant formula indices. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAFormulaSetCommonPairBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem formulaSet_bound_of_common_pair (s w : V)
    (hw : 0 < w) (hneg : PRANegBitFullWitnessBound.negBitMajorant s ≤ w)
    (hpair : (s*s+s)^2+1 ≤ w)
    (hU : ∀ p, p < s → (isSemiformula L).sigma.val.Evalb ![0,p] →
      ∃ t, t < w ∧ PRABitFullWitnessBound.bitMajorant t ≤ w ∧ bitDef.val.Evalb ![p,t] ∧
        (bnd (PRAFixBitUFormulaBound.limInsideBody (L := L))).Evalb ![t,p,w])
    (hBV : ∀ p, p < s → (isSemiformula L).sigma.val.Evalb ![0,p] →
      ∃ v t, v < w ∧ t < w ∧ PRABitFullWitnessBound.bitMajorant v ≤ w ∧
        bitDef.val.Evalb ![(p*p+p)^2,v] ∧
        (bnd (PRABVFixpointBound.limInsideBody (L := L))).Evalb ![v,t,(p*p+p)^2,w]) :
    (isFormulaSet L).sigma.val.Evalb ![s] → (bnd (isFormulaSet L).sigma.val).Evalb ![s,w] := by
  apply PRAFormulaSetExplicitPairBound.formulaSet_bound_of_explicit_pair_histories s w hw hneg hU
  intro p hp hsemi
  obtain ⟨v,t,hv,ht,hsize,hbit,hlim⟩ := hBV p hp hsemi
  have hmono := PRABVPairFamilyBound.bvPair_poly_mono p s (le_of_lt hp)
  have hm : (p*p+p)^2+1 ≤ (s*s+s)^2+1 := by simpa [add_comm] using add_le_add_right hmono 1
  have hbound : (p*p+p)^2+1 ≤ w := le_trans hm hpair
  exact ⟨v,t,hbound,hv,ht,hsize,hbit,hlim⟩
noncomputable def semiSigma0 : ArithmeticSemisentence 1 := PRAFormulaSetSyntaxBound.semiSigma0 (L := L)
noncomputable def boundedULim : ArithmeticSemisentence 3 := PRAFixBitUFormulaBound.boundedLim (L := L)
noncomputable def boundedBVLim : ArithmeticSemisentence 4 := PRABVFixpointBound.boundedLim (L := L)
noncomputable def formulaSet : ArithmeticSemisentence 1 := (isFormulaSet L).sigma.val
noncomputable def boundedFormulaSet : ArithmeticSemisentence 2 := bnd (formulaSet (L := L))
noncomputable def formulaSetCommonPairBody : ArithmeticSemisentence 2 :=
  “s w. 0 < w ∧ (((2*s+1)+(2*s²+1))+s+1) ≤ w ∧ ((s*s+s)²)+1 ≤ w ∧
    (∀ p < s, !((semiSigma0 (L := L))) p → ∃ t < w,
      (((t⁴+1)+(t²+1)+(2*t²+1)+(t⁴+t⁴+2*t+1))+t+1) ≤ w ∧ !bitDef p t ∧ !((boundedULim (L := L))) t p w) ∧
    (∀ p < s, !((semiSigma0 (L := L))) p → ∃ v, ∃ t,
      v < w ∧ t < w ∧
      (((v⁴+1)+(v²+1)+(2*v²+1)+(v⁴+v⁴+2*v+1))+v+1) ≤ w ∧ !bitDef ((p*p+p)²) v ∧ !((boundedBVLim (L := L))) v t ((p*p+p)²) w) ∧
    !((formulaSet (L := L))) s → !((boundedFormulaSet (L := L))) s w”
theorem formulaSetCommonPairBody_model (e : Fin 2 → V) : (formulaSetCommonPairBody (L := L)).Eval e Empty.elim := by
  simp [formulaSetCommonPairBody,boundedULim,PRAFixBitUFormulaBound.boundedLim,
    boundedBVLim,PRABVFixpointBound.boundedLim,boundedFormulaSet,semiSigma0,
    PRAFormulaSetSyntaxBound.semiSigma0,PRAFormulaSetWitnessBound.semiformulaSigma0,Semiformula.eval_substs]
  intro hw hn hpair hu hbv hf
  have hb : ∀ p, p < e 0 → (isSemiformula L).sigma.val.Evalb ![0,p] →
      ∃ v t, v < e 1 ∧ t < e 1 ∧ PRABitFullWitnessBound.bitMajorant v ≤ e 1 ∧
        bitDef.val.Evalb ![(p*p+p)^2,v] ∧
        (bnd (PRABVFixpointBound.limInsideBody (L := L))).Evalb ![v,t,(p*p+p)^2,e 1] := by
    intro p hp hs
    obtain ⟨v,hv,t,ht,hsize,hbit,hlim⟩ := hbv p hp hs
    exact ⟨v,t,hv,ht,hsize,hbit,hlim⟩
  exact formulaSet_bound_of_common_pair (L := L) (e 0) (e 1) hw hn hpair hu hb hf
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def formulaSetCommonPairSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (formulaSetCommonPairBody (L := L))
theorem candidate_proves_formulaSet_common_pair_bound : PRA ⊢ formulaSetCommonPairSentence (L := L) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, formulaSetCommonPairSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact formulaSetCommonPairBody_model e
end DiophantineConsistency.PRAFormulaSetCommonPairBound
