import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAFormulaSetTwoHistoriesBound
import DiophantineConsistency.PRABVPairPolynomial
/-! Formula-set bound with an explicit BV pair polynomial and both history premises. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAFormulaSetExplicitPairBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem formulaSet_bound_of_explicit_pair_histories (s w : V)
    (hw : 0 < w) (hneg : PRANegBitFullWitnessBound.negBitMajorant s ≤ w)
    (hU : ∀ p, p < s → (isSemiformula L).sigma.val.Evalb ![0,p] →
      ∃ t, t < w ∧ PRABitFullWitnessBound.bitMajorant t ≤ w ∧ bitDef.val.Evalb ![p,t] ∧
        (bnd (PRAFixBitUFormulaBound.limInsideBody (L := L))).Evalb ![t,p,w])
    (hBV : ∀ p, p < s → (isSemiformula L).sigma.val.Evalb ![0,p] →
      ∃ v t, ((p*p+p)^2)+1 ≤ w ∧ v < w ∧ t < w ∧
        PRABitFullWitnessBound.bitMajorant v ≤ w ∧ bitDef.val.Evalb ![(p*p+p)^2,v] ∧
        (bnd (PRABVFixpointBound.limInsideBody (L := L))).Evalb ![v,t,(p*p+p)^2,w]) :
    (isFormulaSet L).sigma.val.Evalb ![s] → (bnd (isFormulaSet L).sigma.val).Evalb ![s,w] := by
  apply PRAFormulaSetTwoHistoriesBound.formulaSet_bound_of_two_histories s w hw hneg hU
  intro p hp hsemi
  obtain ⟨v,t,hq,hv,ht,hsize,hbit,hlim⟩ := hBV p hp hsemi
  let q : V := (p*p+p)^2
  have hlt : q < w := lt_of_lt_of_le (lt_succ_iff_le.mpr (le_refl q)) hq
  refine ⟨q,v,t,hlt,hq,?_,hv,ht,hsize,hbit,hlim⟩
  simp [q, PRABVPairPolynomial.bvPair_eq]
noncomputable def semiSigma0 : ArithmeticSemisentence 1 := PRAFormulaSetSyntaxBound.semiSigma0 (L := L)
noncomputable def boundedULim : ArithmeticSemisentence 3 := PRAFixBitUFormulaBound.boundedLim (L := L)
noncomputable def boundedBVLim : ArithmeticSemisentence 4 := PRABVFixpointBound.boundedLim (L := L)
noncomputable def formulaSet : ArithmeticSemisentence 1 := (isFormulaSet L).sigma.val
noncomputable def boundedFormulaSet : ArithmeticSemisentence 2 := bnd (formulaSet (L := L))
noncomputable def formulaSetExplicitPairBody : ArithmeticSemisentence 2 :=
  “s w. 0 < w ∧ (((2*s+1)+(2*s²+1))+s+1) ≤ w ∧
    (∀ p < s, !((semiSigma0 (L := L))) p → ∃ t < w,
      (((t⁴+1)+(t²+1)+(2*t²+1)+(t⁴+t⁴+2*t+1))+t+1) ≤ w ∧ !bitDef p t ∧ !((boundedULim (L := L))) t p w) ∧
    (∀ p < s, !((semiSigma0 (L := L))) p → ∃ v, ∃ t,
      ((p*p+p)²)+1 ≤ w ∧ v < w ∧ t < w ∧
      (((v⁴+1)+(v²+1)+(2*v²+1)+(v⁴+v⁴+2*v+1))+v+1) ≤ w ∧ !bitDef ((p*p+p)²) v ∧ !((boundedBVLim (L := L))) v t ((p*p+p)²) w) ∧
    !((formulaSet (L := L))) s → !((boundedFormulaSet (L := L))) s w”
theorem formulaSetExplicitPairBody_model (e : Fin 2 → V) : (formulaSetExplicitPairBody (L := L)).Eval e Empty.elim := by
  simp [formulaSetExplicitPairBody,boundedULim,PRAFixBitUFormulaBound.boundedLim,
    boundedBVLim,PRABVFixpointBound.boundedLim,boundedFormulaSet,semiSigma0,
    PRAFormulaSetSyntaxBound.semiSigma0,PRAFormulaSetWitnessBound.semiformulaSigma0,Semiformula.eval_substs]
  intro hw hn hu hbv hf
  have hb : ∀ p, p < e 0 → (isSemiformula L).sigma.val.Evalb ![0,p] →
      ∃ v t, ((p*p+p)^2)+1 ≤ e 1 ∧ v < e 1 ∧ t < e 1 ∧
        PRABitFullWitnessBound.bitMajorant v ≤ e 1 ∧ bitDef.val.Evalb ![(p*p+p)^2,v] ∧
        (bnd (PRABVFixpointBound.limInsideBody (L := L))).Evalb ![v,t,(p*p+p)^2,e 1] := by
    intro p hp hs
    obtain ⟨hq,v,hv,t,ht,hsize,hbit,hlim⟩ := hbv p hp hs
    exact ⟨v,t,hq,hv,ht,hsize,hbit,hlim⟩
  exact formulaSet_bound_of_explicit_pair_histories (L := L) (e 0) (e 1) hw hn hu hb hf
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def formulaSetExplicitPairSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (formulaSetExplicitPairBody (L := L))
theorem candidate_proves_formulaSet_explicit_pair_bound : PRA ⊢ formulaSetExplicitPairSentence (L := L) := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact formulaSetExplicitPairBody_model e
end DiophantineConsistency.PRAFormulaSetExplicitPairBound
