import DiophantineConsistency.AdaptiveVPreserve17
import DiophantineConsistency.AdaptiveVPreserve22
import DiophantineConsistency.AdaptiveVPreserve26
import DiophantineConsistency.AdaptiveVSignNamed33
import DiophantineConsistency.AdaptiveVSignNamed42
import DiophantineConsistency.AdaptiveVSignExpression26
import DiophantineConsistency.AdaptiveVSignTransport32

/-! Preserve a constructed auxiliary sign through the named witness extensions. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveVSignFrom16
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem from16 (p : Fin 4 → ℕ) (hb : (2:V) ≤ (p 0:V)) (v : Fin 16 → V)
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveMainScaleWitness16.literal (fun j => (p j:ℤ))) v)
    (hrank : ∃ m : V, 0 < m ∧ SignedRep (AdaptiveRankWitness17.rankExpression (fun j => (p j:ℤ))) v (natural m))
    (hsign : (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV (fun j => (p j:ℤ))) (fun i => v ⟨i.val, by omega⟩)).2 <
      (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV (fun j => (p j:ℤ))) (fun i => v ⟨i.val, by omega⟩)).1) :
    ∃ u : Fin 32 → V, (∀ i, 0 < u i) ∧
      InternalZero (AdaptiveAQ32Literal.literal (fun j => (p j:ℤ))) u ∧ u 24 < u 23 := by
  obtain ⟨m,hm,hr⟩ := hrank
  obtain ⟨v17,hp17,hz17,he17⟩ := AdaptiveRankWitness17.VPreserveProbe.exists_preserving_extension _ v hv hz m hm hr
  obtain ⟨v22,hp22,hz22,he22⟩ := AdaptiveNamedValues22.VPreserveProbe.exists_preserving_extension _ v17 hp17 hz17
  obtain ⟨v26,hp26,hz26,he26⟩ := AdaptiveNamedValues26.VPreserveProbe.exists_preserving_extension p v22 hp22 hz22
  have h13 : (fun i : Fin 13 => v26 ⟨i.val, by omega⟩) = (fun i : Fin 13 => v ⟨i.val, by omega⟩) := by
    funext i
    have h26 := congrFun he26 (⟨i.val, by omega⟩ : Fin 22)
    have h22 := congrFun he22 (⟨i.val, by omega⟩ : Fin 17)
    have h17 := congrFun he17 (⟨i.val, by omega⟩ : Fin 16)
    change v26 ⟨i.val, by omega⟩ = v22 ⟨i.val, by omega⟩ at h26
    change v22 ⟨i.val, by omega⟩ = v17 ⟨i.val, by omega⟩ at h22
    change v17 ⟨i.val, by omega⟩ = v ⟨i.val, by omega⟩ at h17
    exact h26.trans (h22.trans h17)
  have hsign26 : (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV (fun j => (p j:ℤ))) (fun i => v26 ⟨i.val, by omega⟩)).2 <
      (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV (fun j => (p j:ℤ))) (fun i => v26 ⟨i.val, by omega⟩)).1 := by
    simpa only [h13] using hsign
  have hnamed := AdaptiveVSignExpression26.positive_of_13 _ v26 hz26 hsign26
  obtain ⟨v33,hp33,hz33,hs33⟩ := AdaptiveNamedValues33.AdaptiveVSignNamed33.exists_oriented_extension _ v26 hp26 hz26 hnamed
  obtain ⟨v42,hp42,hz42,hs42⟩ := AdaptiveNamedValues42.AdaptiveVSignNamed42.exists_oriented_extension p v33 hp33 hz33 hs33
  exact AdaptiveVSignTransport32.from42 p hb v42 hp42 hz42 hs42
#print axioms from16
end DiophantineConsistency.AdaptiveVSignFrom16
