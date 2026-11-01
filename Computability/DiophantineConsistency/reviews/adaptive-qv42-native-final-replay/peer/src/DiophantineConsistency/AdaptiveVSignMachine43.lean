import DiophantineConsistency.AdaptiveVSignFrom87
import DiophantineConsistency.ArithmeticAdaptivePositiveAuxPair2011
import DiophantineConsistency.AdaptiveVSignTransport43
import DiophantineConsistency.IPRAQV42ConditionalBridge
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveVSignMachine43
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC ArithmeticCantor
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveDirectOrdinate86AuxNorm ArithmeticAdaptiveScaledNorms2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem from16_to43 (p : Fin 4 → ℕ) (hb : (2:V) ≤ (p 0:V)) (v : Fin 16 → V)
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveMainScaleWitness16.literal (fun j => (p j:ℤ))) v)
    (hrank : ∃ m : V, 0 < m ∧ SignedRep (AdaptiveRankWitness17.rankExpression (fun j => (p j:ℤ))) v (natural m))
    (hsign : (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV (fun j => (p j:ℤ))) (fun i => v ⟨i.val, by omega⟩)).2 <
      (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV (fun j => (p j:ℤ))) (fun i => v ⟨i.val, by omega⟩)).1) :
    ∃ u : Fin 43 → V, (∀ i, 0 < u i) ∧
      InternalZero (AdaptiveZ43Context.literal (fun j => (p j:ℤ))) u ∧ u 26 < u 25 := by
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
  exact AdaptiveVSignTransport43.from42 p hb v42 hp42 hz42 hs42

theorem from87_to43 (v : Fin 13 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveFirstRootFactor87Literal.expressionAt87 CurrentWindowCarry2011.ports) v)
    (hsign : (pairEval (eV CurrentWindowCarry2011.ports) v).2 <
      (pairEval (eV CurrentWindowCarry2011.ports) v).1) :
    ∃ u : Fin 43 → V, (∀ i, 0 < u i) ∧ InternalZero (AdaptiveZ43Context.literal CurrentWindowCarry2011.ports) u ∧ u 26 < u 25 := by
  have hbn : 2 ≤ CurrentMasks2011.beta := le_trans (by decide) ArithmeticAdaptiveRankWindow2011.current_bounds_nat.1
  have hbv : (2:V) ≤ (CurrentMasks2011.beta:V) := by exact_mod_cast hbn
  have hb2 : (2:V) ≤ (currentPorts 0:V) := by simpa only [currentPorts, Matrix.cons_val_zero] using hbv
  have hb : 0 < (currentPorts 0:V) := lt_of_lt_of_le (by norm_num : (0:V) < 2) hb2
  have hz' : InternalZero (AdaptiveFirstRootFactor87Literal.expressionAt87 (fun j => (currentPorts j:ℤ))) v := by
    simpa only [currentPorts_cast] using hz
  have hs' : (pairEval (eV (fun j => (currentPorts j:ℤ))) v).2 <
      (pairEval (eV (fun j => (currentPorts j:ℤ))) v).1 := by simpa only [currentPorts_cast] using hsign
  obtain ⟨w,hw,h86,hs86⟩ := AdaptiveVReverseFrom87.from87 currentPorts v hb hv hz' hs'
  have h86fixed : InternalZero (AdaptiveDirectOrdinate86Literal.expressionAt86 CurrentWindowCarry2011.ports) w := by
    simpa only [currentPorts_cast] using h86
  have hopt : InternalZero (AdaptiveDirectOrdinateSquareSums.optimized CurrentWindowCarry2011.ports) w :=
    (AdaptiveDirectOrdinateSquareSums.optimized_zero_iff_original _ w).mpr h86fixed
  have hm := AdaptiveSquareWitnessDirect14.fixed_magnitude_positive w hw hopt
  obtain ⟨v14,hp14,hz14,he14⟩ := AdaptiveSquareWitnessDirect14.exists_positive_extension_with_coordinates _ w hw hopt hm
  have hz14' : InternalZero (AdaptiveSquareWitnessDirect14.literal (fun j => (currentPorts j:ℤ))) v14 := by simpa only [currentPorts_cast] using hz14
  obtain ⟨v15,hp15,hz15,he15⟩ := AdaptiveScaleWitness15.exists_positive_extension_with_coordinates currentPorts v14 hb hp14 hz14'
  obtain ⟨v16,hp16,hz16,he16⟩ := AdaptiveMainScaleWitness16.exists_positive_extension_with_coordinates currentPorts v15 hb hp15 hz15
  have h13 : (fun i : Fin 13 => v16 ⟨i.val, by omega⟩) = w := by
    funext i
    have h16 := congrFun he16 (⟨i.val, by omega⟩ : Fin 15)
    have h15 := congrFun he15 (⟨i.val, by omega⟩ : Fin 14)
    have h14 := congrFun he14 i
    change v16 ⟨i.val, by omega⟩ = v15 ⟨i.val, by omega⟩ at h16
    change v15 ⟨i.val, by omega⟩ = v14 ⟨i.val, by omega⟩ at h15
    change v14 ⟨i.val, by omega⟩ = w i at h14
    exact h16.trans (h15.trans h14)
  have hs16 : (pairEval (eV (fun j => (currentPorts j:ℤ))) (fun i => v16 ⟨i.val, by omega⟩)).2 <
      (pairEval (eV (fun j => (currentPorts j:ℤ))) (fun i => v16 ⟨i.val, by omega⟩)).1 := by
    simpa only [h13] using hs86
  have hz16fixed : InternalZero (AdaptiveMainScaleWitness16.literal CurrentWindowCarry2011.ports) v16 := by
    simpa only [currentPorts_cast] using hz16
  have hrank := AdaptiveRankWitness17.fixed_positive_rank v16 hp16 hz16fixed
  have hrank' : ∃ m : V, 0 < m ∧ SignedRep (AdaptiveRankWitness17.rankExpression (fun j => (currentPorts j:ℤ))) v16 (natural m) := by
    simpa only [currentPorts_cast] using hrank
  obtain ⟨v32,hp32,hz32,hs32⟩ := from16_to43 currentPorts hb2 v16 hp16 hz16 hrank' hs16
  refine ⟨v32,hp32,?_,hs32⟩
  simpa only [currentPorts_cast] using hz32

theorem from_run43 (T : V) (hT : first (ArithmeticMachineRun215.run T)=0) :
    ∃ v : Fin 43 → V, (∀ i, 0 < v i) ∧ v 26 < v 25 ∧
      InternalZero (AdaptiveZ43Context.literal CurrentWindowCarry2011.ports) v := by
  obtain ⟨w,hw,hzero,hsign⟩ := ArithmeticAdaptivePositiveAuxPair2011.oriented_pair_witness_of_run T hT
  have h87 : InternalZero (AdaptiveFirstRootFactor87Literal.expressionAt87 CurrentWindowCarry2011.ports) w := by
    change (splitEval (AdaptiveFirstRootFactor87Literal.expressionAt87 CurrentWindowCarry2011.ports) w).1 =
      (splitEval (AdaptiveFirstRootFactor87Literal.expressionAt87 CurrentWindowCarry2011.ports) w).2
    change (splitEval (expressionAt CurrentWindowCarry2011.ports) w).1 =
      (splitEval (expressionAt CurrentWindowCarry2011.ports) w).2 at hzero
    rw [← AdaptiveFirstRootFactor87Literal.split_expression_eq]
    exact hzero
  obtain ⟨v,hv,hz,hs⟩ := from87_to43 w hw h87 hsign
  exact ⟨v,hv,hs,hz⟩

theorem machineOrients : IPRAQV42ConditionalBridge.MachineOrients := by
  intro W _ _ h
  obtain ⟨t,ht⟩ := h
  exact from_run43 t ht
#print axioms from16_to43
#print axioms from87_to43
#print axioms from_run43
#print axioms machineOrients
end DiophantineConsistency.AdaptiveVSignMachine43
