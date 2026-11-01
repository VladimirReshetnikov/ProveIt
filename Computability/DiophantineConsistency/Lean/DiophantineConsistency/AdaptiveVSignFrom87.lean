import DiophantineConsistency.AdaptiveVReverseFrom87
import DiophantineConsistency.AdaptivePreserveCoordinates16
import DiophantineConsistency.AdaptiveVSignFrom16
import DiophantineConsistency.AdaptiveAQ31
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011

/-! An oriented fixed-port 87 witness yields a positive 31-coordinate zero. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveVSignFrom87
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveDirectOrdinate86AuxNorm ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem from87_to32 (v : Fin 13 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveFirstRootFactor87Literal.expressionAt87 CurrentWindowCarry2011.ports) v)
    (hsign : (pairEval (eV CurrentWindowCarry2011.ports) v).2 <
      (pairEval (eV CurrentWindowCarry2011.ports) v).1) :
    ∃ u : Fin 32 → V, (∀ i, 0 < u i) ∧ InternalZero (AdaptiveAQ32Literal.literal CurrentWindowCarry2011.ports) u ∧ u 24 < u 23 := by
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
  obtain ⟨v32,hp32,hz32,hs32⟩ := AdaptiveVSignFrom16.from16 currentPorts hb2 v16 hp16 hz16 hrank' hs16
  refine ⟨v32,hp32,?_,hs32⟩
  simpa only [currentPorts_cast] using hz32

theorem from87 (v : Fin 13 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveFirstRootFactor87Literal.expressionAt87 CurrentWindowCarry2011.ports) v)
    (hsign : (pairEval (eV CurrentWindowCarry2011.ports) v).2 <
      (pairEval (eV CurrentWindowCarry2011.ports) v).1) :
    ∃ u : Fin 31 → V, (∀ i, 0 < u i) ∧ InternalZero (AdaptiveAQ31Literal.literal CurrentWindowCarry2011.ports) u := by
  obtain ⟨u,hu,hzero,hs⟩ := from87_to32 v hv hz hsign
  exact (AdaptiveAQ31.oriented_exists_iff CurrentWindowCarry2011.ports).mp ⟨u,hu,hs,hzero⟩
#print axioms from87_to32
#print axioms from87
end DiophantineConsistency.AdaptiveVSignFrom87
