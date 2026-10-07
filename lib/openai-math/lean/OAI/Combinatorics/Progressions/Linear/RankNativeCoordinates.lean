import OAI.Combinatorics.Progressions.Linear.NativeCoefficientKernel

namespace OAI

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q}

theorem projectedOrbitCoefficient_native_coordinates (D : I.SunflowerWitness P)
    (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    (k : Fin 4) (i : ι) :
    W.rank.filtration.realFourAmbientCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
        (D.projectedOrbitCoefficient α).val ⟨k, i⟩ =
      (f.baseChange ℝ).repr
        ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ
          (W.horizontalCoefficient hs c τ hG α
            (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)))) i := by
  have hmap := congrFun (W.rank.filtration.realFourHorizontalCoordinates_map
    (Finsupp.weight (fun _ : Unit => 1) α) f (D.projectedOrbitCoefficient α)).symm ⟨k, i⟩
  have hcomponent := W.rank.filtration.realFourHorizontalCoordinates_component
    (Finsupp.weight (fun _ : Unit => 1) α) f
    (W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
      (D.projectedOrbitCoefficient α)) k i
  exact hmap.trans (hcomponent.trans (congrArg
    (fun x => (f.baseChange ℝ).repr
      ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ x) i)
    (D.projectedOrbitCoefficient_native_component hs c τ hG α k)))

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
