import OAI.Combinatorics.Progressions.Linear.NativeCoefficientKernel

namespace OAI

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem exists_bounded_coefficient_corrections (hs : 1 ≤ s) (hP : 0 ≤ P) :
    ∃ E R : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ,
      (∀ α j, |(W.fourRankBasis.baseChange ℝ).repr (E α).val j| ≤
        Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α) ∧
      (∀ α, (fun j => (W.fourRankBasis.baseChange ℝ).repr (R α).val j) ∈
        realDenominatorGrid D.projectedDenominator) ∧
      ∀ α, W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
          (D.projectedOrbitCoefficient α - E α - R α) ∈
        (I.refilteredHorizontalImage D.index D.subalgebra
          (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ := by
  obtain ⟨E, R, hE, hR, hres⟩ := D.exists_projected_corrections hs
  refine ⟨D.projectedRepresentativeLayer E, D.projectedRepresentativeLayer R, ?_, ?_, ?_⟩
  · intro α j
    exact D.projectedRepresentative_slow hP E hE α j
  · intro α
    exact D.projectedRepresentative_grid R hR α
  · intro α
    let f := W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
    have hinner := (map_sub f (D.projectedOrbitCoefficient α) (D.projectedRepresentativeLayer E α)).trans
      (congrArg₂ (fun x y => x - y) (D.projectedOrbitCoefficient_horizontal α)
        (D.projectedRepresentative_horizontal E α))
    have heq := (map_sub f (D.projectedOrbitCoefficient α - D.projectedRepresentativeLayer E α)
      (D.projectedRepresentativeLayer R α)).trans
        (congrArg₂ (fun x y => x - y) hinner (D.projectedRepresentative_horizontal R α))
    exact (congrArg (fun v => v ∈ (I.refilteredHorizontalImage D.index D.subalgebra
      (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ) heq).mpr (hres α)

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
