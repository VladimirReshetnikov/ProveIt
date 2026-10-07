import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialDenseSliceCenter
import OAI.Combinatorics.Progressions.Probability.AllocatedExternalCandidateRetainedSliceLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {step : ℕ}
    (slice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) step)
    (hstep : 0 < step) (hlen : ∀ i, 0 < slice.length i)
    (hne : slice.integerPoints.Nonempty)

include hstep in
theorem retainedLaw_eq_fiberSliceLaw :
    C.retainedLaw slice.integerPoints hne slice.integerPoints_subset_integerBox =
      slice.fiberSliceLaw hlen C.fixed C.fixed_in_box := by
  classical
  have hm (f : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
      (C.retainedLaw slice.integerPoints hne slice.integerPoints_subset_integerBox).complexMean
          (fun site => f site.val) =
        (slice.fiberSliceLaw hlen C.fixed C.fixed_in_box).complexMean
          (fun site => f site.val) := by
    rw [C.retainedLaw_complexMean_parameter, slice.expect_integerPoints hstep,
      slice.fiberSliceLaw_complexMean]
    congr 1
    · ext u
      simp
  have hw (site : A.Site) := congrArg Complex.re
    (hm (fun x => if x = site.val then 1 else 0))
  simp only [FiniteProbabilityWeights.complexMean_re, apply_ite, Complex.one_re,
    Complex.zero_re, Subtype.val_inj, FiniteProbabilityWeights.mean,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hw
  cases hp : C.retainedLaw slice.integerPoints hne slice.integerPoints_subset_integerBox
  cases hq : slice.fiberSliceLaw hlen C.fixed C.fixed_in_box
  simp only [hp, hq] at hw
  congr
  exact funext hw

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}
    (out : P.Conclusion outputCost outputMass outputScore)

theorem siteLaw_eq_fiberSliceLaw (z : out.retained) :
    out.siteLaw z = (out.slice z).fiberSliceLaw
      ((out.slice z).length_pos_of_dense (out.dense z))
      (P.chart ⟨z.val, out.subset z.property⟩).fixed
      (P.chart ⟨z.val, out.subset z.property⟩).fixed_in_box := by
  classical
  exact (P.chart ⟨z.val, out.subset z.property⟩).retainedLaw_eq_fiberSliceLaw
    (out.slice z) (out.step_pos z) ((out.slice z).length_pos_of_dense (out.dense z))
    (out.dense z).nonempty

variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
    {Dmod : ℕ} {Selection : Type} [Fintype Selection]
    {selected : Selection → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod selected τ δslice)
    (qnum : ActualFixedSpatialSlicedForecastNumerics s)
    (z : out.retained)
    (hkeep : ∀ k, (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔
      qnum.Hchild ≤ A.sides k)
    (commonTuple : G → IntegerScalarCubeBox Empty S.value)
    (hkernel : Nonempty G)
    (hcutoff : qnum.Hchild ≤ S.value)
    (hlate : 2 ≤ Real.exp (-outputCost) * (S.value : ℝ))
    (hdensity : qnum.δ ≤ Real.exp (-outputCost))
    (hactive : δslice ≤ Real.exp (-outputCost) / 2)
    (hlog : outputCost + 1 ≤ qnum.v)
    (hprescribed : outputCost + 1 ≤ s.Ppres)
    (hstride : 2 * Real.exp outputCost ≤ qnum.Ptail)

noncomputable def denseSliceInput : ActualFixedSpatialDenseSliceInput s qnum := by
  classical
  exact
    { keep := (P.chart ⟨z.val, out.subset z.property⟩).keep
      keep_iff := hkeep
      step := out.step z
      step_pos := out.step_pos z
      box := out.slice z
      fixed := (P.chart ⟨z.val, out.subset z.property⟩).fixed
      fixed_inside := (P.chart ⟨z.val, out.subset z.property⟩).fixed_in_box
      commonTuple := commonTuple
      cost := outputCost
      dense := (out.slice z).length_lower_of_dense (out.step_pos z) (out.dense z)
      kernel_nonempty := hkernel
      cutoff_le := hcutoff
      late_floor := hlate
      density_le := hdensity
      active_width := hactive
      kernel_log := hlog
      prescribed_log := hprescribed
      stride_cap := hstride }

@[simp] theorem denseSliceInput_cost :
    (out.denseSliceInput s qnum z hkeep commonTuple hkernel hcutoff hlate hdensity
      hactive hlog hprescribed hstride).cost = outputCost := rfl

theorem denseSliceInput_fiberSliceLaw :
    let input := out.denseSliceInput s qnum z hkeep commonTuple hkernel hcutoff hlate
      hdensity hactive hlog hprescribed hstride
    input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside =
      out.siteLaw z := by
  classical
  exact (out.siteLaw_eq_fiberSliceLaw z).symm

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
