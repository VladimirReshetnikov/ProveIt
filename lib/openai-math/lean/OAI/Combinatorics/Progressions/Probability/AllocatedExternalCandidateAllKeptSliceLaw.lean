import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateDenseSliceInput
import OAI.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower

namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} {N : I → ℕ} {q : ℕ}

def keepTrueSlice (S : ResidueBoxSlice N q) :
    ResidueBoxSlice (fun i : {_i : I // True} => N i.val) q :=
  S.comap Subtype.val

def keepTrueParameterEquiv (S : ResidueBoxSlice N q) :
    (∀ i, Fin (S.length i)) ≃ (∀ i, Fin (S.keepTrueSlice.length i)) where
  toFun u i := u i.val
  invFun u i := u ⟨i, trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype I] [DecidableEq I]

theorem keepTrueSlice_fiberSliceLaw_mean (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (fixed : {_i : I // ¬True} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    (f : integerBox N → ℝ) :
    (S.fullSliceLaw hlen).mean f =
      (S.keepTrueSlice.fiberSliceLaw (fun i => hlen i.val) fixed hfixed).mean f := by
  refine (S.fullSliceLaw_mean hlen f).trans
    (Eq.trans ?_ (S.keepTrueSlice.fiberSliceLaw_mean
      (fun i => hlen i.val) fixed hfixed f).symm)
  apply Fintype.expect_equiv S.keepTrueParameterEquiv
  intro u
  rfl

theorem keepTrueSlice_fiberSliceLaw (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (fixed : {_i : I // ¬True} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ)) :
    S.fullSliceLaw hlen =
      S.keepTrueSlice.fiberSliceLaw (fun i => hlen i.val) fixed hfixed := by
  have ext_weight {p p' : FiniteProbabilityWeights (integerBox N)}
      (h : p.weight = p'.weight) : p = p' := by
    cases p
    cases p'
    cases h
    rfl
  apply ext_weight
  funext x
  have hm := S.keepTrueSlice_fiberSliceLaw_mean hlen fixed hfixed
    (fun y => if y = x then 1 else 0)
  simpa [FiniteProbabilityWeights.mean] using hm

theorem fullSliceLaw_returnedFiberLaw (S : ResidueBoxSlice N q)
    (hq : 0 < q) (hlen : ∀ i, 0 < S.length i) {cost : ℝ}
    (hlength : ∀ i, Real.exp (-cost) * (N i : ℝ) ≤ (S.length i : ℝ)) :
    RelativeReturnedFiberLaw (fun _ : I => True) N cost (S.fullSliceLaw hlen) := by
  let fixed : {_i : I // ¬True} → ℤ := fun i => False.elim (i.property trivial)
  have hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ) :=
    fun i => False.elim (i.property trivial)
  exact ⟨fixed, hfixed, q, hq, S.keepTrueSlice, (fun i => hlen i.val),
    (fun i => hlength i.val), S.keepTrueSlice_fiberSliceLaw hlen fixed hfixed⟩

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]
    {keep : I → Prop} [dkeep : DecidablePred keep] {N : I → ℕ} {q : ℕ}

theorem exists_fullSliceLaw_of_keep_eq_true
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (hkeep : keep = (fun _ => True)) (hlen : ∀ i, 0 < S.length i)
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    {cost : ℝ}
    (hlength : ∀ i, Real.exp (-cost) * (N i.val : ℝ) ≤ (S.length i : ℝ)) :
    ∃ (T : ResidueBoxSlice N q) (hT : ∀ i, 0 < T.length i),
      (∀ i, Real.exp (-cost) * (N i : ℝ) ≤ (T.length i : ℝ)) ∧
      S.fiberSliceLaw hlen fixed hfixed = T.fullSliceLaw hT := by
  subst keep
  have hd : dkeep = (fun _ => instDecidableTrue) := Subsingleton.elim _ _
  cases hd
  let T : ResidueBoxSlice N q := S.comap (fun i => ⟨i, trivial⟩)
  have hT : T.keepTrueSlice = S := rfl
  refine ⟨T, (fun i => hlen ⟨i, trivial⟩), (fun i => hlength ⟨i, trivial⟩), ?_⟩
  have h := T.keepTrueSlice_fiberSliceLaw (fun i => hlen ⟨i, trivial⟩) fixed hfixed
  simpa only [hT] using h.symm

end Erdos3.ResidueBoxSlice

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace AllocatedExternalCandidateProblem.Conclusion

theorem exists_fullSliceLaw (out : P.Conclusion outputCost outputMass outputScore)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = (fun _ => True))
    (z : out.retained) :
    ∃ (T : ResidueBoxSlice A.sides (out.step z)) (hlen : ∀ i, 0 < T.length i),
      (∀ i, Real.exp (-outputCost) * (A.sides i : ℝ) ≤ (T.length i : ℝ)) ∧
      out.siteLaw z = T.fullSliceLaw hlen := by
  classical
  obtain ⟨T, hlen, hlength, hlaw⟩ :=
    (out.slice z).exists_fullSliceLaw_of_keep_eq_true
      (hkeep ⟨z.val, out.subset z.property⟩)
      ((out.slice z).length_pos_of_dense (out.dense z))
      (P.chart ⟨z.val, out.subset z.property⟩).fixed
      (P.chart ⟨z.val, out.subset z.property⟩).fixed_in_box
      ((out.slice z).length_lower_of_dense (out.step_pos z) (out.dense z))
  exact ⟨T, hlen, hlength, (out.siteLaw_eq_fiberSliceLaw z).trans hlaw⟩

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
