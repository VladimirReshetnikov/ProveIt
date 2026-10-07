import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAdaptedOptionQuotientFactors
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialGroupMapChart

namespace OAI

section

universe u v

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {P : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)]
    {s d dQ : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (partners : ∀ j, RationalFilteredNilmanifold (P j) s (dp j))
    (partnerOrbit : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

attribute [local irreducible] NilpotentLieFiltration.realPolynomialGroupMap
    NilpotentLieFiltration.weightedAdaptedRealChartHom

theorem optionJoint_lieQuotient_chart_polynomialCoordinates
    {K : Type*} (β : C.Variables → MvPolynomial K ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : K => 1) 1) :
    (optionProduct Q partners).filtration.weightedAdaptedRealChartHom
      (fun _ : C.Variables => 1) (fun _ : K => 1) β hβ
      ((optionProduct Q partners).filtration.realification.polynomialOrbitCoordinates
        (fun _ : C.Variables => 1)
        ((candidate.lieQuotient ideal hI Q hQ hker).optionJoint partners partnerOrbit).orbit) =
      (optionProduct D partners).filtration.realPolynomialGroupMap
        (optionProduct Q partners).filtration
        (optionMarkedLieMap (L := P) (lieQuotientMap ideal))
        (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)
        (fun _ : K => 1)
        ((optionProduct D partners).filtration.weightedAdaptedRealChartHom
          (fun _ : C.Variables => 1) (fun _ : K => 1) β hβ
          ((optionProduct D partners).filtration.realification.polynomialOrbitCoordinates
            (fun _ : C.Variables => 1) (candidate.optionJoint partners partnerOrbit).orbit)) := by
  calc
    _ = (optionProduct Q partners).filtration.weightedAdaptedRealChartHom
        (fun _ : C.Variables => 1) (fun _ : K => 1) β hβ
        ((optionProduct D partners).filtration.realPolynomialGroupMap
          (optionProduct Q partners).filtration
          (optionMarkedLieMap (L := P) (lieQuotientMap ideal))
          (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)
          (fun _ : C.Variables => 1)
          ((optionProduct D partners).filtration.realification.polynomialOrbitCoordinates
            (fun _ : C.Variables => 1) (candidate.optionJoint partners partnerOrbit).orbit)) :=
      congrArg ((optionProduct Q partners).filtration.weightedAdaptedRealChartHom
        (fun _ : C.Variables => 1) (fun _ : K => 1) β hβ)
        (candidate.optionJoint_lieQuotient_polynomialCoordinates
          ideal hI Q hQ hker partners partnerOrbit)
    _ = _ := ((optionProduct D partners).filtration.realPolynomialGroupMap_weightedAdaptedRealChartHom
      (optionProduct Q partners).filtration
      (optionMarkedLieMap (L := P) (lieQuotientMap ideal))
      (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)
      (fun _ : C.Variables => 1) (fun _ : K => 1) β hβ
      ((optionProduct D partners).filtration.realification.polynomialOrbitCoordinates
        (fun _ : C.Variables => 1) (candidate.optionJoint partners partnerOrbit).orbit)).symm

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
