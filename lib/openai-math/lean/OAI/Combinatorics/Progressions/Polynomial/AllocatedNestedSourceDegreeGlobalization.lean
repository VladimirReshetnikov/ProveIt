import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePreparedPhysicalConclusion

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

theorem exists_degreeGlobalizationAt_source_successor (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X]
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
    (weight : (X → ℤ) → ℂ) (p : ℝ) (e : ℕ)
    (source : A.DegreeSourceProfile (s + 1) p e),
    0 ≤ p →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
    (source.front.familyParameter + 2) ^ C ≤ source.inner.x →
    source.inner.x ≤ source.inner.gainLog →
    Real.exp source.inner.x ≤ (S.value : ℝ) →
    ∀ outputCost : ℝ,
    A.DegreeGlobalizationAt (E := E) weight s
      (refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      source.inner.recursiveParameter outputCost →
    source.inner.recursiveParameter ≤ outputCost →
    A.DegreeGlobalizationAt (E := E) weight (s + 1) e p (3 * outputCost + 2) := by
  classical
  obtain ⟨Cgeometry, Cpair, Cbasis, K, T, C, _, _, _, _, _, hC, hterminal⟩ :=
    exists_primitiveFrontQuotient_canonical_physical_terminal s
  refine ⟨C, hC, ?_⟩
  intro m G X _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells
    center _ A weight p e source hp hvariables hfit hgain hscale outputCost lowerIH houtput
    L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hFmark hmark
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  obtain ⟨data⟩ := P.exists_primitiveFrontQuotientData Fmark source (by omega) hp hp le_rfl
    hvariables hD hFmark (fun i j => hmark j i) ℓ hℓ hLip hpositive hweight
    le_rfl le_rfl hnet
  have produced := hterminal Fmark P source data hp hφ le_rfl hfit hgain hscale
  exact AllocatedExternalCandidateProblem.PrimitiveFrontQuotientData.conclusion_of_canonicalPhysicalTerminal
    Fmark P source data hp hφ hsurj hweight hnet outputCost lowerIH houtput produced

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

theorem exists_degreeGlobalizationAt_of_nested_source_profiles (total : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X]
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
    (weight : (X → ℤ) → ℂ) (initial exponent innerDepth : ℕ) (x : ℝ)
    (source : ∀ j : Fin total,
      A.DegreeSourceProfile (total - (j.val + 1) + 1)
        (candidateNestedForwardSeed exponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * j.val) x)
        (candidateNestedDegreeNetExponent total initial j.val)),
    2 ≤ exponent → 0 ≤ x →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x →
    (∀ j, (source j).inner.x = candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * j.val + 1) x) →
    (∀ j, ((source j).front.familyParameter + 2) ^ C ≤ (source j).inner.x) →
    (∀ j, (source j).inner.x ≤ (source j).inner.gainLog) →
    Real.exp (candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * total) x) ≤
        (S.value : ℝ) →
    (∀ j, (source j).inner.recursiveParameter ≤ candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * (j.val + 1)) x) →
    A.DegreeGlobalizationAt (E := E) weight total initial x
      (candidateDegreeReturnBudget total (candidateNestedForwardSeed exponent
        AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * total) x)) := by
  classical
  let Cstep : ℕ → ℕ := fun s => Classical.choose (exists_degreeGlobalizationAt_source_successor s)
  let C := 2 + ∑ s ∈ Finset.range total, Cstep s
  have hC : 2 ≤ C := by dsimp [C]; omega
  have hstepC {s : ℕ} (hs : s < total) : Cstep s ≤ C := by
    have hsum := Finset.single_le_sum (f := Cstep) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hs)
    dsimp only [C]
    omega
  refine ⟨C, hC, ?_⟩
  intro m G X _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells
    center _ A weight initial exponent innerDepth x source hA hx hvariables
    hinner hfront hgain hscale hrecursive
  apply A.degreeGlobalizationAt_nested (E := E) weight total initial exponent innerDepth
    AllocatedExternalCandidateSampler.degreeSourceCountConstants hA hx
  intro j hj q hq lower
  let index : Fin total := ⟨j, hj⟩
  let profile := source index
  have hp : 0 ≤ candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * j) x :=
    candidateNestedForwardSeed_nonneg exponent _ innerDepth (2 * j) hx
  have hvars := hvariables.trans
    (le_candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * j) hA hx)
  have hsmall : Cstep (total - (j + 1)) ≤ C := hstepC (by omega)
  have hf0 := (profile.front.familyBudget hp).hpFamily
  have hfit : (profile.front.familyParameter + 2) ^ Cstep (total - (j + 1)) ≤
      profile.inner.x :=
    (pow_le_pow_right₀ (by linarith only [hf0]) hsmall).trans (hfront index)
  have hsize : Real.exp profile.inner.x ≤ (S.value : ℝ) := by
    apply le_trans _ hscale
    apply Real.exp_le_exp.mpr
    rw [show profile.inner.x = candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * j + 1) x from hinner index]
    exact candidateNestedForwardSeed_monotone exponent _ innerDepth hA hx (by omega)
  have hrec := hrecursive index
  have recur := AllocatedExternalCandidateSampler.DegreeGlobalizationAt.mono_input A lower
    profile.inner.recursiveParameter_nonneg hrec
  have current := (Classical.choose_spec
    (exists_degreeGlobalizationAt_source_successor (total - (j + 1)))).2
    (E := E) A weight _ _ profile hp hvars hfit (hgain index) hsize q recur (hrec.trans hq)
  have hd : total - j = total - (j + 1) + 1 := by omega
  simpa only [hd] using current

end Erdos3.VectorPolynomial

end

end OAI
