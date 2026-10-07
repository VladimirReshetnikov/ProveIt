import OAI.Combinatorics.Progressions.Dynamics.AllocatedCandidateNestedTerminalUniformLayersBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedCanonicalEarlyPrimitiveBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedNestedEndpointDimensionBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedNestedEndpointReturnBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointNumericalBounds
import OAI.Combinatorics.Progressions.Polynomial.AllocatedNestedSourceDegreeGlobalization
import OAI.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastPrimitiveCapBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

noncomputable def preparedRelativeEndpointCapExponent (s : ℕ) : ℕ :=
  2 + (∑ m : Fin (s + 1), preparedConcreteSlicedForecastPrimitiveCapExponent
    m.val 1 1 (preparedCommonRadiusPrimitiveExponent s)) +
      preparedCommonRadiusDensityCapNestedExponent s

theorem preparedRelativeEndpointCapExponent_two_le (s : ℕ) :
    2 ≤ preparedRelativeEndpointCapExponent s := by
  unfold preparedRelativeEndpointCapExponent
  omega

theorem preparedRelativeEndpointCapExponent_primitive_le {s m : ℕ} (hm : m ≤ s) :
    preparedConcreteSlicedForecastPrimitiveCapExponent
      m 1 1 (preparedCommonRadiusPrimitiveExponent s) ≤
        preparedRelativeEndpointCapExponent s := by
  classical
  let j : Fin (s + 1) := ⟨m, by omega⟩
  have hsum : preparedConcreteSlicedForecastPrimitiveCapExponent
      m 1 1 (preparedCommonRadiusPrimitiveExponent s) ≤
      ∑ i : Fin (s + 1), preparedConcreteSlicedForecastPrimitiveCapExponent
        i.val 1 1 (preparedCommonRadiusPrimitiveExponent s) :=
    by
      have h := Finset.single_le_sum
        (f := fun i : Fin (s + 1) => preparedConcreteSlicedForecastPrimitiveCapExponent
          i.val 1 1 (preparedCommonRadiusPrimitiveExponent s))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      exact h
  unfold preparedRelativeEndpointCapExponent
  omega

theorem preparedRelativeEndpointCapExponent_density_le (s : ℕ) :
    preparedCommonRadiusDensityCapNestedExponent s ≤
      preparedRelativeEndpointCapExponent s := by
  unfold preparedRelativeEndpointCapExponent
  omega

theorem preparedRelativeEndpointForecastCap_le_work
    (s m A : ℕ) (hm : m ≤ s)
    (hA : preparedRelativeEndpointCapExponent s ≤ A)
    (constants : ℕ → ℕ) (innerDepth outer inner M nX Jalloc : ℕ)
    {p gainLog Pchart childLog : ℝ} (hp : 0 ≤ p)
    (hgain : gainLog ∈ Set.Icc 0 p) (hchart : Pchart ∈ Set.Icc 0 p)
    (hchild : childLog ∈ Set.Icc 0 p) :
    let x := candidateNestedForwardSeed A constants innerDepth outer p
    let b := preparedFiniteForwardParameter A constants inner x
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ b →
    ((nX + m * M : ℕ) : ℝ) ≤ b →
    preparedConcreteSlicedForecastCapLog m M nX Jalloc
      p (b + 1) (allocatedCommonProductRadiusLog m p p) gainLog 0 Pchart childLog ≤
      preparedFiniteForwardWork A constants inner x := by
  intro x b hDbase hDmod
  have hAtwo := (preparedRelativeEndpointCapExponent_two_le s).trans hA
  have hx : 0 ≤ x := candidateNestedForwardSeed_nonneg A constants innerDepth outer hp
  have hpb : p ≤ b :=
    (le_candidateNestedForwardSeed A constants innerDepth outer hAtwo hp).trans
      (le_preparedFiniteForwardParameter A constants inner hx)
  have hb : 0 ≤ b := hp.trans hpb
  let C := preparedCommonRadiusPrimitiveExponent s
  have hC : 2 ≤ C := preparedCommonRadiusPrimitiveExponent_two_le s
  have hCreal : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hbase : 1 ≤ b + C := by linarith only [hb, hCreal]
  have hpower : b + C ≤ (b + C) ^ C := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ C by omega)
  have hpbound : p ≤ (b + C) ^ C := (by linarith only [hpb, hCreal] : p ≤ b + C).trans hpower
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 p) : a ∈ Set.Icc 0 ((b + C) ^ C) :=
    ⟨ha.1, ha.2.trans hpbound⟩
  have hrad := preparedCommonRadiusPrimitive_bound s m hm hp
  have hrad' : allocatedCommonProductRadiusLog m p p ∈ Set.Icc 0 ((b + C) ^ C) :=
    ⟨hrad.1, hrad.2.trans (pow_le_pow_left₀ (by positivity)
      (add_le_add hpb le_rfl) C)⟩
  have hchild' : childLog ∈ Set.Icc 0 ((b + (1 : ℕ)) ^ (1 : ℕ)) := by
    simp only [Nat.cast_one, pow_one]
    exact ⟨hchild.1, by linarith only [hchild.2, hpb]⟩
  have hcap := preparedConcreteSlicedForecastPrimitiveCapLog_le_work m 1 1 C A
    constants inner M nX Jalloc hAtwo
    ((preparedRelativeEndpointCapExponent_primitive_le hm).trans hA) hx
    hDbase hDmod (lift ⟨hp, le_rfl⟩) hrad' (lift hgain)
    (lift ⟨le_rfl, hp⟩) (lift hchart) hchild'
  simpa only [Nat.cast_one, pow_one] using hcap

theorem preparedRelativeEndpointMarginalCap_le_exp_work
    (s A : ℕ) (hA : preparedRelativeEndpointCapExponent s ≤ A)
    {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m)
    (hm : m ≤ s) (M Jalloc : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M)
    {p : ℝ} (hp : 0 ≤ p)
    (hnum : (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ p)
    (V : Fin m → ℝ≥0) (hV : ∀ j, (V j : ℝ) ≤ Real.exp p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp p)
    (constants : ℕ → ℕ) (innerDepth outer inner : ℕ) :
    max 1 (4 * ∏ j, earlyConstantDensityCap
      (Fintype.card (PreparedSamplerContinuous prep j))
      (preparedSamplerTransverse prep j) (allocatedCommonProductRadius m p p) (V j)) ≤
      Real.exp (preparedFiniteForwardWork A constants inner
        (candidateNestedForwardSeed A constants innerDepth outer p)) := by
  apply max_le
  · exact Real.one_le_exp (preparedFiniteForwardWork_nonneg A constants inner
      (candidateNestedForwardSeed_nonneg A constants innerDepth outer hp))
  · exact prepared_commonRadius_densityCap_nested_bound s A
      ((preparedRelativeEndpointCapExponent_density_le s).trans hA)
      prep hm M Jalloc hM p hp hnum V hV hprofile constants innerDepth outer inner

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped BigOperators TensorProduct

noncomputable def candidateSourceRecursiveNextSeedExponent (s Cprimitive : ℕ) : ℕ :=
  (exists_allocatedCandidateNestedTerminal_uniformLayers_polynomial_budget
    (s + 1) Cprimitive (candidateSourceBackendPolynomial s)).choose

theorem candidateSourceRecursiveNextSeedExponent_ge_two (s Cprimitive : ℕ) :
    2 ≤ candidateSourceRecursiveNextSeedExponent s Cprimitive :=
  (exists_allocatedCandidateNestedTerminal_uniformLayers_polynomial_budget
    (s + 1) Cprimitive (candidateSourceBackendPolynomial s)).choose_spec.1

theorem candidateSourceBackendPolynomial_le_next_seed
    (s Cprimitive m exponent innerDepth outer : ℕ) {x : ℝ}
    (hExponent : candidateSourceRecursiveNextSeedExponent s Cprimitive ≤ exponent)
    (hdepth : s + 2 ≤ innerDepth) (hx : 0 ≤ x)
    (hm : (m : ℝ) ≤ candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth outer x) :
    (candidateSourceBackendPolynomial s).eval₂ (Nat.castRingHom ℝ)
      (nativePhysicalTerminalFullBudget (s + 1) m Cprimitive exponent
        (candidateNestedForwardSeed exponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth outer x)) ≤
      candidateNestedForwardSeed exponent
        AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (outer + 1) x := by
  exact (exists_allocatedCandidateNestedTerminal_uniformLayers_polynomial_budget
    (s + 1) Cprimitive (candidateSourceBackendPolynomial s)).choose_spec.2
      m exponent AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth outer
      hExponent hdepth hx hm

noncomputable def candidateSourceRecursiveUniformExponent (cutoff Cprimitive : ℕ) : ℕ :=
  2 + ∑ s ∈ Finset.range cutoff, candidateSourceRecursiveNextSeedExponent s Cprimitive

theorem candidateSourceRecursiveUniformExponent_ge_two (cutoff Cprimitive : ℕ) :
    2 ≤ candidateSourceRecursiveUniformExponent cutoff Cprimitive := by
  unfold candidateSourceRecursiveUniformExponent
  omega

theorem candidateSourceRecursiveNextSeedExponent_le_uniform (Cprimitive : ℕ)
    {s cutoff : ℕ} (hs : s < cutoff) :
    candidateSourceRecursiveNextSeedExponent s Cprimitive ≤
      candidateSourceRecursiveUniformExponent cutoff Cprimitive := by
  have hsingle : candidateSourceRecursiveNextSeedExponent s Cprimitive ≤
      ∑ r ∈ Finset.range cutoff, candidateSourceRecursiveNextSeedExponent r Cprimitive :=
    Finset.single_le_sum
      (fun r _ => Nat.zero_le (candidateSourceRecursiveNextSeedExponent r Cprimitive))
      (Finset.mem_range.mpr hs)
  unfold candidateSourceRecursiveUniformExponent
  omega

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.InnerSourceProfile
variable {s : ℕ} (source : A.InnerSourceProfile (s + 1))

theorem recursiveParameter_le_next_seed (Cprimitive exponent innerDepth outer : ℕ)
    {x : ℝ}
    (hExponent : candidateSourceRecursiveNextSeedExponent s Cprimitive ≤ exponent)
    (hdepth : s + 2 ≤ innerDepth) (hx : 0 ≤ x)
    (hprimitive : source.Cprimitive = Cprimitive)
    (hschedule : source.scheduleExponent = exponent)
    (hseed : source.x = candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth outer x) :
    source.recursiveParameter ≤ candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (outer + 1) x := by
  have hlayers : (m : ℝ) ≤ candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth outer x := by
    rw [← hseed]
    exact source.layers_input
  apply source.recursiveParameter_polynomial.trans
  simpa only [physicalBudget, hprimitive, hschedule, hseed] using
    candidateSourceBackendPolynomial_le_next_seed s Cprimitive m exponent innerDepth outer
      hExponent hdepth hx hlayers

theorem recursiveParameter_le_next_degree_seed (Cprimitive exponent innerDepth j : ℕ)
    {x : ℝ}
    (hExponent : candidateSourceRecursiveNextSeedExponent s Cprimitive ≤ exponent)
    (hdepth : s + 2 ≤ innerDepth) (hx : 0 ≤ x)
    (hprimitive : source.Cprimitive = Cprimitive)
    (hschedule : source.scheduleExponent = exponent)
    (hseed : source.x = candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * j + 1) x) :
    source.recursiveParameter ≤ candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * (j + 1)) x := by
  simpa only [show 2 * j + 1 + 1 = 2 * (j + 1) by omega] using
    source.recursiveParameter_le_next_seed Cprimitive exponent innerDepth (2 * j + 1)
      hExponent hdepth hx hprimitive hschedule hseed

theorem recursiveParameter_le_next_degree_seed_of_uniform
    (Cprimitive exponent innerDepth cutoff j : ℕ) {x : ℝ}
    (hs : s < cutoff)
    (hExponent : candidateSourceRecursiveUniformExponent cutoff Cprimitive ≤ exponent)
    (hdepth : cutoff + 1 ≤ innerDepth) (hx : 0 ≤ x)
    (hprimitive : source.Cprimitive = Cprimitive)
    (hschedule : source.scheduleExponent = exponent)
    (hseed : source.x = candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * j + 1) x) :
    source.recursiveParameter ≤ candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * (j + 1)) x :=
  source.recursiveParameter_le_next_degree_seed Cprimitive exponent innerDepth j
    ((candidateSourceRecursiveNextSeedExponent_le_uniform Cprimitive hs).trans hExponent)
    (by omega) hx hprimitive hschedule hseed

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

noncomputable def preparedFiniteNestedFrontFitExponent
    (resourceLayers : ℕ) (Pdetect : Polynomial ℕ) (Cstep : ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteNestedFrontFamily_polynomial_next_seed
    resourceLayers Pdetect ((Polynomial.X + 2) ^ Cstep))

theorem preparedFiniteNestedFrontFitExponent_ge_two
    (resourceLayers : ℕ) (Pdetect : Polynomial ℕ) (Cstep : ℕ) :
    2 ≤ preparedFiniteNestedFrontFitExponent resourceLayers Pdetect Cstep :=
  (Classical.choose_spec (exists_preparedFiniteNestedFrontFamily_polynomial_next_seed
    resourceLayers Pdetect ((Polynomial.X + 2) ^ Cstep))).1

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSampler.FrontSourceProfile

variable {degree e : ℕ} {p : ℝ} (source : A.FrontSourceProfile degree p e)

theorem familyParameter_pow_le_next_seed
    (resourceLayers : ℕ) (Pdetect : Polynomial ℕ) (Cstep exponent Cdirect : ℕ)
    (constants : ℕ → ℕ) (outerDepth innerDepth cutoff : ℕ)
    (outer : Fin (outerDepth + 1)) (Bstruct pnum Qstride gainLog stageLog Plate : ℝ)
    (hExponent : preparedFiniteNestedFrontFitExponent resourceLayers Pdetect Cstep ≤ exponent)
    (hdepth : 1 ≤ innerDepth) (hB : 0 ≤ Bstruct)
    (hdegree : degree ≤ cutoff) (hresource : degree ≤ resourceLayers)
    (hnum : pnum ∈ Set.Icc 0 Bstruct) (hstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct)
    (hm : (m : ℝ) ≤ Bstruct)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct) (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hp : p ∈ Set.Icc 0
      (candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct))
    (hu : source.u = preparedFiniteForwardModelPrecision exponent constants 0
      (candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct) gainLog stageLog)
    (hmodel : source.pModel = preparedFiniteForwardWork exponent constants 0
      (candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct))
    (hnative : source.nativeBudget = preparedFiniteNestedSourceNative resourceLayers G
      (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X) Pdetect
      exponent Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate
      (outer, (0 : Fin (innerDepth + 1)), ⟨degree, Nat.lt_succ_of_le hdegree⟩, false)) :
    (source.familyParameter + 2) ^ Cstep ≤
      candidateNestedForwardSeed exponent constants innerDepth (outer.val + 1) Bstruct := by
  have hbound := (Classical.choose_spec
    (exists_preparedFiniteNestedFrontFamily_polynomial_next_seed resourceLayers Pdetect
      ((Polynomial.X + 2) ^ Cstep))).2
    exponent Cdirect constants outerDepth innerDepth cutoff m
    (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X) G
    outer ⟨degree, Nat.lt_succ_of_le hdegree⟩ Bstruct pnum Qstride gainLog stageLog Plate p
    hExponent hdepth hB hresource hnum hstride hg hs hm hvars hX hG hp
  dsimp only [familyParameter, familyCap]
  rw [hu, hmodel, hnative]
  simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat] using hbound

end AllocatedExternalCandidateSampler.FrontSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open AllocatedExternalCandidateSampler
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

theorem exists_degreeGlobalizationAt_of_nested_source_data
    (total resourceLayers Cprimitive : ℕ) (Pdetect : Polynomial ℕ) :
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
    (weight : (X → ℤ) → ℂ) (initial exponent outerDepth innerDepth cutoff Cdirect : ℕ)
    (x pnum Qstride gainLog stageLog Plate : ℝ)
    (hExponent : C ≤ exponent) (houter : 2 * total ≤ outerDepth)
    (hdepth : total + 1 ≤ innerDepth) (hcutoff : total ≤ cutoff)
    (hresource : total ≤ resourceLayers)
    (hx : 0 ≤ x) (hnum : pnum ∈ Set.Icc 0 x) (hstride : Qstride ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hG : (Fintype.card G : ℝ) ≤ x)
    (source : ∀ j : Fin total,
      A.DegreeSourceProfile (total - (j.val + 1) + 1)
        (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * j.val) x)
        (candidateNestedDegreeNetBound total initial)),
    (∀ j, (source j).inner.x = candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * j.val + 1) x) →
    (∀ j, (source j).inner.gainLog = candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * j.val + 1) x) →
    (∀ j, (source j).front.u = preparedFiniteForwardModelPrecision exponent degreeSourceCountConstants
      0 (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * j.val) x)
      gainLog stageLog) →
    (∀ j, (source j).front.pModel = preparedFiniteForwardWork exponent degreeSourceCountConstants
      0 (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * j.val) x)) →
    (∀ j, (source j).front.nativeBudget = preparedFiniteNestedSourceNative resourceLayers G
      (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X) Pdetect
      exponent Cdirect degreeSourceCountConstants x pnum Qstride gainLog stageLog Plate
      ((⟨2 * j.val, by omega⟩ : Fin (outerDepth + 1)), (0 : Fin (innerDepth + 1)),
        (⟨total - (j.val + 1) + 1, by omega⟩ : Fin (cutoff + 1)), false)) →
    (∀ j, (source j).inner.Cprimitive = Cprimitive) →
    (∀ j, (source j).inner.scheduleExponent = exponent) →
    Real.exp (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * total) x) ≤
      (S.value : ℝ) →
    A.DegreeGlobalizationAt (E := E) weight total initial x
      (candidateDegreeReturnBudget total
        (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * total) x)) := by
  obtain ⟨Cstep, hCstep, hglobal⟩ := exists_degreeGlobalizationAt_of_nested_source_profiles total
  let Cfront := preparedFiniteNestedFrontFitExponent resourceLayers Pdetect Cstep
  let Crec := candidateSourceRecursiveUniformExponent total Cprimitive
  let C := 2 + Cfront + Crec
  have hC : 2 ≤ C := by dsimp only [C]; omega
  refine ⟨C, hC, ?_⟩
  intro m G X _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells
    center _ A weight initial exponent outerDepth innerDepth cutoff Cdirect
    x pnum Qstride gainLog stageLog Plate hExponent houter hdepth hcutoff hresource
    hx hnum hstride hg hs hlayers hvariables hX hG source hinner hgain hu hmodel hnative
    hprimitive hschedule hscale
  have hA : 2 ≤ exponent := hC.trans hExponent
  have hfrontExp : Cfront ≤ exponent := by dsimp only [C] at hExponent; omega
  have hrecExp : Crec ≤ exponent := by dsimp only [C] at hExponent; omega
  let reduced := fun j : Fin total => (source j).mono_netExponent
    (candidateNestedForwardSeed_nonneg exponent degreeSourceCountConstants innerDepth (2 * j.val) hx)
    (candidateNestedDegreeNetExponent_le_bound total initial (Nat.le_of_lt j.isLt))
  apply hglobal (E := E) A weight initial exponent innerDepth x reduced hA hx hvariables
  · exact hinner
  · intro j
    have hd : total - (j.val + 1) + 1 ≤ total := by omega
    have hfit := (source j).front.familyParameter_pow_le_next_seed
      resourceLayers Pdetect Cstep exponent Cdirect degreeSourceCountConstants
      outerDepth innerDepth cutoff ⟨2 * j.val, by omega⟩
      x pnum Qstride gainLog stageLog Plate hfrontExp (by omega) hx
      (hd.trans hcutoff) (hd.trans hresource) hnum hstride hg hs hlayers hvariables hX hG
      ⟨candidateNestedForwardSeed_nonneg exponent degreeSourceCountConstants innerDepth (2 * j.val) hx,
        le_rfl⟩ (hu j) (hmodel j) (hnative j)
    change ((source j).front.familyParameter + 2) ^ Cstep ≤ (source j).inner.x
    rw [hinner j]
    exact hfit
  · intro j
    change (source j).inner.x ≤ (source j).inner.gainLog
    rw [hinner j, hgain j]
  · exact hscale
  · intro j
    exact (source j).inner.recursiveParameter_le_next_degree_seed_of_uniform
      Cprimitive exponent innerDepth total j.val (by omega) hrecExp hdepth hx
      (hprimitive j) (hschedule j) (hinner j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open AllocatedExternalCandidateSampler
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

theorem exists_degreeGlobalizationAt_of_complete_nested_source_data
    (total resourceLayers Cprimitive : ℕ) (Pdetect : Polynomial ℕ) :
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
    (weight : (X → ℤ) → ℂ) (initial exponent outerDepth innerDepth cutoff Cdirect Csource : ℕ)
    (x pnum Qstride gainLog stageLog Plate : ℝ)
    (_hExponent : C ≤ exponent) (_houter : 2 * total + 1 ≤ outerDepth)
    (_hdepth : total + 1 ≤ innerDepth) (_hcutoff : total ≤ cutoff)
    (_hresource : total ≤ resourceLayers)
    (_hx : 0 ≤ x) (_hnum : pnum ∈ Set.Icc 0 x) (_hstride : Qstride ∈ Set.Icc 0 x)
    (_hg : gainLog ∈ Set.Icc 0 x) (_hs : stageLog ∈ Set.Icc 0 x)
    (_hlayers : (m : ℝ) ≤ x)
    (_hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (_hX : (Fintype.card X : ℝ) ≤ x) (_hG : (Fintype.card G : ℝ) ≤ x),
    (∀ (outerFront outerInner : Fin (outerDepth + 1)) (d : ℕ),
      ∀ (hd : d ≤ cutoff), d ≤ innerDepth → ∀ pInput : ℝ,
      pInput ∈ Set.Icc 0
        (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerFront.val x) →
      pInput ≤ candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerInner.val x →
      ∃ profile : A.DegreeSourceProfile d pInput (candidateNestedDegreeNetBound total initial),
        profile.inner.x = candidateNestedForwardSeed exponent degreeSourceCountConstants
          innerDepth outerInner.val x ∧
        profile.inner.gainLog = candidateNestedForwardSeed exponent degreeSourceCountConstants
          innerDepth outerInner.val x ∧
        profile.front.u = preparedFiniteForwardModelPrecision exponent degreeSourceCountConstants 0
          (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerFront.val x)
          gainLog stageLog ∧
        profile.front.pModel = preparedFiniteForwardWork exponent degreeSourceCountConstants 0
          (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerFront.val x) ∧
        profile.front.nativeBudget = preparedFiniteNestedSourceNative resourceLayers G
          (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X) Pdetect exponent Cdirect
          degreeSourceCountConstants x pnum Qstride gainLog stageLog Plate
          (outerFront, (0 : Fin (innerDepth + 1)), ⟨d, Nat.lt_succ_of_le hd⟩, false) ∧
        profile.inner.Cprimitive = Cprimitive ∧
        profile.inner.scheduleExponent = exponent ∧ profile.inner.Csource = Csource) →
    Real.exp (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerDepth x) ≤
      (S.value : ℝ) →
    A.DegreeGlobalizationAt (E := E) weight total initial x
      (preparedFiniteForwardParameter exponent degreeSourceCountConstants innerDepth
        (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerDepth x) + 1) := by
  classical
  obtain ⟨Cdata, hCdata, hglobal⟩ :=
    exists_degreeGlobalizationAt_of_nested_source_data total resourceLayers Cprimitive Pdetect
  let C := 2 + Cdata + preparedNestedEndpointReturnExponent total
  have hC : 2 ≤ C := by dsimp only [C]; omega
  refine ⟨C, hC, ?_⟩
  intro m G X _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells
    center _ A weight initial exponent outerDepth innerDepth cutoff Cdirect Csource
    x pnum Qstride gainLog stageLog Plate hExponent houter hdepth hcutoff hresource
    hx hnum hstride hg hs hlayers hvariables hX hG hprofiles hscale
  have hA : 2 ≤ exponent := hC.trans hExponent
  have hdata : Cdata ≤ exponent := by dsimp only [C] at hExponent; omega
  have hreturn : preparedNestedEndpointReturnExponent total ≤ exponent := by
    dsimp only [C] at hExponent
    omega
  let front : Fin total → Fin (outerDepth + 1) := fun j => ⟨2 * j.val, by omega⟩
  let inner : Fin total → Fin (outerDepth + 1) := fun j => ⟨2 * j.val + 1, by omega⟩
  have hchosen := fun j : Fin total => hprofiles (front j) (inner j)
    (total - (j.val + 1) + 1) (by omega) (by omega)
    (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * j.val) x)
    ⟨candidateNestedForwardSeed_nonneg exponent degreeSourceCountConstants innerDepth (2 * j.val) hx,
      le_rfl⟩
    (candidateNestedForwardSeed_monotone exponent degreeSourceCountConstants innerDepth hA hx
      (show 2 * j.val ≤ 2 * j.val + 1 by omega))
  choose source hproperties using hchosen
  have hterminalScale : Real.exp (candidateNestedForwardSeed exponent degreeSourceCountConstants
      innerDepth (2 * total) x) ≤ (S.value : ℝ) :=
    (Real.exp_le_exp.mpr (candidateNestedForwardSeed_monotone exponent degreeSourceCountConstants
      innerDepth hA hx (by omega : 2 * total ≤ outerDepth))).trans hscale
  have rule := hglobal (E := E) A weight initial exponent outerDepth innerDepth cutoff Cdirect
    x pnum Qstride gainLog stageLog Plate hdata (by omega) hdepth hcutoff hresource
    hx hnum hstride hg hs hlayers hvariables hX hG source
    (fun j => (hproperties j).1) (fun j => (hproperties j).2.1)
    (fun j => (hproperties j).2.2.1) (fun j => (hproperties j).2.2.2.1)
    (fun j => (hproperties j).2.2.2.2.1) (fun j => (hproperties j).2.2.2.2.2.1)
    (fun j => (hproperties j).2.2.2.2.2.2.1) hterminalScale
  have hout := candidateDegreeReturnBudget_le_endpointParameter total exponent degreeSourceCountConstants
    innerDepth outerDepth innerDepth hreturn (by omega) houter hx
  exact DegreeGlobalizationAt.mono_output A rule (by linarith only [hout])

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeNativeSourceExponent (s : ℕ) : ℕ :=
  (exists_degreeGlobalizationAt_of_complete_nested_source_data s s
    (preparedCommonRadiusPrimitiveExponent s) (preparedFiniteForwardDetectorPolynomial s)).choose

noncomputable def preparedRelativePositiveExtra (s : ℕ) : ℕ :=
  4 + preparedRelativeNativeSourceExponent s + preparedRelativeEndpointCapExponent s +
    preparedNestedEndpointDimensionExponent s

noncomputable def preparedRelativePositiveSourceExponent (s : ℕ) : ℕ :=
  preparedFiniteNestedSourceExponent s s (candidateNestedDegreeNetBound s 0)
    (preparedCommonRadiusPrimitiveExponent s) 2 (preparedRelativePositiveExtra s)

theorem preparedRelativePositiveSourceExponent_bounds (s : ℕ) :
    2 ≤ preparedRelativePositiveSourceExponent s ∧
    preparedRelativeNativeSourceExponent s ≤ preparedRelativePositiveSourceExponent s ∧
    preparedRelativeEndpointCapExponent s ≤ preparedRelativePositiveSourceExponent s ∧
    preparedNestedEndpointDimensionExponent s ≤ preparedRelativePositiveSourceExponent s ∧
    preparedFiniteNestedSourceSliceExponent s s (preparedCommonRadiusPrimitiveExponent s) + 1 ≤
      preparedRelativePositiveSourceExponent s := by
  obtain ⟨hA, hExtra, _, _, hSlice, _⟩ :=
    preparedFiniteNestedSourceExponent_bounds s s (candidateNestedDegreeNetBound s 0)
      (preparedCommonRadiusPrimitiveExponent s) 2 (preparedRelativePositiveExtra s)
      (preparedRelativePositiveSourceExponent s) le_rfl
  unfold preparedRelativePositiveExtra at hExtra
  exact ⟨hA, by omega, by omega, by omega, hSlice⟩

noncomputable def preparedRelativePositiveEarlyExponent (s : ℕ) : ℕ :=
  (exists_preparedFiniteNestedCanonicalEarlyPrimitive_budget s (2 * s + 2) (s + 1) s
    (candidateNestedDegreeNetBound s 0) (preparedCommonRadiusPrimitiveExponent s) 2
    (preparedRelativePositiveExtra s) AllocatedExternalCandidateSampler.degreeSourceCountConstants).choose

theorem preparedRelativePositiveEarlyExponent_two_le (s : ℕ) :
    2 ≤ preparedRelativePositiveEarlyExponent s :=
  (exists_preparedFiniteNestedCanonicalEarlyPrimitive_budget s (2 * s + 2) (s + 1) s
    (candidateNestedDegreeNetBound s 0) (preparedCommonRadiusPrimitiveExponent s) 2
    (preparedRelativePositiveExtra s) AllocatedExternalCandidateSampler.degreeSourceCountConstants).choose_spec.1

noncomputable def preparedRelativePositiveInputExponent (s : ℕ) : ℕ :=
  (exists_preparedRelativeEndpointInputScale_power_budget s
    (preparedRelativePositiveEarlyExponent s)).choose

theorem preparedRelativePositiveInputExponent_spec (s : ℕ) :
    2 ≤ preparedRelativePositiveInputExponent s ∧ ∀ {B : ℝ}, 0 ≤ B →
      preparedRelativeEndpointUniformKnob s
        (preparedRelativeEndpointInputScale s (preparedRelativePositiveEarlyExponent s) B) ≤
          (B + 2) ^ preparedRelativePositiveInputExponent s :=
  (exists_preparedRelativeEndpointInputScale_power_budget s
    (preparedRelativePositiveEarlyExponent s)).choose_spec

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open AllocatedExternalCandidateSampler
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

variable {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X]
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

theorem degreeGlobalizationAt_of_preparedRelativePositiveSource
    (s : ℕ) (weight : (X → ℤ) → ℂ)
    (x pnum Qstride gainLog stageLog Plate : ℝ)
    (hx : 0 ≤ x) (hnum : pnum ∈ Set.Icc 0 x) (hstride : Qstride ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hG : (Fintype.card G : ℝ) ≤ x)
    (hprofiles :
      ∀ (outerFront outerInner : Fin (2 * s + 2 + 1)) (d : ℕ),
      ∀ (hd : d ≤ s), d ≤ s + 1 → ∀ pInput : ℝ,
      pInput ∈ Set.Icc 0
        (candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants (s + 1) outerFront.val x) →
      pInput ≤ candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
        degreeSourceCountConstants (s + 1) outerInner.val x →
      ∃ profile : A.DegreeSourceProfile d pInput (candidateNestedDegreeNetBound s 0),
        profile.inner.x = candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants (s + 1) outerInner.val x ∧
        profile.inner.gainLog = candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants (s + 1) outerInner.val x ∧
        profile.front.u = preparedFiniteForwardModelPrecision (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants 0
          (candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
            degreeSourceCountConstants (s + 1) outerFront.val x) gainLog stageLog ∧
        profile.front.pModel = preparedFiniteForwardWork (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants 0
          (candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
            degreeSourceCountConstants (s + 1) outerFront.val x) ∧
        profile.front.nativeBudget = preparedFiniteNestedSourceNative s G
          (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
          (preparedFiniteForwardDetectorPolynomial s) (preparedRelativePositiveSourceExponent s) 2
          degreeSourceCountConstants x pnum Qstride gainLog stageLog Plate
          (outerFront, (0 : Fin (s + 1 + 1)), ⟨d, Nat.lt_succ_of_le hd⟩, false) ∧
        profile.inner.Cprimitive = preparedCommonRadiusPrimitiveExponent s ∧
        profile.inner.scheduleExponent = preparedRelativePositiveSourceExponent s ∧
        profile.inner.Csource = preparedFiniteNestedSourceNativeExponent s s 2)
    (hscale : Real.exp (candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
        degreeSourceCountConstants (s + 1) (2 * s + 2) x) ≤ (S.value : ℝ)) :
    A.DegreeGlobalizationAt (E := E) weight s 0 x
      (preparedFiniteForwardParameter (preparedRelativePositiveSourceExponent s)
        degreeSourceCountConstants (s + 1)
        (candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants (s + 1) (2 * s + 2) x) + 1) := by
  classical
  exact (exists_degreeGlobalizationAt_of_complete_nested_source_data s s
    (preparedCommonRadiusPrimitiveExponent s) (preparedFiniteForwardDetectorPolynomial s)).choose_spec.2
    (E := E) A weight 0 (preparedRelativePositiveSourceExponent s)
    (2 * s + 2) (s + 1) s 2 (preparedFiniteNestedSourceNativeExponent s s 2)
    x pnum Qstride gainLog stageLog Plate
    (preparedRelativePositiveSourceExponent_bounds s).2.1
    (by omega) (by omega) le_rfl le_rfl hx hnum hstride hg hs
    hlayers hvariables hX hG hprofiles hscale

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open AllocatedExternalCandidateSampler
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

variable {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X]
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

theorem degreeGlobalizationAt_of_preparedRelativePositiveSource_eq
    (s : ℕ) (hms : m = s) (weight : (X → ℤ) → ℂ)
    (x pnum Qstride gainLog stageLog Plate : ℝ)
    (hx : 0 ≤ x) (hnum : pnum ∈ Set.Icc 0 x) (hstride : Qstride ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hG : (Fintype.card G : ℝ) ≤ x)
    (hprofiles :
      ∀ (outerFront outerInner : Fin (2 * s + 2 + 1)) (d : ℕ),
      ∀ (hd : d ≤ s), d ≤ s + 1 → ∀ pInput : ℝ,
      pInput ∈ Set.Icc 0
        (candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants (s + 1) outerFront.val x) →
      pInput ≤ candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
        degreeSourceCountConstants (s + 1) outerInner.val x →
      ∃ profile : A.DegreeSourceProfile d pInput (candidateNestedDegreeNetBound s 0),
        profile.inner.x = candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants (s + 1) outerInner.val x ∧
        profile.inner.gainLog = candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants (s + 1) outerInner.val x ∧
        profile.front.u = preparedFiniteForwardModelPrecision (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants 0
          (candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
            degreeSourceCountConstants (s + 1) outerFront.val x) gainLog stageLog ∧
        profile.front.pModel = preparedFiniteForwardWork (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants 0
          (candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
            degreeSourceCountConstants (s + 1) outerFront.val x) ∧
        profile.front.nativeBudget = preparedFiniteNestedSourceNative m G
          (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
          (preparedFiniteForwardDetectorPolynomial s) (preparedRelativePositiveSourceExponent s) 2
          degreeSourceCountConstants x pnum Qstride gainLog stageLog Plate
          (outerFront, (0 : Fin (s + 1 + 1)), ⟨d, Nat.lt_succ_of_le hd⟩, false) ∧
        profile.inner.Cprimitive = preparedCommonRadiusPrimitiveExponent s ∧
        profile.inner.scheduleExponent = preparedRelativePositiveSourceExponent s ∧
        profile.inner.Csource = preparedFiniteNestedSourceNativeExponent m s 2)
    (hscale : Real.exp (candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
        degreeSourceCountConstants (s + 1) (2 * s + 2) x) ≤ (S.value : ℝ)) :
    A.DegreeGlobalizationAt (E := E) weight s 0 x
      (preparedFiniteForwardParameter (preparedRelativePositiveSourceExponent s)
        degreeSourceCountConstants (s + 1)
        (candidateNestedForwardSeed (preparedRelativePositiveSourceExponent s)
          degreeSourceCountConstants (s + 1) (2 * s + 2) x) + 1) := by
  classical
  have hthreshold : (exists_degreeGlobalizationAt_of_complete_nested_source_data s m
      (preparedCommonRadiusPrimitiveExponent s) (preparedFiniteForwardDetectorPolynomial s)).choose ≤
      preparedRelativePositiveSourceExponent s := by
    simpa only [hms, preparedRelativeNativeSourceExponent] using
      (preparedRelativePositiveSourceExponent_bounds s).2.1
  exact (exists_degreeGlobalizationAt_of_complete_nested_source_data s m
    (preparedCommonRadiusPrimitiveExponent s) (preparedFiniteForwardDetectorPolynomial s)).choose_spec.2
    (E := E) A weight 0 (preparedRelativePositiveSourceExponent s)
    (2 * s + 2) (s + 1) s 2 (preparedFiniteNestedSourceNativeExponent m s 2)
    x pnum Qstride gainLog stageLog Plate hthreshold
    (by omega) (by omega) le_rfl (by omega) hx hnum hstride hg hs
    hlayers hvariables hX hG hprofiles hscale

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open AllocatedExternalCandidateSampler
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

variable {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X]
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

theorem degreeGlobalizationAt_of_preparedRelativePositiveSource_canonical
    (s : ℕ) (hms : m = s)
    (sourceExponent : ℕ)
    (hExponent : sourceExponent = preparedRelativePositiveSourceExponent s)
    (weight : (X → ℤ) → ℂ)
    (x pnum Qstride gainLog stageLog Plate : ℝ)
    (hx : 0 ≤ x) (hnum : pnum ∈ Set.Icc 0 x) (hstride : Qstride ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hG : (Fintype.card G : ℝ) ≤ x)
    (hprofiles :
      ∀ (outerFront outerInner : Fin (2 * s + 2 + 1)) (d : ℕ),
      ∀ (hd : d ≤ s), d ≤ s + 1 → ∀ pInput : ℝ,
      pInput ∈ Set.Icc 0
        (candidateNestedForwardSeed sourceExponent
          degreeSourceCountConstants (s + 1) outerFront.val x) →
      pInput ≤ candidateNestedForwardSeed sourceExponent
        degreeSourceCountConstants (s + 1) outerInner.val x →
      ∃ profile : A.DegreeSourceProfile d pInput (candidateNestedDegreeNetBound s 0),
        profile.inner.x = candidateNestedForwardSeed sourceExponent
          degreeSourceCountConstants (s + 1) outerInner.val x ∧
        profile.inner.gainLog = candidateNestedForwardSeed sourceExponent
          degreeSourceCountConstants (s + 1) outerInner.val x ∧
        profile.front.u = preparedFiniteForwardModelPrecision sourceExponent
          degreeSourceCountConstants 0
          (candidateNestedForwardSeed sourceExponent
            degreeSourceCountConstants (s + 1) outerFront.val x) gainLog stageLog ∧
        profile.front.pModel = preparedFiniteForwardWork sourceExponent
          degreeSourceCountConstants 0
          (candidateNestedForwardSeed sourceExponent
            degreeSourceCountConstants (s + 1) outerFront.val x) ∧
        profile.front.nativeBudget = preparedFiniteNestedSourceNative m G
          (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
          (preparedFiniteForwardDetectorPolynomial s) sourceExponent 2
          degreeSourceCountConstants x pnum Qstride gainLog stageLog Plate
          (outerFront, (0 : Fin (s + 1 + 1)), ⟨d, Nat.lt_succ_of_le hd⟩, false) ∧
        profile.inner.Cprimitive = preparedCommonRadiusPrimitiveExponent s ∧
        profile.inner.scheduleExponent = sourceExponent ∧
        profile.inner.Csource = preparedFiniteNestedSourceNativeExponent m s 2)
    (hscale : Real.exp (candidateNestedForwardSeed sourceExponent
        degreeSourceCountConstants (s + 1) (2 * s + 2) x) ≤ (S.value : ℝ)) :
    A.DegreeGlobalizationAt (E := E) weight s 0 x
      (preparedFiniteForwardParameter sourceExponent
        degreeSourceCountConstants (s + 1)
        (candidateNestedForwardSeed sourceExponent
          degreeSourceCountConstants (s + 1) (2 * s + 2) x) + 1) := by
  classical
  have hthreshold : (exists_degreeGlobalizationAt_of_complete_nested_source_data s m
      (preparedCommonRadiusPrimitiveExponent s) (preparedFiniteForwardDetectorPolynomial s)).choose ≤
      sourceExponent := by
    rw [hExponent]
    simpa only [hms, preparedRelativeNativeSourceExponent] using
      (preparedRelativePositiveSourceExponent_bounds s).2.1
  have rawRule := (exists_degreeGlobalizationAt_of_complete_nested_source_data s m
    (preparedCommonRadiusPrimitiveExponent s) (preparedFiniteForwardDetectorPolynomial s)).choose_spec.2
    (E := E) A weight 0 sourceExponent
    (2 * s + 2) (s + 1) s 2 (preparedFiniteNestedSourceNativeExponent m s 2)
    x pnum Qstride gainLog stageLog Plate hthreshold
    (by omega) (by omega) le_rfl (by omega) hx hnum hstride hg hs
    hlayers hvariables hX hG hprofiles hscale
  exact rawRule

end Erdos3.VectorPolynomial

end

end OAI
