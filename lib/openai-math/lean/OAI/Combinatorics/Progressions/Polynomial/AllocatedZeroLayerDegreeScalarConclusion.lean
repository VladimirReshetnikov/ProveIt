import OAI.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateExponentialFreezingBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateStepZero
import OAI.Combinatorics.Progressions.Estimates.AllocatedZeroLayerScalarPassage
import OAI.Combinatorics.Progressions.Estimates.ConstantObservableMemberNets
import OAI.Combinatorics.Progressions.Nilpotent.ZeroLayerPhysicalNiltestBudget
import OAI.Combinatorics.Progressions.Probability.PreparedReadyNormalizationMassBudget

namespace OAI

section

namespace Erdos3

open scoped NNReal TensorProduct Classical

namespace PolynomialPatch

variable {V : Type*} {s d : ℕ} (P : PolynomialPatch V s d)
  [Fintype (PolynomialShearIndex P.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]

structure ExternalObservableRegularity (M : ℝ≥0) (p : ℝ) : Prop where
  geometry : (polynomialShearNilmanifold P.weight s P.weight_le).GeometryComplexityLE p
  lip_bound : (P.shearObservableLipBound M : ℝ) ≤ Real.exp p
  lipschitz :
    letI : MetricSpace
      ((polynomialShearFiltration P.weight s P.weight_le).realification.Group ⧸
        polynomialShearRealLattice s P.weight_le) :=
      (polynomialShearNilmanifold P.weight s P.weight_le).metricSpace
    LipschitzWith (P.shearObservableLipBound M) (fun y => (P.shearObservable y : ℂ))
  positive : ∀ y, (P.shearObservable y : ℂ).im = 0 ∧
    0 ≤ (P.shearObservable y : ℂ).re ∧ (P.shearObservable y : ℂ).re ≤ 1

theorem externalObservableRegularity_of_niltest_complexity
    (M : ℝ≥0) (hP : ∀ i, realPolynomialMass (P.form.center i) ≤ M)
    {p : ℝ} (h : (P.shearNiltest M hP).ComplexityLE p) :
    P.ExternalObservableRegularity M p := by
  refine ⟨h.1, ?_, (P.shearNiltest M hP).lipschitz, ?_⟩
  · have hbound := RationalFilteredNilmanifold.Niltest.observable_budget h
    change 2 + 1 + (P.shearObservableLipBound M : ℝ) ≤ Real.exp p at hbound
    linarith
  · exact P.shearNiltest_unitInterval M hP

theorem ExternalObservableRegularity.mono {M : ℝ≥0} {p q : ℝ}
    (h : P.ExternalObservableRegularity M p) (hpq : p ≤ q) :
    P.ExternalObservableRegularity M q where
  geometry := RationalFilteredNilmanifold.GeometryComplexityLE.mono _ h.geometry hpq
  lip_bound := h.lip_bound.trans (Real.exp_le_exp.mpr hpq)
  lipschitz := h.lipschitz
  positive := h.positive

omit [Fintype (PolynomialShearIndex P.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)] in

theorem shearObservable_memberNets {X : Type*} [Fintype X]
    (N : X → ℕ) (hN : ∀ x, 0 < N x) {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖(fun (_ : X → ℤ) y => (P.shearObservable y : ℂ)) x y -
            (fun (_ : X → ℤ) y => (P.shearObservable y : ℂ)) (oc i).val y‖ ≤ η :=
  constantObservable_integerBox_memberNets N hN
    (fun y => (P.shearObservable y : ℂ)) hp e

end PolynomialPatch

theorem exists_polynomialPatch_external_observable_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {V : Type*} {d : ℕ} (P : PolynomialPatch V s d)
      [Fintype (PolynomialShearIndex P.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      (p : ℝ) (hp : 0 ≤ p), (d : ℝ) ≤ p →
      (∀ i, realPolynomialMass (P.form.center i) ≤ p) →
      (P.kernel.lip : ℝ) ≤ Real.exp p →
      P.ExternalObservableRegularity ⟨p, hp⟩ ((p + 2) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_mass_bounded_patch_niltest_budget s
  refine ⟨C, hC, ?_⟩
  intro V d P _ _ _ _ _ p hp hd hcenters hLip
  let M : ℝ≥0 := ⟨p, hp⟩
  have hM : ∀ i, realPolynomialMass (P.form.center i) ≤ M := hcenters
  exact P.externalObservableRegularity_of_niltest_complexity M hM
    (hbudget P M hM p hp hd le_rfl hLip)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

def DegreeGlobalizationAt (weight : (X → ℤ) → ℂ)
    (degree netExponent : ℕ) (p outputCost : ℝ) : Prop :=
  ∀ {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d f : ℕ} (D : RationalFilteredNilmanifold L degree d)
    (Fmark : RationalFilteredNilmanifold M degree f) (φ : L →ₗ⁅ℚ⁆ M),
    (∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j) →
    (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
    D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
    (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
    ∀ (marked : Fmark.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
      (observable : (X → ℤ) → D.Space → ℂ) (ℓ : ℝ≥0),
    (ℓ : ℝ) ≤ Real.exp p →
    (∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x)) →
    (∀ x y, (observable x y).im = 0 ∧ 0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1) →
    (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + netExponent) ^ netExponent) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η) →
    (∀ x, ‖weight x‖ ≤ Real.exp p) →
    ∀ P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight p (Real.exp (-p)) (Real.exp (-p)),
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost)))

theorem degreeGlobalizationAt_zero (weight : (X → ℤ) → ℂ)
    (netExponent : ℕ) (p : ℝ) : A.DegreeGlobalizationAt (E := E) weight 0 netExponent p p := by
  intro L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hF hmap
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  exact P.conclusion_stepZero A D Fmark.filtration φ marked observable weight

theorem DegreeGlobalizationAt.mono_output
    {weight : (X → ℤ) → ℂ} {degree netExponent : ℕ} {p outputCost largerCost : ℝ}
    (rule : A.DegreeGlobalizationAt (E := E) weight degree netExponent p outputCost)
    (hcost : outputCost ≤ largerCost) :
    A.DegreeGlobalizationAt (E := E) weight degree netExponent p largerCost := by
  intro L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hF hmap
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  obtain ⟨out⟩ := rule D Fmark φ hφ hsurj hD hF hmap marked observable ℓ
    hℓ hLip hpositive hnet hweight P
  exact ⟨out.mono hcost (Real.exp_le_exp.mpr (neg_le_neg hcost))
    (Real.exp_le_exp.mpr (neg_le_neg hcost))⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

theorem DegreeGlobalizationAt.mono_input
    {weight : (X → ℤ) → ℂ} {degree netExponent : ℕ} {p q outputCost : ℝ}
    (rule : A.DegreeGlobalizationAt (E := E) weight degree netExponent q outputCost)
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    A.DegreeGlobalizationAt (E := E) weight degree netExponent p outputCost := by
  intro L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hF hmap
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  have hexp : Real.exp p ≤ Real.exp q := Real.exp_le_exp.mpr hpq
  have hneg : Real.exp (-q) ≤ Real.exp (-p) := Real.exp_le_exp.mpr (neg_le_neg hpq)
  let ref := P.budgetRefinement hpq hneg hneg
  have hnet' : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((q + Real.log (1 / η) + netExponent) ^ netExponent) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η := by
    intro η hη hηone
    obtain ⟨n, hn, oc, hoc⟩ := hnet η hη hηone
    have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((one_le_div hη).mpr hηone)
    refine ⟨n, hn.trans (Real.exp_le_exp.mpr ?_), oc, hoc⟩
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hpq]) netExponent
  obtain ⟨out⟩ := rule D Fmark φ hφ hsurj
    (RationalFilteredNilmanifold.GeometryComplexityLE.mono D hD hpq)
    (RationalFilteredNilmanifold.GeometryComplexityLE.mono Fmark hF hpq)
    (fun i j => (hmap i j).trans hpq) marked observable ℓ (hℓ.trans hexp)
    hLip hpositive hnet' (fun x => (hweight x).trans hexp) ref.problem
  exact ⟨ref.conclusion out⟩

theorem DegreeGlobalizationAt.mono_netExponent
    {weight : (X → ℤ) → ℂ} {degree netExponent largerExponent : ℕ} {p outputCost : ℝ}
    (rule : A.DegreeGlobalizationAt (E := E) weight degree largerExponent p outputCost)
    (hp : 1 ≤ p) (hnetExponent : netExponent ≤ largerExponent) :
    A.DegreeGlobalizationAt (E := E) weight degree netExponent p outputCost := by
  intro L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hF hmap
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  apply rule D Fmark φ hφ hsurj hD hF hmap marked observable ℓ hℓ hLip hpositive
    _ hweight P
  intro η hη hηone
  obtain ⟨n, hn, oc, hoc⟩ := hnet η hη hηone
  have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((one_le_div hη).mpr hηone)
  refine ⟨n, hn.trans (Real.exp_le_exp.mpr ?_), oc, hoc⟩
  apply (pow_le_pow_left₀ (by positivity)
    (add_le_add le_rfl (Nat.cast_le.mpr hnetExponent)) netExponent).trans
  exact pow_le_pow_right₀ (by have h := Nat.cast_nonneg (α := ℝ) largerExponent; linarith)
    hnetExponent

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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

namespace AllocatedExternalCandidateProblem

variable {V : Type*} {s d : ℕ} (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    {f : (X → ℤ) → ℝ} {lam cost mass score : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost mass score)

theorem conclusion_of_shearDegreeGlobalization
    {M : ℝ≥0} {p outputCost : ℝ} {netExponent : ℕ}
    (hregularity : patch.ExternalObservableRegularity M p)
    (hp : 0 ≤ p) (hcost : cost ≤ p)
    (hmass : Real.exp (-p) ≤ mass) (hscore : Real.exp (-p) ≤ score)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (rule : A.DegreeGlobalizationAt (E := E)
      (fun x => ((f x - lam : ℝ) : ℂ)) s netExponent p outputCost) :
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  let refinement := P.budgetRefinement hcost hmass hscore
  have hweight (x : X → ℤ) : ‖((f x - lam : ℝ) : ℂ)‖ ≤ Real.exp p := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [(hf x).1, hlam.2],
      by linarith [(hf x).2, hlam.1]⟩).trans (Real.one_le_exp hp)
  obtain ⟨out⟩ := rule
    (polynomialShearNilmanifold patch.weight s patch.weight_le)
    (RationalTorus.trivialNilmanifold s) 0
    (fun _ _ _ => Submodule.zero_mem _)
    (fun j y _ => ⟨0, Submodule.zero_mem _, Subsingleton.elim _ _⟩)
    hregularity.geometry (RationalTorus.trivialNilmanifold_geometry s hp)
    (fun _ j => Fin.elim0 j) 1 (fun _ y => (patch.shearObservable y : ℂ))
    (patch.shearObservableLipBound M) hregularity.lip_bound
    (fun _ => hregularity.lipschitz) (fun _ => hregularity.positive)
    (patch.shearObservable_memberNets N A.size_pos hp netExponent)
    hweight refinement.problem
  exact ⟨refinement.conclusion out⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

noncomputable def allocatedNormalizedShearObservableExponent (s : ℕ) : ℕ :=
  (exists_polynomialPatch_external_observable_budget.{0} s).choose

theorem allocatedNormalizedShearObservableExponent_ge_two (s : ℕ) :
    2 ≤ allocatedNormalizedShearObservableExponent s :=
  (exists_polynomialPatch_external_observable_budget.{0} s).choose_spec.1

noncomputable def allocatedNormalizedCandidateBudget (s dimension : ℕ) (childCost : ℝ) : ℝ :=
  (childCost + (dimension : ℝ) + 2 + 2) ^
    (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose

theorem childCost_le_allocatedNormalizedCandidateBudget (s dimension : ℕ)
    {childCost : ℝ} (hchild : 0 ≤ childCost) :
    childCost ≤ allocatedNormalizedCandidateBudget s dimension childCost := by
  have hpower := (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose_spec.1
  have hbase : 1 ≤ childCost + (dimension : ℝ) + 2 + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) dimension]
  have hpow := le_self_pow₀ hbase (by omega :
    (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose ≠ 0)
  exact (by linarith [Nat.cast_nonneg (α := ℝ) dimension] :
    childCost ≤ childCost + (dimension : ℝ) + 2 + 2).trans hpow

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

namespace AllocatedExternalCandidateProblem

variable {V : Type} {s d : ℕ} (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    {f : (X → ℤ) → ℝ} {target cost childCost normBudget : ℝ}
    {rankBound : ℕ} {productive : Finset A.Path}
    (P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - target : ℝ) : ℂ)) cost
      ((A.law.mass productive /
        ((min rankBound ⌊childCost⌋₊ + 1) * (s + 1) ^ min rankBound ⌊childCost⌋₊ : ℕ)) *
        Real.exp (-normBudget)) (Real.exp (-normBudget)))

theorem exists_normalizedShearDegreeConclusion
    {gainLog gain pGlobal outputCost : ℝ} {netExponent : ℕ}
    (hchild : 0 ≤ childCost) (hd : d ≤ min rankBound ⌊childCost⌋₊)
    (hchildBudget : childCost ≤ normBudget)
    (hcenters : ∀ i, realPolynomialMass (patch.form.center i) ≤ normBudget)
    (hLip : (patch.kernel.lip : ℝ) ≤ Real.exp normBudget)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hReady : gain / 16 < A.law.mass productive)
    (hregularityBudget : (normBudget + 2) ^ allocatedNormalizedShearObservableExponent s ≤ pGlobal)
    (hpGlobal : 0 ≤ pGlobal) (hcost : cost ≤ pGlobal)
    (hscoreBudget : normBudget ≤ pGlobal)
    (hmassBudget : gainLog + 16 + ((s : ℝ) + 1) * childCost + normBudget ≤ pGlobal)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (rule : A.DegreeGlobalizationAt (E := E)
      (fun x => ((f x - target : ℝ) : ℂ)) s netExponent pGlobal outputCost) :
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2
    (polynomialShearNilmanifold patch.weight s patch.weight_le).basis
  have hnorm : 0 ≤ normBudget := hchild.trans hchildBudget
  have hdBudget : (d : ℝ) ≤ normBudget :=
    (Nat.cast_le.mpr (hd.trans (min_le_right _ _))).trans
      ((Nat.floor_le hchild).trans hchildBudget)
  have regularity := PolynomialPatch.ExternalObservableRegularity.mono patch
    ((exists_polynomialPatch_external_observable_budget s).choose_spec.2
      patch normBudget hnorm hdBudget hcenters hLip) hregularityBudget
  have hmass := (Real.exp_le_exp.mpr (neg_le_neg hmassBudget)).trans
    (preparedReady_capped_normalized_mass_lower rankBound s hchild hgain hReady
      (normBudget := normBudget))
  exact P.conclusion_of_shearDegreeGlobalization patch regularity hpGlobal hcost hmass
    (Real.exp_le_exp.mpr (neg_le_neg hscoreBudget)) hf htarget rule

noncomputable def normalizedShearDegreeConclusion
    {gainLog gain pGlobal outputCost : ℝ} {netExponent : ℕ}
    (hchild : 0 ≤ childCost) (hd : d ≤ min rankBound ⌊childCost⌋₊)
    (hchildBudget : childCost ≤ normBudget)
    (hcenters : ∀ i, realPolynomialMass (patch.form.center i) ≤ normBudget)
    (hLip : (patch.kernel.lip : ℝ) ≤ Real.exp normBudget)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hReady : gain / 16 < A.law.mass productive)
    (hregularityBudget : (normBudget + 2) ^ allocatedNormalizedShearObservableExponent s ≤ pGlobal)
    (hpGlobal : 0 ≤ pGlobal) (hcost : cost ≤ pGlobal)
    (hscoreBudget : normBudget ≤ pGlobal)
    (hmassBudget : gainLog + 16 + ((s : ℝ) + 1) * childCost + normBudget ≤ pGlobal)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (rule : A.DegreeGlobalizationAt (E := E)
      (fun x => ((f x - target : ℝ) : ℂ)) s netExponent pGlobal outputCost) :
    P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost)) :=
  Classical.choice (P.exists_normalizedShearDegreeConclusion patch
    hchild hd hchildBudget hcenters hLip hgain hReady hregularityBudget
    hpGlobal hcost hscoreBudget hmassBudget hf htarget rule)

end AllocatedExternalCandidateProblem

theorem AllocatedNormalizedCandidateConclusion.degreeGlobalization
    {s : ℕ} {keep : LayerSamplerVariables G I n B → Prop}
    {centerLift : ∀ j, U j} {productive : Finset A.Path}
    {childCost cost : ℝ} {rankBound : ℕ} {f : (X → ℤ) → ℝ} {target : ℝ}
    (hinit : AllocatedNormalizedCandidateConclusion (E := E) (A := A)
      s keep centerLift productive childCost cost rankBound f target)
    {gainLog gain pGlobal outputCost : ℝ} {netExponent : ℕ}
    (hchild : 0 ≤ childCost)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hReady : gain / 16 < A.law.mass productive)
    (hregularityBudget :
      (allocatedNormalizedCandidateBudget s (Fintype.card (LayerSamplerVariables G I n B))
        childCost + 2) ^ allocatedNormalizedShearObservableExponent s ≤ pGlobal)
    (hpGlobal : 0 ≤ pGlobal) (hcost : cost ≤ pGlobal)
    (hscoreBudget : allocatedNormalizedCandidateBudget s
      (Fintype.card (LayerSamplerVariables G I n B)) childCost ≤ pGlobal)
    (hmassBudget : gainLog + 16 + ((s : ℝ) + 1) * childCost +
      allocatedNormalizedCandidateBudget s (Fintype.card (LayerSamplerVariables G I n B))
        childCost ≤ pGlobal)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (rule : A.DegreeGlobalizationAt (E := E)
      (fun x => ((f x - target : ℝ) : ℂ)) s netExponent pGlobal outputCost) :
    let D := min rankBound ⌊childCost⌋₊
    let normalizedBudget := allocatedNormalizedCandidateBudget s
      (Fintype.card (LayerSamplerVariables G I n B)) childCost
    let retainedMass := (A.law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
      Real.exp (-normalizedBudget)
    ∃ (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
      d ≤ D ∧ d ≤ rankBound ∧
      (patch.kernel.lip : ℝ) ≤ Real.exp normalizedBudget ∧
      (∀ i, realPolynomialMass (patch.form.center i) ≤ normalizedBudget) ∧
      let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
      ∃ P : AllocatedExternalCandidateProblem (E := E) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - target : ℝ) : ℂ)) cost retainedMass (Real.exp (-normalizedBudget)),
        P.productive ⊆ productive ∧ P.centerLift = centerLift ∧
          (∀ z, (P.chart z).keep = keep) ∧
          Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  obtain ⟨d, patch, hd, hrank, hLip, hcenters, hP⟩ := hinit
  let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
  obtain ⟨P, hsubset, hcenter, hkeep⟩ := hP
  refine ⟨d, patch, hd, hrank, hLip, hcenters, P, hsubset, hcenter, hkeep, ?_⟩
  exact P.exists_normalizedShearDegreeConclusion patch hchild hd
    (childCost_le_allocatedNormalizedCandidateBudget s _ hchild)
    hcenters hLip hgain hReady hregularityBudget hpGlobal hcost hscoreBudget
    hmassBudget hf htarget rule

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

theorem exists_allocatedZeroLayer_degree_scalar_conclusion (s n₀ ratio : ℕ)
    (hn₀ : 2 ≤ n₀) (hratio : 2 ≤ ratio)
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscountHalf : discount ≤ 1 / 2) :
    ∃ observableC nativeC scalarE scalarC scalarF : ℕ,
      2 ≤ observableC ∧ 2 ≤ nativeC ∧
      2 ≤ scalarE ∧ 2 ≤ scalarC ∧ 2 ≤ scalarF ∧
    ∀ {G X : Type} [Fintype G] [Fintype X]
      {I Ecol J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
      {U : ∀ j, Submodule ℝ (J j → ℝ)}
      {basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
      {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
      {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
      {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
      {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
      {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
      {hm : ∀ j e, coefficients (poly j) e ∈ U j}
      {σsurplus : ℝ}
      {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
      [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
      (A : AllocatedExternalCandidateSampler B U basis S hb o hR hσ N poly hm
        (unconditionedSpatialTrimFraction (Fintype.card X) σsurplus) 1
        (fun _ : X => 1) {0} center)
      (_hK : Fintype.card (LayerSamplerVariables G I n B) = n₀)
      {V : Type} {d : ℕ} (patch : PolynomialPatch V s d)
      [Fintype (PolynomialShearIndex patch.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      {f : (X → ℤ) → ℝ} {lam cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := Ecol) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold)
      (_hkeep : ∀ z : P.productive, (P.chart z).keep = (fun _ => True))
      (pPatch pGlobal outputCost b : ℝ) (netExponent : ℕ),
      0 ≤ pPatch → (d : ℝ) ≤ pPatch →
      (∀ i, realPolynomialMass (patch.form.center i) ≤ pPatch) →
      (patch.kernel.lip : ℝ) ≤ Real.exp pPatch →
      (pPatch + 2) ^ observableC ≤ pGlobal →
      (pPatch + 2) ^ nativeC ≤ b →
      0 ≤ pGlobal → cost ≤ pGlobal →
      Real.exp (-pGlobal) ≤ massThreshold → Real.exp (-pGlobal) ≤ scoreThreshold →
      2 ≤ b → (Fintype.card X : ℝ) ≤ b →
      0 < σsurplus → σsurplus ≤ 1 → σsurplus⁻¹ ≤ Real.exp b →
      lam ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ lam →
      0 ≤ outputCost → outputCost ≤ b →
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      A.DegreeGlobalizationAt (E := Ecol) (fun x => ((f x - lam : ℝ) : ℂ))
        s netExponent pGlobal outputCost →
      let p := (b + 2) ^ scalarE
      let target := 8 * ((ratio * n₀ : ℕ) + 1 : ℝ) * (p + 1)
      let budget := (target + 2) ^ scalarC
      (∀ i, Real.exp budget ≤ (A.sides i : ℝ)) →
      (∀ i, (A.sides i : ℝ) ≤ (ratio : ℝ) * Real.exp budget) →
      (∀ i, Real.exp ((p + scalarF) ^ scalarF) ≤ (N i : ℝ)) →
      RelativePatchSliceConclusion s N f ((1 - discount) * lam) d
        ((p + scalarF) ^ scalarF) := by
  obtain ⟨observableC, hObservableC, hregularity⟩ :=
    exists_polynomialPatch_external_observable_budget s
  obtain ⟨nativeC, hNativeC, hnative⟩ :=
    exists_zeroLayer_physical_niltest_of_mass_bounds s
  obtain ⟨scalarE, scalarC, scalarF, hE, hC, hF, hpassage⟩ :=
    exists_allocatedZeroLayer_scalar_passage s n₀ ratio hn₀ hratio hdiscount hdiscountHalf
  refine ⟨observableC, nativeC, scalarE, scalarC, scalarF,
    hObservableC, hNativeC, hE, hC, hF, ?_⟩
  intro G X _ _ I Ecol J _ _ n B _ U basis R σ S hb o hR hσ N poly hm
    σsurplus center _ A hK V d patch _ _ _ _ _ f lam cost massThreshold scoreThreshold
    P hkeep pPatch pGlobal outputCost b netExponent
    hpPatch hd hcenter hLip hObservableBudget hNativeBudget
    hpGlobal hcost hmass hscore hb2 hX hsurplus hsurplus1 hsurplusInv
    hlam hlamLower houtputCost houtputCostB hf rule p target budget hlo hhi hN
  have regularity := PolynomialPatch.ExternalObservableRegularity.mono patch
    (hregularity patch pPatch hpPatch hd hcenter hLip) hObservableBudget
  obtain ⟨out⟩ := P.conclusion_of_shearDegreeGlobalization patch regularity
    hpGlobal hcost hmass hscore hf hlam rule
  obtain ⟨hphysicalComplexity, g, _hunit, hg, heval⟩ :=
    hnative patch pPatch hpPatch hd hcenter hLip out.ambient
  have hpatch : relativePatchComplexity patch ≤ b :=
    hphysicalComplexity.trans hNativeBudget
  have houtputThreshold : Real.exp (-b) ≤ Real.exp (-outputCost) :=
    Real.exp_le_exp.mpr (neg_le_neg houtputCostB)
  exact hpassage A hK patch P hkeep out b hb2 hX hsurplus hsurplus1 hsurplusInv
    hlam hlamLower houtputCost houtputCostB houtputThreshold houtputThreshold hpatch
    g (hg.mono hNativeBudget) heval hlo hhi hN (fun x _ => hf x)

end Erdos3.VectorPolynomial

end

end OAI
