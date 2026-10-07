/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedFrontNativeBudget
import OAI.Combinatorics.Progressions.Fourier.AllocatedExternalCandidateSpatialNativeFrequencyTransport

namespace OAI

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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.PositiveKernelPreparation

variable {cost massThreshold scoreThreshold p : ℝ} {e : ℕ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    (prep : P.PositiveKernelPreparation p e)

noncomputable abbrev nativeQuotientIdeal : LieIdeal ℚ L :=
  D.filtration.pivotAnnihilatorIdeal φ
    (fun k => prep.early.eta (kernelProjectionSelectedPivot prep.selected.code k))
    (Finset.univ : Finset (KernelProjectionPresentPivot prep.selected.code)).toList

theorem nativeQuotientIdeal_terminal :
    D.filtration.layer (s + 1) ≤ prep.nativeQuotientIdeal.toSubmodule := by
  rw [D.filtration.terminal]
  exact bot_le

theorem exists_native_descended_quotient
    {nMarkedBasis : ℕ} (markBasis : Basis (Fin nMarkedBasis) ℚ M)
    (pBudget : ℝ) (hs : 1 ≤ s) (hpBudget : 0 ≤ pBudget)
    (hD : D.GeometryComplexityLE pBudget) (hmarkDim : (nMarkedBasis : ℝ) ≤ pBudget)
    (hmark : ∀ i j, rationalLogHeight (markBasis.repr (φ (D.basis j)) i) ≤ pBudget)
    (hqBudget : positiveKernelPreparationParameter p ≤ pBudget) :
    (∀ x ∈ prep.nativeQuotientIdeal, φ x = 0) ∧
    ∃ dQ : ℕ, dQ ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ prep.nativeQuotientIdeal) s dQ,
      Q.filtration = D.filtration.quotientLie prep.nativeQuotientIdeal prep.nativeQuotientIdeal_terminal ∧
      Q.lattice = D.lattice.map (D.filtration.quotientStepHom prep.nativeQuotientIdeal prep.nativeQuotientIdeal_terminal) ∧
      Q.GeometryComplexityLE
        ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s) ∧
      (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap prep.nativeQuotientIdeal (D.basis j)) i) ≤
        (pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ prep.nativeQuotientIdeal))
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ prep.nativeQuotientIdeal)) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 Q.basis
       ∃ descended : (X → ℤ) → Q.Niltest (fullTaggedVariableWeight (X := X) J),
         (∀ x, (descended x).UnitIntervalValued) ∧
         (∀ x y, ‖(descended x).observable y‖ ≤ 1) ∧
         (∀ x, (descended x).ComplexityLE
           ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)) ∧
         (∀ x, letI := Q.metricSpace;
           LipschitzWith
             ⟨Real.exp ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s),
               Real.exp_nonneg _⟩ (descended x).observable) ∧
         (∀ x (g : D.RealGroup), (descended x).observable (QuotientGroup.mk
           (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
             (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap prep.nativeQuotientIdeal) g)) =
             (prep.selected.tests x).observable (QuotientGroup.mk g)) ∧
         (∀ x y η, (∀ z, ‖observable x z - observable y z‖ ≤ η) →
           ∀ z, ‖(descended x).observable z - (descended y).observable z‖ ≤ η) ∧
         ∀ entropy : ℝ → ℝ,
           (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
             ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
               ∀ x ∈ integerBox N, ∃ i, ∀ y,
                 ‖observable x y - observable (rep i).val y‖ ≤ η) →
           ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
             ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
               ∀ x ∈ integerBox N, ∃ i, ∀ y,
                 ‖(descended x).observable y - (descended (rep i).val).observable y‖ ≤ η) := by
  classical
  let ideal := prep.nativeQuotientIdeal
  let hI := prep.nativeQuotientIdeal_terminal
  have hcode : (finrank ℚ ↥(D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) : ℝ) ≤ pBudget := by
    let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
    have hdim := Submodule.finrank_le (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap)
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at hdim
    exact (Nat.cast_le.mpr hdim).trans hD.1
  have hkernel : ideal.toSubmodule = frequencyCodeKernel
      (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) prep.early.eta prep.selected.code :=
    D.filtration.pivotAnnihilatorIdeal_presentPivots_toSubmodule φ prep.early.eta prep.selected.code
  have hker (x : L) (hx : x ∈ ideal) : φ x = 0 := by
    have hx' : x ∈ frequencyCodeKernel
        (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) prep.early.eta prep.selected.code := by
      rw [← hkernel]
      exact hx
    exact ((mem_frequencyCodeKernel _ _ _ x).mp hx').1.2
  obtain ⟨dQ, hdQ, Q, hQF, hQL, hQ, hmap⟩ :=
    (Classical.choose_spec
      (RationalFilteredNilmanifold.exists_nativePresentPivotQuotient_budget.{0, 0, 0})).2
      D markBasis φ prep.early.eta prep.selected.code pBudget hs hpBudget hD hmarkDim hcode
      hmark (fun i j => (prep.early.eta_height i j).trans hqBudget)
  let pDesc := pBudget + (pBudget + 2) ^
    RationalFilteredNilmanifold.nativePresentPivotQuotientExponent + 1
  have hb := RationalFilteredNilmanifold.positiveKernelNativeDescentBudget_bounds s hpBudget
  refine ⟨hker, dQ, hdQ, Q, hQF, hQL, hQ.mono Q (hb.2.2.1.trans hb.2.2.2.1),
    fun i j => (hmap i j).trans (hb.2.2.1.trans hb.2.2.2.1), ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ ideal))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ ideal)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (L ⧸ ideal)) := realification_moduleTopology_t2 Q.basis
  obtain ⟨descended, _, hunit, hnorm, hcomplex, hLip, hrec, hcontract, hnets⟩ :=
    prep.selected.exists_native_descent ideal hkernel hI Q hQF hQL pDesc hb.2.1
      (hqBudget.trans hb.1) (hQ.mono Q hb.2.2.1)
      (fun i j => (hmap i j).trans hb.2.2.1)
  refine ⟨descended, hunit, hnorm, fun x => (hcomplex x).mono hb.2.2.2.2,
    ?_, hrec, ?_, ?_⟩
  · intro x
    let := Q.metricSpace
    exact (hLip x).weaken (show
      Real.exp ((pDesc + 2) ^ RationalFilteredNilmanifold.nativeInvariantFamilyDescentExponent s) ≤
        Real.exp ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)
      from Real.exp_le_exp.mpr hb.2.2.2.2)
  · intro x y η hxy
    apply hcontract x y η
    simpa only [prep.tests_observable] using hxy
  · intro entropy hnet
    apply hnets entropy
    simpa only [prep.tests_observable] using hnet

end AllocatedExternalCandidateProblem.PositiveKernelPreparation
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M t f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.PositiveKernelPreparation

variable {cost massThreshold scoreThreshold p : ℝ} {e : ℕ}
    {P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked observable weight
      cost massThreshold scoreThreshold}
    (prep : P.PositiveKernelPreparation p e)

theorem exists_native_marked_descended_quotient
    (pBudget : ℝ) (hs : 1 ≤ s) (hpBudget : 0 ≤ pBudget)
    (hD : D.GeometryComplexityLE pBudget) (hFmark : FmarkNative.GeometryComplexityLE pBudget)
    (hmark : ∀ i j, rationalLogHeight (FmarkNative.basis.repr (φ (D.basis j)) i) ≤ pBudget)
    (hqBudget : positiveKernelPreparationParameter p ≤ pBudget) :
    ∃ hker : ∀ x ∈ prep.nativeQuotientIdeal, φ x = 0,
    ∃ dQ : ℕ, dQ ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ prep.nativeQuotientIdeal) s dQ,
      Q.filtration = D.filtration.quotientLie prep.nativeQuotientIdeal prep.nativeQuotientIdeal_terminal ∧
      Q.lattice = D.lattice.map (D.filtration.quotientStepHom prep.nativeQuotientIdeal prep.nativeQuotientIdeal_terminal) ∧
      Q.GeometryComplexityLE
        ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s) ∧
      (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap prep.nativeQuotientIdeal (D.basis j)) i) ≤
        (pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s) ∧
      (∀ i j, rationalLogHeight
        (FmarkNative.basis.repr
          (quotientInducedMark prep.nativeQuotientIdeal φ hker (Q.basis j)) i) ≤
        quotientInducedMarkHeightBudget
          ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ prep.nativeQuotientIdeal))
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ prep.nativeQuotientIdeal)) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 Q.basis
       ∃ descended : (X → ℤ) → Q.Niltest (fullTaggedVariableWeight (X := X) J),
         (∀ x, (descended x).UnitIntervalValued) ∧
         (∀ x y, ‖(descended x).observable y‖ ≤ 1) ∧
         (∀ x, (descended x).ComplexityLE
           ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)) ∧
         (∀ x, letI := Q.metricSpace;
           LipschitzWith
             ⟨Real.exp ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s),
               Real.exp_nonneg _⟩ (descended x).observable) ∧
         (∀ x (g : D.RealGroup), (descended x).observable (QuotientGroup.mk
           (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
             (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap prep.nativeQuotientIdeal) g)) =
             (prep.selected.tests x).observable (QuotientGroup.mk g)) ∧
         (∀ x y η, (∀ z, ‖observable x z - observable y z‖ ≤ η) →
           ∀ z, ‖(descended x).observable z - (descended y).observable z‖ ≤ η) ∧
         ∀ entropy : ℝ → ℝ,
           (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
             ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
               ∀ x ∈ integerBox N, ∃ i, ∀ y,
                 ‖observable x y - observable (rep i).val y‖ ≤ η) →
           ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
             ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
               ∀ x ∈ integerBox N, ∃ i, ∀ y,
                 ‖(descended x).observable y - (descended (rep i).val).observable y‖ ≤ η) := by
  classical
  obtain ⟨hker, dQ, hdQ, Q, hQF, hQL, hQ, hprojection, hdescended⟩ :=
    prep.exists_native_descended_quotient FmarkNative.basis pBudget hs hpBudget hD
      hFmark.1 hmark hqBudget
  have hdegree : 1 ≤ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s :=
    (by omega : 1 ≤ 2).trans
      (RationalFilteredNilmanifold.positiveKernelNativeDescentExponent_ge_two s)
  have hinflate : pBudget ≤
      (pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s :=
    le_power_budget hpBudget hdegree
  have hnonneg : 0 ≤
      (pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s :=
    hpBudget.trans hinflate
  have hinduced := D.quotientInducedMark_native_logHeight FmarkNative
    prep.nativeQuotientIdeal Q φ hker hnonneg (hD.mono D hinflate) hQ hprojection
    (fun i j => (hmark i j).trans hinflate)
  exact ⟨hker, dQ, hdQ, Q, hQF, hQL, hQ, hprojection, hinduced, hdescended⟩

end AllocatedExternalCandidateProblem.PositiveKernelPreparation
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace CommonKeepPositiveKernelPreparation
variable {P} {p : ℝ} {e : ℕ} (front : P.CommonKeepPositiveKernelPreparation p e)

theorem exists_sourceProfile_spatialNativeFamily
    (source : A.DegreeSourceProfile s p e)
    (hp : 0 ≤ p) (hcost0 : 0 ≤ cost) (hcost : cost ≤ p)
    (hD : D.GeometryComplexityLE p)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hmass : Real.exp (-p) ≤ massThreshold) :
    let q := positiveKernelPreparationParameter (2 * p)
    let binLog := positiveKernelPreparationBinLog (2 * p) e
    let commonBudget := max source.front.nativeBudget 3
    let Qmodel := max commonBudget (2 * source.front.u + 4 * source.front.pModel + 20)
    let coefficientLog := Qmodel + 2
    let termLog := 2 * Qmodel + 2 * source.front.u + 4 * source.front.pModel + 34
    ∃ (retained : Finset A.Path), retained ⊆ front.prep.selected.retained ∧
      0 < A.law.mass retained ∧
      Real.exp (-(p * (binLog + termLog))) * (A.law.mass front.prep.selected.retained / 2) ≤
        A.law.mass retained ∧
      Real.exp (-(2 * p + q + p * (binLog + termLog) + 2)) ≤ A.law.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
          (KernelProjectionPresentPivot front.prep.selected.code) D Fmark φ marked front.keep cost
          source.front.familyParameter q commonBudget (q + binLog + coefficientLog + 4)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩,
        F.sourceChart = front.problem.precenterChart front.prep.positive_mass ∧
        (∀ a, HEq (F.sourceCandidate a) (front.problem.precenterCandidate front.prep.positive_mass a)) ∧
        F.η = (fun k => front.prep.early.eta
          (kernelProjectionSelectedPivot front.prep.selected.code k)) ∧
        (∀ a ∈ retained, ∀ k,
          Real.exp (-(q + binLog + coefficientLog + 4)) ≤ ‖F.correlation a k‖) ∧
        (∀ a ∈ retained, (F.sourceChart a).path = a) ∧
        (∀ a, (F.sourceChart a).centerLift = P.centerLift) ∧
        (∀ a ∈ retained, Real.exp (-q) ≤ (F.sourceCandidate a).score
          (fun x => (front.prep.selected.tests x).observable) weight) := by
  intro q binLog commonBudget Qmodel coefficientLog termLog
  let : Nonempty (Fin front.prep.binCount) := Fin.pos_iff_nonempty.mp front.prep.binCount_pos
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hp2 : 0 ≤ 2 * p := by positivity
  have hq : 0 ≤ q := positiveKernelPreparationParameter_nonneg hp2
  have hbin : 0 ≤ binLog := positiveKernelPreparationBinLog_nonneg hp2 e
  have hcard : (Fintype.card (Fin front.prep.binCount) : ℝ) ≤ Real.exp binLog := by
    simpa only [Fintype.card_fin] using front.prep.binCard
  have hdim : (finrank ℚ ↥(D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) : ℝ) ≤ p := by
    have h := Submodule.finrank_le (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap)
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at h
    exact (Nat.cast_le.mpr h).trans hD.1
  have hweight' : ∀ x ∈ integerBox N, ‖weight x‖ ≤ Real.exp (2 * p + 3) := by
    intro x _
    exact (hweight x).trans (Real.exp_le_exp.mpr (by linarith only [hp]))
  have hmassSource : Real.exp (-(2 * p)) ≤ A.law.mass front.problem.productive := by
    calc
      _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ massThreshold * Real.exp (-p) := mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)
      _ ≤ _ := front.problem.mass
  have hmarkov : (q + binLog) + (q + q + binLog + 4) + (2 * p + q) + 2 ≤ source.front.u := by
    convert source.front.markov_precision using 1
    dsimp only [q, binLog, positiveKernelMarkovPrecisionParameter]
    ring
  have budget := source.front.familyBudget hp
  obtain ⟨retained, hsub, hpos', hmass', hmassAll, F, hFC, hFcandidate, hFeta, hcorr,
      hpath, hcenter, hscore⟩ :=
    front.prep.selected.exists_localFixedCenter_spatialNativeFamily
      front.prep.representative front.prep.net source.front.narrow source.front.u_nonneg
      source.front.model_nonneg source.front.input_model source.front.native_nonneg
      source.front.slice_nonneg source.front.test_nontrivial source.front.slice_log
      source.front.marginal_one source.front.marginal_bound source.front.projection_precision
      source.front.detection source.front.physical_excess hq hbin hcard hdim hweight'
      hcost0 (hcost.trans source.front.input_slice) source.front.projection_test hmassSource
      hmarkov le_rfl front.keep front.problem_keep source.polynomial_degree
      source.trim_le_one source.width_le_one source.chartConstant source.chartConstant_nonneg
      source.chart_bound source.chart_small budget.hpFamily (hcost.trans budget.cost)
      budget.projection budget.period budget.variation (budget.keepCard front.keep)
  refine ⟨retained, hsub, hpos', hmass', ?_, F, hFC, hFcandidate, hFeta, hcorr, hpath, hcenter, hscore⟩
  calc
    _ = Real.exp (-(q + p * (binLog + termLog) + 2)) * Real.exp (-(2 * p)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(q + p * (binLog + termLog) + 2)) * A.law.mass front.problem.productive :=
      mul_le_mul_of_nonneg_left hmassSource (Real.exp_nonneg _)
    _ ≤ _ := hmassAll

end CommonKeepPositiveKernelPreparation
end AllocatedExternalCandidateProblem
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_primitive_sourceProfile_front
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile s p e)
    (hp : 0 ≤ p) (hcost0 : 0 ≤ cost) (hcost : cost ≤ p)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hD : D.GeometryComplexityLE p)
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hmass : Real.exp (-p) ≤ massThreshold)
    (hscore : Real.exp (-p) ≤ scoreThreshold)
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ accuracy) :
    ∃ front : P.CommonKeepPositiveKernelPreparation p e,
    let q := positiveKernelPreparationParameter (2 * p)
    let binLog := positiveKernelPreparationBinLog (2 * p) e
    let commonBudget := max source.front.nativeBudget 3
    let Qmodel := max commonBudget (2 * source.front.u + 4 * source.front.pModel + 20)
    let coefficientLog := Qmodel + 2
    let termLog := 2 * Qmodel + 2 * source.front.u + 4 * source.front.pModel + 34
    ∃ (retained : Finset A.Path), retained ⊆ front.prep.selected.retained ∧
      0 < A.law.mass retained ∧
      Real.exp (-(p * (binLog + termLog))) * (A.law.mass front.prep.selected.retained / 2) ≤
        A.law.mass retained ∧
      Real.exp (-(2 * p + q + p * (binLog + termLog) + 2)) ≤ A.law.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
          (KernelProjectionPresentPivot front.prep.selected.code) D Fmark φ marked front.keep cost
          source.front.familyParameter q commonBudget (q + binLog + coefficientLog + 4)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩,
        F.sourceChart = front.problem.precenterChart front.prep.positive_mass ∧
        (∀ a, HEq (F.sourceCandidate a) (front.problem.precenterCandidate front.prep.positive_mass a)) ∧
        F.η = (fun k => front.prep.early.eta
          (kernelProjectionSelectedPivot front.prep.selected.code k)) ∧
        (∀ a ∈ retained, ∀ k,
          Real.exp (-(q + binLog + coefficientLog + 4)) ≤ ‖F.correlation a k‖) ∧
        (∀ a ∈ retained, (F.sourceChart a).path = a) ∧
        (∀ a, (F.sourceChart a).centerLift = P.centerLift) ∧
        (∀ a ∈ retained, Real.exp (-q) ≤ (F.sourceCandidate a).score
          (fun x => (front.prep.selected.tests x).observable) weight) := by
  obtain ⟨front⟩ := P.exists_commonKeepPositiveKernelPreparation p e hp hvariables hD
    ℓ hℓ hLip hpositive hweight hmass hscore source.front.narrow hnet
  exact ⟨front, front.exists_sourceProfile_spatialNativeFamily source hp hcost0 hcost
    hD hweight hmass⟩

end AllocatedExternalCandidateProblem
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M t f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked observable weight
      cost massThreshold scoreThreshold)

structure PrimitiveFrontQuotientData {p : ℝ} {e : ℕ}
    (source : A.DegreeSourceProfile s p e) where
  front : P.CommonKeepPositiveKernelPreparation p e
  retained : Finset A.Path
  retained_subset : retained ⊆ front.prep.selected.retained
  mass_pos : 0 < A.law.mass retained
  mass : Real.exp (-source.front.familyParameter) ≤ A.law.mass retained
  family_nonneg : 0 ≤ source.front.familyParameter
  source_geometry : D.GeometryComplexityLE source.front.familyParameter
  mark_geometry : FmarkNative.GeometryComplexityLE source.front.familyParameter
  mark_height : ∀ i j, rationalLogHeight
    (FmarkNative.basis.repr (φ (D.basis j)) i) ≤ source.front.familyParameter
  pivot_card : (Fintype.card (KernelProjectionPresentPivot front.prep.selected.code) : ℝ) ≤
    source.front.familyParameter
  rawFamily : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
    (KernelProjectionPresentPivot front.prep.selected.code) D FmarkNative.filtration φ marked
    front.keep cost source.front.familyParameter (positiveKernelPreparationParameter (2 * p))
    (max source.front.nativeBudget 3) source.front.frontCorrelationLoss
    (Real.exp (max source.front.nativeBudget 3)) (Real.exp (max source.front.nativeBudget 3))
    ⟨Real.exp (max source.front.nativeBudget 3), Real.exp_nonneg _⟩
  sourceChart_eq : rawFamily.sourceChart = front.problem.precenterChart front.prep.positive_mass
  sourceCandidate_heq : ∀ a, HEq (rawFamily.sourceCandidate a)
    (front.problem.precenterCandidate front.prep.positive_mass a)
  frequencies_eq : rawFamily.η = (fun k => front.prep.early.eta
    (kernelProjectionSelectedPivot front.prep.selected.code k))
  correlation : ∀ a ∈ retained, ∀ k,
    Real.exp (-source.front.frontCorrelationLoss) ≤ ‖rawFamily.correlation a k‖
  path_eq : ∀ a ∈ retained, (rawFamily.sourceChart a).path = a
  center_eq : ∀ a, (rawFamily.sourceChart a).centerLift = P.centerLift
  score : ∀ a ∈ retained, Real.exp (-positiveKernelPreparationParameter (2 * p)) ≤
    (rawFamily.sourceCandidate a).score (fun x => (front.prep.selected.tests x).observable) weight
  ideal_killed : ∀ x ∈ front.prep.nativeQuotientIdeal, φ x = 0
  quotientDimension : ℕ
  quotientDimension_le : quotientDimension ≤ d
  quotient : RationalFilteredNilmanifold (L ⧸ front.prep.nativeQuotientIdeal) s quotientDimension
  quotient_filtration : quotient.filtration = D.filtration.quotientLie
    front.prep.nativeQuotientIdeal front.prep.nativeQuotientIdeal_terminal
  quotient_lattice : quotient.lattice = D.lattice.map (D.filtration.quotientStepHom
    front.prep.nativeQuotientIdeal front.prep.nativeQuotientIdeal_terminal)
  quotient_geometry : quotient.GeometryComplexityLE
    ((source.front.familyParameter + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)
  quotient_projection : ∀ i j, rationalLogHeight (quotient.basis.repr
    (lieQuotientMap front.prep.nativeQuotientIdeal (D.basis j)) i) ≤
      (source.front.familyParameter + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s
  quotient_mark : ∀ i j, rationalLogHeight (FmarkNative.basis.repr
    (quotientInducedMark front.prep.nativeQuotientIdeal φ ideal_killed (quotient.basis j)) i) ≤
      quotientInducedMarkHeightBudget ((source.front.familyParameter + 2) ^
        RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)
  descent :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ front.prep.nativeQuotientIdeal))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ front.prep.nativeQuotientIdeal)) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 quotient.basis
    ∃ descended : (X → ℤ) → quotient.Niltest (fullTaggedVariableWeight (X := X) J),
      (∀ x, (descended x).UnitIntervalValued) ∧
      (∀ x y, ‖(descended x).observable y‖ ≤ 1) ∧
      (∀ x, (descended x).ComplexityLE
        ((source.front.familyParameter + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)) ∧
      (∀ x, letI := quotient.metricSpace;
        LipschitzWith
          ⟨Real.exp ((source.front.familyParameter + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s),
            Real.exp_nonneg _⟩ (descended x).observable) ∧
      (∀ x (g : D.RealGroup), (descended x).observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := quotient.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap front.prep.nativeQuotientIdeal) g)) =
          (front.prep.selected.tests x).observable (QuotientGroup.mk g)) ∧
      (∀ x y η, (∀ z, ‖observable x z - observable y z‖ ≤ η) →
        ∀ z, ‖(descended x).observable z - (descended y).observable z‖ ≤ η) ∧
      ∀ entropy : ℝ → ℝ,
        (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ, (count : ℝ) ≤ entropy η ∧
          ∃ rep : Fin count → integerBox N,
            ∀ x ∈ integerBox N, ∃ i, ∀ y,
              ‖observable x y - observable (rep i).val y‖ ≤ η) →
        ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ, (count : ℝ) ≤ entropy η ∧
          ∃ rep : Fin count → integerBox N,
            ∀ x ∈ integerBox N, ∃ i, ∀ y,
              ‖(descended x).observable y - (descended (rep i).val).observable y‖ ≤ η

namespace PrimitiveFrontQuotientData

variable {FmarkNative P} {p : ℝ} {e : ℕ} {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

noncomputable def family := data.rawFamily.withFrequencies
  (fun k => data.front.prep.early.eta
    (kernelProjectionSelectedPivot data.front.prep.selected.code k)) data.frequencies_eq

@[simp] theorem family_eta : data.family.η =
    (fun k => data.front.prep.early.eta
      (kernelProjectionSelectedPivot data.front.prep.selected.code k)) := rfl

@[simp] theorem family_sourceChart : data.family.sourceChart = data.rawFamily.sourceChart := rfl

@[simp] theorem family_sourceCandidate : data.family.sourceCandidate = data.rawFamily.sourceCandidate := rfl

@[simp] theorem family_correlation (a : A.Path)
    (k : KernelProjectionPresentPivot data.front.prep.selected.code) :
    data.family.correlation a k = data.rawFamily.correlation a k := rfl

theorem family_ideal :
    D.filtration.pivotAnnihilatorIdeal φ data.family.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList =
        data.front.prep.nativeQuotientIdeal := rfl

end PrimitiveFrontQuotientData

theorem exists_primitiveFrontQuotientData
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile s p e)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hcost0 : 0 ≤ cost) (hcost : cost ≤ p)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hD : D.GeometryComplexityLE p) (hFmark : FmarkNative.GeometryComplexityLE p)
    (hmark : ∀ i j, rationalLogHeight (FmarkNative.basis.repr (φ (D.basis j)) i) ≤ p)
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hmass : Real.exp (-p) ≤ massThreshold)
    (hscore : Real.exp (-p) ≤ scoreThreshold)
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ accuracy) :
    Nonempty (P.PrimitiveFrontQuotientData FmarkNative source) := by
  classical
  obtain ⟨front, retained, hretained, hpos, _, hmassRaw, F,
    hchart, hcand, heta, hcorr, hpath, hcenter, hscore⟩ :=
    P.exists_primitive_sourceProfile_front source hp hcost0 hcost hvariables hD
      ℓ hℓ hLip hpositive hweight hmass hscore hnet
  have budget := source.front.familyBudget hp
  have hD' := hD.mono D budget.cost
  have hFmark' := hFmark.mono FmarkNative budget.cost
  have hmark' := fun i j => (hmark i j).trans budget.cost
  obtain ⟨hker, dQ, hdQ, Q, hQF, hQL, hQ, hprojection, hinduced, hdescended⟩ :=
    front.prep.exists_native_marked_descended_quotient FmarkNative source.front.familyParameter
      hs budget.hpFamily hD' hFmark' hmark' budget.projection
  have hpivot : (Fintype.card (KernelProjectionPresentPivot front.prep.selected.code) : ℝ) ≤
      source.front.familyParameter := by
    let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
    have hdim := Submodule.finrank_le (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap)
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at hdim
    exact (Nat.cast_le.mpr ((kernelProjectionPresentPivot_card_le front.prep.selected.code).trans hdim)).trans hD'.1
  exact ⟨{
    front := front
    retained := retained
    retained_subset := hretained
    mass_pos := hpos
    mass := (source.front.exp_neg_familyParameter_le_rawMassLoss hp).trans hmassRaw
    family_nonneg := budget.hpFamily
    source_geometry := hD'
    mark_geometry := hFmark'
    mark_height := hmark'
    pivot_card := hpivot
    rawFamily := F
    sourceChart_eq := hchart
    sourceCandidate_heq := hcand
    frequencies_eq := heta
    correlation := hcorr
    path_eq := hpath
    center_eq := hcenter
    score := hscore
    ideal_killed := hker
    quotientDimension := dQ
    quotientDimension_le := hdQ
    quotient := Q
    quotient_filtration := hQF
    quotient_lattice := hQL
    quotient_geometry := hQ
    quotient_projection := hprojection
    quotient_mark := hinduced
    descent := hdescended }⟩

end AllocatedExternalCandidateProblem
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M t f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrimitiveFrontQuotientData

variable {FmarkNative P} {p : ℝ} {e : ℕ} {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

noncomputable def factorFamily (hp : 0 ≤ p) :=
  data.family.withBudget source.front.factorBudget
    (source.front.factorGeometryBudget hp).factor_input

@[simp] theorem factorFamily_eta (hp : 0 ≤ p) : (data.factorFamily hp).η =
    (fun k => data.front.prep.early.eta
      (kernelProjectionSelectedPivot data.front.prep.selected.code k)) := rfl

@[simp] theorem factorFamily_sourceChart (hp : 0 ≤ p) :
    (data.factorFamily hp).sourceChart = data.rawFamily.sourceChart := rfl

@[simp] theorem factorFamily_sourceCandidate (hp : 0 ≤ p) :
    (data.factorFamily hp).sourceCandidate = data.rawFamily.sourceCandidate := rfl

@[simp] theorem factorFamily_native (hp : 0 ≤ p) :
    (data.factorFamily hp).native = data.rawFamily.native := rfl

@[simp] theorem factorFamily_correlation (hp : 0 ≤ p) (a : A.Path)
    (k : KernelProjectionPresentPivot data.front.prep.selected.code) :
    (data.factorFamily hp).correlation a k = data.rawFamily.correlation a k := rfl

theorem factorFamily_sourceChart_eq (hp : 0 ≤ p) :
    (data.factorFamily hp).sourceChart = data.front.problem.precenterChart data.front.prep.positive_mass :=
  data.sourceChart_eq

theorem factorFamily_sourceCandidate_heq (hp : 0 ≤ p) (a : A.Path) :
    HEq ((data.factorFamily hp).sourceCandidate a)
      (data.front.problem.precenterCandidate data.front.prep.positive_mass a) :=
  data.sourceCandidate_heq a

theorem factorFamily_correlation_bound (hp : 0 ≤ p) :
    ∀ a ∈ data.retained, ∀ k, Real.exp (-source.front.frontCorrelationLoss) ≤
      ‖(data.factorFamily hp).correlation a k‖ := data.correlation

theorem factorFamily_path_eq (hp : 0 ≤ p) :
    ∀ a ∈ data.retained, ((data.factorFamily hp).sourceChart a).path = a := data.path_eq

theorem factorFamily_center_eq (hp : 0 ≤ p) :
    ∀ a, ((data.factorFamily hp).sourceChart a).centerLift = P.centerLift := data.center_eq

theorem factorFamily_score (hp : 0 ≤ p) :
    ∀ a ∈ data.retained, Real.exp (-positiveKernelPreparationParameter (2 * p)) ≤
      ((data.factorFamily hp).sourceCandidate a).score
        (fun x => (data.front.prep.selected.tests x).observable) weight := data.score

theorem frozen_side (a : A.Path) (i : {i // ¬data.front.keep i}) :
    (A.sides i.val : ℝ) ≤ Real.exp cost := by
  have hkeep : (data.front.problem.precenterChart data.front.prep.positive_mass a).keep =
      data.front.keep := data.front.problem.precenterChart_keep
        data.front.prep.positive_mass data.front.keep data.front.problem_keep a
  exact data.front.problem.precenterChart_frozen data.front.prep.positive_mass a
    ⟨i.val, by rw [hkeep]; exact i.property⟩

include data in

theorem source_geometry_bound (hp : 0 ≤ p) : D.GeometryComplexityLE source.front.geometryBudget :=
  data.source_geometry.mono D (source.front.factorGeometryBudget hp).geometry_input

include data in
theorem mark_geometry_bound (hp : 0 ≤ p) :
    FmarkNative.GeometryComplexityLE source.front.geometryBudget :=
  data.mark_geometry.mono FmarkNative (source.front.factorGeometryBudget hp).geometry_input

include data in
theorem mark_height_bound (hp : 0 ≤ p) (i j) : rationalLogHeight
    (FmarkNative.basis.repr (φ (D.basis j)) i) ≤ source.front.geometryBudget :=
  (data.mark_height i j).trans (source.front.factorGeometryBudget hp).geometry_input

include data in
theorem native_geometry_bound (hp : 0 ≤ p) :
    max source.front.nativeBudget 3 ≤ source.front.geometryBudget :=
  data.rawFamily.hnative.trans (source.front.factorGeometryBudget hp).geometry_input

theorem pivot_card_bound (hp : 0 ≤ p) :
    (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) ≤
      source.front.geometryBudget :=
  data.pivot_card.trans (source.front.factorGeometryBudget hp).geometry_input

theorem quotient_geometry_bound (hp : 0 ≤ p) :
    data.quotient.GeometryComplexityLE source.front.geometryBudget :=
  data.quotient_geometry.mono data.quotient (source.front.factorGeometryBudget hp).geometry_descent

theorem quotient_projection_bound (hp : 0 ≤ p) (i j) :
    rationalLogHeight (data.quotient.basis.repr
      (lieQuotientMap data.front.prep.nativeQuotientIdeal (D.basis j)) i) ≤ source.front.geometryBudget :=
  (data.quotient_projection i j).trans (source.front.factorGeometryBudget hp).geometry_descent

theorem factorFamily_quotient_filtration (hp : 0 ≤ p) :
    data.quotient.filtration = D.filtration.pivotQuotientFiltration φ (data.factorFamily hp).η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList :=
  data.quotient_filtration

end PrimitiveFrontQuotientData
end AllocatedExternalCandidateProblem
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} {FmarkNative : RationalFilteredNilmanifold M t f} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.PrimitiveFrontQuotientData

variable {cost massThreshold scoreThreshold p : ℝ} {e : ℕ}
    {P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold}
    {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

section QuotientTopology

variable [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))]
    [T2Space (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))]

structure DescendedFamily where
  tests : (X → ℤ) → data.quotient.Niltest (fullTaggedVariableWeight (X := X) J)
  unit : ∀ x, (tests x).UnitIntervalValued
  norm1 : ∀ x y, ‖(tests x).observable y‖ ≤ 1
  complexity : ∀ x, (tests x).ComplexityLE
    ((source.front.familyParameter + 2) ^
      RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)
  lipschitz : ∀ x, letI := data.quotient.metricSpace
    LipschitzWith
      ⟨Real.exp ((source.front.familyParameter + 2) ^
        RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s), Real.exp_nonneg _⟩
      (tests x).observable
  recovery : ∀ x (g : D.RealGroup), (tests x).observable (QuotientGroup.mk
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := data.quotient.filtration.lowerCentralSeries_eq_bot)
      (lieQuotientMap data.front.prep.nativeQuotientIdeal) g)) =
      (data.front.prep.selected.tests x).observable (QuotientGroup.mk g)
  contract_original : ∀ x y η, (∀ z, ‖observable x z - observable y z‖ ≤ η) →
    ∀ z, ‖(tests x).observable z - (tests y).observable z‖ ≤ η
  member_nets : ∀ entropy : ℝ → ℝ,
    (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ, (count : ℝ) ≤ entropy η ∧
      ∃ rep : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (rep i).val y‖ ≤ η) →
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ, (count : ℝ) ≤ entropy η ∧
      ∃ rep : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖(tests x).observable y - (tests (rep i).val).observable y‖ ≤ η

end QuotientTopology

theorem exists_descendedFamily :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 data.quotient.basis
    Nonempty data.DescendedFamily := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
    realification_moduleTopology_t2 data.quotient.basis
  obtain ⟨tests, hunit, hnorm, hcomplexity, hLip, hrecovery, hcontract, hnets⟩ := data.descent
  exact ⟨{
    tests := tests
    unit := hunit
    norm1 := hnorm
    complexity := hcomplexity
    lipschitz := hLip
    recovery := hrecovery
    contract_original := hcontract
    member_nets := hnets }⟩

end AllocatedExternalCandidateProblem.PrimitiveFrontQuotientData
end Erdos3.VectorPolynomial

end

end OAI
