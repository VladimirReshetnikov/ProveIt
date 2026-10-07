import OAI.Combinatorics.Progressions.Linear.AllocatedExternalCandidateCommonKeepPositiveKernelPreparation

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d t n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem Niltest.nativeQuotient_observable_sub_norm_le
    (T : D.Niltest w) (U : D.Niltest v)
    (I : LieIdeal ℚ L) (htop : I.toSubmodule ≤ D.filtration.layer s)
    (Q : RationalFilteredNilmanifold (L ⧸ I) t n) (f g : Q.Space → ℂ)
    (hf : ∀ x : D.RealGroup, f (QuotientGroup.mk
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) x)) =
      (T.kernelProjection I.toSubmodule htop).observable (QuotientGroup.mk x))
    (hg : ∀ x : D.RealGroup, g (QuotientGroup.mk
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) x)) =
      (U.kernelProjection I.toSubmodule htop).observable (QuotientGroup.mk x))
    {η : ℝ} (hTU : ∀ x, ‖T.observable x - U.observable x‖ ≤ η) :
    ∀ x : Q.Space, ‖f x - g x‖ ≤ η := by
  intro q
  induction q using Quotient.inductionOn with
  | h q =>
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ (lieQuotientMap_surjective I) q.coord
    let z : D.RealGroup := ⟨x⟩
    have hz : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) z = q :=
      NilpotentLieBCHGroup.ext hx
    have hfz := hf z
    have hgz := hg z
    rw [hz] at hfz hgz
    rw [hfz, hgz]
    exact T.kernelProjection_observable_sub_norm_le U I.toSubmodule htop hTU
      (QuotientGroup.mk z)

theorem nativeQuotient_member_external_net {A C : Type*}
    (T : A → D.Niltest w) (representative : C → A)
    (I : LieIdeal ℚ L) (htop : I.toSubmodule ≤ D.filtration.layer s)
    (Q : RationalFilteredNilmanifold (L ⧸ I) t n) (f : A → Q.Space → ℂ)
    (hrec : ∀ a (x : D.RealGroup), f a (QuotientGroup.mk
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) x)) =
      ((T a).kernelProjection I.toSubmodule htop).observable (QuotientGroup.mk x))
    {η : ℝ} (hnet : ∀ a, ∃ i, ∀ x,
      ‖(T a).observable x - (T (representative i)).observable x‖ ≤ η) :
    ∀ a, ∃ i, ∀ x : Q.Space, ‖f a x - f (representative i) x‖ ≤ η := by
  intro a
  obtain ⟨i, hi⟩ := hnet a
  exact ⟨i, (T a).nativeQuotient_observable_sub_norm_le (T (representative i))
    I htop Q (f a) (f (representative i)) (hrec a) (hrec (representative i)) hi⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

noncomputable def nativeInvariantFamilyDescentExponent (t : ℕ) : ℕ :=
  Classical.choose (exists_idealInvariant_niltest_budget.{0, 0} t)

theorem nativeInvariantFamilyDescentExponent_ge_two (t : ℕ) :
    2 ≤ nativeInvariantFamilyDescentExponent t :=
  (Classical.choose_spec (exists_idealInvariant_niltest_budget.{0, 0} t)).1

end Erdos3.RationalFilteredNilmanifold

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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.PrecenterKernelSelection

variable {cost massThreshold scoreThreshold p q : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

theorem exists_native_descent
    (ideal : LieIdeal ℚ L)
    (hkernel : ideal.toSubmodule = frequencyCodeKernel top early.eta selected.code)
    (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    {dQ : ℕ} (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ ideal))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ ideal))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ ideal))] [T2Space (ℝ ⊗[ℚ] (L ⧸ ideal))]
    (hQF : Q.filtration = D.filtration.quotientLie ideal hI)
    (hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom ideal hI))
    (pDesc : ℝ) (hpDesc : 0 ≤ pDesc) (hqDesc : q ≤ pDesc)
    (hQ : Q.GeometryComplexityLE pDesc)
    (hmap : ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap ideal (D.basis j)) i) ≤ pDesc) :
    ∃ descended : (X → ℤ) → Q.Niltest (fullTaggedVariableWeight (X := X) J),
      (∀ x, (descended x).orbit =
        D.idealQuotientOrbit ideal hI Q hQF (selected.tests x).orbit) ∧
      (∀ x, (descended x).UnitIntervalValued) ∧
      (∀ x y, ‖(descended x).observable y‖ ≤ 1) ∧
      (∀ x, (descended x).ComplexityLE
        ((pDesc + 2) ^ RationalFilteredNilmanifold.nativeInvariantFamilyDescentExponent s)) ∧
      (∀ x, letI := Q.metricSpace;
        LipschitzWith
          ⟨Real.exp ((pDesc + 2) ^ RationalFilteredNilmanifold.nativeInvariantFamilyDescentExponent s),
            Real.exp_nonneg _⟩ (descended x).observable) ∧
      (∀ x (g : D.RealGroup), (descended x).observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
          (selected.tests x).observable (QuotientGroup.mk g)) ∧
      (∀ x y η, (∀ z, ‖(T x).observable z - (T y).observable z‖ ≤ η) →
        ∀ z, ‖(descended x).observable z - (descended y).observable z‖ ≤ η) ∧
      ∀ entropy : ℝ → ℝ,
        (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
          ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
            ∀ x ∈ integerBox N, ∃ i, ∀ y,
              ‖(T x).observable y - (T (rep i).val).observable y‖ ≤ η) →
        ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
          ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
            ∀ x ∈ integerBox N, ∃ i, ∀ y,
              ‖(descended x).observable y - (descended (rep i).val).observable y‖ ≤ η := by
  classical
  have hinvariant (x : X → ℤ) (g : D.RealGroup)
      (hg : g.coord ∈ ideal.toSubmodule.baseChange ℝ) (y : D.Space) :
      (selected.tests x).observable (g • y) = (selected.tests x).observable y := by
    apply selected.invariant x g _ y
    simpa only [hkernel] using hg
  have hex (x : X → ℤ) := (Classical.choose_spec
    (RationalFilteredNilmanifold.exists_idealInvariant_niltest_budget.{0, 0} s)).2
    D ideal hI Q hQF hQL (selected.tests x)
    pDesc hpDesc ((selected.test_bounds x).2.1.mono hqDesc) hQ hmap (hinvariant x)
  choose descended horbit hnorm hcomplex hrecovery heval hunit using hex
  have hpositive (x : X → ℤ) : (descended x).UnitIntervalValued :=
    hunit x (selected.test_bounds x).1
  have htopIdeal : ideal.toSubmodule ≤ D.filtration.layer s := by
    rw [hkernel]
    exact (finiteFrequencyKernel_le top _ _).trans htop
  have hrecOriginal (x : X → ℤ) (g : D.RealGroup) :
      (descended x).observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        ((T x).kernelProjection ideal.toSubmodule htopIdeal).observable (QuotientGroup.mk g) := by
    rw [hrecovery, selected.identity]
    congr 2
    exact hkernel.symm
  have hcontract (x y : X → ℤ) (η : ℝ)
      (hxy : ∀ z, ‖(T x).observable z - (T y).observable z‖ ≤ η) :
      ∀ z, ‖(descended x).observable z - (descended y).observable z‖ ≤ η :=
    (T x).nativeQuotient_observable_sub_norm_le (T y) ideal htopIdeal Q
      (descended x).observable (descended y).observable (hrecOriginal x) (hrecOriginal y) hxy
  refine ⟨descended, horbit, hpositive, fun x y => (hpositive x).norm_le_one y,
    hcomplex, ?_, hrecovery, hcontract, ?_⟩
  · intro x
    let := Q.metricSpace
    apply (descended x).lipschitz.weaken
    change ((descended x).lipBound : ℝ) ≤
      Real.exp ((pDesc + 2) ^ RationalFilteredNilmanifold.nativeInvariantFamilyDescentExponent s)
    unfold RationalFilteredNilmanifold.nativeInvariantFamilyDescentExponent
    have h := (descended x).observable_budget (hcomplex x)
    linarith [(descended x).normBound.coe_nonneg]
  · intro entropy hnet η hη hη1
    obtain ⟨n, hn, rep, hrep⟩ := hnet η hη hη1
    refine ⟨n, hn, rep, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := hrep x hx
    exact ⟨i, hcontract x (rep i).val η hi⟩

end AllocatedExternalCandidateProblem.PrecenterKernelSelection
end Erdos3.VectorPolynomial

end

end OAI
