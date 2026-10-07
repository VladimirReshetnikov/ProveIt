import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateOptionJointConclusion
import OAI.Combinatorics.Progressions.Lattices.UniformExternalMarkedAffineSliceFreezingDictionary

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

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

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : F.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D F φ marked)

noncomputable def freezingNativeOrbit :
    (D.filtration.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group :=
  D.filtration.realification.polynomialOrbitCoordinates (fun _ : C.Variables => 1) candidate.orbit

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in

theorem freezingNativeOrbit_value (u : C.Variables → ℤ) :
    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom
      (fun _ : C.Variables => 1) (fun i => (u i : ℝ)) (C.freezingNativeOrbit candidate)) : D.Space) =
      candidate.value u := by
  rw [freezingNativeOrbit, D.filtration.nativeFrozenMarkedOrbitCoordinates_realValue,
    polynomialOrbitRealEval_integer]
  rfl

noncomputable def freezingOriginalValue
    (tests : (X → ℤ) → D.Niltest (fun _ : C.Variables => 1)) (u : C.Variables → ℤ) : ℂ :=
  (tests (C.physical u)).observable (QuotientGroup.mk
    (D.filtration.adaptedPolynomialRealValueHom (fun _ : C.Variables => 1)
      (fun i => (u i : ℝ)) (C.freezingNativeOrbit candidate)))

@[simp] theorem freezingOriginalValue_eq
    (tests : (X → ℤ) → D.Niltest (fun _ : C.Variables => 1)) (u : C.Variables → ℤ) :
    C.freezingOriginalValue candidate tests u =
      (tests (C.physical u)).observable (candidate.value u) := by
  unfold freezingOriginalValue
  rw [C.freezingNativeOrbit_value candidate]

variable (sectionMap : M →ₗ[ℚ] L)
    (hsectionLayer : ∀ j, ∀ y ∈ F.layer j, sectionMap y ∈ D.filtration.layer j)
    (EF RF : (F.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)
    (middle : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)

noncomputable def freezingFrozenValue
    (tests : (X → ℤ) → D.Niltest (fun _ : C.Variables => 1))
    (left right : D.RealGroup) (u : C.Variables → ℤ) : ℂ :=
  (tests (C.physical u)).markedFrozenValue F (fun _ : C.Variables => 1)
    sectionMap hsectionLayer EF RF middle left right u

theorem finiteFreezing_of_selection
    {Left Right : Type*} (Q modulus : ℕ) (hQ : 0 < Q) (hmodulus : 0 < modulus)
    (left : Left → D.RealGroup) (right : Right → D.RealGroup)
    (tests : (X → ℤ) → D.Niltest (fun _ : C.Variables => 1)) (weight : (X → ℤ) → ℂ)
    {budget Bweight Lip ε τ θ Sscore : ℝ}
    (hQbound : (Q : ℝ) ≤ max 1 budget) (hmodulusBound : (modulus : ℝ) ≤ budget)
    (htwo : ∀ i, 2 ≤ C.slice.length i)
    (hlong : ∀ i, 2 * budget * max 1 budget ≤ (C.slice.length i : ℝ))
    {densityCost : ℝ}
    (hsourceDense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      densityCost C.slice.integerPoints)
    (hθ : 0 < θ) (herr : 0 ≤ Bweight * (Lip * ε))
    (hscore : Sscore ≤ candidate.score (fun x value => (tests x).observable value) weight)
    (hselect :
      (∀ i, 0 < C.slice.length i) →
      (∀ i v, v < C.slice.length i →
        |((C.slice.start i : ℤ) : ℝ) + C.step * v| ≤ (A.sides i.val : ℝ)) →
      (∀ i, (C.step : ℝ) * C.slice.length i ≤ 2 * (A.sides i.val : ℝ)) →
      (∀ i, 2 * (modulus : ℝ) ≤ (1 / (Q : ℝ)) * C.slice.length i) →
      (Sscore ≤ 𝔼 x : (∀ i, Fin (C.slice.length i)),
        (weight (C.physical (affineParentIntegerPoint C.slice.length
            (fun i => (C.slice.start i : ℤ)) C.step x)) *
          C.freezingOriginalValue candidate tests (affineParentIntegerPoint C.slice.length
            (fun i => (C.slice.start i : ℤ)) C.step x)).re) →
      ∃ T : ResidueBoxSlice C.slice.length modulus, (∀ i, 0 < T.length i) ∧
        (∀ i, θ * C.slice.length i /
          (4 * modulus * Q * (Fintype.card C.Variables + 1 : ℝ)) ≤ T.length i) ∧
        ∃ i j,
          (∀ x : ∀ k, Fin (T.length k),
            ‖C.freezingOriginalValue candidate tests
                (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x) -
              C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
                (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)‖ ≤ Lip * ε) ∧
          (∀ x : ∀ k, Fin (T.length k),
            ‖weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
                C.freezingOriginalValue candidate tests
                  (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x) -
              weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
                C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
                  (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)‖ ≤ Bweight * (Lip * ε)) ∧
          τ < 𝔼 x : (∀ k, Fin (T.length k)),
            (weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
              C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
                (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)).re) :
    ∃ slice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) (C.step * modulus),
      IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
        (densityCost + Real.log ((4 * modulus * Q * (Fintype.card C.Variables + 1 : ℝ)) / θ))
        slice.integerPoints ∧
      slice.integerPoints ⊆ C.slice.integerPoints ∧
      ∃ i j,
        (∀ u ∈ slice.integerPoints,
          ‖(tests (C.physical u)).observable (candidate.value u) -
            C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j) u‖ ≤ Lip * ε) ∧
        (∀ u ∈ slice.integerPoints,
          ‖weight (C.physical u) * (tests (C.physical u)).observable (candidate.value u) -
            weight (C.physical u) *
              C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j) u‖ ≤
            Bweight * (Lip * ε)) ∧
        τ < (𝔼 u ∈ slice.integerPoints, weight (C.physical u) *
          C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j) u).re ∧
        τ - Bweight * (Lip * ε) ≤
          (𝔼 u ∈ slice.integerPoints, weight (C.physical u) *
            (tests (C.physical u)).observable (candidate.value u)).re := by
  have hparent (i) (v : ℕ) (hv : v < C.slice.length i) :
      |((C.slice.start i : ℤ) : ℝ) + C.step * v| ≤ (A.sides i.val : ℝ) := by
    simp only [Int.cast_natCast]
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast (C.slice.inside i v hv).le
  have hwidth (i) : (C.step : ℝ) * C.slice.length i ≤ 2 * (A.sides i.val : ℝ) := by
    exact_mod_cast C.slice.stride_mul_length_le_twice i (htwo i)
  have hlarge (i) : 2 * (modulus : ℝ) ≤ (1 / (Q : ℝ)) * C.slice.length i := by
    have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
    have hmnonneg : (0 : ℝ) ≤ modulus := Nat.cast_nonneg _
    have hBnonneg : 0 ≤ budget := hmnonneg.trans hmodulusBound
    have hprod : (2 * (modulus : ℝ)) * Q ≤ (C.slice.length i : ℝ) := by
      calc
        _ ≤ (2 * budget) * max 1 budget :=
          mul_le_mul (mul_le_mul_of_nonneg_left hmodulusBound (by norm_num)) hQbound
            (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hBnonneg)
        _ ≤ _ := hlong i
    have hdiv := (le_div_iff₀ hQpos).mpr hprod
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm (C.slice.length i : ℝ)] using hdiv
  have hindexed : Sscore ≤ 𝔼 x : (∀ i, Fin (C.slice.length i)),
      (weight (C.physical (affineParentIntegerPoint C.slice.length
          (fun i => (C.slice.start i : ℤ)) C.step x)) *
        C.freezingOriginalValue candidate tests (affineParentIntegerPoint C.slice.length
          (fun i => (C.slice.start i : ℤ)) C.step x)).re := by
    rw [AllocatedExternalLocalCandidate.score, C.slice.expect_integerPoints C.step_pos,
      Complex.re_expect] at hscore
    have hpoint (x : ∀ i, Fin (C.slice.length i)) :
        affineParentIntegerPoint C.slice.length (fun i => (C.slice.start i : ℤ)) C.step x =
          C.slice.integerPoint x := by
      funext i
      simp only [affineParentIntegerPoint, ResidueBoxSlice.integerPoint,
        ResidueBoxSlice.point, Nat.cast_add, Nat.cast_mul]
    simpa only [C.freezingOriginalValue_eq candidate tests, hpoint] using hscore
  obtain ⟨T, hTlen, hTlong, i, j, herror, hweighted, hfrozen⟩ :=
    hselect (C.slice.length_pos_of_dense hsourceDense) hparent hwidth hlarge hindexed
  have hdenom : (0 : ℝ) < 4 * modulus * Q * (Fintype.card C.Variables + 1) := by
    have hmpos : (0 : ℝ) < modulus := Nat.cast_pos.mpr hmodulus
    have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
    positivity
  refine ⟨C.slice.composeSlice T,
    C.slice.composeSlice_isDenseCommonStrideBox_of_fraction T C.step_pos hmodulus hsourceDense
      hθ hdenom hTlong,
    C.slice.composeSlice_integerPoints_subset T, i, j, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [C.slice.composeSlice_integerPoints_eq_affine_image T] at hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    simpa only [C.freezingOriginalValue_eq candidate tests] using herror x
  · intro u hu
    rw [C.slice.composeSlice_integerPoints_eq_affine_image T] at hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    simpa only [C.freezingOriginalValue_eq candidate tests] using hweighted x
  · rw [C.slice.expect_composeSlice_integerPoints T C.step_pos hmodulus, Complex.re_expect]
    exact hfrozen
  · rw [C.slice.expect_composeSlice_integerPoints T C.step_pos hmodulus, Complex.re_expect]
    let orig := fun x : ∀ k, Fin (T.length k) =>
      weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
        C.freezingOriginalValue candidate tests
          (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)
    let froz := fun x : ∀ k, Fin (T.length k) =>
      weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
        C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
          (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)
    have he := complex_expect_error_le Finset.univ froz orig herr (by
      intro x _
      simpa only [norm_sub_rev] using hweighted x)
    have hre := (Complex.re_le_norm _).trans he
    rw [Complex.sub_re, Complex.re_expect, Complex.re_expect] at hre
    have hmean : τ - Bweight * (Lip * ε) ≤ 𝔼 x, (orig x).re := by
      change τ < 𝔼 x, (froz x).re at hfrozen
      linarith
    simpa only [orig, C.freezingOriginalValue_eq candidate tests] using hmean

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
