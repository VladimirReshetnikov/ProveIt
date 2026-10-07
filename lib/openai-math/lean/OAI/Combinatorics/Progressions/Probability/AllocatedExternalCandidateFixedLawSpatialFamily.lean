import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {Ω Freq Bin : Type} [Fintype Ω] [Fintype Bin] [Nonempty Bin]
    {LG LM : Type} [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d t rank : ℕ} (D : RationalFilteredNilmanifold LG s d)
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {cost : ℝ} (C : Ω → AllocatedExternalLocalChart (E := Deck) A cost)
    (candidate : ∀ a, AllocatedExternalLocalCandidate (C a) D Fmark φ marked)
    (hξ1 : ξ ≤ 1)

theorem exists_fixedLaw_spatial_native_family
    (external : Freq → integerBox N → D.Niltest (fullTaggedVariableWeight (X := X) J))
    (representative : Bin → integerBox N)
    (eta : Freq → LG →ₗ[ℚ] ℚ)
    {p pLocal pNative r inputBound ε δ coefficientBound termBound : ℝ}
    (hcomplex : ∀ f x, (external f x).ComplexityLE pLocal)
    (hnet : ∀ f x, ∃ i, ∀ y, ‖(external f x).observable y -
      (external f (representative i)).observable y‖ ≤ ε)
    (input : integerBox N → ℂ)
    (models : (Freq × Bin) → CenteredForecastModel (integerBox N))
    (periodCap coverCap : ℝ) (Lip : ℝ≥0)
    (hnativeModels : ∀ branch i, (models branch).models i ∈
      twistedNativeSampleFunctions (fun _ : X => 1) s pNative
        (fun x : integerBox N => x.val)
        (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
          (x : integerBox N) => twist.eval N poly x.val))
    (hmodel : ∀ branch, externalNetMaskFamily (fun f x => (external f x).observable)
        (fun f i => (external f (representative i)).observable) hnet input branch =
      (∑ i, (models branch).coefficient i • (models branch).models i) + (models branch).residual)
    (hcoefficient : ∀ branch, (∑ i, |(models branch).coefficient i|) ≤ coefficientBound)
    (hterms : ∀ branch, ((models branch).nterms : ℝ) ≤ termBound)
    (hM : 0 < coefficientBound) (hterm : 1 ≤ termBound)
    (code : Fin rank → Option Freq)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (hB : 0 ≤ inputBound) (hδ : 0 < δ) (herror : inputBound * ε ≤ δ / 2)
    (hinput : ∀ x, ‖input x‖ ≤ inputBound)
    {Eres sliceBudget testBudget : ℝ}
    (hcost0 : 0 ≤ cost)
    (hshort : ∀ a ∈ H, ∀ i : {i // ¬(C a).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : pLocal ≤ testBudget)
    (hUniform : ∀ a ∈ H, ∀ f i,
      ∀ packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget,
        ‖𝔼 site ∈ packet.slice.subtypeSites,
          (models (f, i)).residual (A.boxedPhysical hξ1 (C a).path site) *
            packet.weight site.val‖ ≤ Real.exp (-Eres))
    (hresBudget : Real.exp (pLocal - Eres) ≤ (δ / (2 * Fintype.card Bin)) / 2)
    (hscore : ∀ a ∈ H, ∀ i f, code i = some f → δ ≤
      ‖(C a).localLaw.complexMean (fun site =>
        input (A.boxedPhysical hξ1 (C a).path site) *
          (external f (A.boxedPhysical hξ1 (C a).path site)).observable
            ((candidate a).siteValue site))‖)
    (hcorrBudget : Real.exp (-r) ≤ (δ / (2 * Fintype.card Bin)) / (2 * coefficientBound))
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (C a).keep = keep)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : 0 ≤ p) (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r)
    (hcost : cost ≤ p) (hlocal : pLocal ≤ p) (hnative : pNative ≤ p)
    (hperiod : periodCap * coverCap ≤ Real.exp p)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
    (hetaHeight : ∀ f i, rationalLogHeight (eta f (D.basis i)) ≤ p)
    (hvertical : ∀ f x z, z ∈ D.filtration.realification.subgroup s → ∀ y,
      (external f x).observable (z • y) = CircleFourier.character
        ((realifyFunctional (eta f) z.coord : ℝ) : CircleFourier.Circle) *
          (external f x).observable y)
    (hK : (Fintype.card {i // keep i} : ℝ) ≤ p) :
    ∃ (retained : Finset Ω), retained ⊆ H ∧ 0 < outer.mass retained ∧
      outer.mass H / ((Fintype.card Bin : ℝ) ^ rank * termBound ^ rank) ≤ outer.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω
          (KernelProjectionPresentPivot code) D Fmark φ marked keep cost p pLocal pNative r
          periodCap coverCap Lip,
        F.sourceChart = C ∧ (∀ a, HEq (F.sourceCandidate a) (candidate a)) ∧
        F.η = (fun k => eta (kernelProjectionSelectedPivot code k)) ∧
        ∀ a ∈ retained, ∀ k, Real.exp (-r) ≤ ‖F.correlation a k‖ := by
  have hresidual : ∀ a ∈ H, ∀ f i,
      ‖(C a).localLaw.complexMean (fun site =>
        (models (f, i)).residual (A.boxedPhysical hξ1 (C a).path site) *
          (external f (representative i)).observable ((candidate a).siteValue site))‖ ≤
            (δ / (2 * Fintype.card Bin)) / 2 := by
    intro a ha f i
    exact ((candidate a).localLaw_residual_le_exp_of_universal_native_budget
      (external f (representative i)) (hcomplex f _) hcost0 (hshort a ha)
      hSliceBudget hTestBudget
      (fun site => (models (f, i)).residual (A.boxedPhysical hξ1 (C a).path site))
      (hUniform a ha f i)).trans hresBudget
  obtain ⟨chosen, twist, value, native, retained, hsub, hpos, hmass, _, hcorr⟩ :=
    exists_external_kernel_precenter_native_point_partners D external representative hcomplex hnet
      input models (fun _ : X => 1) s pNative (fun x : integerBox N => x.val)
      (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
        (x : integerBox N) => twist.eval N poly x.val)
      hnativeModels hmodel hcoefficient hterms hM hterm code outer H hH
      (fun a => (C a).localLaw) (fun a => (candidate a).siteValue)
      (fun a => A.boxedPhysical hξ1 (C a).path)
      hB hδ herror hinput hresidual hscore
  let F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω
      (KernelProjectionPresentPivot code) D Fmark φ marked keep cost p pLocal pNative r
      periodCap coverCap Lip := {
    hpoly := hpoly
    hτ1 := hτ1
    hξ := hξ1
    hσ1 := hσ1
    Cgeo := Cgeo
    hCgeo := hCgeo
    hchart := hchart
    hsmall := hsmall
    sourceChart := C
    keep_eq := hkeep
    sourceCandidate := candidate
    reference := fun _ k => external (kernelProjectionSelectedPivot code k) (representative (chosen k))
    nativeValue := value
    native := native
    twist := fun _ => twist
    hp := hp
    hpLocal := hpLocal
    hr := hr
    hcost := hcost
    hlocal := hlocal
    hnative := hnative
    hperiod := by
      intro a k
      rw [Nat.cast_mul]
      exact (mul_le_mul (twist k).modulus_bound (twist k).cover_bound
        (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans (twist k).modulus_bound)).trans hperiod
    hvariation := hvariation
    hV := fun _ k => hcomplex _ _
    η := fun k => eta (kernelProjectionSelectedPivot code k)
    hηheight := fun k i => hetaHeight _ i
    hη := fun _ k => hvertical _ _
    hK := hK }
  refine ⟨retained, hsub, hpos, hmass, F, rfl, (fun _ => HEq.rfl), rfl, ?_⟩
  intro a ha k
  apply hcorrBudget.trans
  simpa only [AllocatedExternalCandidateSpatialNativeFamily.correlation,
    AllocatedExternalCandidateSpatialNativeFamily.sitePhysicalBox, F, boxedPhysical, mul_assoc, mul_left_comm, mul_comm]
    using hcorr a ha k

end AllocatedExternalCandidateSampler
end
end Erdos3.VectorPolynomial

end

end OAI
