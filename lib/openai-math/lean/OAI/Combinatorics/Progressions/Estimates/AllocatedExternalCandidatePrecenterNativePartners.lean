import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

def boxedPhysical (hξ1 : ξ ≤ 1) (z : A.Path) (site : A.Site) : integerBox N :=
  ⟨A.physical z site, A.physical_mem_integerBox hξ1 z site⟩

@[simp] theorem boxedPhysical_val (hξ1 : ξ ≤ 1) (z : A.Path) (site : A.Site) :
    (A.boxedPhysical hξ1 z site).val = A.physical z site := rfl

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {Ω Freq Bin : Type*} [Fintype Ω] [Fintype Bin] [Nonempty Bin]
    {LG LM : Type*} [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d t rank : ℕ} (D : RationalFilteredNilmanifold LG s d)
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {cost : ℝ} (C : Ω → AllocatedExternalLocalChart (E := Deck) A cost)
    (candidate : ∀ a, AllocatedExternalLocalCandidate (C a) D Fmark φ marked)
    (hξ1 : ξ ≤ 1)

theorem exists_precenter_native_partners
    (external : Freq → integerBox N → D.Niltest (fullTaggedVariableWeight (X := X) J))
    (representative : Bin → integerBox N)
    {p inputBound ε δ coefficientBound termBound residualBound : ℝ}
    (hcomplex : ∀ f x, (external f x).ComplexityLE p)
    (hnet : ∀ f x, ∃ i, ∀ y, ‖(external f x).observable y -
      (external f (representative i)).observable y‖ ≤ ε)
    (input : integerBox N → ℂ)
    (models : (Freq × Bin) → CenteredForecastModel (integerBox N))
    (degree : ℕ) (budget periodCap coverCap : ℝ) (Lip : ℝ≥0)
    {Y Forecast : Type*} [MeasurableSpace Y]
    (jointLaw : Measure Y) (referenceLaw : FiniteProbabilityWeights (integerBox N))
    (forecast : Forecast → integerBox N → ℂ)
    (localSeminorm : (integerBox N → ℂ) → ℝ)
    (selectedLocal : (integerBox N → ℂ) → (Y → ℂ) → Prop)
    (hmodels : ∀ branch, CenteredForecastModelBounds jointLaw
      (twistedNativeSampleFunctions (fun _ : X => 1) degree budget
        (fun x : integerBox N => x.val)
        (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
          (x : integerBox N) => twist.eval N poly x.val))
      referenceLaw forecast localSeminorm selectedLocal
      (externalNetMaskFamily (fun f x => (external f x).observable)
        (fun f i => (external f (representative i)).observable) hnet input branch)
      coefficientBound residualBound termBound (models branch))
    (hM : 0 < coefficientBound) (hterm : 1 ≤ termBound)
    (code : Fin rank → Option Freq)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (hB : 0 ≤ inputBound) (hδ : 0 < δ) (herror : inputBound * ε ≤ δ / 2)
    (hinput : ∀ x, ‖input x‖ ≤ inputBound)
    (hresidual : ∀ a ∈ H, ∀ f i,
      ‖(C a).localLaw.complexMean (fun site =>
        (models (f, i)).residual (A.boxedPhysical hξ1 (C a).path site) *
          (external f (representative i)).observable ((candidate a).siteValue site))‖ ≤
            (δ / (2 * Fintype.card Bin)) / 2)
    (hscore : ∀ a ∈ H, ∀ i f, code i = some f → δ ≤
      ‖(C a).localLaw.complexMean (fun site =>
        input (A.boxedPhysical hξ1 (C a).path site) *
          (external f (A.boxedPhysical hξ1 (C a).path site)).observable
            ((candidate a).siteValue site))‖) :
    ∃ (chosen : KernelProjectionPresentPivot code → Bin)
      (fixedTwist : KernelProjectionPresentPivot code →
        NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (nativeValue : KernelProjectionPresentPivot code → integerBox N → ℂ)
      (_native : ∀ k, NativeSampleModel (fun _ : X => 1) degree budget
        (fun x : integerBox N => x.val) (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      outer.mass H / ((Fintype.card Bin : ℝ) ^ rank * termBound ^ rank) ≤ outer.mass retained ∧
      (∀ a k, ((external (kernelProjectionSelectedPivot code k) (representative (chosen k))).withOrbit
        (candidate a).orbit).ComplexityLE p) ∧
      ∀ a ∈ retained, ∀ k, (δ / (2 * Fintype.card Bin)) / (2 * coefficientBound) ≤
        ‖(C a).localLaw.complexMean (fun site =>
          star ((fixedTwist k).eval N poly (A.physical (C a).path site)) *
            ((external (kernelProjectionSelectedPivot code k) (representative (chosen k))).observable
              ((candidate a).siteValue site) *
                nativeValue k (A.boxedPhysical hξ1 (C a).path site)))‖ := by
  obtain ⟨chosen, fixedTwist, nativeValue, hnative, retained, hsub, hpos, hmass, hcomp, hcorr⟩ :=
    exists_external_kernel_precenter_native_point_partners D external representative hcomplex hnet
      input models (fun _ : X => 1) degree budget (fun x : integerBox N => x.val)
      (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
        (x : integerBox N) => twist.eval N poly x.val)
      (fun branch => (hmodels branch).1)
      (fun branch => (hmodels branch).2.1)
      (fun branch => (hmodels branch).2.2.1)
      (fun branch => (hmodels branch).2.2.2.2.2.1)
      hM hterm code outer H hH (fun a => (C a).localLaw)
      (fun a => (candidate a).siteValue) (fun a => A.boxedPhysical hξ1 (C a).path)
      hB hδ herror hinput hresidual hscore
  refine ⟨chosen, fixedTwist, nativeValue, hnative, retained, hsub, hpos, hmass,
    fun a k => hcomp k, ?_⟩
  intro a ha k
  convert hcorr a ha k using 1
  congr 2
  funext site
  simp only [boxedPhysical_val]
  ring

end AllocatedExternalCandidateSampler

end

end Erdos3.VectorPolynomial

end

end OAI
