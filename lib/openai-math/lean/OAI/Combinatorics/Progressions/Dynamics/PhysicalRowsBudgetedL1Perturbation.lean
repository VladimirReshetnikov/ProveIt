import OAI.Combinatorics.Progressions.Estimates.PhysicalRowsCoveredL1Perturbation
import OAI.Combinatorics.Progressions.Sampling.AmbientL1SamplingBudget

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_physical_jet_l1_perturbation_budgeted (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hLg : (Lg : ℝ) ≤ Real.exp T)
    (_hCf : (Cf : ℝ) ≤ Real.exp T) (_hCg : (Cg : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T)
    (ideal : EuclideanJetLayers U O → ℂ) (_hi : Measurable ideal)
    {δ : ℝ} (_happrox : ∀ y, ‖ideal y - g (coveredJetAmbientTorus U 1 y)‖ ≤ δ)
    {E : ℝ} (_hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - ideal y‖
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coveredJetAmbientTorus U 1
          (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z))) -
          ideal (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z))‖) ≤ E + 2 * δ + (2 * η + ε) := by
  obtain ⟨A₀, hA₀, hsample⟩ := exists_physical_jet_covered_l1_perturbation m dim
  obtain ⟨A, hA, hthreshold⟩ := exists_ambientL1SamplingThreshold_bound A₀
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η hη hdim hLf hLg hCf hCg hjet hηT ideal hi δ happ E hmass
  obtain ⟨hQ, hTQ, hTP, hLip, hηQ, hfreq, hcoeff⟩ :=
    ambientL1SamplingBudget_bounds hT hLf hLg hCf hCg hjet hηT
  have heTP := Real.exp_le_exp.mpr hTP
  have hlarge := Real.exp_le_exp.mpr (hthreshold T hT)
  exact hsample rows hinj hrows (hT.trans hTP) (hn.trans hTP) (hd.trans hTP) U μ ν p hp hm
    q hq (hqT.trans heTP) stride hs hS (hST.trans heTP) hρ hε
    (hρT.trans heTP) (hεT.trans heTP) hstride H (fun i => hlarge.trans (hsize i)) hrank
    (hlarge.trans hR) G hG V hV hwidth f g Lf Lg Cf Cg hf hg hfb hgb
    hη hQ (hdim.trans hTQ) hLip hηQ hfreq hcoeff ideal hi happ hmass

end Erdos3.BooleanCubeKernel

end

end OAI
