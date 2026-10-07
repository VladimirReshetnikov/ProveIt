import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredL1Source

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_translated_physical_jet_probability_mass (m dim : ℕ) :
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
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
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
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → EuclideanJetLayers U O → ℝ)
    (_hg0 : ∀ a z, 0 ≤ g a z)
    (_hgi : ∀ a, Integrable (g a) (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))))
    (_hgmass : ∀ a, (∫ z, g a z ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) = 1)
    (f : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Cf : ℝ≥0) (_hf : LipschitzWith Lf f) (_hfb : ∀ z, ‖f z‖ ≤ Cf)
    (_hactual : ∀ z, law.complexMean (fun a => (g a z : ℂ)) = f (coveredJetAmbientTorus U 1 z))
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hCf : (Cf : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        law.mean (fun a => g a (physicalCubeRowSample U q rows p _hm
          (translatePhysicalCube base (standardPhysicalCubeOutput z))))) ≤ 1 + (2 * η + ε) := by
  obtain ⟨A, hA, hsample⟩ := exists_translated_physical_jet_l1_perturbation m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR G hG V hV hwidth
    Y _ law g hg0 hgi hgmass f Lf Cf hf hfb hactual η hη hdim hLf hCf hjet hηT
  have hnorm (z) : ‖f (coveredJetAmbientTorus U 1 z)‖ = law.mean (fun a => g a z) := by
    rw [← hactual, FiniteProbabilityWeights.complexMean_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (law.mean_nonneg (fun a => hg0 a z))]
  have hmass : (∫ z, ‖f (coveredJetAmbientTorus U 1 z) - 0‖
      ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ 1 := by
    simp only [sub_zero, hnorm]
    rw [law.integral_mean _ _ hgi]
    simp only [hgmass, law.mean_const, le_refl]
  obtain ⟨hZ, he⟩ := hsample rows hinj hrows hT hn hd U μ ν base p hp hm q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank hR G hG V hV hwidth
    f (fun _ => 0) Lf 0 Cf 0 hf (LipschitzWith.const 0) hfb (fun _ => by simp)
    hη hdim hLf (by positivity) hCf (by positivity) hjet hηT (fun _ => 0) measurable_const
    (δ := 0) (fun _ => by simp) hmass
  refine ⟨hZ, ?_⟩
  simpa only [sub_zero, hnorm, mul_zero, add_zero] using he

theorem exists_translated_physical_jet_probability_window_mass (m dim : ℕ) :
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
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
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
    {K : Type*} [Fintype K] (root : K → ℤ) (D : Matrix (Fin dim) K ℤ)
    (residue : ColumnResiduePattern (Option K) I stride)
    (Hwindow : I → ℝ) (_hHwindow : ∀ i, 0 < Hwindow i)
    (_hcoef : ∀ i t, (∑ k, |(physicalCubeCoefficient root D t k : ℝ)|) ≤ Hwindow i)
    (_hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hwindow i)
    (_hwidth : ∀ z : Option (Fin dim) × I, ρ * H z.2 ≤ referenceJetEnvelopeWidths stride Hwindow z)
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → EuclideanJetLayers U O → ℝ)
    (_hg0 : ∀ a z, 0 ≤ g a z)
    (_hgi : ∀ a, Integrable (g a) (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))))
    (_hgmass : ∀ a, (∫ z, g a z ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) = 1)
    (f : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Cf : ℝ≥0) (_hf : LipschitzWith Lf f) (_hfb : ∀ z, ‖f z‖ ≤ Cf)
    (_hactual : ∀ z, law.complexMean (fun a => (g a z : ℂ)) = f (coveredJetAmbientTorus U 1 z))
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hCf : (Cf : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T) (_hsmall : 2 * η + ε ≤ 3),
    (∑ v ∈ spatialWindow Hwindow 4, law.mean (fun a => g a (physicalCubeRowSample U q rows p _hm
      (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative stride residue) stride v)))) ≤
      (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × I)) *
        (∏ i, ∏ _t : Unit ⊕ Fin dim, Hwindow i) := by
  obtain ⟨A, hA, hsample⟩ := exists_translated_physical_jet_probability_mass m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR K _ root D residue Hwindow hHwindow hcoef hscale hwidth
    Y _ law g hg0 hgi hgmass f Lf Cf hf hfb hactual η hη hdim hLf hCf hjet hηT hsmall
  let target := columnResiduePattern stride (standardPhysicalCubeFrame
    (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride residue)))
  let V := referenceJetEnvelopeWidths (q := dim) stride Hwindow
  obtain ⟨hZ, he⟩ := hsample rows hinj hrows hT hn hd U μ ν base p hp hm q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank hR {target} (Finset.singleton_nonempty _)
    V (referenceJetEnvelopeWidths_pos stride hs Hwindow hHwindow) hwidth law g hg0 hgi hgmass
    f Lf Cf hf hfb hactual hη hdim hLf hCf hjet hηT
  have hraw := physicalReconstruction_sum_le_sampled_mass stride hs root D residue Hwindow hHwindow hcoef hscale
    (fun v => law.mean (fun a => g a (physicalCubeRowSample U q rows p hm (translatePhysicalCube base v))))
    (fun v => law.mean_nonneg (fun a => hg0 a _)) hZ
  rw [referenceJetEnvelope_volume stride hs Hwindow] at hraw
  have hvol : 0 ≤ (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × I) *
      (∏ i, ∏ _t : Unit ⊕ Fin dim, Hwindow i) := by
    apply mul_nonneg (pow_nonneg (div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le) _)
    exact Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun _ _ => (hHwindow i).le))
  have hfour := he.trans (show 1 + (2 * η + ε) ≤ 4 by linarith)
  have hout := hraw.trans (mul_le_mul_of_nonneg_left hfour hvol)
  simp_rw [← physicalResidueReconstruction_translate] at hout
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hout

theorem exists_translated_physical_jet_density_window_mass (m dim : ℕ) :
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
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
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
    {K : Type*} [Fintype K] (root : K → ℤ) (D : Matrix (Fin dim) K ℤ)
    (residue : ColumnResiduePattern (Option K) I stride)
    (Hwindow : I → ℝ) (_hHwindow : ∀ i, 0 < Hwindow i)
    (_hcoef : ∀ i t, (∑ k, |(physicalCubeCoefficient root D t k : ℝ)|) ≤ Hwindow i)
    (_hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hwindow i)
    (_hwidth : ∀ z : Option (Fin dim) × I, ρ * H z.2 ≤ referenceJetEnvelopeWidths stride Hwindow z)
    (g : EuclideanJetLayers U O → ℝ)
    (_hg0 : ∀ z, 0 ≤ g z)
    (_hgi : Integrable g (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))))
    (_hgmass : (∫ z, g z ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) = 1)
    (f : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Cf : ℝ≥0) (_hf : LipschitzWith Lf f) (_hfb : ∀ z, ‖f z‖ ≤ Cf)
    (_hactual : ∀ z, (g z : ℂ) = f (coveredJetAmbientTorus U 1 z))
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hCf : (Cf : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T) (_hsmall : 2 * η + ε ≤ 3),
    (∑ v ∈ spatialWindow Hwindow 4, g (physicalCubeRowSample U q rows p _hm
      (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative stride residue) stride v))) ≤
      (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × I)) *
        (∏ i, ∏ _t : Unit ⊕ Fin dim, Hwindow i) := by
  obtain ⟨A, hA, hsample⟩ := exists_translated_physical_jet_probability_window_mass m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR K _ root D residue Hwindow hHwindow hcoef hscale hwidth
    g hg0 hgi hgmass f Lf Cf hf hfb hactual η hη hdim hLf hCf hjet hηT hsmall
  let law : FiniteProbabilityWeights Unit := {
    weight := fun _ => 1
    nonneg := fun _ => zero_le_one
    total := by simp }
  have he := hsample rows hinj hrows hT hn hd U μ ν base p hp hm q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank hR root D residue Hwindow hHwindow hcoef hscale hwidth
    law (fun _ => g) (fun _ => hg0) (fun _ => hgi) (fun _ => hgmass) f Lf Cf hf hfb
    (fun z => by simpa only [law.complexMean_const] using hactual z)
    hη hdim hLf hCf hjet hηT hsmall
  simpa only [law.mean_const] using he

end Erdos3.BooleanCubeKernel

end

end OAI
