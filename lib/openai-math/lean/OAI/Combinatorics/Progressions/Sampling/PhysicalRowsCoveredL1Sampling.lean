import OAI.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_physical_jet_covered_l1_sampling (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ P)
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
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Q)
    (_hLQ : (((Lf + Lg) * ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P)
    {E : ℝ} (_hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) -
      g (coveredJetAmbientTorus U 1 y)‖
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coveredJetAmbientTorus U 1
          (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z))) -
          g (coveredJetAmbientTorus U 1
            (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z)))‖) ≤ E + 2 * η + ε := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_ambient_l1_sampling m
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows P hP hn hd U _ _ _ μ _ _ ν _ _ p hp hm q hq hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP E hmass
  let jet := coefficientAmbientRowsJet (J := J) rows
  let Ljet : ℝ≥0 := ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0)
  have hjet : LipschitzWith Ljet jet := coefficientAmbientRowsJet_lipschitz rows
  have hhaar : (∫ x, ‖f (jet (coefficientAmbientTorus U x)) -
      g (jet (coefficientAmbientTorus U x))‖ ∂μ) ≤ E := by
    let error := fun y => ‖f (coveredJetAmbientTorus U 1 y) - g (coveredJetAmbientTorus U 1 y)‖
    let rowJet := euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin dim) (Fin dim) ℤ) rows
    have hperiod : integerScalarLattice (Fin dim) (1 : ℤ) ≤
        (1 : Matrix (Fin dim) (Fin dim) ℤ).mulVecLin.range := by
      intro v _
      exact ⟨v, by simp⟩
    have hp := euclideanCoefficientJetMap_measurePreserving U (fun _ => 0)
      (1 : Matrix (Fin dim) (Fin dim) ℤ) 1 one_ne_zero hperiod rows hinj hrows μ ν
    have he : AEStronglyMeasurable error (Measure.map rowJet μ) := by
      rw [hp.map_eq]
      exact (((hf.continuous.comp (coveredJetAmbientTorus_continuous U 1)).sub
        (hg.continuous.comp (coveredJetAmbientTorus_continuous U 1))).norm).aestronglyMeasurable
    have hi := (integral_map hp.measurable.aemeasurable he).symm
    rw [hp.map_eq] at hi
    simp only [jet, coefficientAmbientRowsJet_eq]
    exact hi.trans_le hmass
  have hLip : (((Lf * Ljet + Lg * Ljet : ℝ≥0) : ℝ)) ≤ Real.exp Q := by
    simpa only [add_mul] using hLQ
  obtain ⟨hZ, he⟩ := hsample hP hn hd U μ p hp hm q hq hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun z => f (jet z)) (fun z => g (jet z)) (Lf * Ljet) (Lg * Ljet) Cf Cg
    (hf.comp hjet) (hg.comp hjet) (fun z => hfb _) (fun z => hgb _)
    hη hQ hdim hLip hηQ hfreqP hcoeffP hhaar
  refine ⟨hZ, ?_⟩
  have hid (z : Option (Fin dim) × I → ℤ) :
      jet (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm q
        (fun k j => (z (k,j) : ℝ)))) =
      coveredJetAmbientTorus U 1
        (physicalCubeRowSample U q rows p hm (standardPhysicalCubeOutput z)) :=
    (coefficientAmbientRowsJet_eq rows U _).trans
      (congrArg (coveredJetAmbientTorus U 1) (by
        have he : standardPhysicalCubeFrame (standardPhysicalCubeOutput z) = z := by
          funext t
          rcases t with ⟨k, x⟩
          cases k <;> rfl
        simpa only [he] using
          coefficientCoverSample_physicalRows U q p hp hm rows (standardPhysicalCubeOutput z)))
  simpa only [hid] using he

end Erdos3.BooleanCubeKernel

end

end OAI
