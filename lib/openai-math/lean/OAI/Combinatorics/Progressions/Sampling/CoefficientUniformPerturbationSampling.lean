import OAI.Combinatorics.Progressions.Estimates.CoefficientCoverSampleTower
import OAI.Combinatorics.Progressions.Estimates.CoefficientPairCover
import OAI.Combinatorics.Progressions.Estimates.ComplexSampledSquarePerturbation

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_coefficient_ambient_cover_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
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
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (L B : ℝ≥0) (_hf : LipschitzWith L f) (_hb : ∀ y, ‖f y‖ ≤ B)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q)
    (_hLQ : (L : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) * B ≤ Real.exp P),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        f (coefficientAmbientTorus U (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ))))) -
      (∫ x, f (coefficientAmbientTorus U x) ∂μ)‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_cover_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U _ _ μ _ _ p hp hm q hq hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f L B hf hb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP
  obtain ⟨F, inst, frequency, coeff, _, hfreq, hcoeff, happ⟩ :=
    exists_ambient_torus_fourier_approximation f L B hf hb hη hQ hdim hLQ hηQ
  let _ := inst
  have hcont : Continuous (coefficientAmbientTorus (K := K) U) := by
    apply continuous_pi
    intro a
    exact (continuous_apply a.2).comp ((subspaceAmbientTorus_continuous (U a.1.1)).comp
      ((continuous_apply a.1).comp (coefficientCoordinateTorus_continuous U)))
  have hi : Integrable (fun x => f (coefficientAmbientTorus U x)) μ :=
    Integrable.of_bound (hf.continuous.comp hcont).measurable.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun x => hb _))
  have he (x) : ‖f (coefficientAmbientTorus U x) - coefficientTorusFourierSum U
      (fun a => coefficientSlotFrequency (fun s i => frequency a ⟨s,i⟩)) coeff x‖ ≤ η := by
    simpa only [coefficientAmbientTorus_character, coefficientTorusFourierSum] using happ (coefficientAmbientTorus U x)
  exact hcomparison hP hn hd U μ (Real.exp_nonneg _) hfreqP
    (fun a => coefficientSlotFrequency (fun s i => frequency a ⟨s,i⟩))
    (fun a => coefficientSlotFrequency_bound _ (fun s i => hfreq a ⟨s,i⟩)) coeff
    (mul_nonneg (Real.exp_nonneg _) B.coe_nonneg) hcoeffP hcoeff p hp hm q hq hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun x => f (coefficientAmbientTorus U x)) hi hη.le he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_coefficient_ambient_pair_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (a b D : ℕ) (_ha : 0 < a) (_hb : 0 < b) (_hD : 0 < D) (_hdiv : a * b ∣ D)
    (_hqP : ((a * b : ℕ) : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (Lf Lg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ 1) (_hgb : ∀ y, ‖g y‖ ≤ 1)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q)
    (_hLQ : ((Lf * b + Lg * a : ℝ≥0) : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) ≤ Real.exp P),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (f (coefficientAmbientTorus U (affineCoefficientCoverSample U p _hm a (fun k j => (z (k, j) : ℝ)))) *
          star (g (coefficientAmbientTorus U (affineCoefficientCoverSample U p _hm b (fun k j => (z (k, j) : ℝ))))))) -
      (∫ x, f ((D / a) • coefficientAmbientTorus U x) * star (g ((D / b) • coefficientAmbientTorus U x)) ∂μ)‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_ambient_cover_sampling m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U _ _ _ μ _ _ p hp hm a b D ha hb hD hdiv hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg hf hg hfb hgb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP
  let pair := fun z => f (b • z) * star (g (a • z))
  have hpair := ambient_pair_lipschitz b a f g hf hg hfb hgb
  obtain ⟨hZ, he⟩ := hsample hP hn hd U μ p hp hm (a * b) (Nat.mul_pos ha hb) hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    pair (Lf * b + Lg * a) 1 hpair.1 hpair.2 hη hQ hdim hLQ hηQ hfreqP
    (by simpa only [NNReal.coe_one, mul_one] using hcoeffP)
  have hfa (z : Option K → I → ℝ) :
      b • coefficientAmbientTorus U (affineCoefficientCoverSample U p hm (a * b) z) =
        coefficientAmbientTorus U (affineCoefficientCoverSample U p hm a z) := by
    simpa only [coefficientAmbientTorus_cover, mul_comm b a] using
      congrArg (coefficientAmbientTorus U) (affineCoefficientCoverSample_product_projection U p hm b a hb z)
  have hgb' (z : Option K → I → ℝ) :
      a • coefficientAmbientTorus U (affineCoefficientCoverSample U p hm (a * b) z) =
        coefficientAmbientTorus U (affineCoefficientCoverSample U p hm b z) := by
    simpa only [coefficientAmbientTorus_cover] using
      congrArg (coefficientAmbientTorus U) (affineCoefficientCoverSample_product_projection U p hm a b ha z)
  refine ⟨hZ, ?_⟩
  rw [coefficientAmbient_pair_integral_divisors U μ D a b hD ha hb hdiv f g hf.continuous hg.continuous]
  simpa only [pair, hfa, hgb'] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_coefficient_ambient_square_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    {T : Type*} [Fintype T] (period : T → ℕ) (_hperiod : ∀ t, 0 < period t)
    (D : ℕ) (_hD : 0 < D) (_hdiv : ∀ a b, period a * period b ∣ D)
    (_hqP : ∀ a b, ((period a * period b : ℕ) : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (_hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x)
    (coeff : T → ℂ) (f : T → (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (L : T → ℝ≥0) (_hf : ∀ t, LipschitzWith (L t) (f t)) (_hfb : ∀ t y, ‖f t y‖ ≤ 1)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q)
    (_hLQ : ∀ a b, ((L a * period b + L b * period a : ℝ≥0) : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) ≤ Real.exp P),
    |selectedResidueDensityMass stride G V (fun z =>
        ‖∑ t, coeff t * f t (coefficientAmbientTorus U
          (affineCoefficientCoverSample U p _hm (period t) (fun k j => (z (k,j) : ℝ))))‖ ^ 2) -
      ∫ x, ‖∑ t, coeff t * f t ((D / period t) • coefficientAmbientTorus U x)‖ ^ 2 ∂μ| ≤
        (∑ t, ‖coeff t‖) ^ 2 * (2 * η + ε) := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_ambient_pair_sampling m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U _ _ _ μ _ _ p hp hm T _ period hperiod D hD hdiv hqP
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    hZ coeff f L hf hfb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP
  let law := selectedResidueSmoothPMF stride G V hV hZ
  let sampled := fun t (z : Option K × I → ℤ) => f t (coefficientAmbientTorus U
    (affineCoefficientCoverSample U p hm (period t) (fun k j => (z (k,j) : ℝ))))
  let reference := fun t (x : CoefficientTorus (K := K) U) =>
    f t ((D / period t) • coefficientAmbientTorus U x)
  have hsb (t z) : ‖sampled t z‖ ≤ 1 := hfb t _
  have hrb (t z) : ‖reference t z‖ ≤ 1 := hfb t _
  have hrc (t) : Continuous (reference t) :=
    (hf t).continuous.comp ((coefficientAmbientTorus_continuous U).nsmul (D / period t))
  have hsi (a b) : Integrable (fun z => sampled a z * star (sampled b z)) law.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by
        rw [norm_mul, norm_star]
        exact (mul_le_mul (hsb a z) (hsb b z) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)))
  have hri (a b) : Integrable (fun z => reference a z * star (reference b z)) μ :=
    Integrable.of_bound ((hrc a).mul (hrc b).star).measurable.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by
        rw [norm_mul, norm_star]
        exact (mul_le_mul (hrb a z) (hrb b z) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)))
  have hpair (a b) : ‖(∫ z, sampled a z * star (sampled b z) ∂law.toMeasure) -
      ∫ z, reference a z * star (reference b z) ∂μ‖ ≤ 2 * η + ε := by
    obtain ⟨_, he⟩ := hsample hP hn hd U μ p hp hm (period a) (period b) D
      (hperiod a) (hperiod b) hD (hdiv a b) (hqP a b) stride hs
      hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
      (f a) (f b) (L a) (L b) (hf a) (hf b) (hfb a) (hfb b)
      hη hQ hdim (hLQ a b) hηQ hfreqP hcoeffP
    rw [PMF.integral_eq_tsum law _ (hsi a b)]
    simpa only [Complex.real_smul] using he
  have hbound (z) : ‖∑ t, coeff t * sampled t z‖ ≤ ∑ t, ‖coeff t‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _ => ?_))
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hsb t z)
  have hi : Integrable (fun z => ‖∑ t, coeff t * sampled t z‖ ^ 2) law.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((∑ t, ‖coeff t‖) ^ 2)
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound z) 2))
  rw [selectedResidueDensityMass_integral stride G V hV hZ _ hi]
  exact finiteComplex_l2_integral_comparison law.toMeasure μ coeff sampled reference hsi hri hpair

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_coefficient_ambient_l1_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
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
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q)
    (_hLQ : ((Lf + Lg : ℝ≥0) : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P)
    {E : ℝ} (_hmass : (∫ x, ‖f (coefficientAmbientTorus U x) -
      g (coefficientAmbientTorus U x)‖ ∂μ) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coefficientAmbientTorus U (affineCoefficientCoverSample U p _hm q
          (fun k j => (z (k,j) : ℝ)))) -
          g (coefficientAmbientTorus U (affineCoefficientCoverSample U p _hm q
            (fun k j => (z (k,j) : ℝ))))‖) ≤ E + 2 * η + ε := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_ambient_cover_sampling m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U _ _ μ _ _ p hp hm q hq hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP E hmass
  let error := fun z => ‖f z - g z‖
  have hl : LipschitzWith (Lf + Lg) error := by
    simpa only [one_mul, Function.comp_def, Pi.sub_apply] using
      lipschitzWith_one_norm.comp (hf.sub hg)
  have hb (z) : error z ≤ (Cf + Cg : ℝ≥0) :=
    (norm_sub_le _ _).trans (add_le_add (hfb z) (hgb z))
  have hlc : LipschitzWith (Lf + Lg) (fun z => (error z : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [Complex.isometry_ofReal.dist_eq]
    exact hl.dist_le_mul z w
  have hbc (z) : ‖(error z : ℂ)‖ ≤ (Cf + Cg : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ error z from norm_nonneg _)]
    exact hb z
  obtain ⟨hZ, he⟩ := hsample hP hn hd U μ p hp hm q hq hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun z => (error z : ℂ)) (Lf + Lg) (Cf + Cg) hlc hbc hη hQ hdim hLQ hηQ hfreqP hcoeffP
  refine ⟨hZ, ?_⟩
  let law := selectedResidueSmoothPMF stride G V hV hZ
  let sample := fun z : Option K × I → ℤ =>
    error (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm q
      (fun k j => (z (k,j) : ℝ))))
  have hi : Integrable sample law.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (Cf + Cg : ℝ≥0)
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hb _))
  have he' : ‖(∫ z, (sample z : ℂ) ∂law.toMeasure) -
      ∫ x, (error (coefficientAmbientTorus U x) : ℂ) ∂μ‖ ≤ 2 * η + ε := by
    rw [PMF.integral_eq_tsum law _ hi.ofReal]
    simpa only [Complex.real_smul] using he
  rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at he'
  rw [selectedResidueDensityMass_integral stride G V hV hZ _ hi]
  have hle := (le_abs_self _).trans he'
  linarith only [hle, hmass]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_coefficient_ambient_perturbation_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    {T : Type*} [Fintype T] (period : T → ℕ) (_hperiod : ∀ t, 0 < period t)
    (D : ℕ) (_hD : 0 < D) (_hdiv : ∀ a b, period a * period b ∣ D)
    (_hqP : ∀ a b, ((period a * period b : ℕ) : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (_hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x)
    (coeff : T → ℂ) (f : T → (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (L : T → ℝ≥0) (_hf : ∀ t, LipschitzWith (L t) (f t)) (_hfb : ∀ t y, ‖f t y‖ ≤ 1)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q)
    (_hLQ : ∀ a b, ((L a * period b + L b * period a : ℝ≥0) : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) ≤ Real.exp P)
    (actual : (Option K × I → ℤ) → ℂ)
    (reference : CoefficientTorus (K := K) U → ℂ)
    (_href : Integrable (fun z => ‖reference z‖ ^ 2) μ)
    {δ E : ℝ} (_hδ : 0 ≤ δ) (_hE : (∫ z, ‖reference z‖ ^ 2 ∂μ) ≤ E)
    (_hactual : ∀ z, ‖actual z - ∑ t, coeff t * f t (coefficientAmbientTorus U
      (affineCoefficientCoverSample U p _hm (period t) (fun k j => (z (k,j) : ℝ))))‖ ≤ δ)
    (_hreference : ∀ z, ‖reference z - ∑ t, coeff t * f t ((D / period t) • coefficientAmbientTorus U z)‖ ≤ δ),
    selectedResidueDensityMass stride G V (fun z => ‖actual z‖ ^ 2) ≤
      6 * δ ^ 2 + 4 * E + 2 * (∑ t, ‖coeff t‖) ^ 2 * (2 * η + ε) := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_ambient_square_sampling m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U _ _ _ μ _ _ p hp hm T _ period hperiod D hD hdiv hqP
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    hZ coeff f L hf hfb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP
    actual reference href δ E hδ hE hactual hreference
  let law := selectedResidueSmoothPMF stride G V hV hZ
  let sampled := fun (z : Option K × I → ℤ) => ∑ t, coeff t * f t (coefficientAmbientTorus U
    (affineCoefficientCoverSample U p hm (period t) (fun k j => (z (k,j) : ℝ))))
  let referenceSum := fun z : CoefficientTorus (K := K) U =>
    ∑ t, coeff t * f t ((D / period t) • coefficientAmbientTorus U z)
  have hrc : Continuous referenceSum := continuous_finsetSum _ (fun t _ =>
    continuous_const.mul ((hf t).continuous.comp ((coefficientAmbientTorus_continuous U).nsmul _)))
  have hbound (z) : ‖sampled z‖ ≤ ∑ t, ‖coeff t‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _ => ?_))
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hfb t _)
  have hi : Integrable (fun z => ‖sampled z‖ ^ 2) law.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((∑ t, ‖coeff t‖) ^ 2)
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound z) 2))
  have hai : Integrable (fun z => ‖actual z‖ ^ 2) law.toMeasure := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      ((δ + ∑ t, ‖coeff t‖) ^ 2)
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    calc
      ‖actual z‖ ≤ ‖actual z - sampled z‖ + ‖sampled z‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := add_le_add (hactual z) (hbound z)
  have he := hsample hP hn hd U μ p hp hm period hperiod D hD hdiv hqP
    stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth hZ
    coeff f L hf hfb hη hQ hdim hLQ hηQ hfreqP hcoeffP
  change |selectedResidueDensityMass stride G V (fun z => ‖sampled z‖ ^ 2) -
    ∫ z, ‖referenceSum z‖ ^ 2 ∂μ| ≤ _ at he
  rw [selectedResidueDensityMass_integral stride G V hV hZ _ hi] at he
  have hr := complex_square_integral_uniform_perturbation μ reference referenceSum (fun _ => 0)
    hrc.measurable measurable_const
    (fun z => by simpa only [norm_sub_rev] using hreference z)
    (by simpa only [sub_zero] using href) (by simpa only [sub_zero] using hE)
  simp only [sub_zero] at hr
  have hsamp : (∫ z, ‖sampled z‖ ^ 2 ∂law.toMeasure) ≤
      2 * δ ^ 2 + 2 * E + (∑ t, ‖coeff t‖) ^ 2 * (2 * η + ε) := by
    have ht := (le_abs_self _).trans he
    linarith
  have ha := complex_square_integral_uniform_perturbation law.toMeasure sampled actual (fun _ => 0)
    (measurable_of_countable _) measurable_const hactual
    (by simpa only [sub_zero] using hi) (by simpa only [sub_zero] using hsamp)
  simp only [sub_zero] at ha
  rw [selectedResidueDensityMass_integral stride G V hV hZ _ hai]
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def coefficientSquareInputBudget {A : Type*} [Semiring A] (P : A) : A :=
  let Q := 2 * P + 4
  2 * Q * (2 * Q + 2) ^ 4 + 2 * P + 4

theorem exists_coefficient_uniform_square_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ}, 0 ≤ P → (Fintype.card I : ℝ) ≤ P →
    (Fintype.card (Option K × I) : ℝ) ≤ P →
    (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ P →
    ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) →
    ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {T : Type*} [Fintype T] (period : T → ℕ), (∀ t, 0 < period t) →
    (∀ t, (period t : ℝ) ≤ Real.exp P) →
    ∀ (D : ℕ), 0 < D → (∀ a b, period a * period b ∣ D) →
    ∀ (stride : I → ℕ), (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp P) →
    ∀ {R ρ ε : ℝ}, 0 < ρ → 0 < ε → 1 / ρ ≤ Real.exp P → 1 / ε ≤ Real.exp P →
    ∀ (H : I → ℝ), (∀ i, Real.exp ((P + A) ^ A) ≤ H i) →
    (∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j)) →
    Real.exp ((P + A) ^ A) ≤ R →
    ∀ (G : Finset (ColumnResiduePattern (Option K) I stride)), G.Nonempty →
    ∀ (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z), (∀ z, ρ * H z.2 ≤ V z) →
    (0 < ∑' z, selectedResidueSmoothWeight stride G V z) →
    ∀ (coeff : T → ℂ) (f : T → (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (L : T → ℝ≥0), (∀ t, LipschitzWith (L t) (f t)) → (∀ t z, ‖f t z‖ ≤ 1) →
    (∀ t, (L t : ℝ) ≤ Real.exp P) →
    |selectedResidueDensityMass stride G V (fun z =>
      ‖∑ t, coeff t * f t (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm (period t)
        (fun k j => (z (k,j) : ℝ))))‖ ^ 2) -
      ∫ z, ‖∑ t, coeff t * f t ((D / period t) • coefficientAmbientTorus U z)‖ ^ 2 ∂μ| ≤
      (∑ t, ‖coeff t‖) ^ 2 * ε := by
  obtain ⟨A₀, _, hsample⟩ := exists_coefficient_ambient_square_sampling m
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    ((coefficientSquareInputBudget (Polynomial.X : Polynomial ℕ) + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd hdim U _ _ _ μ _ _ p hp hm T _ period hperiod hperiodP D hD hdiv
    stride hs hstride R ρ ε hρ hε hρP hεP H hsize hrank hR G hG V hV hwidth hZ coeff f L hf hfb hLP
  let Q := 2 * P + 4
  let B := coefficientSquareInputBudget P
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hPQ : P ≤ Q := by dsimp [Q]; linarith
  have hBeq : B = 2 * Q * (2 * Q + 2) ^ 4 + Q := by
    dsimp only [B, coefficientSquareInputBudget, Q]
    ring
  have hQB : Q ≤ B := by
    rw [hBeq]
    exact le_add_of_nonneg_left (by positivity)
  have hPB : P ≤ B := hPQ.trans hQB
  have hB : 0 ≤ B := hP.trans hPB
  have hePB := Real.exp_le_exp.mpr hPB
  have hfreq : (2 * Q + 2) ^ 4 ≤ B := by
    have hQ1 : 1 ≤ 2 * Q := by dsimp [Q]; linarith
    have hh := mul_le_mul_of_nonneg_right hQ1 (pow_nonneg (by linarith : 0 ≤ 2 * Q + 2) 4)
    dsimp [B, coefficientSquareInputBudget] at *
    dsimp [Q] at *
    nlinarith
  have hcoeff : 2 * Q * (2 * Q + 2) ^ 4 ≤ B := by
    rw [hBeq]
    exact le_add_of_nonneg_right hQ
  have hcost : (B + A₀) ^ A₀ ≤ (P + A) ^ A := by
    simpa [B, coefficientSquareInputBudget, Polynomial.eval₂_pow] using hbudget P hP
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hi4 : 1 / (ε / 4) ≤ Real.exp Q := by
    calc
      _ = 4 * (1 / ε) := by ring
      _ ≤ Real.exp 4 * Real.exp P := mul_le_mul h4 hεP (by positivity) (Real.exp_pos _).le
      _ = Real.exp (4 + P) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [Q]; linarith)
  have hi2 : 1 / (ε / 2) ≤ Real.exp B := by
    have hh : 1 / (ε / 2) ≤ 1 / (ε / 4) := by
      rw [one_div_div, one_div_div]
      exact div_le_div_of_nonneg_right (by norm_num) hε.le
    exact hh.trans (hi4.trans (Real.exp_le_exp.mpr hQB))
  have hpair (a b) : ((period a * period b : ℕ) : ℝ) ≤ Real.exp B := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul (hperiodP a) (hperiodP b) (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [Q] at hQB; linarith)
  have hpairL (a b) : ((L a * period b + L b * period a : ℝ≥0) : ℝ) ≤ Real.exp Q := by
    have h1 := mul_le_mul (hLP a) (hperiodP b) (Nat.cast_nonneg _) (Real.exp_pos _).le
    have h2 := mul_le_mul (hLP b) (hperiodP a) (Nat.cast_nonneg _) (Real.exp_pos _).le
    calc
      _ ≤ 2 * (Real.exp P * Real.exp P) := by simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast]; linarith
      _ ≤ Real.exp 4 * Real.exp (2 * P) := by
        rw [show Real.exp (2 * P) = Real.exp P * Real.exp P by rw [← Real.exp_add]; congr 1; ring]
        gcongr
        linarith
      _ = Real.exp Q := by rw [← Real.exp_add]; congr 1; dsimp [Q]; ring
  have hh := hsample hB (hn.trans hPB) (hd.trans hPB) U μ p hp hm period hperiod D hD hdiv hpair
    stride hs (Real.exp_pos P).le hePB hρ (by positivity : 0 < ε / 2) (hρP.trans hePB) hi2 hstride
    H (fun i => (Real.exp_le_exp.mpr hcost).trans (hsize i)) hrank
    ((Real.exp_le_exp.mpr hcost).trans hR) G hG V hV hwidth hZ coeff f L hf hfb
    (by positivity : 0 < ε / 4) hQ (hdim.trans hPQ) hpairL
    (by simpa only [one_div] using hi4) (Real.exp_le_exp.mpr hfreq) (Real.exp_le_exp.mpr hcoeff)
  convert hh using 1
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_coefficient_uniform_perturbation_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ}, 0 ≤ P → (Fintype.card I : ℝ) ≤ P →
    (Fintype.card (Option K × I) : ℝ) ≤ P →
    (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ P →
    ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) →
    ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {T : Type*} [Fintype T] (period : T → ℕ), (∀ t, 0 < period t) →
    (∀ t, (period t : ℝ) ≤ Real.exp P) →
    ∀ (D : ℕ), 0 < D → (∀ a b, period a * period b ∣ D) →
    ∀ (stride : I → ℕ), (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp P) →
    ∀ {R ρ ε : ℝ}, 0 < ρ → 0 < ε → 1 / ρ ≤ Real.exp P → 1 / ε ≤ Real.exp P →
    ∀ (H : I → ℝ), (∀ i, Real.exp ((P + A) ^ A) ≤ H i) →
    (∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j)) →
    Real.exp ((P + A) ^ A) ≤ R →
    ∀ (G : Finset (ColumnResiduePattern (Option K) I stride)), G.Nonempty →
    ∀ (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z), (∀ z, ρ * H z.2 ≤ V z) →
    (0 < ∑' z, selectedResidueSmoothWeight stride G V z) →
    ∀ (coeff : T → ℂ) (f : T → (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (L : T → ℝ≥0), (∀ t, LipschitzWith (L t) (f t)) → (∀ t z, ‖f t z‖ ≤ 1) →
    (∀ t, (L t : ℝ) ≤ Real.exp P) →
    ∀ (actual : (Option K × I → ℤ) → ℂ)
    (reference : CoefficientTorus (K := K) U → ℂ),
    Integrable (fun z => ‖reference z‖ ^ 2) μ →
    ∀ {δ E : ℝ}, (∫ z, ‖reference z‖ ^ 2 ∂μ) ≤ E →
    (∀ z, ‖actual z - ∑ t, coeff t * f t (coefficientAmbientTorus U
      (affineCoefficientCoverSample U p hm (period t) (fun k j => (z (k,j) : ℝ))))‖ ≤ δ) →
    (∀ z, ‖reference z - ∑ t, coeff t * f t ((D / period t) • coefficientAmbientTorus U z)‖ ≤ δ) →
    selectedResidueDensityMass stride G V (fun z => ‖actual z‖ ^ 2) ≤
      6 * δ ^ 2 + 4 * E + 2 * (∑ t, ‖coeff t‖) ^ 2 * ε := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_uniform_square_sampling m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd hdim U _ _ _ μ _ _ p hp hm T _ period hperiod hperiodP D hD hdiv
    stride hs hstride R ρ ε hρ hε hρP hεP H hsize hrank hR G hG V hV hwidth hZ coeff f L hf hfb hLP
    actual reference href δ E hE hactual hreference
  let law := selectedResidueSmoothPMF stride G V hV hZ
  let sampled := fun (z : Option K × I → ℤ) => ∑ t, coeff t * f t (coefficientAmbientTorus U
    (affineCoefficientCoverSample U p hm (period t) (fun k j => (z (k,j) : ℝ))))
  let referenceSum := fun z : CoefficientTorus (K := K) U =>
    ∑ t, coeff t * f t ((D / period t) • coefficientAmbientTorus U z)
  have hrc : Continuous referenceSum := continuous_finsetSum _ (fun t _ =>
    continuous_const.mul ((hf t).continuous.comp ((coefficientAmbientTorus_continuous U).nsmul _)))
  have hbound (z) : ‖sampled z‖ ≤ ∑ t, ‖coeff t‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _ => ?_))
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hfb t _)
  have hi : Integrable (fun z => ‖sampled z‖ ^ 2) law.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((∑ t, ‖coeff t‖) ^ 2)
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound z) 2))
  have hai : Integrable (fun z => ‖actual z‖ ^ 2) law.toMeasure := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      ((δ + ∑ t, ‖coeff t‖) ^ 2)
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    calc
      ‖actual z‖ ≤ ‖actual z - sampled z‖ + ‖sampled z‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := add_le_add (hactual z) (hbound z)
  have he := hsample hP hn hd hdim U μ p hp hm period hperiod hperiodP D hD hdiv
    stride hs hstride hρ hε hρP hεP H hsize hrank hR G hG V hV hwidth hZ coeff f L hf hfb hLP
  change |selectedResidueDensityMass stride G V (fun z => ‖sampled z‖ ^ 2) -
    ∫ z, ‖referenceSum z‖ ^ 2 ∂μ| ≤ _ at he
  rw [selectedResidueDensityMass_integral stride G V hV hZ _ hi] at he
  have hr := complex_square_integral_uniform_perturbation μ reference referenceSum (fun _ => 0)
    hrc.measurable measurable_const
    (fun z => by simpa only [norm_sub_rev] using hreference z)
    (by simpa only [sub_zero] using href) (by simpa only [sub_zero] using hE)
  simp only [sub_zero] at hr
  have hsamp : (∫ z, ‖sampled z‖ ^ 2 ∂law.toMeasure) ≤
      2 * δ ^ 2 + 2 * E + (∑ t, ‖coeff t‖) ^ 2 * ε := by
    have ht := (le_abs_self _).trans he
    linarith
  have ha := complex_square_integral_uniform_perturbation law.toMeasure sampled actual (fun _ => 0)
    (measurable_of_countable _) measurable_const hactual
    (by simpa only [sub_zero] using hi) (by simpa only [sub_zero] using hsamp)
  simp only [sub_zero] at ha
  rw [selectedResidueDensityMass_integral stride G V hV hZ _ hai]
  linarith

end Erdos3.VectorPolynomial

end

end OAI
