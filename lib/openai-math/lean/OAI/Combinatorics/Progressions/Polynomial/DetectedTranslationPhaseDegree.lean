import OAI.Combinatorics.Progressions.Estimates.DetectedTranslationNormalizedLogBounds
import OAI.Combinatorics.Progressions.Geometry.TranslationLogCoordinateHomogeneous
import OAI.Combinatorics.Progressions.Geometry.TranslationLogCoordinateScaling

namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weightedSupportDrop_pderiv {w : σ → ℕ} {n r : ℕ}
    {P : MvPolynomial σ R} (hP : P ∈ weightedSupportDrop w n r) (i : σ) :
    pderiv i P ∈ weightedSupportDrop w n (r + w i) := by
  classical
  intro a ha
  have ha' : a + Finsupp.single i 1 ∈ P.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    have hn : (pderiv i P).coeff a ≠ 0 := MvPolynomial.mem_support_iff.mp ha
    rw [coeff_pderiv, hz, zero_mul] at hn
    exact hn rfl
  have hh := hP ha'
  change Finsupp.weight w (a + Finsupp.single i 1) + r ≤ n at hh
  rw [map_add, Finsupp.weight_single, one_smul] at hh
  change Finsupp.weight w a + (r + w i) ≤ n
  omega

variable {U B : Type*} [Fintype B]

theorem translationDirectionalDerivative_mem_weightedSupportDrop
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, b i ∈ weightedSupportLE v (w i))
    {d r : ℕ} {P : MvPolynomial (U ⊕ B) ℝ}
    (hP : P ∈ weightedSupportDrop (Sum.elim v w) d r) :
    translationDirectionalDerivative b P ∈ weightedSupportDrop (Sum.elim v w) d r := by
  rw [translationDirectionalDerivative_apply]
  apply (weightedSupportDrop (Sum.elim v w) d r).sum_mem
  intro i _
  have hb' : rename Sum.inl (b i) ∈ weightedSupportLE (Sum.elim v w) (w i) := by
    rw [← weightedSupportDrop_zero] at ⊢
    exact weightedSupportDrop_rename Sum.inl (fun _ => rfl)
      (by rw [weightedSupportDrop_zero]; exact hb i)
  have hder := weightedSupportDrop_pderiv hP (Sum.inr i)
  have hmul := weightedSupportLE_mul_drop hb' hder
  intro a ha
  have hh := hmul ha
  change Finsupp.weight (Sum.elim v w) a + (r + w i) ≤ w i + d at hh
  change Finsupp.weight (Sum.elim v w) a + r ≤ d
  omega

theorem translationDirectionalDerivative_pow_mem_weightedSupportDrop
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, b i ∈ weightedSupportLE v (w i))
    {d r : ℕ} {P : MvPolynomial (U ⊕ B) ℝ}
    (hP : P ∈ weightedSupportDrop (Sum.elim v w) d r) (k : ℕ) :
    (translationDirectionalDerivative b ^ k) P ∈
      weightedSupportDrop (Sum.elim v w) d r := by
  induction k with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact translationDirectionalDerivative_mem_weightedSupportDrop v w b hb ih

theorem translationDirectionalSeries_mem_weightedSupportDrop
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, b i ∈ weightedSupportLE v (w i))
    {d r : ℕ} {P : MvPolynomial (U ⊕ B) ℝ}
    (hP : P ∈ weightedSupportDrop (Sum.elim v w) d r) (N : ℕ) :
    translationDirectionalSeries N b P ∈ weightedSupportDrop (Sum.elim v w) d r := by
  unfold translationDirectionalSeries
  apply (weightedSupportDrop (Sum.elim v w) d r).sum_mem
  intro k _
  exact (weightedSupportDrop (Sum.elim v w) d r).smul_mem _
    (translationDirectionalDerivative_pow_mem_weightedSupportDrop v w b hb hP k)

theorem translationDirectionalDerivative_mem_weightedSupportLE
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, b i ∈ weightedSupportLE v (w i))
    {d : ℕ} {P : MvPolynomial (U ⊕ B) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim v w) d) :
    translationDirectionalDerivative b P ∈ weightedSupportLE (Sum.elim v w) d := by
  rw [← weightedSupportDrop_zero] at hP ⊢
  exact translationDirectionalDerivative_mem_weightedSupportDrop v w b hb hP

theorem translationDirectionalSeries_mem_weightedSupportLE
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, b i ∈ weightedSupportLE v (w i))
    {d : ℕ} {P : MvPolynomial (U ⊕ B) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim v w) d) (N : ℕ) :
    translationDirectionalSeries N b P ∈ weightedSupportLE (Sum.elim v w) d := by
  rw [← weightedSupportDrop_zero] at hP ⊢
  exact translationDirectionalSeries_mem_weightedSupportDrop v w b hb hP N

theorem translationDirectionalSeries_mem_weightedSupportLT
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, b i ∈ weightedSupportLE v (w i))
    {d : ℕ} {P : MvPolynomial (U ⊕ B) ℝ}
    (hP : P ∈ weightedSupportLT (Sum.elim v w) d) (N : ℕ) :
    translationDirectionalSeries N b P ∈ weightedSupportLT (Sum.elim v w) d := by
  rw [← weightedSupportDrop_one] at hP ⊢
  exact translationDirectionalSeries_mem_weightedSupportDrop v w b hb hP N

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)

theorem weightedBasis_base_abs_le_one (a : WeightedBasisIndex w d) (i : σ) :
    |((weightedBasis w d hw a).val.base i : ℝ)| ≤ 1 := by
  classical
  cases a with
  | inl j =>
    rw [weightedBasis_inl_base]
    by_cases h : i = j <;> simp [h]
  | inr a => simp

theorem weightedBasis_polynomial_mass_le_one (a : WeightedBasisIndex w d) :
    realPolynomialMass
      (MvPolynomial.map (Rat.castHom ℝ) (weightedBasis w d hw a).val.polynomial) ≤ 1 := by
  cases a with
  | inl i => simp [realPolynomialMass_zero]
  | inr a => simp [realPolynomialMass_monomial]

theorem weightedBasis_base_integer (a : WeightedBasisIndex w d) (i : σ) :
    ∃ z : ℤ, (z : ℚ) = (weightedBasis w d hw a).val.base i := by
  classical
  cases a with
  | inl j =>
    rw [weightedBasis_inl_base]
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | inr a => exact ⟨0, by simp⟩

theorem weightedBasis_base_real_grid (a : WeightedBasisIndex w d) :
    (fun i => ((weightedBasis w d hw a).val.base i : ℝ)) ∈ realDenominatorGrid 1 := by
  choose z hz using weightedBasis_base_integer w d hw a
  refine ⟨z, funext (fun i => ?_)⟩
  change (z i : ℝ) = ((1 : ℕ) : ℝ) * ((weightedBasis w d hw a).val.base i : ℝ)
  rw [Nat.cast_one, one_mul]
  exact_mod_cast hz i

theorem weightedBasis_polynomial_real_grid (a : WeightedBasisIndex w d) :
    realPolynomialCoefficientGrid 1
      (MvPolynomial.map (Rat.castHom ℝ) (weightedBasis w d hw a).val.polynomial) := by
  apply (realPolynomialCoefficientGrid_iff 1 _).mpr
  simp only [Nat.cast_one, map_one, one_mul]
  cases a with
  | inl i =>
    simp only [weightedBasis_inl_polynomial, map_zero]
    exact (integralRealPolynomialSubring σ).zero_mem
  | inr a =>
    simp only [weightedBasis_inr_polynomial, map_monomial, map_one]
    exact ⟨monomial a.val (1 : ℤ), by simp⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationGroupPolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    PolynomialTranslationGroupOver (MvPolynomial U ℝ) B :=
  nativeTranslationGroupPolynomial w d (weightedBasis w d hw)
    (detectedTranslationSymbolLift w d hw hwd M hM D E).log

noncomputable def detectedTranslationBaseCoordinatePolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (i : B) : MvPolynomial U ℝ :=
  (detectedTranslationGroupPolynomial w d hw hwd M hM D E).base i

noncomputable def detectedTranslationPhasePolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    MvPolynomial (U ⊕ B) ℝ :=
  packTranslationPolynomial
    (detectedTranslationGroupPolynomial w d hw hwd M hM D E).polynomial

theorem detectedTranslationGroupPolynomial_eq_logGroup
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationGroupPolynomial w d hw hwd M hM D E =
      translationLogGroupPolynomial w d (weightedBasis w d hw)
        (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E) := rfl

theorem detectedTranslationPhasePolynomial_eq_logMixed
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationPhasePolynomial w d hw hwd M hM D E =
      translationLogMixedGroupPolynomial w d (weightedBasis w d hw)
        (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E) := rfl

theorem detectedTranslationGroupPolynomial_specialize
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u)
        (detectedTranslationGroupPolynomial w d hw hwd M hM D E) =
      detectedTranslationGroupEval w d hw hwd M hM D u E :=
  nativeTranslationGroupPolynomial_orbit w d hwd (weightedBasis w d hw)
    (fun _ : U => 1) (detectedTranslationSymbolLift w d hw hwd M hM D E) u

theorem detectedTranslationBaseCoordinatePolynomial_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (u : U → ℝ) (i : B) :
    eval u (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i) =
      (detectedTranslationGroupEval w d hw hwd M hM D u E).base i :=
  congrArg (fun g => g.base i)
    (detectedTranslationGroupPolynomial_specialize w d hw hwd M hM D E u)

theorem detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (i : B) :
    detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i =
      nativeTranslationLogCoordinate w d (weightedBasis w d hw)
        (detectedTranslationSymbolLift w d hw hwd M hM D E).log (Sum.inl i) := by
  apply MvPolynomial.funext
  intro u
  rw [detectedTranslationBaseCoordinatePolynomial_eval]
  change (bchRealTranslationHom w d hwd
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval (fun _ : U => 1) u
      (detectedTranslationSymbolLift w d hw hwd M hM D E))).base i = _
  rw [bchRealTranslationHom_base_coordinate w d hw hwd]
  exact VectorPolynomial.coordinate_eval₂
    (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)) u _

theorem detectedTranslationBaseCoordinatePolynomial_eq_scalarSymbol
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (i : B) :
    detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i =
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
        b ω hN (fun _ : U => 1) (detectedTranslationBaseFunctional w d hw hwd M hM D i) E := by
  rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
  exact detectedTranslationSymbolLift_base_coordinate w d hw hwd M hM D b ω hN E i

theorem detectedTranslationPhasePolynomial_specialize
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (u : U → ℝ) :
    aeval (Sum.elim (fun i => C (u i)) X)
        (detectedTranslationPhasePolynomial w d hw hwd M hM D E) =
      (detectedTranslationGroupEval w d hw hwd M hM D u E).polynomial := by
  rw [detectedTranslationPhasePolynomial, packTranslationPolynomial_specialize]
  exact congrArg PolynomialTranslationGroupOver.polynomial
    (detectedTranslationGroupPolynomial_specialize w d hw hwd M hM D E u)

theorem detectedTranslationPhasePolynomial_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (u : U → ℝ) (a : B → ℝ) :
    eval (Sum.elim u a) (detectedTranslationPhasePolynomial w d hw hwd M hM D E) =
      eval a (detectedTranslationGroupEval w d hw hwd M hM D u E).polynomial := by
  rw [detectedTranslationPhasePolynomial, packTranslationPolynomial_eval]
  exact congrArg (fun g => eval a g.polynomial)
    (detectedTranslationGroupPolynomial_specialize w d hw hwd M hM D E u)

theorem detectedTranslationPhasePolynomial_coeff
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (α : U →₀ ℕ) (β : B →₀ ℕ) :
    (detectedTranslationPhasePolynomial w d hw hwd M hM D E).coeff (α.sumElim β) =
      ((detectedTranslationGroupPolynomial w d hw hwd M hM D E).polynomial.coeff β).coeff α :=
  coeff_packTranslationPolynomial _ α β

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

theorem detectedTranslationPhasePolynomial_normalized_mass
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ k, realPolynomialMass (scaleMvPolynomialAxes H
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k)) ≤ A) :
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E)) ≤
      ((d : ℝ) + 1) * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * A) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * A)) ^ d := by
  have h := realPolynomialMass_translationLogMixedGroupPolynomial_scale w d hw hwd
    (weightedBasis w d hw) (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E) H hA (by norm_num : (0 : ℝ) ≤ 1)
    hf (weightedBasis_base_abs_le_one w d hw) (weightedBasis_polynomial_mass_le_one w d hw)
  rw [detectedTranslationPhasePolynomial_eq_logMixed]
  simpa only [mul_one] using h

theorem detectedTranslationPhasePolynomial_coefficientGrid
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    {q : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k)) :
    realPolynomialCoefficientGrid (d.factorial * q ^ (d + 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E) := by
  have hbase (k : WeightedBasisIndex w d) (i : B) :
      ∃ z : ℤ, (z : ℝ) = ((1 : ℕ) : ℝ) * ((weightedBasis w d hw k).val.base i : ℝ) := by
    obtain ⟨z, hz⟩ := weightedBasis_base_integer w d hw k i
    refine ⟨z, ?_⟩
    simp only [Nat.cast_one, one_mul]
    exact_mod_cast hz
  have h := translationLogMixedGroupPolynomial_coefficientGrid_of_inputs w d hwd
    (weightedBasis w d hw) (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E)
    hf hbase (weightedBasis_polynomial_real_grid w d hw)
  rw [detectedTranslationPhasePolynomial_eq_logMixed]
  simpa only [mul_one] using h

variable {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationPhasePolynomial_mass_of_slow [Fintype U]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hproj : ∀ k i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) :
    let Z := ((Fintype.card U : ℝ) + 1) ^ d * ((Fintype.card ι : ℝ) * H * A)
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim T (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E)) ≤
      ((d : ℝ) + 1) * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * Z) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * Z)) ^ d := by
  dsimp only
  apply detectedTranslationPhasePolynomial_normalized_mass w d hw hwd M hM D E T (by positivity)
  intro k
  exact detectedTranslationLogCoordinate_normalized_mass w d hw hwd M hM D b ω hN
    T hT hA hH k (hproj k) E hE

theorem detectedTranslationBaseCoordinatePolynomial_mass_of_slow [Fintype U]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hproj : ∀ k i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) (i : B) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)) ≤
      ((Fintype.card U : ℝ) + 1) ^ d * ((Fintype.card ι : ℝ) * H * A) := by
  rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
  exact detectedTranslationLogCoordinate_normalized_mass w d hw hwd M hM D b ω hN
    T hT hA hH (Sum.inl i) (hproj (Sum.inl i)) E hE

theorem detectedTranslationGroupPolynomials_grid_of_symbol
    (m : ℕ)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m E) :
    let q := matrixDenominator (detectedTranslationLogProjectionMatrix w d hw b ω) * m
    realPolynomialCoefficientGrid (d.factorial * q ^ (d + 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E) ∧
    ∀ i, realPolynomialCoefficientGrid (d.factorial * q ^ (d + 1))
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i) := by
  let q := matrixDenominator (detectedTranslationLogProjectionMatrix w d hw b ω) * m
  have hf := detectedTranslationLogCoordinate_common_coefficient_grid w d hw hwd M hM D b ω hN m E hE
  constructor
  · exact detectedTranslationPhasePolynomial_coefficientGrid w d hw hwd M hM D E hf
  · intro i
    apply realPolynomialCoefficientGrid_mono (show q ∣ d.factorial * q ^ (d + 1) from ?_)
    · rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
      exact hf (Sum.inl i)
    · exact dvd_mul_of_dvd_right (dvd_pow_self q (by omega : d + 1 ≠ 0)) _

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

theorem detectedTranslationPhasePolynomial_isWeightedHomogeneous
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationPhasePolynomial w d hw hwd M hM D E).IsWeightedHomogeneous
      (Sum.elim (fun _ : U => 1) w) d := by
  rw [detectedTranslationPhasePolynomial_eq_logMixed,
    translationLogMixedGroupPolynomial_eq_series w d hwd]
  have hf := detectedTranslationLogCoordinate_homogeneous w d hw hwd M hM D E
  exact translationDirectionalSeries_isWeightedHomogeneous (fun _ : U => 1) w d _
    (translationLogBasePolynomial_weightedBasis_isWeightedHomogeneous (fun _ : U => 1) w d hw _ hf)
    (pack_translationLogPhasePolynomial_weightedBasis_isWeightedHomogeneous (fun _ : U => 1) w d hw _ hf)

theorem detectedTranslationPhasePolynomial_weightedSupportLE
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationPhasePolynomial w d hw hwd M hM D E ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
  intro α hα
  exact (detectedTranslationPhasePolynomial_isWeightedHomogeneous w d hw hwd M hM D E
    (mem_support_iff.mp hα)).le

theorem detectedTranslationPhasePolynomial_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationPhasePolynomial w d hw hwd M hM D E).totalDegree ≤ d := by
  have hP := detectedTranslationPhasePolynomial_weightedSupportLE w d hw hwd M hM D E
  rw [totalDegree_eq]
  apply Finset.sup_le
  intro α hα
  have hweight : α.sum (fun _ n => n) ≤ Finsupp.weight (Sum.elim (fun _ : U => 1) w) α := by
    change (∑ i ∈ α.support, α i) ≤ ∑ i ∈ α.support, α i • Sum.elim (fun _ : U => 1) w i
    apply Finset.sum_le_sum
    intro i _
    cases i with
    | inl i => simp
    | inr i => simpa only [Sum.elim_inr, smul_eq_mul] using Nat.le_mul_of_pos_right (α (Sum.inr i)) (hw i)
  rw [Finsupp.card_toMultiset]
  change (α.sum fun _ n => n) ≤ d
  exact hweight.trans (hP hα)

theorem detectedTranslationPhasePolynomial_scaled_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) :
    (scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E)).totalDegree ≤ d :=
  (scaleMvPolynomialAxes_totalDegree_le _ _).trans
    (detectedTranslationPhasePolynomial_totalDegree w d hw hwd M hM D E)

theorem detectedTranslationBaseCoordinatePolynomial_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) (i : B) :
    (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i).totalDegree ≤ w i := by
  rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
  have h := detectedTranslationLogCoordinate_homogeneous w d hw hwd M hM D E (Sum.inl i)
  rw [totalDegree_eq]
  apply Finset.sup_le
  intro α hα
  have hh := h (mem_support_iff.mp hα)
  rw [Finsupp.card_toMultiset]
  change (α.sum fun _ n => n) ≤ w i
  simpa only [Finsupp.weight_apply, smul_eq_mul, mul_one, weightedBasisGrade, Sum.elim_inl] using hh.le

theorem detectedTranslationBaseCoordinatePolynomial_scaled_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (i : B) :
    (scaleMvPolynomialAxes H
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)).totalDegree ≤ w i :=
  (scaleMvPolynomialAxes_totalDegree_le _ _).trans
    (detectedTranslationBaseCoordinatePolynomial_totalDegree w d hw hwd M hM D E i)

theorem detectedTranslationPhasePolynomial_scaled_weightedSupportLE
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) :
    scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E) ∈
        weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
  scaleMvPolynomialAxes_mem_weightedSupportLE _ _ _
    (detectedTranslationPhasePolynomial_weightedSupportLE w d hw hwd M hM D E)

end Erdos3.PolynomialTranslationLie

end

end OAI
