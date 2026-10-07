import OAI.Combinatorics.Progressions.Estimates.DetectedTranslationMajorBase

namespace OAI

section

namespace Erdos3

theorem realSpanIntegerRowBound_le_exp_of_imageHeight (n m H : ℕ) {p a : ℝ}
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hm : (m : ℝ) ≤ p)
    (himage : (imageDefiningHeight n m H : ℝ) ≤ Real.exp a) :
    (realSpanIntegerRowBound n m H : ℝ) ≤ Real.exp ((p * p + 1) * a) := by
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (imageDefiningHeight n m H)) himage (m * m)
  rw [← Real.exp_nat_mul] at hpow
  rw [realSpanIntegerRowBound, Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp ((m * m : ℕ) * a) * Real.exp a :=
      mul_le_mul hpow himage (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((((m : ℝ) * m) + 1) * a) := by
      rw [← Real.exp_add, Nat.cast_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ ha
      have hsq := mul_le_mul hm hm (Nat.cast_nonneg _) hp
      linarith

theorem samplingProjectedImage_row_le_exp (n m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) :
    (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
      Real.exp ((p * p + 1) * (((p + 2) ^ 4 + 3) ^ 10)) := by
  have hpq : p ≤ (p + 2) ^ 4 + 1 :=
    (le_power_budget hp (by decide : 1 ≤ 4)).trans (le_add_of_nonneg_right (by norm_num))
  have hheight := imageDefiningHeight_le_exp n m ⌈Real.exp ((p + 2) ^ 4)⌉₊
    (by positivity : 0 ≤ (p + 2) ^ 4 + 1) (hn.trans hpq) (hm.trans hpq)
    (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4))
  apply realSpanIntegerRowBound_le_exp_of_imageHeight n m _ hp (by positivity) hm
  convert hheight using 1
  congr 2
  ring

theorem exists_samplingProjectedImage_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n m : ℕ) (p : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (m : ℝ) ≤ p →
      (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
        Real.exp ((p + C) ^ C) ∧
      (m : ℝ) * realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ *
          Real.exp ((p + 3) ^ 3) ≤ Real.exp ((p + C) ^ C) := by
  let T : Polynomial ℕ := Polynomial.X +
    (Polynomial.X * Polynomial.X + 1) * (((Polynomial.X + 2) ^ 4 + 3) ^ 10) +
      (Polynomial.X + 3) ^ 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro n m p hp hn hm
  let R : ℝ := (p * p + 1) * (((p + 2) ^ 4 + 3) ^ 10)
  have htotal : p + R + (p + 3) ^ 3 ≤ (p + C) ^ C := by
    simpa only [T, R, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_one, Polynomial.eval₂_ofNat]
      using hbudget p hp
  have hrow := samplingProjectedImage_row_le_exp n m hp hn hm
  change (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp R at hrow
  have hR : R ≤ (p + C) ^ C := by
    have hcubic : 0 ≤ (p + 3) ^ 3 := by positivity
    linarith
  refine ⟨hrow.trans (Real.exp_le_exp.mpr hR), ?_⟩
  have hmexp : (m : ℝ) ≤ Real.exp p := hm.trans (by linarith [Real.add_one_le_exp p])
  calc
    _ ≤ Real.exp p * Real.exp R * Real.exp ((p + 3) ^ 3) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hmexp hrow (Nat.cast_nonneg _) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp (p + R + (p + 3) ^ 3) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr htotal

end Erdos3

end

section

namespace Erdos3

theorem exists_samplingProjectedImage_complete_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n m : ℕ) (p : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (m : ℝ) ≤ p →
      Real.exp ((p + 3) ^ 3) ≤ Real.exp ((p + C) ^ C) ∧
      (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
        Real.exp ((p + C) ^ C) ∧
      (m : ℝ) * realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ *
        Real.exp ((p + 3) ^ 3) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨a, ha, hbudget⟩ := exists_samplingProjectedImage_budget
  refine ⟨a + 3, by omega, ?_⟩
  intro n m p hp hn hm
  have hbase : (1 : ℝ) ≤ p + (a + 3 : ℕ) := by
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    push_cast
    linarith
  have haC : p + a ≤ p + (a + 3 : ℕ) := by push_cast; linarith
  have hthreeC : p + 3 ≤ p + (a + 3 : ℕ) := by
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    push_cast
    linarith
  have hlarge : (p + a) ^ a ≤ (p + (a + 3 : ℕ)) ^ (a + 3) :=
    (pow_le_pow_left₀ (by positivity) haC a).trans
      (pow_le_pow_right₀ hbase (by omega))
  have hsmall : (p + 3) ^ 3 ≤ (p + (a + 3 : ℕ)) ^ (a + 3) :=
    (pow_le_pow_left₀ (by positivity) hthreeC 3).trans
      (pow_le_pow_right₀ hbase (by omega))
  obtain ⟨hrow, herror⟩ := hbudget n m p hp hn hm
  exact ⟨Real.exp_le_exp.mpr hsmall,
    hrow.trans (Real.exp_le_exp.mpr hlarge),
    herror.trans (Real.exp_le_exp.mpr hlarge)⟩

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial
open scoped Matrix

variable {B L : Type} {σ ι J : Type*} [Fintype B] [Fintype ι] [Fintype J]
    [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslation_samplingRank_le_base_span
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 ≤ p)
    (hB : (Fintype.card B : ℝ) ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hprod : E * P * Q = X)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (h : ℕ) (R : ℝ) (retained : Submodule ℝ (B → ℝ))
    (hrank : HasLayerSamplingRank h T R retained
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X))
    (hgridR : Real.exp ((p + 3)^3) ≤ R)
    (hrowR : (realSpanIntegerRowBound (Fintype.card J) (Fintype.card B)
      ⌈Real.exp ((p + 2)^4)⌉₊ : ℝ) ≤ R)
    (hcost : (Fintype.card B : ℝ) *
      (realSpanIntegerRowBound (Fintype.card J) (Fintype.card B)
        ⌈Real.exp ((p + 2)^4)⌉₊ : ℝ) * Real.exp ((p + 3)^3) ≤ R) :
    retained ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  let H : ℕ := ⌈Real.exp ((p + 2)^4)⌉₊
  let A : Matrix B J ℚ := fun i j => detectedTranslationBaseMap w d hw hwd M hM D (v j) i
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    exact rationalHeightLE_ceil_exp
      (detectedTranslationBaseFunctional_value_logHeight w d hw hwd M hM D
        b ω hN hp hι hb (v j) (hvheight j) i)
  obtain ⟨q, hq, hqbound, hgrid⟩ :=
    detectedTranslationBasePolynomial_exists_coefficient_grid w d hw hwd M hM D
      b ω hN hp hι hb hB m hm hmp Q hQ
  apply samplingRank_le_real_column_span_of_decomposition A (one_le_ceil_exp _) hA
    h T R (Real.exp ((p + 3)^3)) retained
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X)
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E)
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P)
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q)
    q hq hT hrank
    (detectedTranslationBasePolynomial_factorization w d hw hwd M hM D b ω hN hd E P Q X hprod)
    (detectedTranslationBasePolynomial_slow_coefficients w d hw hwd M hM D b ω hN hp hι hb T hT E hE)
    (detectedTranslationBasePolynomial_fast_coefficients_mem_span w d hw hwd M hM D b ω hN W v hv P hP)
    hgrid (hqbound.trans hgridR) hrowR hcost

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial
open scoped Matrix

universe u v z

theorem exists_detectedTranslation_samplingRank_le_base_span :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B L : Type} {σ : Type u} {ι : Type v} {J : Type z}
    [Fintype B] [Fintype ι] [Fintype J] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (_hd : 1 ≤ d) {p : ℝ} (_hp : 0 ≤ p)
    (_hB : (Fintype.card B : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hJ : (Fintype.card J : ℝ) ≤ p)
    (_hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hprod : E * P * Q = X)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (_hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (_hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (_hm : 0 < m) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (h : ℕ) (R : ℝ) (retained : Submodule ℝ (B → ℝ))
    (_hrank : HasLayerSamplingRank h T R retained
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X))
    (_hR : Real.exp ((p + C)^C) ≤ R),
    retained ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  obtain ⟨C, hC, hbudget⟩ := exists_samplingProjectedImage_complete_budget
  refine ⟨C, hC, ?_⟩
  intro B L σ ι J _ _ _ _ _ w d hw hwd _ M hM e D b ω hN hd p hp hB hι hJ
    hb W v hv hvheight E P Q X hprod T hT hE hP m hm hmp hQ h R retained hrank hR
  obtain ⟨hgrid, hrow, hcost⟩ := hbudget (Fintype.card J) (Fintype.card B) p hp hJ hB
  exact detectedTranslation_samplingRank_le_base_span w d hw hwd M hM D b ω hN
    hd hp hB hι hb W v hv hvheight E P Q X hprod T hT hE hP m hm hmp hQ
    h R retained hrank (hgrid.trans hR) (hrow.trans hR) (hcost.trans hR)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Matrix

theorem exists_majorTranslation_samplingRank_le_real_base_image :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B L : Type} {σ ι J : Type}
    [Fintype B] [Fintype ι] [Fintype J] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (_hd : 1 ≤ d) {p : ℝ} (_hp : 0 ≤ p)
    (_hB : (Fintype.card B : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hJ : (Fintype.card J : ℝ) ≤ p)
    (_hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (F : MvPolynomial (σ ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) d)
    (A : B → MvPolynomial σ ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (_hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (_hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (_hm : 0 < m) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (h : ℕ) (R : ℝ) (retained : Submodule ℝ (B → ℝ))
    (_hrank : HasLayerSamplingRank h T R retained
      (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B)
        (fun i => weightedHomogeneousComponent (fun _ : σ => 1) (w i) (A i))))
    (_hR : Real.exp ((p + C)^C) ≤ R),
    retained ≤
      (((W.map (weightedTranslationGradedProjection
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))).toSubmodule).baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) := by
  obtain ⟨C, hC, hcontain⟩ := exists_detectedTranslation_samplingRank_le_base_span
  refine ⟨C, hC, ?_⟩
  intro B L σ ι J _ _ _ _ _ w d hw hwd _ M hM e D b ω hN hd p hp hB hι hJ
    hb W v hv hvheight F hF A hA partner E P Q hprod T hT hE hP m hm hmp hQ
    h R retained hrank hR
  rw [← detectedTranslationBase_span_eq_real_image w d hw hwd M hM D W v hv]
  apply hcontain w d hw hwd M hM D b ω hN hd hp hB hι hJ hb W v hv hvheight
    E P Q _ hprod T hT hE hP m hm hmp hQ h R retained _ hR
  rw [detectedTranslationBasePolynomial_majorOrbitSymbol w d hw hwd M hM D b ω hN F hF A hA partner]
  exact hrank

end Erdos3.PolynomialTranslationLie

end

end OAI
