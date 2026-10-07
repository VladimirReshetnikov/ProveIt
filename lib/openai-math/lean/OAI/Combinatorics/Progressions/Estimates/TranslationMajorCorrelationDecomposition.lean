import OAI.Combinatorics.Progressions.Dynamics.TranslationMajorDecompositionBudget
import OAI.Combinatorics.Progressions.Geometry.DetectedTranslationUniformCoordinateBounds
import OAI.Combinatorics.Progressions.Lattices.AlgebraicMajorIntegerRestoration
import OAI.Combinatorics.Progressions.Polynomial.AlgebraicMajorWeightedDegree
import OAI.Combinatorics.Progressions.Polynomial.RationalPolynomialFromRealGrid

namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem realPolynomialMass_weightedHomogeneousComponent_le
    {σ : Type*} (P : MvPolynomial σ ℝ) (w : σ → ℕ) (d : ℕ) :
    realPolynomialMass (weightedHomogeneousComponent w d P) ≤ realPolynomialMass P := by
  classical
  have hs : (weightedHomogeneousComponent w d P).support ⊆ P.support := by
    rw [support_weightedHomogeneousComponent]
    exact Finset.filter_subset _ _
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support hs]
  apply Finset.sum_le_sum
  intro α _
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact le_rfl
  · simpa only [abs_zero] using abs_nonneg (P.coeff α)

theorem realPolynomialMass_specializeMajorParameters_zero_le
    {U B : Type*} (P : MvPolynomial (U ⊕ B) ℝ) :
    realPolynomialMass (specializeMajorParameters (RingHom.id ℝ) P 0) ≤ realPolynomialMass P := by
  have h := realPolynomialMass_substitution_le P
    (Sum.elim (fun _ : U => (0 : MvPolynomial B ℝ)) X)
    (M := 1) le_rfl (fun i => by
      cases i with
      | inl i => simpa only [Sum.elim_inl, realPolynomialMass_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
      | inr i => exact (realPolynomialMass_X i).le) (d := P.totalDegree) le_rfl
  simpa only [specializeMajorParameters, RingHomCompTriple.comp_eq, RingHom.coe_comp,
    Function.comp_apply, RingHom.id_apply, Pi.zero_apply, map_zero, one_pow, mul_one] using h

theorem reducedMajorZeroSlice_mass_le
    {U B : Type*} [Fintype U] [Fintype B]
    (w : B → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    realPolynomialMass (specializeMajorParameters (RingHom.id ℝ)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (fractionalCoefficientPolynomial F)) 0) ≤
      ((Fintype.card U : ℝ) + (Fintype.card B : ℝ) + 1)^d := by
  apply (realPolynomialMass_specializeMajorParameters_zero_le _).trans
  apply (realPolynomialMass_weightedHomogeneousComponent_le _ _ _).trans
  have h := fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE F
    (Sum.elim (fun _ : U => 1) w) (fun i => by cases i <;> simp_all) d hF
  simpa only [Fintype.card_sum, Nat.cast_add] using h

theorem positiveWeightedSupport_totalDegree_le
    {σ : Type*} {R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (w : σ → ℕ) (hw : ∀ i, 0 < w i) {d : ℕ}
    (hP : P ∈ weightedSupportLE w d) : P.totalDegree ≤ d := by
  unfold totalDegree
  apply Finset.sup_le
  intro α hα
  exact (exponentSum_le_positive_weight w hw α).trans (hP hα)

theorem specializeMajorParameters_zero_totalDegree_le
    {U B : Type*} (P : MvPolynomial (U ⊕ B) ℝ) :
    (specializeMajorParameters (RingHom.id ℝ) P 0).totalDegree ≤ P.totalDegree := by
  have h := polynomial_substitution_totalDegree_le_ring P
    (Sum.elim (fun _ : U => (0 : MvPolynomial B ℝ)) X)
    (k := 1) (fun i => by cases i <;> simp) le_rfl
  simpa only [specializeMajorParameters, RingHomCompTriple.comp_eq, RingHom.coe_comp,
    Function.comp_apply, RingHom.id_apply, Pi.zero_apply, map_zero, Nat.mul_one] using h

theorem reducedMajorZeroSlice_totalDegree_le
    {U B : Type*} (w : B → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (F : MvPolynomial (U ⊕ B) ℝ) :
    (specializeMajorParameters (RingHom.id ℝ)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (fractionalCoefficientPolynomial F)) 0).totalDegree ≤ d := by
  apply (specializeMajorParameters_zero_totalDegree_le _).trans
  apply positiveWeightedSupport_totalDegree_le _ (Sum.elim (fun _ : U => 1) w)
    (fun i => by cases i <;> simp_all)
  intro α hα
  exact ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    (mem_support_iff.mp hα)).le

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationNormalizedBase
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (i : B) : MvPolynomial U ℝ :=
  scaleMvPolynomialAxes H (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)

noncomputable def detectedTranslationNormalizedPhase
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
    (detectedTranslationPhasePolynomial w d hw hwd M hM D E)

theorem detectedTranslationNormalizedBase_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (hH : ∀ i, H i ≠ 0) (u : U → ℝ) (i : B) :
    eval (fun j => u j / H j) (detectedTranslationNormalizedBase w d hw hwd M hM D E H i) =
      (detectedTranslationGroupEval w d hw hwd M hM D u E).base i := by
  rw [detectedTranslationNormalizedBase, scaleMvPolynomialAxes_eval]
  have hc : (fun j => H j * (u j / H j)) = u := by
    funext j
    exact mul_div_cancel₀ (u j) (hH j)
  rw [hc, detectedTranslationBaseCoordinatePolynomial_eval]

theorem detectedTranslationNormalizedPhase_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (hH : ∀ i, H i ≠ 0) (u : U → ℝ) (z : B → ℝ) :
    eval (Sum.elim (fun j => u j / H j) z)
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) =
      eval z (detectedTranslationGroupEval w d hw hwd M hM D u E).polynomial := by
  rw [detectedTranslationNormalizedPhase, scaleMvPolynomialAxes_eval]
  have hc : (fun j => Sum.elim H (fun _ : B => 1) j *
      Sum.elim (fun i => u i / H i) z j) = Sum.elim u z := by
    funext j
    cases j with
    | inl i => exact mul_div_cancel₀ (u i) (hH i)
    | inr i => exact one_mul _
  rw [hc, detectedTranslationPhasePolynomial_eval]

theorem detectedTranslationGroupEval_normalized_left
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (hH : ∀ i, H i ≠ 0) (u : U → ℝ) :
    normalizedMajorLeft
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H) H u =
      detectedTranslationGroupEval w d hw hwd M hM D u E := by
  apply PolynomialTranslationGroupOver.ext
  · funext i
    exact detectedTranslationNormalizedBase_eval w d hw hwd M hM D E H hH u i
  · apply MvPolynomial.funext
    intro z
    change eval z (specializeMajorParameters (RingHom.id ℝ) _ _) = _
    rw [specializeMajorParameters_eval, eval₂_id]
    exact detectedTranslationNormalizedPhase_eval w d hw hwd M hM D E H hH u z

theorem exists_detectedTranslation_rational_right
    (Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (q : ℕ) (hq : 0 < q)
    (hphase : realPolynomialCoefficientGrid q
      (detectedTranslationPhasePolynomial w d hw hwd M hM D Q))
    (hbase : ∀ i, realPolynomialCoefficientGrid q
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i)) :
    ∃ (Qrat : MvPolynomial (U ⊕ B) ℚ) (a : B → MvPolynomial U ℚ),
      map (algebraMap ℚ ℝ) Qrat = detectedTranslationPhasePolynomial w d hw hwd M hM D Q ∧
      (∀ i, map (algebraMap ℚ ℝ) (a i) =
        detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i) ∧
      (fun α => Qrat.coeff α) ∈ denominatorGrid q ∧
      (∀ i, (fun α => (a i).coeff α) ∈ denominatorGrid q) ∧
      Qrat.totalDegree = (detectedTranslationPhasePolynomial w d hw hwd M hM D Q).totalDegree ∧
      ∀ u, rationalMajorRight Qrat a u = detectedTranslationGroupEval w d hw hwd M hM D u Q := by
  obtain ⟨Qrat, hQrat, hQgrid, hQdegree⟩ :=
    exists_rationalPolynomial_of_realCoefficientGrid _ hq hphase
  choose a ha hagrid _hadegree using fun i =>
    exists_rationalPolynomial_of_realCoefficientGrid _ hq (hbase i)
  refine ⟨Qrat, a, hQrat, ha, hQgrid, hagrid, hQdegree, ?_⟩
  intro u
  apply PolynomialTranslationGroupOver.ext
  · funext i
    change eval₂ (algebraMap ℚ ℝ) u (a i) = _
    rw [← eval_map, ha i]
    exact detectedTranslationBaseCoordinatePolynomial_eval w d hw hwd M hM D Q u i
  · apply MvPolynomial.funext
    intro z
    change eval z (specializeMajorParameters (algebraMap ℚ ℝ) Qrat u) = _
    rw [specializeMajorParameters_eval, ← eval_map, hQrat]
    exact detectedTranslationPhasePolynomial_eval w d hw hwd M hM D Q u z

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem exists_detectedTranslation_normalized_decomposition
    (hd : 0 < d)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : U => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W))
    (V : MvPolynomial B ℚ) (H : U → ℝ) (hH : ∀ i, H i ≠ 0)
    (q r : ℕ) (hq : 0 < q) (Cbase : ℝ) (hCbase : 0 ≤ Cbase)
    (hphaseGrid : realPolynomialCoefficientGrid q
      (detectedTranslationPhasePolynomial w d hw hwd M hM D Q))
    (hbaseGrid : ∀ i, realPolynomialCoefficientGrid q
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i))
    (hVgrid : (fun α => V.coeff α) ∈ denominatorGrid q)
    (hEdegree : (detectedTranslationNormalizedPhase w d hw hwd M hM D E H).totalDegree ≤ r)
    (hVdegree : V.totalDegree ≤ r)
    (heMass : ∀ i, realPolynomialMass
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H i) ≤ Cbase) :
    let fast := W.map (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))
    let K := (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
    let Ftop := weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F
    let F₀ := specializeMajorParameters (RingHom.id ℝ) Ftop 0
    (∀ x ∈ fast, ∀ z ∈ fast.toSubmodule.map
      (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) →
    (∀ u, (detectedTranslationGroupEval w d hw hwd M hM D u Q).base ∈ K) →
    ∃ (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ),
      (∀ u z, z ∈ K → eval (Sum.elim u z) Ftop =
        eval (Sum.elim (fun i => u i / H i)
          (fun j => z j - eval u (majorTranslationTopCoordinates w A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) R) ∧
      realPolynomialMass S ≤ realPolynomialMass F₀ +
        (realPolynomialMass (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) +
          realPolynomialMass (map (algebraMap ℚ ℝ) V)) * (1 + Cbase)^r ∧
      (fun α => R.coeff α) ∈ denominatorGrid (q^(r+1)) := by
  intro fast K Ftop F₀ hderiv hright
  obtain ⟨Qrat, a, _, _, hQgrid, hagrid, _, hQeval⟩ :=
    exists_detectedTranslation_rational_right w d hw hwd M hM D Q q hq hphaseGrid hbaseGrid
  have hfactor (u : U → ℝ) : algebraicMajorSymbol Ftop F₀
      (majorTranslationTopCoordinates w A) u =
        normalizedMajorLeft (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
          (detectedTranslationNormalizedBase w d hw hwd M hM D E H) H u *
        detectedTranslationGroupEval w d hw hwd M hM D u P * rationalMajorRight Qrat a u := by
    rw [detectedTranslationGroupEval_normalized_left w d hw hwd M hM D E H hH,
      hQeval]
    exact detectedTranslationGroupEval_major_factorization w d hw hwd M hM D b ω hN
      F hF A hA partner E P Q hprod u
  apply algebraic_major_normalized_decomposition_on_subspace K Ftop F₀
    (majorTranslationTopCoordinates w A)
    (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
    (detectedTranslationNormalizedBase w d hw hwd M hM D E H) Qrat a V H
    (fun u => detectedTranslationGroupEval w d hw hwd M hM D u P) hfactor
  · exact detectedTranslationGroupEval_fast_potential w d hw hwd M hM D b ω hN
      hd W P hP V hderiv
  · intro u
    have heq := congrArg PolynomialTranslationGroupOver.base (hQeval u)
    change (fun i => eval₂ (algebraMap ℚ ℝ) u (a i)) = _ at heq
    rw [heq]
    exact hright u
  · exact hCbase
  · exact heMass
  · exact hEdegree
  · exact hVdegree
  · exact hQgrid
  · exact hVgrid
  · exact hagrid

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem exists_detectedTranslation_normalized_weighted_decomposition
    (hd : 0 < d)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : U => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W))
    (V : MvPolynomial B ℚ) (H : U → ℝ) (hH : ∀ i, H i ≠ 0)
    (q : ℕ) (hq : 0 < q) (Cbase : ℝ) (hCbase : 0 ≤ Cbase)
    (hphaseGrid : realPolynomialCoefficientGrid q
      (detectedTranslationPhasePolynomial w d hw hwd M hM D Q))
    (hbaseGrid : ∀ i, realPolynomialCoefficientGrid q
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i))
    (hVgrid : (fun α => V.coeff α) ∈ denominatorGrid q)
    (hVweight : V ∈ weightedSupportLE w d)
    (heMass : ∀ i, realPolynomialMass
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H i) ≤ Cbase) :
    let fast := W.map (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))
    let K := (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
    let Ftop := weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F
    let F₀ := specializeMajorParameters (RingHom.id ℝ) Ftop 0
    (∀ x ∈ fast, ∀ z ∈ fast.toSubmodule.map
      (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) →
    (∀ u, (detectedTranslationGroupEval w d hw hwd M hM D u Q).base ∈ K) →
    ∃ (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ),
      (∀ u z, z ∈ K → eval (Sum.elim u z) Ftop =
        eval (Sum.elim (fun i => u i / H i)
          (fun j => z j - eval u (majorTranslationTopCoordinates w A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) R) ∧
      realPolynomialMass S ≤ realPolynomialMass F₀ +
        (realPolynomialMass (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) +
          realPolynomialMass (map (algebraMap ℚ ℝ) V)) * (1 + Cbase)^d ∧
      (fun α => R.coeff α) ∈ denominatorGrid (q^(d+1)) ∧
      S ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      R ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      S.totalDegree ≤ d ∧ R.totalDegree ≤ d := by
  intro fast K Ftop F₀ hderiv hright
  obtain ⟨Qrat, a, hQmap, hamap, hQgrid, hagrid, _hQratDegree, hQeval⟩ :=
    exists_detectedTranslation_rational_right w d hw hwd M hM D Q q hq hphaseGrid hbaseGrid
  have hfactor (u : U → ℝ) : algebraicMajorSymbol Ftop F₀
      (majorTranslationTopCoordinates w A) u =
        normalizedMajorLeft (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
          (detectedTranslationNormalizedBase w d hw hwd M hM D E H) H u *
        detectedTranslationGroupEval w d hw hwd M hM D u P * rationalMajorRight Qrat a u := by
    rw [detectedTranslationGroupEval_normalized_left w d hw hwd M hM D E H hH,
      hQeval]
    exact detectedTranslationGroupEval_major_factorization w d hw hwd M hM D b ω hN
      F hF A hA partner E P Q hprod u
  have hpotential := detectedTranslationGroupEval_fast_potential w d hw hwd M hM D b ω hN
    hd W P hP V hderiv
  have haright (u : U → ℝ) : (fun j => eval₂ (algebraMap ℚ ℝ) u (a j)) ∈ K := by
    have heq := congrArg PolynomialTranslationGroupOver.base (hQeval u)
    change (fun i => eval₂ (algebraMap ℚ ℝ) u (a i)) = _ at heq
    rw [heq]
    exact hright u
  have hFtopweight : Ftop ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
    intro α hα
    exact ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (mem_support_iff.mp hα)).le
  have hF₀weight : F₀ ∈ weightedSupportLE w d :=
    specializeMajorParameters_zero_weightedSupportLE w hFtopweight
  have hEweight : detectedTranslationNormalizedPhase w d hw hwd M hM D E H ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
    detectedTranslationPhasePolynomial_scaled_weightedSupportLE w d hw hwd M hM D E H
  have heweight (i : B) : detectedTranslationNormalizedBase w d hw hwd M hM D E H i ∈
      weightedSupportLE (fun _ : U => 1) (w i) :=
    (mem_weightedSupportLE_one_iff _ _).mpr
      (detectedTranslationBaseCoordinatePolynomial_scaled_totalDegree w d hw hwd M hM D E H i)
  have hQweight : Qrat ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
    apply weightedSupportLE_of_map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
    rw [hQmap]
    exact detectedTranslationPhasePolynomial_weightedSupportLE w d hw hwd M hM D Q
  have haweight (i : B) : a i ∈ weightedSupportLE (fun _ : U => 1) (w i) := by
    apply weightedSupportLE_of_map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
    rw [hamap i]
    exact (mem_weightedSupportLE_one_iff _ _).mpr
      (detectedTranslationBaseCoordinatePolynomial_totalDegree w d hw hwd M hM D Q i)
  have hVrealweight : map (algebraMap ℚ ℝ) V ∈ weightedSupportLE w d := by
    intro α hα
    exact hVweight (support_map_subset (algebraMap ℚ ℝ) V hα)
  have hVdegree : V.totalDegree ≤ d := weightedSupportLE_totalDegree_le_of_pos hw hVweight
  have hVrealDegree : (map (algebraMap ℚ ℝ) V).totalDegree ≤ d :=
    weightedSupportLE_totalDegree_le_of_pos hw hVrealweight
  have hEdegree : (detectedTranslationNormalizedPhase w d hw hwd M hM D E H).totalDegree ≤ d :=
    detectedTranslationPhasePolynomial_scaled_totalDegree w d hw hwd M hM D E H
  have hSweight := majorSlowPolynomial_weightedSupportLE (fun _ : U => 1) w F₀
    (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
    (map (algebraMap ℚ ℝ) V)
    (detectedTranslationNormalizedBase w d hw hwd M hM D E H)
    hF₀weight hEweight hVrealweight heweight
  have hRweight := majorRationalPolynomial_weightedSupportLE (fun _ : U => 1) w
    Qrat V a hQweight hVweight haweight
  have hpos (i : U ⊕ B) : 0 < Sum.elim (fun _ : U => 1) w i := by
    cases i with
    | inl i => exact Nat.zero_lt_one
    | inr i => exact hw i
  refine ⟨majorSlowPolynomial F₀
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (map (algebraMap ℚ ℝ) V)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H),
    majorRationalPolynomial Qrat V a, ?_, ?_, ?_, hSweight, hRweight,
    weightedSupportLE_totalDegree_le_of_pos hpos hSweight,
    weightedSupportLE_totalDegree_le_of_pos hpos hRweight⟩
  · exact algebraic_major_normalized_identity_on_subspace K Ftop F₀
      (majorTranslationTopCoordinates w A)
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H) Qrat a V H
      (fun u => detectedTranslationGroupEval w d hw hwd M hM D u P)
      hfactor hpotential haright
  · exact algebraic_major_normalized_slow_mass F₀
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) V
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H)
      hCbase heMass hEdegree hVrealDegree
  · exact majorRationalPolynomial_denominatorGrid Qrat V a q d hVdegree hQgrid hVgrid hagrid

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_decomposition
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (_htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (_hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (_hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      ∀ (retained : Fin d → Submodule ℝ (Fin m → ℝ)),
      (∀ h, HasLayerSamplingRank (h.val + 1) (fun i => (lengths i : ℝ))
        (Real.exp ((p + C)^C)) (retained h)
        (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i)))) →
      (∀ α, coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i))) α ∈
        ⨆ h, retained h) →
      ∃ (fast : LieSubalgebra ℚ (weightedSubalgebra w d))
        (g : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → weightedSubalgebra w d)
        (Slow : MvPolynomial (U ⊕ Fin m) ℝ)
        (RatPart : MvPolynomial (U ⊕ Fin m) ℚ) (qOut : ℕ),
        (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L) : ℝ) ≤ (p+C)^C ∧
        Submodule.span ℚ (Set.range g) = fast.toSubmodule ∧
        BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) fast.toSubmodule ∧
        (∀ j i, rationalLogHeight ((weightedBasis w d hw).repr (g j) i) ≤ (p+C)^C) ∧
        BasisGradedSubmodule (Pi.basisFun ℝ (Fin m)) w
          ((fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
        (∀ h, retained h ≤ (fast.toSubmodule.baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
        realPolynomialMass Slow ≤ Real.exp ((p+C)^C) ∧
        (∀ α, |Slow.coeff α| ≤ Real.exp ((p+C)^C)) ∧
        0 < qOut ∧ (qOut : ℝ) ≤ Real.exp ((p+C)^C) ∧
        (fun α => RatPart.coeff α) ∈ denominatorGrid qOut ∧
        (∀ α, (RatPart.coeff α).den ≤ qOut) ∧
        Slow ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
        RatPart ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
        ∀ (u : U → ℝ) (z : Fin m → ℝ),
          z ∈ (fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) →
          eval (Sum.elim u z) (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F) =
            eval (Sum.elim (fun i => u i / (lengths i : ℝ))
              (fun j => z j - eval u (majorTranslationTopCoordinates w A j))) Slow +
              eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) RatPart := by
  obtain ⟨a, ha, hdata⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_separated_data d hd
  let c := detectedTranslationCoordinateConstant d
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorDecomposition_budget d a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
    retained hrank hAret
  let p₁ : ℝ := (p+a)^a
  let B : ℝ := p₁ + (p₁+c)^c + (2*p+2)^d + 1
  have hp₁ : 0 ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).1
  have hpp₁ : p ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).2.1
  obtain ⟨hb₁, hb₂, hbmass, hbden⟩ := hbudget p hp
  have hTpos (i : U) : 0 < (lengths i : ℝ) := by exact_mod_cast hlengths i
  have hlarge₁ (i : U) : Real.exp ((p+a)^a) ≤ (lengths i : ℝ) :=
    (Real.exp_le_exp.mpr hb₁).trans (hlarge i)
  have hrank₁ h := (hrank h).mono (Real.exp_le_exp.mpr hb₁) hTpos
  obtain ⟨b, ω, hLayers, hb, l, E, P, Q, W, v, fast, V, qV,
      hl, hlp, hprod, hE, hQ, hfast, hfastdef, hv, hW, hh, hP, hV,
      hderiv, hqV, hqVp, hVgrid, hVmass, hVcoeff, hret, hgroup⟩ :=
    hdata w hw hwd M hM D htd Ψ F hF A hA K T hT hLip R p hp hgeometry hbound hR hRcap
      origin lengths hlengths hU hlarge₁ β hβ hcorr retained hrank₁ hAret
  let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
  let partner := D.raiseStepRealOrbit htd.le R.orbit
  have hdim : (Fintype.card (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L))) : ℝ) ≤ p₁ := by
    simpa only [Fintype.card_fin] using
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_pair_finrank_le_budget
        (D.raiseStep htd.le) hgeometry (D.raiseStep_geometry htd.le hR.1) ha
  have hbase₀ : (Fintype.card (Fin m) : ℝ) ≤ p :=
    weightedTranslationResidueNilmanifold_base_card_le w d hw hwd M hM hgeometry
  have hbase := hbase₀.trans hpp₁
  obtain ⟨qNat, hqNat, hqNatp, hEmass, hebase, hphaseGrid, hbaseGrid⟩ :=
    detectedTranslationGroupCoordinates_uniform_bounds w d hw hwd M hM (D.raiseStep htd.le)
      b ω hLayers hp₁ (hU.trans hpp₁) hbase hdim hb (fun i => (lengths i : ℝ)) hTpos E Q hE l hl hlp hQ
  have hcpow : 0 ≤ (p₁+c)^c := by positivity
  have hdpow : 0 ≤ (2*p+2)^d := by positivity
  have hpB : p₁ ≤ B := by dsimp only [B]; linarith only [hcpow, hdpow]
  have hcB : (p₁+c)^c ≤ B := by dsimp only [B]; linarith only [hp₁, hdpow]
  have hB : 0 ≤ B := hp₁.trans hpB
  let F₀ := specializeMajorParameters (RingHom.id ℝ)
    (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d (fractionalCoefficientPolynomial F)) 0
  have hF₀mass : realPolynomialMass F₀ ≤ Real.exp B := by
    apply (reducedMajorZeroSlice_mass_le w hw d F hF).trans
    apply (pow_le_pow_left₀ (by positivity)
      (show (Fintype.card U : ℝ) + (Fintype.card (Fin m) : ℝ) + 1 ≤ 2*p+2 by linarith) d).trans
    have hb : (2*p+2)^d ≤ B := by dsimp only [B]; linarith only [hp₁, hcpow]
    exact hb.trans (by linarith only [Real.add_one_le_exp B])
  have hVm : realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp B :=
    hVmass.trans (Real.exp_le_exp.mpr hpB)
  have hEm : realPolynomialMass
      (detectedTranslationNormalizedPhase w d hw hwd M hM (D.raiseStep htd.le) E (fun i => (lengths i : ℝ))) ≤ Real.exp B :=
    hEmass.trans (Real.exp_le_exp.mpr hcB)
  have heb (i : Fin m) : realPolynomialMass
      (detectedTranslationNormalizedBase w d hw hwd M hM (D.raiseStep htd.le) E (fun i => (lengths i : ℝ)) i) ≤ Real.exp B :=
    (hebase i).trans (Real.exp_le_exp.mpr hcB)
  have hqVm : (qV : ℝ) ≤ Real.exp B := hqVp.trans (Real.exp_le_exp.mpr hpB)
  have hqNm : (qNat : ℝ) ≤ Real.exp B := hqNatp.trans (Real.exp_le_exp.mpr hcB)
  have hphaseGrid' := realPolynomialCoefficientGrid_mono (dvd_mul_left qNat qV) hphaseGrid
  have hbaseGrid' i := realPolynomialCoefficientGrid_mono (dvd_mul_left qNat qV) (hbaseGrid i)
  have hVgrid' := denominatorGrid_subset_of_dvd (dvd_mul_right qV qNat) hVgrid
  let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d := liePiEval true
  let hφ := pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le)
  let g := detectedTranslationProjectedGenerators N.filtration w d hw hwd φ hφ v
  have hgspan : Submodule.span ℚ (Set.range g) = fast.toSubmodule := by
    rw [hfastdef]
    exact detectedTranslationProjectedGenerators_span N.filtration w d hw hwd φ hφ W v hv
  have hgdata := residuePairProjectedGenerators_data w d hw hwd M hM (D.raiseStep htd.le)
    b ω hLayers W v hv hp₁ hdim hb hh
  have hgheight : ∀ j i, rationalLogHeight ((weightedBasis w d hw).repr (g j) i) ≤ (p+C)^C :=
    fun j i => (hgdata.2.2.1 j i).trans hb₂
  have hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) fast.toSubmodule := by
    rw [hfastdef]
    exact weightedTranslationGradedProjection_image_graded N.filtration w d hw hwd φ hφ b ω hLayers W hW
  have hVweight : V ∈ weightedSupportLE w d :=
    fun _ hα => (hV (mem_support_iff.mp hα)).le
  have hnormal := exists_detectedTranslation_normalized_weighted_decomposition w d hw hwd M hM
    (D.raiseStep htd.le) b ω hLayers hd (fractionalCoefficientPolynomial F)
    (fractionalCoefficientPolynomial_mem_weightedSupportLE F (Sum.elim (fun _ : U => 1) w) d hF)
    A hA partner E P Q hprod W hP V (fun i => (lengths i : ℝ)) (fun i => (hTpos i).ne')
    (qV*qNat) (Nat.mul_pos hqV hqNat) (Real.exp B) (Real.exp_pos B).le
    hphaseGrid' hbaseGrid' hVgrid' hVweight heb
  dsimp only at hnormal
  rw [← hfastdef] at hnormal
  obtain ⟨Slow, RatPart, hidentity, hSlowMass, hRatGrid, hSlowW, hRatW, _, _⟩ :=
    hnormal hderiv (fun u => (hgroup u).2)
  let qOut := (qV*qNat)^(d+1)
  have hqOut : 0 < qOut := pow_pos (Nat.mul_pos hqV hqNat) _
  have hdsq : (d : ℝ) ≤ ((d+1 : ℕ) : ℝ)^2 := by
    push_cast
    nlinarith [sq_nonneg (d : ℝ), Nat.cast_nonneg (α := ℝ) d]
  have hmassBudget : ((d : ℝ)+3)*(B+2) ≤ (p+C)^C :=
    (mul_le_mul_of_nonneg_right (by linarith : (d : ℝ)+3 ≤ ((d+1 : ℕ) : ℝ)^2+3)
      (by positivity : 0 ≤ B+2)).trans hbmass
  have hdenBudget : 2*((d : ℝ)+1)*B ≤ (p+C)^C :=
    (mul_le_mul_of_nonneg_right (by linarith : 2*((d : ℝ)+1) ≤ 2*(((d+1 : ℕ) : ℝ)^2+1)) hB).trans hbden
  have hSlowFinal : realPolynomialMass Slow ≤ Real.exp ((p+C)^C) := by
    apply hSlowMass.trans
    apply (algebraicMajor_mass_le_exp d hB (realPolynomialMass_nonneg _)
      (realPolynomialMass_nonneg _) (realPolynomialMass_nonneg _) (Real.exp_pos B).le
      hF₀mass hEm hVm le_rfl).trans
    exact Real.exp_le_exp.mpr hmassBudget
  have hqFinal : (qOut : ℝ) ≤ Real.exp ((p+C)^C) :=
    (algebraicMajor_denominator_le_exp d qV qNat hqVm hqNm).trans (Real.exp_le_exp.mpr hdenBudget)
  obtain ⟨hrestGrid, hrestW, hrestIdentity⟩ := algebraic_major_restore_integer_coefficients
    F (Sum.elim (fun _ : U => 1) w) d
    ((fast.toSubmodule.baseChange ℝ).map (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)))
    (majorTranslationTopCoordinates w A) (fun i => (lengths i : ℝ)) Slow RatPart qOut hRatGrid hRatW hidentity
  refine ⟨fast, g, Slow, restoredMajorRemainder F (Sum.elim (fun _ : U => 1) w) d RatPart,
    qOut, ?_, hgspan, hgraded, hgheight,
    weightedTranslationBase_real_image_graded w d hw fast.toSubmodule hgraded g hgspan,
    hret, hSlowFinal, ?_, hqOut, hqFinal,
    hrestGrid, (fun α => den_le_of_mem_denominatorGrid hqOut hrestGrid α), hSlowW, hrestW, hrestIdentity⟩
  · simpa only [Fintype.card_fin] using hdim.trans hb₁
  · intro α
    exact (realPolynomialMass_coeff_le Slow α).trans hSlowFinal

end Erdos3.PolynomialTranslationLie

end

end OAI
