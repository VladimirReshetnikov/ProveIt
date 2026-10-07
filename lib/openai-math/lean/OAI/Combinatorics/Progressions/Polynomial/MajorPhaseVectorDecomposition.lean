import OAI.Combinatorics.Progressions.Estimates.LowTaggedGradedSpace
import OAI.Combinatorics.Progressions.Estimates.RestrictedSymbolAlgebraicMajorStep
import OAI.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

def MajorPhaseDetectedConclusion {m : ℕ} {X L : Type}
    [Fintype X] [LieRing L] [LieAlgebra ℚ L]
    (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (N : X → ℕ) (B : ℝ) : Prop :=
  let w := lowTaggedWeight J d
  ∃ (fast : LieSubalgebra ℚ (weightedSubalgebra w d))
    (g : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → weightedSubalgebra w d)
    (S : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (R : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ) (q : ℕ),
    (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L) : ℝ) ≤ B ∧
    Submodule.span ℚ (Set.range g) = fast.toSubmodule ∧
    BasisGradedSubmodule (weightedBasis w d (lowTaggedWeight_pos J d))
      (weightedBasisGrade w d) fast.toSubmodule ∧
    (∀ j i, rationalLogHeight ((weightedBasis w d (lowTaggedWeight_pos J d)).repr (g j) i) ≤ B) ∧
    BasisGradedSubmodule (Pi.basisFun ℝ _) w ((fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
    (∀ h, lowTaggedRetained J d U h ≤ (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
    realPolynomialMass S ≤ Real.exp B ∧
    (∀ α, |S.coeff α| ≤ Real.exp B) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp B ∧
    (fun α => R.coeff α) ∈ denominatorGrid q ∧
    (∀ α, (R.coeff α).den ≤ q) ∧
    S ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) w) d ∧
    R ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) w) d ∧
    ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ),
      z ∈ (fast.toSubmodule.baseChange ℝ).map
        (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) →
      MvPolynomial.eval (Sum.elim u z)
          (weightedHomogeneousComponent (Sum.elim (fun _ : X => 1) w) d F) =
        MvPolynomial.eval (Sum.elim (fun i => u i / (N i : ℝ))
          (fun j => z j - MvPolynomial.eval u
            (majorTranslationTopCoordinates w
              (fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)) j))) S +
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) R

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module RationalFilteredNilmanifold PolynomialTranslationLie

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] (d : ℕ)

noncomputable def majorPhaseTaggedGenerators {A : Type*}
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d)
    (j : Fin m) (hj : j.val + 1 ≤ d) (a : A) (i : J j) : ℚ :=
  (g a).val.base (lowTaggedSlot J d j hj i)

 theorem majorPhaseTaggedGenerators_span {A : Type*}
    (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d))
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d)
    (hg : Submodule.span ℚ (Set.range g) = fast.toSubmodule)
    (hgraded : BasisGradedSubmodule
      (weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d))
      (weightedBasisGrade (lowTaggedWeight J d) d) fast.toSubmodule)
    (j : Fin m) (hj : j.val + 1 ≤ d) :
    lowTaggedSubspaceFamily J d
      ((fast.toSubmodule.baseChange ℝ).map
        (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))) j =
      Submodule.span ℝ (Set.range (fun a i => (majorPhaseTaggedGenerators J d g j hj a i : ℝ))) := by
  have hK := weightedTranslationBase_real_image_graded (lowTaggedWeight J d) d
    (lowTaggedWeight_pos J d) fast.toSubmodule hgraded g hg
  have hspan := realifyCoordinateMap_image_eq_span fast.toSubmodule g hg
    (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype)
  rw [hspan] at hK ⊢
  exact lowTaggedSubspaceFamily_span J d _ hK j hj

 theorem majorPhaseTaggedGenerators_logHeight {A : Type*}
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d) {B : ℝ}
    (hheight : ∀ a i, rationalLogHeight
      ((weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d)).repr (g a) i) ≤ B)
    (j : Fin m) (hj : j.val + 1 ≤ d) (a : A) (i : J j) :
    rationalLogHeight (majorPhaseTaggedGenerators J d g j hj a i) ≤ B := by
  have h := hheight a (Sum.inl (lowTaggedSlot J d j hj i))
  simpa only [weightedBasis_repr_inl, majorPhaseTaggedGenerators] using h

theorem majorPhaseTaggedGenerators_mem_iff {A : Type*}
    (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d))
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d)
    (hg : Submodule.span ℚ (Set.range g) = fast.toSubmodule)
    (hgraded : BasisGradedSubmodule
      (weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d))
      (weightedBasisGrade (lowTaggedWeight J d) d) fast.toSubmodule)
    (x : ∀ j, J j → ℝ) :
    lowTaggedCoordinates J d x ∈ (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype)) ↔
      ∀ j (hj : j.val + 1 ≤ d), x j ∈
        Submodule.span ℝ (Set.range (fun a i => (majorPhaseTaggedGenerators J d g j hj a i : ℝ))) := by
  have hK := weightedTranslationBase_real_image_graded (lowTaggedWeight J d) d
    (lowTaggedWeight_pos J d) fast.toSubmodule hgraded g hg
  rw [lowTaggedCoordinates_mem_iff_low J d _ hK x]
  constructor
  · intro hx j hj
    rw [← majorPhaseTaggedGenerators_span J d fast g hg hgraded j hj]
    exact hx j hj
  · intro hx j hj
    rw [majorPhaseTaggedGenerators_span J d fast g hg hgraded j hj]
    exact hx j hj

theorem MajorPhaseDetectedConclusion.exists_tagged_generators
    {X L : Type} [Fintype X] [LieRing L] [LieAlgebra ℚ L]
    (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (N : X → ℕ) (B : ℝ)
    (h : MajorPhaseDetectedConclusion (L := L) J d U poly c F N B) :
    ∃ (n : ℕ) (V : ∀ j, Submodule ℝ (J j → ℝ))
      (v : ∀ j : Fin m, j.val + 1 ≤ d → Fin n → J j → ℚ),
      (n : ℝ) ≤ B ∧ (∀ j, U j ≤ V j) ∧
      (∀ j (hj : j.val + 1 ≤ d), V j =
        Submodule.span ℝ (Set.range (fun a i => (v j hj a i : ℝ)))) ∧
      (∀ j (hj : j.val + 1 ≤ d) a i, rationalLogHeight (v j hj a i) ≤ B) ∧
      ∀ j, d < j.val + 1 → V j = ⊤ := by
  obtain ⟨fast, g, S, R, q, hn, hg, hgraded, hheight, hKgraded, hret, _⟩ := h
  let K := (fast.toSubmodule.baseChange ℝ).map
    (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))
  refine ⟨_, lowTaggedSubspaceFamily J d K, majorPhaseTaggedGenerators J d g, hn,
    le_lowTaggedSubspaceFamily J d U K hret, ?_, ?_, ?_⟩
  · exact majorPhaseTaggedGenerators_span J d fast g hg hgraded
  · exact majorPhaseTaggedGenerators_logHeight J d g hheight
  · exact lowTaggedSubspaceFamily_of_high J d K

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

variable {m : ℕ} {X L : Type} [Fintype X] [LieRing L] [LieAlgebra ℚ L]
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)

noncomputable def majorPhaseDetectedRealBase
    (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d)) :
    Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :=
  (fast.toSubmodule.baseChange ℝ).map
    (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))

variable {η V : Type*} [Fintype η] [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
variable (N : X → ℕ) (B : ℝ) (eV : Basis η ℝ V)
variable (p : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ V)

def MajorPhaseVectorDetectedConclusion : Prop :=
  let w := lowTaggedWeight J d
  let wt := Sum.elim (fun _ : X => 1) w
  ∃ (fast : η → LieSubalgebra ℚ (weightedSubalgebra w d))
    (g : η → Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → weightedSubalgebra w d)
    (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ V) (q : ℕ),
    (∀ i, (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L) : ℝ) ≤ B ∧
      Submodule.span ℚ (Set.range (g i)) = (fast i).toSubmodule ∧
      BasisGradedSubmodule (weightedBasis w d (lowTaggedWeight_pos J d))
        (weightedBasisGrade w d) (fast i).toSubmodule ∧
      ∀ j a, rationalLogHeight ((weightedBasis w d (lowTaggedWeight_pos J d)).repr (g i j) a) ≤ B) ∧
    (∀ i, BasisGradedSubmodule (Pi.basisFun ℝ _) w (majorPhaseDetectedRealBase J d (fast i))) ∧
    (∀ i h, lowTaggedRetained J d U h ≤ majorPhaseDetectedRealBase J d (fast i)) ∧
    (∀ i, realPolynomialMass (coordinate (eV.coord i).toAddMonoidHom slow) ≤ Real.exp B) ∧
    (∀ i α, |eV.coord i (coefficients slow α)| ≤ Real.exp B) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * B) ∧
    (∀ i, realPolynomialCoefficientGrid q (coordinate (eV.coord i).toAddMonoidHom rat)) ∧
    (∀ i, coordinate (eV.coord i).toAddMonoidHom slow ∈ weightedSupportLE wt d) ∧
    (∀ i, coordinate (eV.coord i).toAddMonoidHom rat ∈ weightedSupportLE wt d) ∧
    ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ),
      (∀ i, z ∈ majorPhaseDetectedRealBase J d (fast i)) →
      eval₂ (Sum.elim u z) p =
        eval₂ (Sum.elim u z) (realChartSubstitute
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (majorTranslationTopCoordinates w
              (fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)))) slow) +
        eval₂ (Sum.elim u z) rat

theorem majorPhaseVectorDetectedConclusion_of_coordinates
    (hp : ∀ α, Finsupp.weight (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) α ≠ d →
      coefficients p α = 0)
    (hscalar : ∀ i, MajorPhaseDetectedConclusion (L := L) J d U poly c
      (coordinate (eV.coord i).toAddMonoidHom p) N B) :
    MajorPhaseVectorDetectedConclusion (L := L) J d U poly c N B eV p := by
  classical
  simp only [MajorPhaseDetectedConclusion] at hscalar
  choose fast g S Q q hdim hspan hgrade hheight hbase hretain hmass hcoeff
    hq hqB hgrid hden hS hQ hvalue using hscalar
  let slow := ofCoordinates (R := ℚ) eV S
  let rat := ofCoordinates (R := ℚ) eV (fun i => MvPolynomial.map (algebraMap ℚ ℝ) (Q i))
  refine ⟨fast, g, slow, rat, ∏ i, q i,
    (fun i => ⟨hdim i, hspan i, hgrade i, hheight i⟩), hbase, hretain, ?_, ?_,
    majorPhaseCoordinateDenominator_pos q hq,
    majorPhaseCoordinateDenominator_le_exp q B hqB, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [slow, coordinate_ofCoordinates] using hmass i
  · intro i α
    have h := congrArg (fun polynomial : MvPolynomial _ _ => polynomial.coeff α)
      (coordinate_ofCoordinates (R := ℚ) eV S i)
    rw [coeff_coordinate] at h
    exact h ▸ hcoeff i α
  · intro i
    dsimp only [rat]
    rw [coordinate_ofCoordinates]
    exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr
      (majorPhaseCoordinateDenominator_grid q Q hgrid i)
  · intro i
    simpa only [slow, coordinate_ofCoordinates] using hS i
  · intro i
    dsimp only [rat]
    rw [coordinate_ofCoordinates]
    intro α hα
    apply hQ i
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    apply MvPolynomial.mem_support_iff.mp hα
    change (Q i).coeff α = 0 at hz
    change (MvPolynomial.map (algebraMap ℚ ℝ) (Q i)).coeff α = 0
    rw [MvPolynomial.coeff_map, hz, map_zero]
  · intro u z hz
    rw [eval₂_normalizedRealPolynomialChart]
    apply eV.equivFun.injective
    funext i
    change eV.coord i (eval₂ (Sum.elim u z) p) = eV.coord i (_ + _)
    rw [map_add, coordinate_eval₂, coordinate_eval₂, coordinate_eval₂]
    simp only [slow, rat, coordinate_ofCoordinates, MvPolynomial.eval_map]
    have hhom : (coordinate (eV.coord i).toAddMonoidHom p).IsWeightedHomogeneous
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d := by
      intro α hα
      by_contra hweight
      apply hα
      rw [coeff_coordinate, hp α hweight, map_zero]
    simpa only [weightedHomogeneousComponent_eq_self hhom] using hvalue i u z (hz i)

omit [Fintype X] in

theorem majorPhaseVectorDetectedConclusion_grade_data
    (h : MajorPhaseVectorDetectedConclusion (L := L) J d U poly c N B eV p) :
    ∃ (K : η → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
      (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ V) (q : ℕ),
      (∀ i, BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d) (K i)) ∧
      (∀ i h, lowTaggedRetained J d U h ≤ K i) ∧
      (∀ i α, |eV.coord i (coefficients slow α)| ≤ Real.exp B) ∧
      0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * B) ∧
      (∀ i, realPolynomialCoefficientGrid q (coordinate (eV.coord i).toAddMonoidHom rat)) ∧
      (∀ i, coordinate (eV.coord i).toAddMonoidHom slow ∈
        weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d) ∧
      (∀ i, coordinate (eV.coord i).toAddMonoidHom rat ∈
        weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d) ∧
      ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ),
        (∀ i, z ∈ K i) →
        eval₂ (Sum.elim u z) p =
          eval₂ (Sum.elim u z) (realChartSubstitute
            (normalizedRealPolynomialChart (fun i => (N i : ℝ))
              (majorTranslationTopCoordinates (lowTaggedWeight J d)
                (fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)))) slow) +
          eval₂ (Sum.elim u z) rat := by
  obtain ⟨fast, g, slow, rat, q, _, hgrade, hretain, _, hcoeff, hq, hqB,
    hgrid, hslow, hrat, hvalue⟩ := h
  exact ⟨fun i => majorPhaseDetectedRealBase J d (fast i), slow, rat, q,
    hgrade, hretain, hcoeff, hq, hqB, hgrid, hslow, hrat, hvalue⟩

end Erdos3.VectorPolynomial

end

end OAI
