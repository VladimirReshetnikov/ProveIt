/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Fourier.AllocatedJetFourierData
import OAI.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid

namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Classical

theorem euclideanAmbientTorus_normalized {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) {n : ℕ}
    (b : Basis (Fin n) ℝ (euclideanSubspace U)ᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice (euclideanSubspace U))
    (x : euclideanSubspace U × (Fin n → ℤ)) (i : D) :
    subspaceAmbientTorus U (euclideanSubspaceTorusEquiv U
      (normalizedLatticeQuotient (euclideanSubspace U) b hb x)) i =
        (normalizedLatticePoint (euclideanSubspace U) b x i : UnitAddCircle) := by
  let u := normalizedLatticeRepresentative (euclideanSubspace U) b hb x
  have hu : QuotientAddGroup.mk' _ u = normalizedLatticeQuotient (euclideanSubspace U) b hb x :=
    normalizedLatticeRepresentative_mk (euclideanSubspace U) b hb x
  rw [← hu, euclideanSubspaceTorusEquiv_mk, subspaceAmbientTorus_mk, euclideanSubspaceArrayEquiv_apply]
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub]
  obtain ⟨z, hz⟩ := (mem_standardEuclideanLattice D _).mp
    (normalizedLatticePoint_sub_mem_of_mk_eq (euclideanSubspace U) b hb u x hu) i
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨z, by simpa only [zsmul_eq_mul, mul_one, PiLp.sub_apply] using hz⟩

theorem normalizedCoveredChart_projection {D Q : Type*} [Fintype D] [Fintype Q]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) {n : ℕ} (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (bW : Basis Q ℤ (latticeSection (standardEuclideanLattice D) W))
    (d : ℕ) [NeZero d] (x : (W × (Fin n → ℤ)) × (Q → ZMod d)) :
    quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d
      (normalizedCoveredChart W b hb bW d x) = normalizedLatticeQuotient W b hb x.1 := by
  let Γ := (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let e := coverKernelBasisEquiv Γ bW d (Nat.pos_of_ne_zero (NeZero.ne d))
  have hk : quotientIntegerCover Γ d (e x.2).val = 0 := (e x.2).property
  change quotientIntegerCover Γ d (normalizedCoverLift W b hb d x.1 + (e x.2).val) = _
  rw [map_add,
    normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d)), hk, add_zero]

namespace VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredJetAmbientTorus (d : ℕ) (y : EuclideanJetLayers U O) :
    JetAmbientIndex O J → UnitAddCircle := fun a =>
  subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    (quotientIntegerCover (latticeSection (standardEuclideanLattice (J a.1))
      (euclideanSubspace (U a.1))).toAddSubgroup d (y a.1 a.2.1))) a.2.2

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_continuous (d : ℕ) :
    Continuous (coveredJetAmbientTorus (O := O) U d) := by
  apply continuous_pi
  intro a
  exact (continuous_apply a.2.2).comp ((subspaceAmbientTorus_continuous (U a.1)).comp
    ((euclideanSubspaceTorusEquiv_continuous (U a.1)).comp
      ((quotientIntegerCover_continuous _ d).comp
        ((continuous_apply a.2.1).comp (continuous_apply a.1)))))

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_chart
    {I Q : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (Q j)] {n : Fin m → ℕ}
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (z : MixedCoveredJetSource I O Q n d) :
    coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z) =
      fun a => (mixedJetAmbientPoint U b o z.1 a : UnitAddCircle) := by
  funext a
  change subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    (quotientIntegerCover _ d (normalizedCoveredChart _ (b a.1) (hb a.1) (bW a.1) d
      (mixedCoveredJetCoordinates U o d z a.1 a.2.1)))) a.2.2 = _
  rw [normalizedCoveredChart_projection]
  exact euclideanAmbientTorus_normalized (U a.1) (b a.1) (hb a.1) _ a.2.2

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ}
variable {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_coefficient (d : ℕ) (x : CoefficientTorus (K := K) U)
    (j : Fin m) (o : O j) (i : J j) :
    coveredJetAmbientTorus U d (euclideanCoefficientJetMap U root D rows x) ⟨j, o, i⟩ =
      ∑ e : BoundedCoefficientExponent K (j.val + 1),
        ((d : ℤ) * boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e) •
          coefficientAmbientTorus U x ⟨⟨j, e⟩, i⟩ := by
  change subspaceAmbientTorus (U j) (euclideanSubspaceTorusEquiv (U j)
    (d • euclideanCoefficientJetMap U root D rows x j o)) i = _
  rw [euclideanCoefficientJetMap_apply, map_nsmul, map_sum, map_nsmul, map_sum]
  simp only [map_zsmul, euclideanCoefficientEquiv_apply, AddEquiv.apply_symm_apply,
    Pi.smul_apply, Finset.sum_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e _
  change d • (boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e •
    coefficientAmbientTorus U x ⟨⟨j, e⟩, i⟩) = _
  rw [← natCast_zsmul, ← mul_smul]

noncomputable def jetAmbientCoefficientFrequency (d : ℕ)
    (frequency : JetAmbientIndex O J → ℤ) : ∀ j, (K →₀ ℕ) → J j → ℤ :=
  coefficientSlotFrequency (fun s i => ∑ o : O s.1,
    frequency ⟨s.1, o, i⟩ * ((d : ℤ) *
      boundedCoefficientJetMatrix root D (s.1.val + 1) (rows s.1) o s.2))

theorem jetAmbientCoefficientFrequency_character (d : ℕ)
    (frequency : JetAmbientIndex O J → ℤ) (x : CoefficientTorus (K := K) U) :
    (∏ a, CircleFourier.character
      (frequency a • coveredJetAmbientTorus U d (euclideanCoefficientJetMap U root D rows x) a)) =
      coefficientTorusCharacter U (jetAmbientCoefficientFrequency root D rows d frequency) x := by
  let f : CoefficientAmbientIndex K J → ℤ := fun a => ∑ o : O a.1.1,
    frequency ⟨a.1.1, o, a.2⟩ * ((d : ℤ) *
      boundedCoefficientJetMatrix root D (a.1.1.val + 1) (rows a.1.1) o a.1.2)
  change _ = coefficientTorusCharacter U (coefficientSlotFrequency (fun s i => f ⟨s, i⟩)) x
  rw [← coefficientAmbientTorus_character U f x]
  rw [Fintype.prod_sigma, Fintype.prod_sigma]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fintype.prod_prod_type]
  simp only [f, coveredJetAmbientTorus_coefficient, Finset.smul_sum, ← mul_smul,
    CircleFourier.character_fintype_sum, Finset.sum_smul]
  let t := fun (o : O j) (i : J j) (e : BoundedCoefficientExponent K (j.val + 1)) =>
    CircleFourier.character ((frequency ⟨j, o, i⟩ *
      ((d : ℤ) * boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e)) •
        coefficientAmbientTorus U x ⟨⟨j, e⟩, i⟩)
  change (∏ o, ∏ i, ∏ e, t o i e) = ∏ e, ∏ i, ∏ o, t o i e
  calc
    _ = ∏ o, ∏ e, ∏ i, t o i e :=
      Finset.prod_congr rfl (fun _ _ => Finset.prod_comm)
    _ = ∏ e, ∏ o, ∏ i, t o i e := Finset.prod_comm
    _ = _ := Finset.prod_congr rfl (fun _ _ => Finset.prod_comm)

omit [Fintype α] [∀ j, Fintype (J j)] in
theorem jetAmbientCoefficientFrequency_bound (d : ℕ)
    (frequency : JetAmbientIndex O J → ℤ) {C M : ℝ} (hC : 0 ≤ C)
    (hf : ∀ a, |(frequency a : ℝ)| ≤ C)
    (hD : ∀ j o e, |(boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e : ℝ)| ≤ M)
    (j : Fin m) (e : K →₀ ℕ) (he : e.degree ≤ j.val + 1) (i : J j) :
    |(jetAmbientCoefficientFrequency root D rows d frequency j e i : ℝ)| ≤
      Fintype.card (O j) * (C * ((d : ℝ) * M)) := by
  change |(coefficientSlotFrequency _ j e i : ℝ)| ≤ _
  rw [coefficientSlotFrequency, dite_eq_left he, Int.cast_sum]
  calc
    _ ≤ ∑ o : O j, |((frequency ⟨j, o, i⟩ * ((d : ℤ) *
      boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o ⟨e, he⟩) : ℤ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _o : O j, C * ((d : ℝ) * M) := by
      apply Finset.sum_le_sum
      intro o _
      simp only [Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      exact mul_le_mul (hf _) (mul_le_mul_of_nonneg_left (hD j o _) (Nat.cast_nonneg d))
        (mul_nonneg (Nat.cast_nonneg d) (abs_nonneg _)) hC
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "single" => (fun _ : Fin m => Unit)

noncomputable def rowSiteAmbientTorus (s : Finset α) (z : JetAmbientIndex rowTypes J → UnitAddCircle) :
    JetAmbientIndex single J → UnitAddCircle :=
  fun a => ∑ t : rowTypes a.1, rowRestrictedSiteMatrix (rowSets a.1) s t • z ⟨a.1, t, a.2.2⟩

omit [Fintype α] in
theorem rowSiteAmbientTorus_lipschitz (s : Finset α) :
    LipschitzWith (∑ j, ((rowSets j).card : ℝ≥0)) (rowSiteAmbientTorus (J := J) rowSets s) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, t, k⟩
  have hterm (u : rowTypes j) :
      dist (rowRestrictedSiteMatrix (rowSets j) s u • z ⟨j, u, k⟩)
        (rowRestrictedSiteMatrix (rowSets j) s u • w ⟨j, u, k⟩) ≤ dist z w := by
    simp only [rowRestrictedSiteMatrix, booleanReconstructionMatrix]
    split_ifs
    · simpa only [one_zsmul] using dist_le_pi_dist z w ⟨j, u, k⟩
    · simp only [zero_zsmul, dist_self]
      exact dist_nonneg
  have hc : ((rowSets j).card : ℝ≥0) ≤ ∑ j, ((rowSets j).card : ℝ≥0) :=
    Finset.single_le_sum (f := fun j => ((rowSets j).card : ℝ≥0)) (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    dist (rowSiteAmbientTorus rowSets s z ⟨j, t, k⟩) (rowSiteAmbientTorus rowSets s w ⟨j, t, k⟩) ≤
        ∑ _u : rowTypes j, dist z w := (dist_sum_sum_le _ _ _).trans (Finset.sum_le_sum (fun u _ => hterm u))
    _ = ((rowSets j).card : ℝ) * dist z w := by simp
    _ ≤ ((∑ j, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) * dist z w :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg

omit [Fintype α] in
theorem coveredRowsSiteValue_ambient (U : ∀ j, Submodule ℝ (J j → ℝ))
    (d : ℕ) (y : EuclideanJetLayers U rowTypes) (s : Finset α) :
    coveredJetAmbientTorus U d (coveredRowsSiteValue rowSets U y s) =
      rowSiteAmbientTorus rowSets s (coveredJetAmbientTorus U d y) := by
  funext a
  simp only [coveredJetAmbientTorus, coveredRowsSiteValue, rowSiteAmbientTorus,
    map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical Matrix

theorem standardPhysicalSite_apply {q : ℕ} (s : Finset (Fin q)) (i : Fin q) :
    standardPhysicalSite s i = if i ∈ s then 1 else 0 := by
  simp [standardPhysicalSite, integerAffineCube, Matrix.one_apply]

theorem boundedSiteMatrix_standard {q h : ℕ} (s : Finset (Fin q))
    (e : BoundedCoefficientExponent (Fin q) h) :
    boundedSiteMatrix h standardPhysicalSite s e = if e.val.support ⊆ s then 1 else 0 := by
  change (∏ i ∈ e.val.support, standardPhysicalSite s i ^ e.val i) = _
  simp only [standardPhysicalSite_apply]
  by_cases hs : e.val.support ⊆ s
  · rw [ite_eq_left hs]
    exact Finset.prod_eq_one (fun i hi => by rw [ite_eq_left (hs hi), one_pow])
  · rw [ite_eq_right hs]
    obtain ⟨i, hi, his⟩ := Finset.not_subset.mp hs
    exact Finset.prod_eq_zero hi (by rw [ite_eq_right his, zero_pow (Finsupp.mem_support_iff.mp hi)])

theorem boundedCoefficientJetMatrix_standard {q h : ℕ} {O : Type*}
    (rows : O → Finset (Fin q)) (o : O) (e : BoundedCoefficientExponent (Fin q) h) :
    boundedCoefficientJetMatrix (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) h rows o e =
      if rows o = e.val.support then 1 else 0 := by
  rw [← booleanJetExtractionMatrix_mul_boundedSite]
  change (booleanJetExtractionMatrix rows *ᵥ (fun s => boundedSiteMatrix h standardPhysicalSite s e)) o = _
  rw [booleanJetExtractionMatrix_mulVec]
  simp only [boundedSiteMatrix_standard]
  exact booleanCoefficient_monomial e.val.support (rows o)

theorem coefficientExponent_support_card_le {K : Type*} (e : K →₀ ℕ) :
    e.support.card ≤ e.degree := by
  calc
    _ = ∑ _i ∈ e.support, 1 := by simp
    _ ≤ ∑ i ∈ e.support, e i := Finset.sum_le_sum
      (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    _ = _ := rfl

noncomputable def standardJetFrequency {m q : ℕ} {J : Fin m → Type*}
    (d : ℕ) (frequency : JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → ℤ) :
    ∀ j, (Fin q →₀ ℕ) → J j → ℤ :=
  jetAmbientCoefficientFrequency (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) d frequency

theorem standardJetFrequency_apply {m q : ℕ} {J : Fin m → Type*}
    (d : ℕ) (frequency : JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → ℤ)
    (j : Fin m) (e : Fin q →₀ ℕ) (he : e.degree ≤ j.val + 1) (i : J j) :
    standardJetFrequency d frequency j e i =
      frequency ⟨j, ⟨e.support, (coefficientExponent_support_card_le e).trans he⟩, i⟩ * (d : ℤ) := by
  unfold standardJetFrequency jetAmbientCoefficientFrequency
  rw [coefficientSlotFrequency, dite_eq_left he]
  simp only [boundedCoefficientJetMatrix_standard]
  let s : BoundedBooleanJet (Fin q) (j.val + 1) :=
    ⟨e.support, (coefficientExponent_support_card_le e).trans he⟩
  rw [Finset.sum_eq_single s]
  · simp [s]
  · intro b _ hbs
    have hb : b.val ≠ e.support := fun h => hbs (Subtype.ext h)
    simp [hb]
  · simp

theorem standardJetFrequency_bound {m q : ℕ} {J : Fin m → Type*}
    (d : ℕ) (frequency : JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → ℤ)
    {C : ℝ} (hf : ∀ a, |(frequency a : ℝ)| ≤ C)
    (j : Fin m) (e : Fin q →₀ ℕ) (he : e.degree ≤ j.val + 1) (i : J j) :
    |(standardJetFrequency d frequency j e i : ℝ)| ≤ C * d := by
  rw [standardJetFrequency_apply d frequency j e he i, Int.cast_mul, Int.cast_natCast, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  exact mul_le_mul_of_nonneg_right (hf _) (Nat.cast_nonneg d)

theorem standardJetFrequency_character {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (frequency : JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → ℤ)
    (x : CoefficientTorus (K := Fin q) U) :
    (∏ a, CircleFourier.character
      (frequency a • coveredJetAmbientTorus U d (standardPhysicalJetMap U x) a)) =
      coefficientTorusCharacter U (standardJetFrequency d frequency) x :=
  jetAmbientCoefficientFrequency_character U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) d frequency x

end Erdos3.BooleanCubeKernel

end

end OAI
