/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
import OAI.Combinatorics.Progressions.Geometry.BoundedBooleanRowTransport
import OAI.Combinatorics.Progressions.Linear.PhysicalCubeMatrix

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def identityCoefficientFrame (K : Type*) : Option K → K → ℝ :=
  fun k i => k.elim 0 (fun j => if j = i then 1 else 0)

theorem affineParameterSubstitution_identity {K : Type*} [Fintype K] :
    affineParameterSubstitution (identityCoefficientFrame K) = fun i => MvPolynomial.X i := by
  funext i
  simp [affineParameterSubstitution, identityCoefficientFrame, rowPolynomial]

theorem affineSampleCoefficientArray_identity {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial K ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (s : CoefficientSlot K m) :
    (affineSampleCoefficientArray U p hm (identityCoefficientFrame K) s).val =
      coefficients (p s.1) s.2.val := by
  rw [affineSampleCoefficientArray_val, affineParameterSubstitution_identity, substitute_X]

theorem exists_coefficient_sample_realization {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (d : ℕ) (hd : 0 < d) (x : CoefficientTorus (K := K) U) :
    ∃ (p : ∀ j, VectorPolynomial K ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (p j) e ∈ U j),
      (∀ j, DegreeLE (1 : K → ℕ) (j.val + 1) (p j)) ∧
      affineCoefficientCoverSample U p hm d (identityCoefficientFrame K) = x := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  let p := fun j : Fin m => map (U j).subtype
    (boundedArrayPolynomial (j.val + 1) (fun e => (d : ℝ) • a ⟨j,e⟩))
  have hm : ∀ j e, coefficients (p j) e ∈ U j := by
    intro j e
    rw [show p j = map (U j).subtype
      (boundedArrayPolynomial (j.val + 1) (fun e => (d : ℝ) • a ⟨j,e⟩)) from rfl,
      coefficients_map]
    exact Subtype.property _
  have hp (j) : DegreeLE (1 : K → ℕ) (j.val + 1) (p j) :=
    (boundedArrayPolynomial_degreeLE (j.val + 1) _).map (U j).subtype
  refine ⟨p, hm, hp, ?_⟩
  have ha : affineSampleCoefficientArray U p hm (identityCoefficientFrame K) = (d : ℝ) • a := by
    funext s
    apply Subtype.ext
    rw [affineSampleCoefficientArray_identity]
    dsimp only [p]
    rw [coefficients_map, boundedArrayPolynomial_coeff]
    rfl
  have hn : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  rw [affineCoefficientCoverSample, ha, smul_smul, inv_mul_cancel₀ hn, one_smul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

def physicalCubeVertexValue {I α : Type*} (v : I → (Unit ⊕ α) → ℤ) (s : Finset α) : I → ℤ :=
  fun i => v i (.inl ()) + ∑ a ∈ s, v i (.inr a)

theorem physicalCubeVertexValue_rootDifferences {I K α : Type*} [Fintype K]
    (root : K → ℤ) (difference : Matrix α K ℤ) (base : I → ℤ)
    (z : Option K × I → ℤ) (s : Finset α) :
    physicalCubeVertexValue (physicalCubeRootDifferences root difference base z) s =
      jointIntegerPhysicalSite (integerAffineCube root difference s) (base, z) := by
  funext i
  exact physicalCubeRootDifferences_vertex root difference base z i s

theorem integerSiteValue_affine_physical {I K : Type*} [Fintype K] {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) (base : I → ℤ)
    (z : Option K × I → ℤ) (s : Finset (Fin q)) :
    (fun i => (base i : ℝ)) + integerSiteValue (affineSite root difference s)
        (fun k i => (z (k, i) : ℝ)) =
      fun i => (physicalCubeVertexValue (physicalCubeRootDifferences root (Matrix.of difference) base z) s i : ℝ) := by
  rw [physicalCubeVertexValue_rootDifferences]
  change (fun i => (base i : ℝ)) + physicalAffineSite (integerAffineCube root (Matrix.of difference) s) z = _
  exact (jointIntegerPhysicalSite_cast (integerAffineCube root (Matrix.of difference) s) (base, z)).symm

noncomputable def physicalCubeCoveredSample {I : Type*} {m q : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (v : I → (Unit ⊕ Fin q) → ℤ) :
    ∀ j, SubspaceArrayTorus (Finset (Fin q)) (U j) := fun j =>
  QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
    ((D : ℝ)⁻¹ • fun s => eval (fun i => (physicalCubeVertexValue v s i : ℝ))
      (restrictCoefficients (U j) (p j) (hm j)))

theorem affineCoveredSiteSample_physical {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : I → ℤ) (z : Option K × I → ℤ) :
    affineCoveredSiteSample U root difference D
        (fun j => translate (fun i => (base i : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
        (fun k i => (z (k, i) : ℝ)) =
      physicalCubeCoveredSample U D p hm (physicalCubeRootDifferences root (Matrix.of difference) base z) := by
  funext j
  rw [affineCoveredSiteSample_eq_values]
  dsimp only [physicalCubeCoveredSample]
  apply congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j)))
  apply congrArg (fun v : Finset (Fin q) → U j => (D : ℝ)⁻¹ • v)
  funext s
  apply Subtype.ext
  rw [eval_restrictCoefficients, eval_restrictCoefficients, eval_translate]
  apply congrArg (fun x : I → ℝ => eval x (p j))
  funext i
  have h := congrFun (integerSiteValue_affine_physical root difference base z s) i
  simpa only [Pi.add_apply, add_comm] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

noncomputable def physicalCubeSiteTest {I : Type*} {q : ℕ}
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (v : I → (Unit ⊕ Fin q) → ℤ) : ℂ :=
  ∏ s, test s (fun i => (physicalCubeVertexValue v s i : ℝ))

theorem physicalCubeSiteTest_norm_le {I : Type*} {q : ℕ}
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1)
    (v : I → (Unit ⊕ Fin q) → ℤ) : ‖physicalCubeSiteTest test v‖ ≤ 1 := by
  rw [physicalCubeSiteTest, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun s _ => htest s _)

theorem layeredSiteWeight_physicalCube {I K : Type*} [Fintype K] {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) (base : I → ℤ)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (z : Option K × I → ℤ) :
    layeredSiteWeight 0 (fun s => affineSite root difference s)
        (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ)) =
      physicalCubeSiteTest test (physicalCubeRootDifferences root (Matrix.of difference) base z) := by
  simp only [layeredSiteWeight, map_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, one_mul, physicalCubeSiteTest]
  apply Finset.prod_congr rfl
  intro s _
  rw [integerSiteValue_affine_physical]

noncomputable def physicalCubeCoveredTest {I K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ) (c : F → ℂ)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (v : I → (Unit ⊕ Fin q) → ℤ) : ℂ :=
  physicalCubeSiteTest test v * retainedSiteFourierSum U root difference frequency b c
    (physicalCubeCoveredSample U D p hm v)

theorem physicalCubeCoveredTest_norm_le {I K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ) (c : F → ℂ)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1)
    (v : I → (Unit ⊕ Fin q) → ℤ) :
    ‖physicalCubeCoveredTest U root difference D p hm frequency b c test v‖ ≤ ∑ a, ‖c a‖ := by
  unfold physicalCubeCoveredTest
  rw [norm_mul]
  exact (mul_le_mul (physicalCubeSiteTest_norm_le test htest v)
    (retainedSiteFourierSum_norm_le U root difference frequency b c _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem physicalCubeCoveredTest_of_frame {I K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ) (c : F → ℂ)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (base : I → ℤ) (z : Option K × I → ℤ) :
    layeredSiteWeight 0 (fun s => affineSite root difference s)
        (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ)) *
      retainedSiteFourierSum U root difference frequency b c
        (affineCoveredSiteSample U root difference D
          (fun j => translate (fun i => (base i : ℝ)) (p j))
          (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
          (fun k i => (z (k, i) : ℝ))) =
      physicalCubeCoveredTest U root difference D p hm frequency b c test
        (physicalCubeRootDifferences root (Matrix.of difference) base z) := by
  rw [layeredSiteWeight_physicalCube, affineCoveredSiteSample_physical]
  rfl

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

noncomputable def starVertexSiteFactor {α V : Type*} [Fintype α]
    (factor : Unit ⊕ α → V → ℂ) (s : Finset α) (v : V) : ℂ :=
  ∏ i, if spatialStarVertex i = s then factor i v else 1

theorem starVertexSiteFactor_bound {α V : Type*} [Fintype α]
    (factor : Unit ⊕ α → V → ℂ) (hfactor : ∀ i v, ‖factor i v‖ ≤ 1)
    (s : Finset α) (v : V) : ‖starVertexSiteFactor factor s v‖ ≤ 1 := by
  rw [starVertexSiteFactor, norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i _
  split_ifs
  · exact hfactor i v
  · simp

theorem starVertexSiteFactor_prod {α V : Type*} [Fintype α]
    (factor : Unit ⊕ α → V → ℂ) (v : Finset α → V) :
    (∏ s, starVertexSiteFactor factor s (v s)) =
      ∏ i, factor i (v (spatialStarVertex i)) := by
  unfold starVertexSiteFactor
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  simp

theorem physicalCubeVertexValue_star {X α : Type*}
    (v : X → (Unit ⊕ α) → ℤ) (i : Unit ⊕ α) :
    physicalCubeVertexValue v (spatialStarVertex i) = fun x => spatialStar (v x) i := by
  funext x
  exact (spatialStar_vertex (v x) i).symm

theorem starVertexSiteFactor_physicalCube {X α : Type*} [Fintype α]
    (factor : Unit ⊕ α → (X → ℤ) → ℂ) (v : X → (Unit ⊕ α) → ℤ) :
    (∏ s, starVertexSiteFactor factor s (physicalCubeVertexValue v s)) =
      ∏ i, factor i (fun x => spatialStar (v x) i) := by
  rw [starVertexSiteFactor_prod]
  simp only [physicalCubeVertexValue_star]

theorem starVertexSiteFactor_test {X : Type*} {dim : ℕ}
    (factor : Unit ⊕ Fin dim → (X → ℤ) → ℂ)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    (∏ i, factor i (fun x => spatialStar (v x) i)) * physicalCubeSiteTest test v =
      ∏ s, test s (fun x => (physicalCubeVertexValue v s x : ℝ)) *
        starVertexSiteFactor factor s (physicalCubeVertexValue v s) := by
  rw [Finset.prod_mul_distrib, starVertexSiteFactor_physicalCube]
  exact mul_comm _ _

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem coefficientTorusFourierSum_sample {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (z : Option K → I → ℝ) :
    coefficientTorusFourierSum U frequency c (affineSampleCoefficientTorus U p hm z) =
      affineCubeFourierSum frequency p c z := by
  unfold coefficientTorusFourierSum affineCubeFourierSum
  apply Finset.sum_congr rfl
  intro a _
  rw [coefficientTorusCharacter_sample U (frequency a) p hp hm z]

theorem coefficientCoverSample_sites {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (z : Option K → I → ℝ) :
    coefficientSiteTorusMap U (fun s k => affineSite root difference s (some k))
        (affineCoefficientCoverSample U p hm D z) =
      affineCoveredSiteSample U root difference D p hm z := by
  funext j
  rw [affineCoefficientCoverSample, coefficientSiteTorusMap_mk]
  change QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
    (matrixModuleAction (fun s d =>
      (boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k)) s d : ℝ))
      ((D : ℝ)⁻¹ • fun d => coefficients
        (substitute (affineParameterSubstitution z) (restrictCoefficients (U j) (p j) (hm j))) d.val)) = _
  rw [map_smul, ← siteEvaluation_bounded_coefficients _ _
    (degreeLE_substitute_affine _ (affineParameterSubstitution_degree z) _
      (degreeLE_restrictCoefficients (U j) (p j) (hm j) (hp j)))]
  rfl

noncomputable def physicalCubeEuclideanSample {I : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (v : I → (Unit ⊕ Fin q) → ℤ) :
    EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) :=
  euclideanJetEquiv U (siteBooleanJetTorusMap U
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    (physicalCubeCoveredSample U D p hm v))

theorem coefficientCoverSample_physicalJet {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : I → ℤ) (z : Option K × I → ℤ) :
    euclideanCoefficientJetMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
        (affineCoefficientCoverSample U (fun j => translate (fun i => (base i : ℝ)) (p j))
          (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
          D (fun k i => (z (k, i) : ℝ))) =
      physicalCubeEuclideanSample U D p hm (physicalCubeRootDifferences root (Matrix.of difference) base z) := by
  have hs := coefficientCoverSample_sites U root difference D
    (fun j => translate (fun i => (base i : ℝ)) (p j))
    (fun j => degreeLE_translate (1 : I → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
    (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
    (fun k i => (z (k, i) : ℝ))
  rw [affineCoveredSiteSample_physical] at hs
  exact congrArg (fun t : SiteTorus (Finset (Fin q)) U => euclideanJetEquiv U
    (siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) t)) hs

noncomputable def physicalCubePositiveTest {I : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (D : ℕ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (f : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (v : I → (Unit ⊕ Fin q) → ℤ) : ℂ :=
  physicalCubeSiteTest test v * (f (physicalCubeEuclideanSample U D p hm v) : ℂ)

theorem physicalCubePositiveTest_norm_le {I : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (D : ℕ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (f : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    {B : ℝ} (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) B)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1)
    (v : I → (Unit ⊕ Fin q) → ℤ) : ‖physicalCubePositiveTest U D p hm f test v‖ ≤ B := by
  rw [physicalCubePositiveTest, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hf _).1]
  exact (mul_le_mul_of_nonneg_right (physicalCubeSiteTest_norm_le test htest v) (hf _).1).trans
    (by simpa only [one_mul] using (hf _).2)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

noncomputable def physicalCubeRowSample {X : Type*} {m dim : ℕ}
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (rows : ∀ j, O j → Finset (Fin dim))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    EuclideanJetLayers U O :=
  euclideanJetEquiv U (siteBooleanJetTorusMap U rows (physicalCubeCoveredSample U d p hm v))

theorem physicalCubeRowSample_standard {X : Type*} {m dim : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    physicalCubeRowSample U d
      (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
      p hm v = physicalCubeEuclideanSample U d p hm v := rfl

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem sampled_jet_approximation_global {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (d : ℕ) (hd : 0 < d)
    (φ : SiteTorus (Finset (Fin q)) U → ℂ)
    (g : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    {η : ℝ}
    (happrox : ∀ (p : ∀ j, VectorPolynomial K ℝ (J j → ℝ)),
      (∀ j, DegreeLE (1 : K → ℕ) (j.val + 1) (p j)) →
      ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K → K → ℝ),
        ‖φ (affineCoveredSiteSample U root difference d p hm z) -
          (g (euclideanCoefficientJetMap U root (Matrix.of difference)
            (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
            (affineCoefficientCoverSample U p hm d z)) : ℂ)‖ ≤ η)
    (x : CoefficientTorus (K := K) U) :
    ‖φ (coefficientSiteTorusMap U (fun s k => affineSite root difference s (some k)) x) -
      (g (euclideanCoefficientJetMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) x) : ℂ)‖ ≤ η := by
  obtain ⟨p, hm, hp, hx⟩ := exists_coefficient_sample_realization U d hd x
  have h := happrox p hp hm (identityCoefficientFrame K)
  have hs := coefficientCoverSample_sites U root difference d p hp hm (identityCoefficientFrame K)
  rw [← hs, hx] at h
  exact h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix

def standardPhysicalCubeOutput {X : Type*} {q : ℕ}
    (z : Option (Fin q) × X → ℤ) : X → (Unit ⊕ Fin q) → ℤ :=
  fun x => Sum.elim (fun _ => z (none,x)) (fun i => z (some i,x))

def standardPhysicalCubeFrame {X : Type*} {q : ℕ}
    (v : X → (Unit ⊕ Fin q) → ℤ) : Option (Fin q) × X → ℤ :=
  fun z => Option.elim' (v z.2 (.inl ())) (fun i => v z.2 (.inr i)) z.1

theorem standardPhysicalCubeOutput_frame {X : Type*} {q : ℕ}
    (v : X → (Unit ⊕ Fin q) → ℤ) :
    standardPhysicalCubeOutput (standardPhysicalCubeFrame v) = v := by
  funext x i
  rcases i with i | i
  · cases i; rfl
  · rfl

theorem standardPhysicalCubeFrame_injective {X : Type*} {q : ℕ} :
    Function.Injective (standardPhysicalCubeFrame (X := X) (q := q)) := by
  intro v w h
  have he := congrArg standardPhysicalCubeOutput h
  simpa only [standardPhysicalCubeOutput_frame] using he

theorem physicalCubeRootDifferences_standard {X : Type*} {q : ℕ}
    (z : Option (Fin q) × X → ℤ) :
    physicalCubeRootDifferences (fun _ : Fin q => 0) (1 : Matrix (Fin q) (Fin q) ℤ) 0 z =
      standardPhysicalCubeOutput z := by
  funext x i
  rcases i with i | i
  · cases i
    rw [physicalCubeRootDifferences_root]
    simp [jointIntegerPhysicalSite, integerPhysicalSite, standardPhysicalCubeOutput]
  · rw [physicalCubeRootDifferences_direction]
    simp [Matrix.one_apply, standardPhysicalCubeOutput]

noncomputable def standardPhysicalJetMap {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    CoefficientTorus (K := Fin q) U →+
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) :=
  euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))

theorem affineCoveredSiteSample_zero_base_physical {X K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (d : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K × X → ℤ) :
    affineCoveredSiteSample U root difference d p hm (fun k x => (z (k,x) : ℝ)) =
      physicalCubeCoveredSample U d p hm (physicalCubeRootDifferences root (Matrix.of difference) 0 z) := by
  funext j
  rw [affineCoveredSiteSample_eq_values]
  dsimp only [physicalCubeCoveredSample]
  apply congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j)))
  apply congrArg (fun v : Finset (Fin q) → U j => (d : ℝ)⁻¹ • v)
  funext s
  apply congrArg (fun x => eval x (restrictCoefficients (U j) (p j) (hm j)))
  funext x
  have h := congrFun (integerSiteValue_affine_physical root difference (0 : X → ℤ) z s) x
  simpa only [Pi.zero_apply, Int.cast_zero, Pi.add_apply, zero_add] using h

theorem coefficientCoverSample_standardPhysicalJet {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option (Fin q) × X → ℤ) :
    standardPhysicalJetMap U
      (affineCoefficientCoverSample U p hm d (fun k x => (z (k,x) : ℝ))) =
      physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z) := by
  let D : Fin q → Fin q → ℤ := fun i j => if i = j then 1 else 0
  have hD : Matrix.of D = (1 : Matrix (Fin q) (Fin q) ℤ) := by
    ext i j
    simp [D, Matrix.one_apply]
  have h := coefficientCoverSample_sites U (fun _ : Fin q => 0)
    D d p hp hm (fun k x => (z (k,x) : ℝ))
  have hs := affineCoveredSiteSample_zero_base_physical U (fun _ : Fin q => 0)
    D d p hm z
  rw [hs, hD, physicalCubeRootDifferences_standard] at h
  have hjet : euclideanCoefficientJetMap U (fun _ : Fin q => 0) (Matrix.of D)
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
      (affineCoefficientCoverSample U p hm d (fun k x => (z (k,x) : ℝ))) =
      physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z) :=
    congrArg (fun t : SiteTorus (Finset (Fin q)) U => euclideanJetEquiv U
    (siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) t)) h
  rw [hD] at hjet
  exact hjet

theorem physicalCubeEuclideanSample_frame {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalCubeEuclideanSample U d p hm v = standardPhysicalJetMap U
      (affineCoefficientCoverSample U p hm d (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))) := by
  rw [coefficientCoverSample_standardPhysicalJet U d p hp hm, standardPhysicalCubeOutput_frame]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem physicalCubeRowSample_fintype_independent
    {X : Type*} {m dim : ℕ} {J O : Fin m → Type*} [hJ : ∀ j, Fintype (J j)]
    (hO₁ hO₂ : ∀ j, Fintype (O j))
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (rows : ∀ j, O j → Finset (Fin dim))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) :
    @physicalCubeRowSample X m dim J O hJ hO₁ U d rows p hm =
      @physicalCubeRowSample X m dim J O hJ hO₂ U d rows p hm := by
  exact congrArg (fun hO => @physicalCubeRowSample X m dim J O hJ hO U d rows p hm)
    (Subsingleton.elim hO₁ hO₂)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

theorem coefficientSite_eq_of_euclideanJet_eq {α K L : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype L] {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (root' : L → ℤ) (D' : Matrix α L ℤ)
    (x : CoefficientTorus (K := K) U) (y : CoefficientTorus (K := L) U)
    (h : euclideanCoefficientJetMap U root D
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) x =
      euclideanCoefficientJetMap U root' D'
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y) :
    coefficientSiteTorusMap U (integerAffineCube root D) x =
      coefficientSiteTorusMap U (integerAffineCube root' D') y := by
  have hj := (euclideanJetEquiv U).injective h
  have hs := congrArg (siteFromLowBooleanJets U) hj
  exact (siteFromLowBooleanJets_coefficient U root D x).symm.trans
    (hs.trans (siteFromLowBooleanJets_coefficient U root' D' y))

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

def standardPhysicalSite {q : ℕ} : Finset (Fin q) → Fin q → ℤ :=
  integerAffineCube (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)

theorem standard_jet_site_approximation {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice (Fin q) a ≤ D.mulVecLin.range)
    (φ : SiteTorus (Finset (Fin q)) U → ℂ)
    (g : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    {η : ℝ}
    (happrox : ∀ x : CoefficientTorus (K := K) U,
      ‖φ (coefficientSiteTorusMap U (integerAffineCube root D) x) -
        (g (euclideanCoefficientJetMap U root D
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) x) : ℂ)‖ ≤ η)
    (y : CoefficientTorus (K := Fin q) U) :
    ‖φ (coefficientSiteTorusMap U standardPhysicalSite y) - (g (standardPhysicalJetMap U y) : ℂ)‖ ≤ η := by
  obtain ⟨x, hx⟩ := euclideanCoefficientJetMap_surjective U root D a ha hperiod
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    (fun _ => Subtype.val_injective) (fun _ o => o.property) (standardPhysicalJetMap U y)
  have hs := coefficientSite_eq_of_euclideanJet_eq U root D (fun _ => 0)
    (1 : Matrix (Fin q) (Fin q) ℤ) x y hx
  have h := happrox x
  rw [hs, hx] at h
  exact h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem standardPhysicalJetMap_measurePreserving :
    MeasurePreserving (standardPhysicalJetMap (q := q) U) μ
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))) := by
  have hperiod : integerScalarLattice (Fin q) (1 : ℤ) ≤
      (1 : Matrix (Fin q) (Fin q) ℤ).mulVecLin.range := by
    intro v _
    exact ⟨v, by simp⟩
  exact euclideanCoefficientJetMap_measurePreserving U (fun _ => 0)
    (1 : Matrix (Fin q) (Fin q) ℤ) 1 one_ne_zero hperiod
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    (fun _ => Subtype.val_injective) (fun _ s => s.property) μ ν

theorem standardPhysicalJetMap_density_mass
    (g : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (hg : Integrable g
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))))
    (hmass : (∫ y, g y ∂(Measure.pi (fun j =>
      Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j)))) = 1) :
    Integrable (fun y => g (standardPhysicalJetMap U y)) μ ∧
      (∫ y, g (standardPhysicalJetMap U y) ∂μ) = 1 := by
  have h := standardPhysicalJetMap_measurePreserving U μ ν
  refine ⟨h.integrable_comp_of_integrable hg, ?_⟩
  have hg' : AEStronglyMeasurable g (Measure.map (standardPhysicalJetMap U) μ) := by
    rw [h.map_eq]
    exact hg.aestronglyMeasurable
  rw [← hmass]
  simpa only [h.map_eq] using (integral_map h.measurable.aemeasurable hg').symm

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

variable {X : Type*} {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

noncomputable def physicalSingleSiteValue (w : X → ℝ) : EuclideanJetLayers U (fun _ => Unit) :=
  fun j _ => (euclideanSubspaceTorusEquiv (U j)).symm
    (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
      (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j))))

theorem physicalCubeEuclideanSample_site_reconstruction
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (v : X → (Unit ⊕ Fin q) → ℤ) :
    siteFromLowBooleanJets U ((euclideanJetEquiv U).symm (physicalCubeEuclideanSample U d p hm v)) =
      physicalCubeCoveredSample U d p hm v := by
  rw [physicalCubeEuclideanSample_frame U d p hp hm v]
  change siteFromLowBooleanJets U ((euclideanJetEquiv U).symm (euclideanJetEquiv U
    (coefficientBooleanJetTorusMap U (fun _ : Fin q => 0) (1 : Matrix (Fin q) (Fin q) ℤ)
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
      (affineCoefficientCoverSample U p hm d
        (fun k x => (standardPhysicalCubeFrame v (k, x) : ℝ)))))) = _
  rw [AddEquiv.symm_apply_apply, siteFromLowBooleanJets_coefficient]
  let D : Fin q → Fin q → ℤ := fun i j => if i = j then 1 else 0
  have hD : Matrix.of D = (1 : Matrix (Fin q) (Fin q) ℤ) := by
    ext i j
    simp [D, Matrix.one_apply]
  have h := coefficientCoverSample_sites U (fun _ : Fin q => 0) D d p hp hm
    (fun k x => (standardPhysicalCubeFrame v (k, x) : ℝ))
  rw [affineCoveredSiteSample_zero_base_physical, hD, physicalCubeRootDifferences_standard,
    standardPhysicalCubeOutput_frame] at h
  exact h

theorem coveredBooleanSiteValue_physical
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (v : X → (Unit ⊕ Fin q) → ℤ) (s : Finset (Fin q)) :
    coveredBooleanSiteValue U (physicalCubeEuclideanSample U d p hm v) s =
      physicalSingleSiteValue U d p hm (fun x => (physicalCubeVertexValue v s x : ℝ)) := by
  funext j t
  cases t
  rw [coveredBooleanSiteValue_eq_siteFromLow, physicalCubeEuclideanSample_site_reconstruction U d p hm hp v]
  rfl

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

variable {X : Type*} {m dim : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem coveredRowsSiteValue_physical
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (v : X → (Unit ⊕ Fin dim) → ℤ) (s : Finset (Fin dim)) :
    coveredRowsSiteValue (fun j : Fin m => boundedBooleanJetRows (Fin dim) (j.val + 1)) U
      (physicalCubeRowSample U d (fun _ => Subtype.val) p hm v) s =
        physicalSingleSiteValue U d p hm (fun x => (physicalCubeVertexValue v s x : ℝ)) := by
  let P (O : Fin m → Type) [∀ j, Fintype (O j)]
      (rows : ∀ j, O j → Finset (Fin dim)) : Prop :=
    ∀ (v : X → (Unit ⊕ Fin dim) → ℤ) (s : Finset (Fin dim)) (j : Fin m),
      (∑ t : O j, (if rows j t ⊆ s then (1 : ℤ) else 0) •
        physicalCubeRowSample U d rows p hm v j t) =
          physicalSingleSiteValue U d p hm (fun x => (physicalCubeVertexValue v s x : ℝ)) j ()
  have hstd : P (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) (fun _ => Subtype.val) := by
    intro v s j
    have h := congrArg (fun y => y j ()) (coveredBooleanSiteValue_physical U d p hm hp v s)
    simpa only [coveredBooleanSiteValue, boundedBooleanReconstructionMatrix,
      physicalCubeRowSample_standard] using h
  have h := boundedBooleanJetRows_family_transport (fun j : Fin m => j.val + 1) P hstd
    (fun j => Finset.Subtype.fintype (boundedBooleanJetRows (Fin dim) (j.val + 1)))
  funext j t
  cases t
  exact h v s j

end Erdos3.BooleanCubeKernel

end

end OAI
