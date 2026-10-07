/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residueSiteIndicator_affine {m : ℕ} [NeZero m] (q : ℕ) (hq : 0 < q)
    (offset : ℤ) (a : ZMod m) (z : ℤ) :
    residueSiteIndicator (m := q * m)
        ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m))
        (offset + (q : ℤ) * z) = residueSiteIndicator a z := by
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hval : ((a.val : ℤ) : ZMod m) = a := by simp
  have heq :
      ((offset + (q : ℤ) * z : ℤ) : ZMod (q * m)) =
        ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m)) ↔
      (z : ZMod m) = a := by
    calc
      _ ↔ ((q * m : ℕ) : ℤ) ∣
          (offset + (q : ℤ) * (a.val : ℤ)) - (offset + (q : ℤ) * z) :=
        ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _
      _ ↔ (m : ℤ) ∣ (a.val : ℤ) - z := by
        rw [Nat.cast_mul, show
          (offset + (q : ℤ) * (a.val : ℤ)) - (offset + (q : ℤ) * z) =
            (q : ℤ) * ((a.val : ℤ) - z) by ring, mul_dvd_mul_iff_left hqz]
      _ ↔ (z : ZMod m) = ((a.val : ℤ) : ZMod m) :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).symm
      _ ↔ (z : ZMod m) = a := by rw [hval]
  unfold residueSiteIndicator
  simp only [heq]

noncomputable def affineResidueIntervalSiteWeight (b r H : ℝ) (q : ℕ)
    (offset : ℤ) {m : ℕ} (a : ZMod m) (k : Fin (intervalSiteCount b r)) (u : ℤ) : ℝ :=
  residueSiteIndicator (m := q * m)
      ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m)) u *
    intervalSiteWeight b r k (((u : ℝ) - offset) / ((q : ℝ) * H))

theorem affineResidueIntervalSiteWeight_range (b H : ℝ) {r : ℝ} (hr : 0 < r)
    (q : ℕ) (offset : ℤ) {m : ℕ} (a : ZMod m)
    (k : Fin (intervalSiteCount b r)) (u : ℤ) :
    0 ≤ affineResidueIntervalSiteWeight b r H q offset a k u ∧
      affineResidueIntervalSiteWeight b r H q offset a k u ≤ 1 := by
  have ha := residueSiteIndicator_range
    (m := q * m) ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m)) u
  have hk := intervalSiteWeight_range b hr k (((u : ℝ) - offset) / ((q : ℝ) * H))
  exact ⟨mul_nonneg ha.1 hk.1,
    (mul_le_mul ha.2 hk.2 hk.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem affineResidueIntervalSiteWeight_pullback (b r H : ℝ) (q : ℕ) (hq : 0 < q)
    (offset : ℤ) {m : ℕ} [NeZero m] (a : ZMod m)
    (k : Fin (intervalSiteCount b r)) (z : ℤ) :
    affineResidueIntervalSiteWeight b r H q offset a k (offset + (q : ℤ) * z) =
      residueIntervalSiteWeight b r H a k z := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold affineResidueIntervalSiteWeight residueIntervalSiteWeight
  rw [residueSiteIndicator_affine q hq]
  congr 2
  push_cast
  rw [add_sub_cancel_left, mul_div_mul_left _ _ hqR]

noncomputable def affineVectorResidueSiteWeight {X : Type*} [Fintype X]
    (b r : ℝ) (H : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {m : ℕ} (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r)) (u : X → ℤ) : ℂ :=
  ∏ x, (affineResidueIntervalSiteWeight b r (H x) (q x) (offset x) (a x) (k x) (u x) : ℂ)

theorem affineVectorResidueSiteWeight_bound {X : Type*} [Fintype X]
    (b : ℝ) {r : ℝ} (hr : 0 < r) (H : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {m : ℕ} (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r)) (u : X → ℤ) :
    ‖affineVectorResidueSiteWeight b r H q offset a k u‖ ≤ 1 := by
  rw [affineVectorResidueSiteWeight, norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro x _
  have h := affineResidueIntervalSiteWeight_range b (H x) hr (q x) (offset x) (a x) (k x) (u x)
  simpa only [Complex.norm_real, Real.norm_of_nonneg h.1] using h.2

theorem affineVectorResidueSiteWeight_pullback {X : Type*} [Fintype X]
    (b r : ℝ) (H : X → ℝ) (q : X → ℕ) (hq : ∀ x, 0 < q x) (offset : X → ℤ)
    {m : ℕ} [NeZero m] (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r))
    (z : X → ℤ) :
    affineVectorResidueSiteWeight b r H q offset a k (fun x => offset x + (q x : ℤ) * z x) =
      vectorResidueSiteWeight b r H a k z := by
  unfold affineVectorResidueSiteWeight vectorResidueSiteWeight
  apply Finset.prod_congr rfl
  intro x _
  rw [affineResidueIntervalSiteWeight_pullback b r (H x) (q x) (hq x)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem affineVectorResidueSiteWeight_factorization {X : Type*} [Fintype X]
    (b r : ℝ) (H : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {m : ℕ} (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r)) (u : X → ℤ) :
    affineVectorResidueSiteWeight b r H q offset a k u =
      (∏ x, (residueSiteIndicator (m := q x * m)
        ((offset x + (q x : ℤ) * ((a x).val : ℤ) : ℤ) : ZMod (q x * m)) (u x) : ℂ)) *
      vectorIntervalSiteWeight b r k (fun x => ((u x : ℝ) - offset x) / ((q x : ℝ) * H x)) := by
  simp only [affineVectorResidueSiteWeight, affineResidueIntervalSiteWeight,
    vectorIntervalSiteWeight, Complex.ofReal_mul, Finset.prod_mul_distrib]

theorem vectorIntervalSiteWeight_affine_lipschitz {X : Type*} [Fintype X]
    (b : ℝ) {r : ℝ≥0} (hr : 0 < r) (k : X → Fin (intervalSiteCount b r))
    (slope shift : X → ℝ) {L : ℝ≥0} (hslope : ∀ x, |slope x| ≤ L) :
    LipschitzWith ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L)
      (fun y : X → ℝ => vectorIntervalSiteWeight b r k (fun x => slope x * y x + shift x)) := by
  have haffine : LipschitzWith L (fun y : X → ℝ => fun x => slope x * y x + shift x) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    apply (dist_pi_le_iff (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
    intro x
    calc
      dist (slope x * y x + shift x) (slope x * z x + shift x) =
          |slope x| * dist (y x) (z x) := by
        simp only [Real.dist_eq]
        rw [show slope x * y x + shift x - (slope x * z x + shift x) =
          slope x * (y x - z x) by ring, abs_mul]
      _ ≤ (L : ℝ) * dist y z :=
        mul_le_mul (hslope x) (dist_le_pi_dist y z x) dist_nonneg L.coe_nonneg
  exact (vectorIntervalSiteWeight_lipschitz b hr k).comp haffine

theorem affineVectorInterval_normalized_lipschitz {X : Type*} [Fintype X]
    (b : ℝ) {r : ℝ≥0} (hr : 0 < r) (k : X → Fin (intervalSiteCount b r))
    (H N : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {L : ℝ≥0} (hscale : ∀ x, |N x / ((q x : ℝ) * H x)| ≤ L) :
    LipschitzWith ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L)
      (fun y : X → ℝ => vectorIntervalSiteWeight b r k
        (fun x => (N x * y x - offset x) / ((q x : ℝ) * H x))) := by
  have h := vectorIntervalSiteWeight_affine_lipschitz b hr k
    (fun x => N x / ((q x : ℝ) * H x))
    (fun x => -(offset x : ℝ) / ((q x : ℝ) * H x)) hscale
  convert h using 1
  funext y
  congr 1
  funext x
  ring

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalCubeVertexValue_residueReconstruction {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ)
    (v : X → (Unit ⊕ α) → ℤ) (s : Finset α) (x : X) :
    physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s x =
      physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) s x +
        (q x : ℤ) * physicalCubeVertexValue v s x := by
  simp only [physicalCubeVertexValue, physicalResidueReconstruction,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

noncomputable def physicalResidueStarFactor {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (b r : ℝ) (H : X → ℝ)
    {m : ℕ} (t : X → SpatialSiteLabel α m b r) (i : Unit ⊕ α) (u : X → ℤ) : ℂ :=
  affineVectorResidueSiteWeight b r H q
    (physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) (spatialStarVertex i))
    (fun x => (t x).1 i) (fun x => (t x).2 i) u

noncomputable def physicalResidueSpatialSiteFactor {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (b r : ℝ) (H : X → ℝ)
    {m : ℕ} (t : X → SpatialSiteLabel α m b r) (s : Finset α) (u : X → ℤ) : ℂ :=
  starVertexSiteFactor (physicalResidueStarFactor root D base residue q b r H t) s u

theorem physicalResidueSpatialSiteFactor_bound {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (b : ℝ) {r : ℝ} (hr : 0 < r)
    (H : X → ℝ) {m : ℕ} (t : X → SpatialSiteLabel α m b r)
    (s : Finset α) (u : X → ℤ) :
    ‖physicalResidueSpatialSiteFactor root D base residue q b r H t s u‖ ≤ 1 := by
  apply starVertexSiteFactor_bound
  intro i y
  exact affineVectorResidueSiteWeight_bound b hr H q _ _ _ y

theorem physicalResidueStarFactor_pullback {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (b r : ℝ) (H : X → ℝ) {m : ℕ} [NeZero m]
    (t : X → SpatialSiteLabel α m b r) (i : Unit ⊕ α)
    (v : X → (Unit ⊕ α) → ℤ) :
    physicalResidueStarFactor root D base residue q b r H t i
        (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v)
          (spatialStarVertex i)) =
      vectorResidueSiteWeight b r H (fun x => (t x).1 i) (fun x => (t x).2 i)
        (fun x => spatialStar (v x) i) := by
  unfold physicalResidueStarFactor
  have hvertex :
      physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v)
          (spatialStarVertex i) =
        fun x => physicalCubeVertexValue (physicalCubeRootDifferences root D base residue)
          (spatialStarVertex i) x + (q x : ℤ) * spatialStar (v x) i := by
    funext x
    rw [physicalCubeVertexValue_residueReconstruction, physicalCubeVertexValue_star v i]
  rw [hvertex]
  exact affineVectorResidueSiteWeight_pullback b r H q hq _ _ _ _

theorem physicalResidueSpatialSiteFactor_prod {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (b r : ℝ) (H : X → ℝ) {m : ℕ} [NeZero m]
    (t : X → SpatialSiteLabel α m b r) (v : X → (Unit ⊕ α) → ℤ) :
    (∏ s, physicalResidueSpatialSiteFactor root D base residue q b r H t s
      (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s)) =
      ∏ i, vectorResidueSiteWeight b r H (fun x => (t x).1 i) (fun x => (t x).2 i)
        (fun x => spatialStar (v x) i) := by
  unfold physicalResidueSpatialSiteFactor
  rw [starVertexSiteFactor_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact physicalResidueStarFactor_pullback root D base residue q hq b r H t i v

theorem physicalResidue_spatialSiteExpansion {K X J : Type*} {dim : ℕ}
    [Fintype K] [Fintype X] [DecidableEq X] [Fintype J]
    (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (A : Matrix (Unit ⊕ Fin dim) (Unit ⊕ Fin dim) ℤ)
    (B : X → Matrix (Unit ⊕ Fin dim) J ℤ) (m : ℕ) [NeZero m]
    (f : X → ((Unit ⊕ Fin dim) → ℝ) → ℝ) (H : X → ℝ) (b r : ℝ)
    (v : X → (Unit ⊕ Fin dim) → ℤ)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) :
    (∏ x, spatialSiteApprox A (B x) m (f x) (H x) b r (v x)) *
        physicalCubeSiteTest test (physicalResidueReconstruction root D base residue q v) =
      ∑ t : X → SpatialSiteLabel (Fin dim) m b r,
        (∏ x, spatialSiteCoefficient A (B x) m (f x) b r (t x)) *
          ∏ s, test s (fun x =>
            (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s x : ℝ)) *
              physicalResidueSpatialSiteFactor root D base residue q b r H t s
                (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s) := by
  rw [vectorSpatialSiteExpansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_assoc, Finset.prod_mul_distrib,
    physicalResidueSpatialSiteFactor_prod root D base residue q hq]
  congr 1
  exact mul_comm _ _

theorem exists_physicalResidue_spatialSiteExpansion {K X J : Type*} {dim : ℕ}
    [Fintype K] [Fintype X] [DecidableEq X] [Fintype J]
    (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (A : Matrix (Unit ⊕ Fin dim) (Unit ⊕ Fin dim) ℤ)
    (B : X → Matrix (Unit ⊕ Fin dim) J ℤ) (m : ℕ) [NeZero m]
    (f : X → ((Unit ⊕ Fin dim) → ℝ) → ℝ) (H : X → ℝ) (b : ℝ) {r : ℝ} (hr : 0 < r)
    {G C : ℝ} (hindex : ∀ x, ((pivotFullImage A (B x)).toAddSubgroup.index : ℝ) ≤ G)
    (hf : ∀ x y, |f x y| ≤ C) :
    ∃ coefficient : (X → SpatialSiteLabel (Fin dim) m b r) → ℂ,
    ∃ twist : (X → SpatialSiteLabel (Fin dim) m b r) → Finset (Fin dim) → (X → ℤ) → ℂ,
      (∑ t, ‖coefficient t‖) ≤
        ((m : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          (intervalSiteCount b r : ℝ)^Fintype.card (Unit ⊕ Fin dim) * (G * C))^Fintype.card X ∧
      (∀ t s u, ‖twist t s u‖ ≤ 1) ∧
      ∀ (v : X → (Unit ⊕ Fin dim) → ℤ) (test : Finset (Fin dim) → (X → ℝ) → ℂ),
        (∏ x, spatialSiteApprox A (B x) m (f x) (H x) b r (v x)) *
            physicalCubeSiteTest test (physicalResidueReconstruction root D base residue q v) =
          ∑ t, coefficient t * ∏ s,
            test s (fun x =>
              (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s x : ℝ)) *
            twist t s (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s) := by
  refine ⟨fun t => ∏ x, spatialSiteCoefficient A (B x) m (f x) b r (t x),
    physicalResidueSpatialSiteFactor root D base residue q b r H, ?_, ?_, ?_⟩
  · exact vectorSpatialSiteCoefficient_sum_bound A B m f b r hindex hf
  · intro t s u
    exact physicalResidueSpatialSiteFactor_bound root D base residue q b hr H t s u
  · intro v test
    exact physicalResidue_spatialSiteExpansion root D base residue q hq A B m f H b r v test

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators NNReal

theorem exists_physicalResidue_coarseSiteExpansion {K X J : Type*} {dim : ℕ}
    [Fintype K] [Fintype X] [DecidableEq X] [Fintype J]
    (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (A : Matrix (Unit ⊕ Fin dim) (Unit ⊕ Fin dim) ℤ)
    (B : X → Matrix (Unit ⊕ Fin dim) J ℤ) (m : ℕ) [NeZero m]
    (hp : ∀ x, integerScalarLattice (Unit ⊕ Fin dim) (m : ℤ) ≤ pivotFullImage A (B x))
    (f : X → ((Unit ⊕ Fin dim) → ℝ) → ℝ) {Lip : ℝ≥0}
    (hf : ∀ x, LipschitzWith Lip (f x))
    (H : X → ℝ) {G C b coarse : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hindex : ∀ x, ((pivotFullImage A (B x)).toAddSubgroup.index : ℝ) ≤ G)
    (hcap : ∀ x y, |f x y| ≤ C) (hb : 0 < b) (hcoarse : 0 < coarse) :
    ∃ coefficient : (X → SpatialSiteLabel (Fin dim) m b coarse) → ℂ,
    ∃ twist : (X → SpatialSiteLabel (Fin dim) m b coarse) → Finset (Fin dim) → (X → ℤ) → ℂ,
      (∑ t, ‖coefficient t‖) ≤
        ((m : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          (intervalSiteCount b coarse : ℝ)^Fintype.card (Unit ⊕ Fin dim) * (G * C))^Fintype.card X ∧
      (∀ t s u, ‖twist t s u‖ ≤ 1) ∧
      ∀ (fine : ℝ), 0 < fine → fine ≤ coarse →
      ∀ (v : X → (Unit ⊕ Fin dim) → ℤ),
        (∀ x i, |((spatialStar (v x) i : ℤ) : ℝ) / H x| ≤ b) →
      ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s u, ‖test s u‖ ≤ 1) →
        ‖(∏ x, spatialSiteApprox A (B x) m (f x) (H x) b fine (v x)) *
            physicalCubeSiteTest test (physicalResidueReconstruction root D base residue q v) -
          ∑ t, coefficient t * ∏ s,
            test s (fun x =>
              (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s x : ℝ)) *
            twist t s (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s)‖ ≤
          Fintype.card X * (8 * G * Lip * coarse) * (1 + G * C)^Fintype.card X := by
  obtain ⟨coefficient, twist, hcoeff, htwist, hexact⟩ :=
    exists_physicalResidue_spatialSiteExpansion root D base residue q hq A B m f H b hcoarse hindex hcap
  refine ⟨coefficient, twist, hcoeff, htwist, ?_⟩
  intro fine hfine hle v hv test htest
  rw [← hexact v test, ← sub_mul, norm_mul]
  have herror := vectorSpatialSiteApprox_remesh A B m hp f hf H hG hC hindex hcap hb
    hfine hcoarse v hv
  have htest' := physicalCubeSiteTest_norm_le test htest
    (physicalResidueReconstruction root D base residue q v)
  calc
    _ ≤ Fintype.card X * (4 * G * Lip * (fine + coarse)) * (1 + G * C)^Fintype.card X :=
      (mul_le_mul herror htest' (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ ≤ Fintype.card X * (4 * G * Lip * (coarse + coarse)) * (1 + G * C)^Fintype.card X := by
      gcongr
    _ = _ := by ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

def physicalResidueQuotient {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (u : X → (Unit ⊕ α) → ℤ) :
    X → (Unit ⊕ α) → ℤ :=
  fun x i => (u x i - physicalCubeRootDifferences root D base r x i) / (q x : ℤ)

theorem physicalResidueQuotient_reconstruction {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (v : X → (Unit ⊕ α) → ℤ) :
    physicalResidueQuotient root D base r q
      (physicalResidueReconstruction root D base r q v) = v := by
  funext x i
  have hn : (q x : ℤ) ≠ 0 := by exact_mod_cast (hq x).ne'
  simp only [physicalResidueQuotient, physicalResidueReconstruction,
    add_sub_cancel_left, Int.mul_ediv_cancel_left _ hn]

theorem physicalResidueReconstruction_quotient {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (u : X → (Unit ⊕ α) → ℤ)
    (hu : ∀ x i, (u x i : ZMod (q x)) =
      (physicalCubeRootDifferences root D base r x i : ZMod (q x))) :
    physicalResidueReconstruction root D base r q
      (physicalResidueQuotient root D base r q u) = u := by
  funext x i
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub
    (physicalCubeRootDifferences root D base r x i) (u x i) (q x)).mp (hu x i).symm
  simp only [physicalResidueReconstruction, physicalResidueQuotient,
    Int.mul_ediv_cancel' hd, add_sub_cancel]

theorem physicalResidueReconstruction_mem_range_iff {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (u : X → (Unit ⊕ α) → ℤ) :
    u ∈ Set.range (physicalResidueReconstruction root D base r q) ↔
      ∀ x i, (u x i : ZMod (q x)) =
        (physicalCubeRootDifferences root D base r x i : ZMod (q x)) := by
  constructor
  · rintro ⟨v, rfl⟩ x i
    simp [physicalResidueReconstruction]
  · intro hu
    exact ⟨physicalResidueQuotient root D base r q u,
      physicalResidueReconstruction_quotient root D base r q u hu⟩

theorem physicalResidueReconstruction_mem_range_star_iff {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (u : X → (Unit ⊕ α) → ℤ) :
    u ∈ Set.range (physicalResidueReconstruction root D base r q) ↔
      ∀ x i, ((spatialStar (u x) i : ℤ) : ZMod (q x)) =
        ((spatialStar (physicalCubeRootDifferences root D base r x) i : ℤ) : ZMod (q x)) := by
  rw [physicalResidueReconstruction_mem_range_iff]
  constructor
  · intro hu x i
    cases i with
    | inl i => cases i; exact hu x (.inl ())
    | inr i => simpa only [spatialStar, Sum.elim_inr, Int.cast_add] using
        congrArg₂ (· + ·) (hu x (.inl ())) (hu x (.inr i))
  · intro hu x i
    have hr := hu x (.inl ())
    change (u x (.inl ()) : ZMod (q x)) =
      (physicalCubeRootDifferences root D base r x (.inl ()) : ZMod (q x)) at hr
    cases i with
    | inl i => cases i; exact hr
    | inr i =>
      have hi := hu x (.inr i)
      simp only [spatialStar, Sum.elim_inr, Int.cast_add, hr] at hi
      exact add_left_cancel hi

theorem physicalResidueReconstruction_mem_range_sites_iff {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (u : X → (Unit ⊕ α) → ℤ) :
    u ∈ Set.range (physicalResidueReconstruction root D base r q) ↔
      ∀ (s : Finset α) x, (physicalCubeVertexValue u s x : ZMod (q x)) =
        (physicalCubeVertexValue (physicalCubeRootDifferences root D base r) s x : ZMod (q x)) := by
  constructor
  · rintro ⟨v, rfl⟩ s x
    simp [physicalCubeVertexValue_residueReconstruction]
  · intro hu
    apply (physicalResidueReconstruction_mem_range_star_iff root D base r q u).mpr
    intro x i
    simpa only [physicalCubeVertexValue_star] using hu (spatialStarVertex i) x

theorem physicalResidueReconstruction_mem_image_iff {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (window : Finset (X → (Unit ⊕ α) → ℤ)) (u : X → (Unit ⊕ α) → ℤ) :
    u ∈ window.image (physicalResidueReconstruction root D base r q) ↔
      (∀ x i, (u x i : ZMod (q x)) =
        (physicalCubeRootDifferences root D base r x i : ZMod (q x))) ∧
      physicalResidueQuotient root D base r q u ∈ window := by
  classical
  constructor
  · intro hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    refine ⟨(physicalResidueReconstruction_mem_range_iff root D base r q _).mp ⟨v, rfl⟩, ?_⟩
    simpa only [physicalResidueQuotient_reconstruction root D base r q hq] using hv
  · rintro ⟨hu, hw⟩
    exact Finset.mem_image.mpr ⟨physicalResidueQuotient root D base r q u, hw,
      physicalResidueReconstruction_quotient root D base r q u hu⟩

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem affineResidueIntervalSiteWeight_nonzero_residue
    (b r H : ℝ) (q : ℕ) (offset : ℤ) {m : ℕ} (a : ZMod m)
    (k : Fin (intervalSiteCount b r)) (u : ℤ)
    (hu : affineResidueIntervalSiteWeight b r H q offset a k u ≠ 0) :
    (u : ZMod q) = (offset : ZMod q) := by
  have he : (u : ZMod (q * m)) =
      ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m)) := by
    by_contra h
    exact hu (by simp only [affineResidueIntervalSiteWeight, residueSiteIndicator, ite_eq_right h, zero_mul])
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub u
    (offset + (q : ℤ) * (a.val : ℤ)) (q * m)).mp he
  have hq : (q : ℤ) ∣ ((q * m : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
    exact dvd_mul_right _ _
  have hs := (hq.trans hd).sub (dvd_mul_right (q : ℤ) (a.val : ℤ))
  have heq : (offset + (q : ℤ) * (a.val : ℤ) - u) - (q : ℤ) * (a.val : ℤ) =
      offset - u := by ring
  rw [heq] at hs
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub u offset q).mpr hs

theorem affineVectorResidueSiteWeight_nonzero_residue {X : Type*} [Fintype X]
    (b r : ℝ) (H : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {m : ℕ} (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r)) (u : X → ℤ)
    (hu : affineVectorResidueSiteWeight b r H q offset a k u ≠ 0) :
    ∀ x, (u x : ZMod (q x)) = (offset x : ZMod (q x)) := by
  intro x
  have hx := (Finset.prod_ne_zero_iff.mp hu) x (Finset.mem_univ x)
  apply affineResidueIntervalSiteWeight_nonzero_residue b r (H x) (q x)
    (offset x) (a x) (k x) (u x)
  intro hz
  exact hx (by simp only [hz, Complex.ofReal_zero])

theorem physicalResidueSpatialSiteFactor_prod_nonzero_mem_range
    {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (b r : ℝ) (H : X → ℝ)
    {m : ℕ} (t : X → SpatialSiteLabel α m b r) (u : X → (Unit ⊕ α) → ℤ)
    (hu : (∏ s, physicalResidueSpatialSiteFactor root D base residue q b r H t s
      (physicalCubeVertexValue u s)) ≠ 0) :
    u ∈ Set.range (physicalResidueReconstruction root D base residue q) := by
  simp only [physicalResidueSpatialSiteFactor, starVertexSiteFactor_prod] at hu
  apply (physicalResidueReconstruction_mem_range_star_iff root D base residue q u).mpr
  intro x i
  have hi := (Finset.prod_ne_zero_iff.mp hu) i (Finset.mem_univ i)
  have hx := affineVectorResidueSiteWeight_nonzero_residue b r H q
    (physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) (spatialStarVertex i))
    (fun x => (t x).1 i) (fun x => (t x).2 i)
    (physicalCubeVertexValue u (spatialStarVertex i)) hi x
  simpa only [physicalCubeVertexValue_star] using hx

end Erdos3.BooleanCubeKernel

end

end OAI
