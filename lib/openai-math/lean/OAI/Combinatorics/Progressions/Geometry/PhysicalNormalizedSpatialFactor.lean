import OAI.Combinatorics.Progressions.Lattices.PhysicalSpatialResidueSupport

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical NNReal

variable {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ)
variable (b : ℝ) (r : ℝ≥0) (H N : X → ℝ) {m : ℕ}
variable (t : X → SpatialSiteLabel α m b r) (s : Finset α)

local notation "offset" => (fun i : Unit ⊕ α =>
  physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) (spatialStarVertex i))

noncomputable def physicalResidueSpatialMask (u : X → ℤ) : ℂ :=
  starVertexSiteFactor (fun i u => ∏ x,
    (residueSiteIndicator (m := q x * m)
      ((offset i x + (q x : ℤ) * (((t x).1 i).val : ℤ) : ℤ) : ZMod (q x * m)) (u x) : ℂ)) s u

noncomputable def physicalResidueSpatialSmooth (y : X → ℝ) : ℂ :=
  starVertexSiteFactor (fun i y => vectorIntervalSiteWeight b r (fun x => (t x).2 i)
    (fun x => (N x * y x - offset i x) / ((q x : ℝ) * H x))) s y

theorem physicalResidueSpatialSiteFactor_normalized (hN : ∀ x, N x ≠ 0) (u : X → ℤ) :
    physicalResidueSpatialSiteFactor root D base residue q b r H t s u =
      physicalResidueSpatialMask root D base residue q b r t s u *
        physicalResidueSpatialSmooth root D base residue q b r H N t s (fun x => (u x : ℝ) / N x) := by
  unfold physicalResidueSpatialSiteFactor physicalResidueSpatialMask physicalResidueSpatialSmooth
  unfold starVertexSiteFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : spatialStarVertex i = s
  · simp only [hi, ite_true, physicalResidueStarFactor]
    rw [affineVectorResidueSiteWeight_factorization]
    congr 1
    apply congrArg (vectorIntervalSiteWeight b r (fun x => (t x).2 i))
    funext x
    congr 1
    field_simp [hN x]
  · simp only [hi, ite_false, mul_one]

theorem physicalResidueSpatialSmooth_bounds (hr : 0 < r) {L : ℝ≥0}
    (hscale : ∀ x, |N x / ((q x : ℝ) * H x)| ≤ L) :
    (∀ y, ‖physicalResidueSpatialSmooth root D base residue q b r H N t s y‖ ≤ 1) ∧
      LipschitzWith (Fintype.card (Unit ⊕ α) *
        ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L))
        (physicalResidueSpatialSmooth root D base residue q b r H N t s) := by
  let f := fun (i : Unit ⊕ α) (y : X → ℝ) =>
    if spatialStarVertex i = s then vectorIntervalSiteWeight b r (fun x => (t x).2 i)
      (fun x => (N x * y x - offset i x) / ((q x : ℝ) * H x)) else 1
  have hn (i : Unit ⊕ α) (y : X → ℝ) : ‖f i y‖ ≤ (1 : ℝ≥0) := by
    dsimp only [f]
    split_ifs
    · exact vectorIntervalSiteWeight_bound b (show (0 : ℝ) < r from hr) _ _
    · simp
  have hl (i : Unit ⊕ α) :
      LipschitzWith ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L) (f i) := by
    by_cases hi : spatialStarVertex i = s
    · simpa only [f, hi, ite_true] using
        affineVectorInterval_normalized_lipschitz b hr (fun x => (t x).2 i) H N q (offset i) hscale
    · simpa only [f, hi, ite_false] using
        (LipschitzWith.const (α := X → ℝ) (1 : ℂ)).weaken (show 0 ≤ _ from zero_le)
  have hp := bounded_lipschitz_fintype_prod f (B := 1) (le_refl _) hl hn
  refine ⟨?_, ?_⟩
  · intro y
    simpa only [physicalResidueSpatialSmooth, starVertexSiteFactor, f, one_pow, NNReal.coe_one] using hp.1 y
  · apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [physicalResidueSpatialSmooth, starVertexSiteFactor, f, one_pow, mul_one] using hp.2.dist_le_mul y z

theorem physicalResidueSpatialSmooth_pre_lipschitz (hr : 0 < r) {L : ℝ≥0}
    (hscale : ∀ x, |N x / ((q x : ℝ) * H x)| ≤ L)
    {P EX ES EL : ℝ} (hP : 0 ≤ P) (hb : 0 ≤ b)
    (hbox : b ≤ Real.exp P) (hrinv : 1 / (r : ℝ) ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ Real.exp EX)
    (hS : (Fintype.card (Unit ⊕ α) : ℝ) ≤ Real.exp ES) (hL : (L : ℝ) ≤ Real.exp EL) :
    LipschitzWith ⟨Real.exp (ES + EX + (3 * P + 6) + EL), Real.exp_nonneg _⟩
      (physicalResidueSpatialSmooth root D base residue q b r H N t s) := by
  apply (physicalResidueSpatialSmooth_bounds root D base residue q b r H N t s hr hscale).2.weaken
  apply NNReal.coe_le_coe.mp
  change (Fintype.card (Unit ⊕ α) : ℝ) *
      ((Fintype.card X : ℝ) * ((2 * (intervalSiteCount b r : ℝ) + 1) / (r : ℝ)) * L) ≤ _
  have hi := intervalSiteLipschitz_le_exp hb (show (0 : ℝ) < r from hr) hP hbox hrinv
  have hxi := mul_le_mul hX hi (by positivity) (Real.exp_pos EX).le
  have hxl := mul_le_mul hxi hL L.coe_nonneg (by positivity)
  apply (mul_le_mul hS hxl (by positivity) (Real.exp_pos ES).le).trans_eq
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem trimmedSpatialRootScale_normalized_ratio {X : Type*}
    (N q : X → ℕ) {τ : ℝ} (hτ : 0 < τ) (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x) (x : X) :
    (N x : ℝ) / ((q x : ℝ) * trimmedSpatialRootScale τ N q x) = 8 / τ := by
  have hn : (N x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hN x).ne'
  have hq' : (q x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hq x).ne'
  unfold trimmedSpatialRootScale
  field_simp [hn, hq', hτ.ne']

end Erdos3.BooleanCubeKernel

end

end OAI
