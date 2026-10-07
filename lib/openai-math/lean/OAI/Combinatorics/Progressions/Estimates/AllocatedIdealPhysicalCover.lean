import OAI.Combinatorics.Progressions.Geometry.AllocatedWindowMixedSupport
import OAI.Combinatorics.Progressions.Geometry.PhysicalRowChartMatching
import OAI.Combinatorics.Progressions.Polynomial.CoveredPolynomialSiteFactor

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} {A S : Type*} [Fintype A]
variable (e : A → ScalarSiteExpansion S) (selected : A → Σ j : Fin m, Fin (n j))
variable (k : ∀ a, (e a).Term) (s : S)

local notation "period" => commonSitePeriod e k
local notation "scale" => (fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a)))

theorem exists_allocated_cover_site_factor (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {E : Fin m → Type*} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    ∃ g : ((Σ j, J j) → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (((Fintype.card A * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * period) (4 * period)) g ∧
      (∀ y, ‖g y‖ ≤ 2) ∧
      ∀ (u : ∀ j, euclideanSubspace (U j)) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (∀ j, (QuotientAddGroup.mk (u j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
          normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w j))) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        g (fun a => ((((u a.1).val a.2) / period : ℝ) : UnitAddCircle)) =
          siteFamilyFactor e k s (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
            (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) / (scale) a) := by
  classical
  let : NeZero period := ⟨(commonSitePeriod_pos e he k).ne'⟩
  let residue := fun (r : ∀ j, Fin (n j) → ZMod period) (a : A) =>
    ZMod.castHom (commonSitePeriod_dvd e k a) (ZMod ((e a).period (k a))) (r (selected a).1 (selected a).2)
  let F := fun (r : ∀ j, Fin (n j) → ZMod period) (v : (Σ j, J j) → ℝ) =>
    allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s (residue r)
      (allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered v))
  have hF (r : ∀ j, Fin (n j) → ZMod period) :
      LipschitzWith (((Fintype.card A * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j))) (F r) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    have hc := (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR Cforward hforward K hK).dist_le_mul
      (singleSiteFromLayered v) (singleSiteFromLayered w)
    have hs := singleSiteFromLayered_lipschitz.dist_le_mul v w
    simp only [NNReal.coe_one, one_mul] at hs
    have hd := hc.trans (mul_le_mul_of_nonneg_left hs (NNReal.coe_nonneg _))
    have ht := (allocatedFullGridSiteFactor_bounds B U b e selected hR he Q hQ k s (residue r)).2.dist_le_mul
      (allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered v))
      (allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered w))
    simpa only [NNReal.coe_mul, mul_assoc] using
      ht.trans (mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg _))
  have hB (r : ∀ j, Fin (n j) → ZMod period) (v : (Σ j, J j) → ℝ) : ‖F r v‖ ≤ 1 :=
    (allocatedFullGridSiteFactor_bounds B U b e selected hR he Q hQ k s (residue r)).1 _
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_layered_cover_site_extension
    (fun j => euclideanSubspace (U j)) bW b hb period F
    (((Fintype.card A * L) * Q) * (K * ∑ j, Cforward j * Fintype.card (J j))) 1 hF hB
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa only [mul_one] using hg
  · simpa using hgb
  · intro u w hu hw
    have hval := hvalue u (fun j => orthonormalMixedChart (o j) (w j)) hu hw
    change g _ = allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s
      (fun a => ZMod.castHom (commonSitePeriod_dvd e k a) (ZMod ((e a).period (k a)))
        ((w (selected a).1).2 (selected a).2 : ZMod period))
      (allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered
        (fun a : Σ j, J j => normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
          (orthonormalMixedChart (o a.1) (w a.1)) a.2))) at hval
    simp only [map_intCast] at hval
    rw [allocatedFullAmbientSiteCoordinates_layered_point,
      allocatedFullGridSiteFactor_point B U b e selected hR k s] at hval
    exact hval

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem lipschitz_complex_div_two {X : Type*} [PseudoMetricSpace X]
    (f : X → ℂ) (K : ℝ≥0) (hf : LipschitzWith (2 * K) f) :
    LipschitzWith K (fun x => f x / 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← sub_div, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have h := hf.dist_le_mul x y
  simp only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat] at h
  nlinarith only [h]

theorem complex_div_two_norm_le {z : ℂ} (hz : ‖z‖ ≤ 2) : ‖z / 2‖ ≤ 1 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_div, h2]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa using hz)

theorem two_scaled_product_identity {S : Type*} [Fintype S] (c : ℂ) (f : S → ℂ) :
    ((2 : ℂ) ^ Fintype.card S * c) * (∏ s, f s / 2) = c * ∏ s, f s := by
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  have h2 : (2 : ℂ) ^ Fintype.card S ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [h2]

attribute [local instance] ScalarSiteExpansion.termFinite

noncomputable def coverSiteCoefficient {A S : Type*} [Fintype A] [Fintype S]
    (e : A → ScalarSiteExpansion S) (k : ∀ a, (e a).Term) : ℂ :=
  (2 : ℂ) ^ Fintype.card S * siteFamilyCoefficient e k

theorem coverSiteCoefficient_bound {A S : Type*} [Fintype A] [Fintype S]
    (e : A → ScalarSiteExpansion S) {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a)) :
    (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card S * ∏ a, C a := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  simp only [coverSiteCoefficient, norm_mul, norm_pow, h2, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (siteFamily_coefficient_le e he) (by positivity)

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} {A S : Type*} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion S) (selected : A → Σ j : Fin m, Fin (n j))

local notation "scale" => (fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a)))

theorem exists_allocated_cover_site_expansion (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {E : Fin m → Type*} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    ∃ g : (∀ a, (e a).Term) → S → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card A * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card S * ∏ a, C a ∧
      ∀ (u : S → ∀ j, euclideanSubspace (U j)) (w : S → ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (∀ s j, (QuotientAddGroup.mk (u s j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
          normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w s j))) →
        (∀ s j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w s j)) i| ≤ 1 / 4) →
        (∑ k, coverSiteCoefficient e k * ∏ s,
          g k s (fun a => ((((u s a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle))) =
          siteFamilyEval e (fun s a => (w s (selected a).1).2 (selected a).2)
            (fun s a => ((w s (selected a).1).2 (selected a).2 : ℝ) / (scale) a) := by
  have hex (k : ∀ a, (e a).Term) (s : S) := exists_allocated_cover_site_factor (G := G)
    B U b e selected k s hR he Q hQ o Cforward hforward K hK hb bW
  choose raw hLip hNorm hValue using hex
  let g := fun k s v => raw k s v / 2
  refine ⟨g, ?_, coverSiteCoefficient_bound e he, ?_⟩
  · intro k s
    exact ⟨lipschitz_complex_div_two (raw k s) _ (hLip k s),
      fun v => complex_div_two_norm_le (hNorm k s v)⟩
  · intro u w hu hw
    have hv (k : ∀ a, (e a).Term) (s : S) := hValue k s (u s) (w s) (hu s) (hw s)
    dsimp only [g]
    simp_rw [hv]
    unfold siteFamilyEval coverSiteCoefficient
    apply Finset.sum_congr rfl
    intro k _
    exact two_scaled_product_identity (siteFamilyCoefficient e k) _

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal
attribute [local instance] ScalarSiteExpansion.termFinite

open Module Submodule

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} {A S : Type*} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion S) (selected : A → Σ j : Fin m, Fin (n j))

local notation "scale" => (fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a)))

theorem exists_allocated_normalized_cover_site_expansion (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {E : Fin m → Type*} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    ∃ g : (∀ a, (e a).Term) → S → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card A * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card S * ∏ a, C a ∧
      (∀ k s (u : ∀ j, euclideanSubspace (U j)) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (∀ j, (QuotientAddGroup.mk (u j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
          normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w j))) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        g k s (fun a => ((((u a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) =
          allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s
            (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
            (allocatedFullMixedSiteValue (R := R) U b w) / 2) ∧
      ∀ (u : S → ∀ j, euclideanSubspace (U j)) (w : S → ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (∀ s j, (QuotientAddGroup.mk (u s j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
          normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w s j))) →
        (∀ s j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w s j)) i| ≤ 1 / 4) →
        (∑ k, coverSiteCoefficient e k * ∏ s,
          g k s (fun a => ((((u s a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle))) =
          siteFamilyEval e (fun s a => (w s (selected a).1).2 (selected a).2)
            (fun s a => ((w s (selected a).1).2 (selected a).2 : ℝ) / (scale) a) := by
  have hex (k : ∀ a, (e a).Term) (s : S) := exists_allocated_cover_site_factor (G := G)
    B U b e selected k s hR he Q hQ o Cforward hforward K hK hb bW
  choose raw hLip hNorm hValue using hex
  let g := fun k s v => raw k s v / 2
  refine ⟨g, ?_, coverSiteCoefficient_bound e he, ?_, ?_⟩
  · intro k s
    exact ⟨lipschitz_complex_div_two (raw k s) _ (hLip k s),
      fun v => complex_div_two_norm_le (hNorm k s v)⟩
  · intro k s u w hu hw
    rw [allocatedFullGridSiteFactor_point B U b e selected hR k s _ w]
    exact congrArg (fun z : ℂ => z / 2) (hValue k s u w hu hw)
  · intro u w hu hw
    have hv (k : ∀ a, (e a).Term) (s : S) := hValue k s (u s) (w s) (hu s) (hw s)
    dsimp only [g]
    simp_rw [hv]
    unfold siteFamilyEval coverSiteCoefficient
    apply Finset.sum_congr rfl
    intro k _
    exact two_scaled_product_identity (siteFamilyCoefficient e k) _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

universe uα

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "ambient" => JetAmbientIndex (fun _ : Fin m => Unit) J

@[instance_reducible]
noncomputable def activeAmbientAxisDecidableEq : DecidableEq activeAxes := Classical.decEq _

attribute [local instance 2000] activeAmbientAxisDecidableEq

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "lipBound" => (fun (L Q D : ℝ≥0) (Cforward : Fin m → ℝ≥0) (K : ℝ≥0) =>
  max (((Fintype.card activeAxes * L) * Q) * (K * ∑ j, Cforward j * Fintype.card (J j))) (2 * D))

noncomputable def allocatedActiveAmbientPoint (k : ∀ a, (e a).Term)
    (z : MixedCoveredJetSource I O E n d) (s : Finset α) :
    (activeAxes → UnitAddCircle) × (ambient → UnitAddCircle) :=
  ((fun a => (↑((((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a.val).1).2 (ig a.val).2 () : ℝ) /
    (e a).period (k a)) : UnitAddCircle)),
    coveredJetAmbientTorus U d (coveredRowsSiteValue rowSets U (chart z) s))

noncomputable def allocatedActiveAmbientSum
    (g : (∀ a, (e a).Term) → Finset α → (activeAxes → UnitAddCircle) × (ambient → UnitAddCircle) → ℂ)
    (z : MixedCoveredJetSource I O E n d) : ℂ :=
  ∑ k, periodicAmbientSiteCoefficient e k * ∏ s,
    g k s (allocatedActiveAmbientPoint B U b S rowSets o hb bW d e k z s)

omit [Fintype α] in
theorem allocatedActiveAmbientPoint_chart (k : ∀ a, (e a).Term)
    (z : MixedCoveredJetSource I O E n d) (s : Finset α) :
    allocatedActiveAmbientPoint B U b S rowSets o hb bW d e k z s =
      ((fun a => (↑((((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a.val).1).2 (ig a.val).2 () : ℝ) /
        (e a).period (k a)) : UnitAddCircle)),
      coveredJetAmbientTorus U d (chart (mixedCoveredRowsSiteValue rowSets d z s))) := by
  rw [mixedCoveredRowsSiteValue_chart]
  rfl

theorem allocatedActiveAmbientSum_chart
    (g : (∀ a, (e a).Term) → Finset α → (activeAxes → UnitAddCircle) × (ambient → UnitAddCircle) → ℂ)
    (z : MixedCoveredJetSource I O E n d) :
    allocatedActiveAmbientSum B U b S rowSets o hb bW d e g z =
      ∑ k, periodicAmbientSiteCoefficient e k * ∏ s,
        g k s ((fun a => (↑((((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a.val).1).2 (ig a.val).2 () : ℝ) /
          (e a).period (k a)) : UnitAddCircle)),
          coveredJetAmbientTorus U d (chart (mixedCoveredRowsSiteValue rowSets d z s))) := by
  unfold allocatedActiveAmbientSum
  simp_rw [allocatedActiveAmbientPoint_chart]

def ActiveAmbientRepresentation (L : ℝ≥0) : Prop :=
  ∃ g : (∀ a, (e a).Term) → Finset α → (activeAxes → UnitAddCircle) × (ambient → UnitAddCircle) → ℂ,
    (∀ k s, LipschitzWith L (g k s) ∧ ∀ p, ‖g k s p‖ ≤ 1) ∧
    ∀ z : MixedCoveredJetSource I O E n d,
      (∀ s, mixedCoveredRowsSiteValue rowSets d z s ∈ mixedCoveredJetRegion U o b d
        (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))) →
      allocatedActiveAmbientSum B U b S rowSets o hb bW d e g z =
        allocatedActiveSiteApproximation B U b S rowSets e
          (allocatedActiveRowsOfMixed B U b S rowSets z.1)

theorem exists_allocated_active_ambient_representation (hR : ∀ j, 0 < R j)
    {T V C H : activeAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Q)
    (D : ℝ≥0) (hD : ∀ a, V a ≤ D)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    ActiveAmbientRepresentation B U b S rowSets o hb bW d e (lipBound L Q D Cforward K) := by
  obtain ⟨g, hg, hvalue⟩ := exists_allocated_periodic_ambient_site_expansion (G := G)
    (A := activeAxes) (S := Finset α)
    B U b e (fun a : activeAxes => ig a.val) hR he Q hQ D hD o Cforward hforward K hK hb bW d
  refine ⟨g, hg, ?_⟩
  intro z hs
  rw [allocatedActiveAmbientSum_chart, allocatedActiveSiteApproximation_mixed B U b S rowSets d e z]
  dsimp only [allocatedGridNaturalScale]
  exact hvalue (fun s => mixedCoveredRowsSiteValue rowSets d z s) hs

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value) (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

def ActiveAmbientProfileRepresentation (L : ℝ≥0) (C : ℝ) : Prop :=
  ∃ g : (∀ a, (e a).Term) → Finset α → (activeAxes → UnitAddCircle) × (ambient → UnitAddCircle) → ℂ,
    (∀ k s, LipschitzWith L (g k s) ∧ ∀ p, ‖g k s p‖ ≤ 1) ∧
    (∑ k, ‖periodicAmbientSiteCoefficient e k‖) ≤ C ∧
    ∀ z : MixedCoveredJetSource I O E n d,
      z ∈ mixedCoveredJetRegion U o b d (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)) →
      (∀ s, mixedCoveredRowsSiteValue rowSets d z s ∈ mixedCoveredJetRegion U o b d
        (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))) →
      allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e (chart z) =
        allocatedActiveSiteChartPrefactor B U b S rowSets d hR hσ x hb o bW q y₀ hcell f z *
          allocatedActiveAmbientSum B U b S rowSets o hb bW d e g z

theorem exists_allocated_active_ambient_profile
    {T V C H : activeAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Q)
    (D : ℝ≥0) (hD : ∀ a, V a ≤ D)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    ActiveAmbientProfileRepresentation B U b S rowSets o hb bW d e hR hσ x q y₀ hcell f
      (lipBound L Q D Cforward K) ((4 : ℝ) ^ Fintype.card (Finset α) * ∏ a, C a) := by
  obtain ⟨g, hg, hvalue⟩ := exists_allocated_active_ambient_representation
    B U b S rowSets o hb bW d e hR he Q hQ D hD Cforward hforward K hK
  have hc : (∑ k, ‖periodicAmbientSiteCoefficient e k‖) ≤
      (4 : ℝ) ^ Fintype.card (Finset α) * ∏ a, C a :=
    periodicAmbientSiteCoefficient_bound (A := activeAxes) (S := Finset α) e he
  refine ⟨g, hg, hc, ?_⟩
  intro z hz hs
  rw [hvalue z hs]
  exact allocatedActiveSiteProfile_mixed B U b S rowSets d hR hσ x hb o bW q y₀ hcell f e z hz

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

universe uα

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d]
variable (x : G → IntegerScalarCubeBox α S.value) (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "siteH" => (fun a : activeAxes => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a)))
  (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "chart" => mixedCoveredJetChart U o b hb bW d

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))

theorem exists_allocated_window_cover_profile
    {Nt V Cc : activeAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L ((siteH) a))
    (Q : ℝ≥0) (hQ : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTi : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hTw : ∀ j i, allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤ T j)
    (hσ1 : ∀ j, σ j ≤ 1)
    (hf : ∀ v, f v ≠ 0 → ∀ a : {a // ¬grid a}, ∀ t : O a.val.1,
      |v ⟨a, t⟩| ≤ T a.val.1 * R a.val.1)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ finiteRowChartRadius (rowSets j).card (Fintype.card (I j)) (C j) (T j)) :
    ∃ g : (∀ a, (e a).Term) → Finset α → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card activeAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card (Finset α) * ∏ a, Cc a ∧
      ∀ (z : MixedCoveredJetSource I O E n d),
        z ∈ mixedCoveredJetRegion U o b d
          (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)) →
        ∀ (u : Finset α → ∀ j, euclideanSubspace (U j)),
          (∀ s j, (QuotientAddGroup.mk (u s j) : euclideanSubspace (U j) ⧸
            (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
            normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j)
              (mixedCoveredJetCoordinates U o d (mixedCoveredRowsSiteValue rowSets d z s) j ()).1) →
          allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e (chart z) =
            allocatedActiveWindowPrefactor B U b S rowSets d hR hσ x hb o bW q y₀ hcell f z *
              ∑ k, coverSiteCoefficient e k * ∏ s,
                g k s (fun a => ((((u s a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) := by
  obtain ⟨g, hg, hc, hv⟩ := exists_allocated_cover_site_expansion (G := G)
    (A := activeAxes) (S := Finset α) B U b e (fun a => ig a.val) hR he Q hQ
    o Cforward hforward K hK hb bW
  refine ⟨g, hg, hc, ?_⟩
  intro z hz u hu
  rw [allocatedActiveSiteProfile_window B U b S rowSets d hR hσ x hb o bW q y₀ hcell f e
    hrows (fun a => (he a).support) z hz]
  by_cases hp : allocatedActiveWindowPrefactor B U b S rowSets d hR hσ x hb o bW q y₀ hcell f z = 0
  · rw [hp, zero_mul, zero_mul]
  · have hs := allocatedActiveWindowPrefactor_sites_quarter B U b hR hσ S rowSets d x q y₀ hcell
      T hTi hTw hb o bW f hT hσ1 hf C hC hchart
      (fun j => finiteRowChartRadius_budget _ _ (hC j) (hT j) (hR j).le (hsmall j)) z hz hp
    congr 1
    rw [allocatedActiveSiteApproximation_mixed B U b S rowSets d e z]
    symm
    dsimp only [allocatedGridNaturalScale]
    exact hv u (fun s j => mixedArrayRegroup (I j) (Fin (n j)) Unit
      ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) hu
      (fun s j i => (hs s j (Set.mem_univ j) () (Set.mem_univ ())).1 i)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical NNReal

universe uα

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d]
variable (x : G → IntegerScalarCubeBox α S.value) (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "siteH" => (fun a : activeAxes => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a)))
  (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "chart" => mixedCoveredJetChart U o b hb bW d

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))

local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

noncomputable def allocatedGlobalWindowPrefactor (y : EuclideanJetLayers U O) : ℂ :=
  allocatedComplexGridMultiplier B U b S O hb o bW d
    (allocatedSelectedGridExtension B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
      (allocatedActiveGrid B U b S)
      (fun z => if ∀ a, z a ∈ allocatedGridSiteWindow B rowSets U b S a.val then 1 else 0)
      (allocatedActiveNaturalVolume B U b S rowSets)) y *
    (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f y : ℂ)

theorem allocatedGlobalWindowPrefactor_apply (z : MixedCoveredJetSource I O E n d)
    (hz : z ∈ region) :
    allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x q y₀ hcell hb o bW f (chart z) =
      allocatedActiveWindowPrefactor B U b S rowSets d hR hσ x hb o bW q y₀ hcell f z := by
  rw [allocatedGlobalWindowPrefactor, allocatedComplexGridMultiplier_apply B U b S O hb o bW d _ z hz]
  unfold allocatedSelectedGridExtension selectedProductExtension allocatedActiveWindowPrefactor
    allocatedActiveWindowCondition allocatedActiveRowsOfMixed allocatedActiveSiteChartPrefactor
  dsimp only
  split_ifs <;> ring

theorem allocatedGlobalWindowPrefactor_zero (y : EuclideanJetLayers U O)
    (hy : y ∉ chart '' region) :
    allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x q y₀ hcell hb o bW f y = 0 := by
  rw [allocatedGlobalWindowPrefactor, allocatedComplexGridMultiplier_zero B U b S O hb o bW d _ y hy, zero_mul]

theorem allocatedGlobalWindowPrefactor_measurable (hf : Measurable f) :
    Measurable (allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x q y₀ hcell hb o bW f) := by
  unfold allocatedGlobalWindowPrefactor
  apply Measurable.mul
  · apply allocatedComplexGridMultiplier_measurable
    exact allocatedSelectedGridExtension_measurable B U b hR hσ S x rows q
      (principalResidueLabel q y₀) hcell (allocatedActiveGrid B U b S) _ _
  · exact (allocatedWholeMaskedGridlessProfile_measurable B U b S x y₀ rows hb o bW d q f hf).complex_ofReal

theorem allocatedActiveSiteProfile_zero_outside (y : EuclideanJetLayers U O)
    (hy : y ∉ chart '' region) :
    allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e y = 0 := by
  rw [allocatedActiveSiteProfile, allocatedComplexGridMultiplier_zero B U b S O hb o bW d _ y hy, zero_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "siteH" => (fun a : activeAxes => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a)))
  (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem exists_allocated_physical_cover_profile
    {Nt V Cc : activeAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L ((siteH) a))
    (Q : ℝ≥0) (hQ : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTi : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hTw : ∀ j i, allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤ T j)
    (hσ1 : ∀ j, σ j ≤ 1)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ finiteRowChartRadius (rowSets j).card (Fintype.card (I j)) (C j) (T j)) :
    ∃ g : (∀ a, (e a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card activeAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
          {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ),
        (∀ v, f v ≠ 0 → ∀ a : {a // ¬grid a}, ∀ t : O a.val.1,
          |v ⟨a, t⟩| ≤ T a.val.1 * R a.val.1) →
        ∀ {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
            allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e
                (physicalCubeRowSample U d rows p hm v) =
              allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x q y₀ hcell hb o bW f
                (physicalCubeRowSample U d rows p hm v) *
                ∑ k, coverSiteCoefficient e k * ∏ s,
                  g k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
                    (p a.1) a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) := by
  obtain ⟨g, hg, hc, hv⟩ := exists_allocated_cover_site_expansion (G := G)
    (A := activeAxes) (S := Finset (Fin dim)) B U b e (fun a => ig a.val) hR he Q hQ
    o Cforward hforward K hK hb bW
  refine ⟨g, hg, hc, ?_⟩
  intro x f hf X p hp hm v
  have hrows (j : Fin m) (t : Finset (Fin dim)) (ht : t ∈ rowSets j) : t.card ≤ j.val + 1 :=
    (mem_boundedBooleanJetRows _ _).mp ht
  by_cases hy : physicalCubeRowSample U d rows p hm v ∈ chart '' region
  · obtain ⟨z, hz, hzy⟩ := hy
    rw [← hzy, allocatedGlobalWindowPrefactor_apply B U b hR hσ S rowSets d x q y₀ hcell hb o bW f z hz,
      allocatedActiveSiteProfile_window B U b S rowSets d hR hσ x hb o bW q y₀ hcell f e
        hrows (fun a => (he a).support) z hz]
    by_cases hzero : allocatedActiveWindowPrefactor B U b S rowSets d hR hσ x hb o bW q y₀ hcell f z = 0
    · rw [hzero, zero_mul, zero_mul]
    · have hs := allocatedActiveWindowPrefactor_sites_quarter B U b hR hσ S rowSets d x q y₀ hcell
        T hTi hTw hb o bW f hT hσ1 hf C hC hchart
        (fun j => finiteRowChartRadius_budget _ _ (hC j) (hT j) (hR j).le (hsmall j)) z hz hzero
      have hmatch := physicalRowChart_base_matching U o b hb bW d p hp hm v z hzy
      have hval := hv
        (fun s => physicalEuclideanSitePoint U p hm (fun z => (physicalCubeVertexValue v s z : ℝ)))
        (fun s j => mixedArrayRegroup (I j) (Fin (n j)) Unit
          ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) hmatch
        (fun s j i => (hs s j (Set.mem_univ j) () (Set.mem_univ ())).1 i)
      apply congrArg (fun a : ℂ =>
        allocatedActiveWindowPrefactor B U b S rowSets d hR hσ x hb o bW q y₀ hcell f z * a)
      rw [allocatedActiveSiteApproximation_mixed B U b S rowSets d e z]
      simpa only [allocatedGridNaturalScale, physicalEuclideanSitePoint_apply,
        mixedArrayRegroup_apply] using hval.symm
  · rw [allocatedActiveSiteProfile_zero_outside B U b hR hσ S rowSets d x q y₀ hcell hb o bW f e _ hy,
      allocatedGlobalWindowPrefactor_zero B U b hR hσ S rowSets d x q y₀ hcell hb o bW f _ hy,
      zero_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "siteH" => (fun a : activeAxes => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a)))
  (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem exists_allocated_ideal_physical_cover
    {Nt V Cc : activeAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L ((siteH) a))
    (Q : ℝ≥0) (hQ : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hσ1 : ∀ j, σ j ≤ 1)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets C j) :
    ∃ g : (∀ a, (e a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card activeAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      ∀ (δ : ℝ≥0), 0 < δ → δ ≤ 1 →
        ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
          {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
            allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell
                (allocatedPhysicalLongIdeal B U b hR S rowSets δ) e
                (physicalCubeRowSample U d rows p hm v) =
              allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x q y₀ hcell hb o bW
                (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
                (physicalCubeRowSample U d rows p hm v) *
                ∑ k, coverSiteCoefficient e k * ∏ s,
                  g k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
                    (p a.1) a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) := by
  obtain ⟨g, hg, hc, hv⟩ := exists_allocated_physical_cover_profile B U b hR hσ S
    d q y₀ hcell hb o bW e he Q hQ Cforward hforward K hK
    (allocatedIdealCoverSupport B rowSets) (allocatedIdealCoverSupport_nonneg B rowSets)
    (allocatedIdealCoverSupport_inactive B rowSets) (allocatedIdealCoverSupport_window B rowSets)
    hσ1 C hC hchart hsmall
  refine ⟨g, hg, hc, ?_⟩
  intro δ hδ hδ1 x X p hp hm v
  exact hv x (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
    (allocatedPhysicalLongIdeal_cover_support B U b hR S rowSets δ hδ hδ1) p hp hm v

end Erdos3.VectorPolynomial

end

end OAI
