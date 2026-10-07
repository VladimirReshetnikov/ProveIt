import OAI.Combinatorics.Progressions.Dynamics.AllocatedFiniteIdealMaskBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {A V : Type*} [Fintype A] (e : A → ScalarSiteExpansion V)
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (r : ℝ≥0) (hr : 0 < r) (k : ∀ a, (e a).Term) (s : V)
variable (residue : ∀ a, ZMod ((e a).period (k a)))
variable (f : (LayerSamplerAxis I n → ℝ) → ℂ)

noncomputable def allocatedNormalizedGridIdealFactor (y : LayerSamplerAxis I n → ℝ) : ℂ :=
  (allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s residue y / 2) *
    bufferedCoordinateProjection (allocatedGridAxis (I := I) U b S.value) r hr f y

theorem allocatedNormalizedGridIdealFactor_bounds (hR : ∀ j, 0 < R j)
    {T C H K : A → ℝ} {L LI : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (C a) (H a) L (K a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (hf : ∀ y, ‖f y‖ ≤ 1)
    (hI : LipschitzWith LI (bufferedCoordinateProjection
      (allocatedGridAxis (I := I) U b S.value) r hr f)) :
    (∀ y, ‖allocatedNormalizedGridIdealFactor B U b S e selected r hr k s residue f y‖ ≤ 1) ∧
      LipschitzWith ((Fintype.card A * L) * Q + LI)
        (allocatedNormalizedGridIdealFactor B U b S e selected r hr k s residue f) := by
  have hg := allocatedFullGridSiteFactor_bounds B U b e selected hR he Q hQ k s residue
  have hgn (y : LayerSamplerAxis I n → ℝ) :
      ‖allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s residue y / 2‖ ≤ 1 :=
    complex_div_two_norm_le ((hg.1 y).trans (by norm_num))
  have hgL := lipschitz_complex_div_two
    (allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s residue)
    ((Fintype.card A * L) * Q) (hg.2.weaken (by nlinarith [show (0 : ℝ≥0) ≤ (Fintype.card A * L) * Q from zero_le]))
  have hin := bufferedCoordinateProjection_norm_le
    (allocatedGridAxis (I := I) U b S.value) r hr f hf
  refine ⟨fun y => ?_, ?_⟩
  · rw [allocatedNormalizedGridIdealFactor, norm_mul]
    exact (mul_le_mul (hgn y) (hin y) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · have hprod := lipschitz_mul_of_bounds _ _ hgL hI (Bf := 1) (Bg := 1) hgn hin
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [allocatedNormalizedGridIdealFactor, one_mul, add_comm] using hprod.dist_le_mul y z

theorem allocatedNormalizedGridIdealFactor_pre_lipschitz (hR : ∀ j, 0 < R j)
    {T C H K : A → ℝ} {L LI : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (C a) (H a) L (K a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (hf : ∀ y, ‖f y‖ ≤ 1)
    (hI : LipschitzWith LI (bufferedCoordinateProjection
      (allocatedGridAxis (I := I) U b S.value) r hr f))
    {D eL eQ eI : ℝ} (hD : 0 ≤ D) (heL : 0 ≤ eL) (heQ : 0 ≤ eQ) (heI : 0 ≤ eI)
    (hA : (Fintype.card A : ℝ) ≤ D) (hL : (L : ℝ) ≤ Real.exp eL)
    (hQexp : (Q : ℝ) ≤ Real.exp eQ) (hIexp : (LI : ℝ) ≤ Real.exp eI) :
    LipschitzWith ⟨Real.exp (D + eL + eQ + eI + 1), Real.exp_nonneg _⟩
      (allocatedNormalizedGridIdealFactor B U b S e selected r hr k s residue f) := by
  apply (allocatedNormalizedGridIdealFactor_bounds B U b S e selected r hr k s residue f
    hR he Q hQ hf hI).2.weaken
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast]
  have hcard : (Fintype.card A : ℝ) ≤ Real.exp D := hA.trans (by linarith [Real.add_one_le_exp D])
  have hgrid : (Fintype.card A : ℝ) * L * Q ≤ Real.exp (D + eL + eQ) := by
    calc
      _ ≤ (Real.exp D * Real.exp eL) * Real.exp eQ :=
        mul_le_mul (mul_le_mul hcard hL L.coe_nonneg (Real.exp_pos _).le)
          hQexp Q.coe_nonneg (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hsum : (Fintype.card A : ℝ) * L * Q + LI ≤ 2 * Real.exp (D + eL + eQ + eI) := by
    have hg : (Fintype.card A : ℝ) * L * Q ≤ Real.exp (D + eL + eQ + eI) :=
      hgrid.trans (Real.exp_le_exp.mpr (by linarith only [heI]))
    have hi : (LI : ℝ) ≤ Real.exp (D + eL + eQ + eI) :=
      hIexp.trans (Real.exp_le_exp.mpr (by linarith only [hD, heL, heQ]))
    linarith only [hg, hi]
  apply hsum.trans
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  exact (mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le).trans_eq
    (by rw [← Real.exp_add]; congr 1; ring)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j a, coefficients (p j) a ∈ U j) (u : X → ℝ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "base" => (fun w : MixedCoveredJetSource I single E n d =>
  fun j => mixedArrayRegroup (I j) (Fin (n j)) Unit ((Prod.fst w) j) ())

theorem physicalSingleSiteChart_base_matching
    (w : MixedCoveredJetSource I (fun _ : Fin m => Unit) E n d)
    (hw : chart w = physicalSingleSiteValue U d p hm u) (j : Fin m) :
    (QuotientAddGroup.mk (physicalEuclideanSitePoint U p hm u j) : euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
      normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j)
        (orthonormalMixedChart (o j) (base w j)) := by
  have h := congrArg (fun y : EuclideanJetLayers U (fun _ => Unit) =>
    quotientIntegerCover (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j))).toAddSubgroup d (y j ())) hw
  rw [physicalSingleSiteValue_projection] at h
  change quotientIntegerCover _ d (normalizedCoveredChart (euclideanSubspace (U j))
    (b j) (hb j) (bW j) d (mixedCoveredJetCoordinates U o d w j ())) = _ at h
  rw [normalizedCoveredChart_projection] at h
  exact h.symm

theorem allocatedNormalizedGridIdealFactor_physical
    (g : (((Σ j, J j) → UnitAddCircle) → ℂ))
    (hg : ∀ (u₀ : ∀ j, euclideanSubspace (U j)) (w₀ : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
      (∀ j, (QuotientAddGroup.mk (u₀ j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w₀ j))) →
      (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w₀ j)) i| ≤ 1 / 4) →
      g (fun a => ((((u₀ a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) =
        allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s
          (fun a => ((w₀ (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
          (allocatedFullMixedSiteValue (R := R) U b w₀) / 2)
    (period : ℕ) (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (w : MixedCoveredJetSource I (fun _ : Fin m => Unit) E n d)
    (hw : w ∈ mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)))
    (hphysical : chart w = physicalSingleSiteValue U d p hm u) :
    g (fun a => (((eval u (p a.1) a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) *
      allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f
        (physicalSingleSiteValue U d p hm u) =
      (if mixedCoveredSiteResidue d period w = label then (1 : ℂ) else 0) *
        allocatedNormalizedGridIdealFactor B U b S e selected r hr k s
          (fun a => ((base w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a)))) f
          (allocatedFullMixedSiteValue (R := R) U b (base w)) := by
  have hmatch := physicalSingleSiteChart_base_matching U b o hb bW d p hm u w hphysical
  have hvalue := hg (physicalEuclideanSitePoint U p hm u) (base w) hmatch
    (fun j i => (hw j (Set.mem_univ j) () (Set.mem_univ ())).1 i)
  simp only [physicalEuclideanSitePoint_apply] at hvalue
  rw [hvalue, ← hphysical, allocatedMaskedSiteChartFactor_normalized B U b S o hb bW d r hr period label f w hw]
  simp only [allocatedNormalizedGridIdealFactor]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {A V : Type*} [Fintype A] (e : A → ScalarSiteExpansion V)
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (r : ℝ≥0) (hr : 0 < r) (k : ∀ a, (e a).Term) (s : V)
variable (residue : ∀ a, ZMod ((e a).period (k a)))
variable (f : (LayerSamplerAxis I n → ℝ) → ℂ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j a, coefficients (p j) a ∈ U j) (u : X → ℝ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "base" => (fun w : MixedCoveredJetSource I single E n d =>
  fun j => mixedArrayRegroup (I j) (Fin (n j)) Unit ((Prod.fst w) j) ())

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedNormalizedGridIdealFactor_smallBox
    (g : (((Σ j, J j) → UnitAddCircle) → ℂ))
    (hg : ∀ (u₀ : ∀ j, euclideanSubspace (U j)) (w₀ : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
      (∀ j, (QuotientAddGroup.mk (u₀ j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w₀ j))) →
      (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w₀ j)) i| ≤ 1 / 4) →
      g (fun a => ((((u₀ a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) =
        allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s
          (fun a => ((w₀ (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
          (allocatedFullMixedSiteValue (R := R) U b w₀) / 2)
    (period : ℕ) (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (w : MixedCoveredJetSource I (fun _ : Fin m => Unit) E n d)
    (hw : w ∈ mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeSmallBox (J j)))
    (hphysical : chart w = physicalSingleSiteValue U d p hm u) :
    g (fun a => (((eval u (p a.1) a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) *
      allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f
        (physicalSingleSiteValue U d p hm u) =
      (if mixedCoveredSiteResidue d period w = label then (1 : ℂ) else 0) *
        allocatedNormalizedGridIdealFactor B U b S e selected r hr k s
          (fun a => ((base w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a)))) f
          (allocatedFullMixedSiteValue (R := R) U b (base w)) := by
  by_cases hbuf : bufferedCoordinateProjection (allocatedGridAxis (I := I) U b S.value)
      r hr f (allocatedFullMixedSiteValue (R := R) U b (base w)) = 0
  · have hmasked := allocatedMaskedSiteChartFactor_smallBox B U b S o hb bW d r hr period
      hR C hC hchart hbudget label f w hw
    rw [← hphysical, hmasked]
    simp only [allocatedNormalizedGridIdealFactor, hbuf, mul_zero]
  · have hquarter := allocatedBufferedMixedSiteFactor_nonzero_mem_quarter B U b S r hr f
      hR o d w hbuf C hC hchart hbudget
    exact allocatedNormalizedGridIdealFactor_physical B U b S e selected r hr k s f
      o hb bW d p hm u g hg period label w hquarter hphysical

end Erdos3.VectorPolynomial

end

end OAI
