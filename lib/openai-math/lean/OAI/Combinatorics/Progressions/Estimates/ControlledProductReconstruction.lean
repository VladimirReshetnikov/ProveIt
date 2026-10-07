/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Dynamics.FiniteProductBudget
import OAI.Combinatorics.Progressions.Dynamics.ImageCoverBudget
import OAI.Combinatorics.Progressions.Dynamics.ImageReconstructionLogBudget
import OAI.Combinatorics.Progressions.Dynamics.NativeHorizontalLiftBudget
import OAI.Combinatorics.Progressions.Dynamics.ReconstructionConstantBudget
import OAI.Combinatorics.Progressions.Nilpotent.FactorwiseBCHCovers

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]
  [∀ a, LieAlgebra ℚ (M a)]
  {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realification_liePiEval_liePiMap (φ : ∀ a, L →ₗ⁅ℚ⁆ M a)
    (x : ℝ ⊗[ℚ] L) (a : α) :
    realificationLieHom (liePiEval a) (realificationLieHom (liePiMap φ) x) =
      realificationLieHom (φ a) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Fintype α] {κ : α → Type*}

theorem realification_pi_basis_repr (f : ∀ a, Basis (κ a) ℚ (M a))
    (x : ℝ ⊗[ℚ] (∀ a, M a)) (a : α) (i : κ a) :
    ((Pi.basis f).baseChange ℝ).repr x ⟨a, i⟩ =
      ((f a).baseChange ℝ).repr (realificationLieHom (liePiEval a) x) i := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul,
      Pi.basis_repr, liePiEval_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem realification_liePiMap_eq_zero_iff (f : ∀ a, Basis (κ a) ℚ (M a))
    (φ : ∀ a, L →ₗ⁅ℚ⁆ M a) (x : ℝ ⊗[ℚ] L) :
    realificationLieHom (liePiMap φ) x = 0 ↔ ∀ a, realificationLieHom (φ a) x = 0 := by
  constructor
  · intro hx a
    rw [← realification_liePiEval_liePiMap φ x a, hx, map_zero]
  · intro hx
    apply ((Pi.basis f).baseChange ℝ).repr.injective
    ext ⟨a, i⟩
    rw [realification_pi_basis_repr, realification_liePiEval_liePiMap, hx]
    simp only [map_zero, Finsupp.zero_apply]

theorem mem_realification_liePiMap_ker_iff {s : ℕ}
    (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (φ : ∀ a, L →ₗ⁅ℚ⁆ M a)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL)) :
    g ∈ (realificationMap (hnil := hL)
      (hM := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot) (liePiMap φ)).ker ↔
      ∀ a, g ∈ (realificationMap (hnil := hL) (hM := (F a).lowerCentralSeries_eq_bot) (φ a)).ker := by
  constructor
  · intro hg a
    have hzero : realificationLieHom (liePiMap φ) g.coord = 0 :=
      congrArg NilpotentLieBCHGroup.coord (MonoidHom.mem_ker.mp hg)
    apply MonoidHom.mem_ker.mpr
    apply NilpotentLieBCHGroup.ext
    exact (realification_liePiMap_eq_zero_iff f φ g.coord).mp hzero a
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply NilpotentLieBCHGroup.ext
    apply (realification_liePiMap_eq_zero_iff f φ g.coord).mpr
    intro a
    exact congrArg NilpotentLieBCHGroup.coord (MonoidHom.mem_ker.mp (hg a))

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_controlled_rational_image_reconstruction (s : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ {ι κ L M : Type*} [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (hM : LieModule.lowerCentralSeries ℚ M M s = ⊥)
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (_hH : 1 ≤ H)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (_hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Λ)
    (hΛout : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (_hcL : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (_hcM : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H)
    (_hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (_hcover : Λ.map realificationHom ⊓ (realificationMap (hnil := hL) (hM := hM) φ).range ≤
      (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ))
    (u : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) ⧸
      Γ.map realificationHom) → ℂ)
    (_hker : ∀ k ∈ (realificationMap (hnil := hL) (hM := hM) φ).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x))
    (ℓ B : ℝ≥0)
    (_hu : letI := realificationQuotientMetricSpace e Γ l hl hΓ; LipschitzWith ℓ u)
    (_hub : ∀ x, ‖u x‖ ≤ B)
    (p : ℝ) (_hp : 0 ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hℓp : (ℓ : ℝ) ≤ Real.exp p) (_hBp : (B : ℝ) ≤ Real.exp p),
    letI := realificationQuotientMetricSpace f Λ m hm hΛout
    ∃ (v : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s (realification_lowerCentralSeries_eq_bot hM) ⧸
      Λ.map realificationHom) → ℂ) (K : ℝ≥0),
      (K : ℝ) ≤ Real.exp ((p + N) ^ N) ∧ LipschitzWith K v ∧ (∀ y, ‖v y‖ ≤ 2 * B) ∧
      ∀ x, v (QuotientGroup.mk (realificationMap (hnil := hL) (hM := hM) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨C, _, hrep⟩ := exists_bounded_image_representatives s
  obtain ⟨D, _, hprod⟩ := exists_bch_triple_product_exp_bound s 1
  obtain ⟨F, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s 1
  obtain ⟨E, _, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s D
  obtain ⟨Z, _, hlog⟩ := exists_bchLogMetricConstant_exp_bound s
  obtain ⟨N, hN, hbudget⟩ := exists_generalReconstructionLogBudget_bound C D E F Z
  refine ⟨N, hN, ?_⟩
  intro ι κ L M _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL hM e f φ Γ Λ l m H hl hm hH
    hΓ hΛin hΛout hcL hcM hφ hcover u hker ℓ B hu hub p hp hι hκ hHp hmp hℓp hBp

  classical
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (f.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  let Φ := realificationMap (hnil := hL) (hM := hM) φ
  let J := Φ.range
  obtain ⟨Q, hQ, hJ⟩ := exists_realified_image_defining_matrix (hL := hL) (hM := hM) e f φ hH hφ
  let HQ : ℝ≥0 := (2 * ((Fintype.card ι + 1) * (H * rationalKernelHeight (Fintype.card κ) H) ^ Fintype.card ι) : ℕ)
  have hQabs : ∀ i j, |(Q i j : ℝ)| ≤ HQ := by
    intro i j
    change |(Q i j : ℝ)| ≤ ((2 * ((Fintype.card ι + 1) *
      (H * rationalKernelHeight (Fintype.card κ) H) ^ Fintype.card ι) : ℕ) : ℝ)
    exact (hQ i j).abs_real_le
  let R := (((p + 2) ^ 4 + C) ^ C) + (p + 2) ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let q := p + R + 1
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  let S := {g | g ∈ J ∧ ∀ i, |(f.baseChange ℝ).repr g.coord i| ≤ Real.exp R}
  have hrepS : ∀ y : CosetImage Φ (Λ.map realificationHom),
      ∃ x, projectToCosetImage Φ (Λ.map realificationHom) x = y ∧ Φ x ∈ S := by
    intro y
    obtain ⟨x, hx, hxb⟩ := hrep hL hM e f φ Λ m H p hm hΛin hcL hφ hp hι hκ hHp hmp y
    exact ⟨x, hx, ⟨⟨x, rfl⟩, hxb⟩⟩
  have hlarge {g} (hg : g ∈ S) : ∀ i, |(f.baseChange ℝ).repr g.coord i| ≤ Real.exp ((q + 2) ^ 1) := by
    intro i
    apply (hg.2 i).trans
    apply Real.exp_le_exp.mpr
    dsimp [q]
    simp only [pow_one]
    linarith
  let W : ℝ≥0 := ⟨Real.exp ((q + D) ^ D), Real.exp_nonneg _⟩
  have hW : 1 ≤ W := Real.one_le_exp (by positivity)
  have hprodS : ∀ x ∈ S, ∀ y ∈ S, ∀ i, |(f.baseChange ℝ).repr (y⁻¹ * x).coord i| ≤ W := by
    intro x hx y hy i
    have h := hprod (f.baseChange ℝ) (lieStructureConstants f) H q
      (realification_lowerCentralSeries_eq_bot hM) y⁻¹ x 1
      (fun i j k => (realLieBasis_structure f i j k).symm) hq (hκ.trans hpq)
      (hHp.trans (Real.exp_le_exp.mpr hpq)) hcM
      (fun j => by simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hlarge hy j)
      (hlarge hx) (fun j => by simp only [coord_one, map_zero, Finsupp.zero_apply, abs_zero]; positivity) i
    change |(f.baseChange ℝ).repr (y⁻¹ * x).coord i| ≤ Real.exp ((q + D) ^ D)
    simpa only [mul_one] using h
  obtain ⟨Kleft, _, hKleftBound, hKleft⟩ := hleft (f.baseChange ℝ) (lieStructureConstants f) H q
    (realification_lowerCentralSeries_eq_bot hM)
    (fun i j k => (realLieBasis_structure f i j k).symm) hq (hκ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hcM
  obtain ⟨ε, hε, hεinv, hgap⟩ := exists_uniform_lattice_image_gap (f.baseChange ℝ)
    (lieStructureConstants f) (fun i j k => (realLieBasis_structure f i j k).symm) hcM
    Q HQ W Kleft hW hQabs m hm J (Λ.map realificationHom) hJ
    (realification_subgroup_grid f Λ m hΛout) S (fun _ h => h.1) hprodS
    (fun y hy => hKleft y⁻¹ (fun j => by
      simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hlarge hy j))
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_image_section e f φ.toLinearMap hH hφ
  have hσB : ∀ i j, |(e.baseChange ℝ).repr (σ.baseChange ℝ ((f.baseChange ℝ) j)) i| ≤
      (rationalKernelHeight (Fintype.card κ) H : ℝ) := by
    intro i j
    rw [linearMap_baseChange_basis]
    exact (hσH i j).abs_real_le
  let T := bchLogMetricConstant s (Fintype.card κ) H 1
  let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ)
    (rationalKernelHeight (Fintype.card κ) H) * ((Fintype.card κ : ℝ≥0) + 1) * T
  have hlift := exists_local_metric_lifts_on_image
    (hnil := realification_lowerCentralSeries_eq_bot hL) (hM := realification_lowerCentralSeries_eq_bot hM)
    (e.baseChange ℝ) (f.baseChange ℝ) (realificationLieHom φ) (σ.baseChange ℝ)
    (linearMap_baseChange_image_section φ.toLinearMap σ hσ) (rationalKernelHeight (Fintype.card κ) H)
    hσB (lieStructureConstants f) (fun i j k => (realLieBasis_structure f i j k).symm) hcM
  let := realificationQuotientMetricSpace e Γ l hl hΓ
  have hpull : LipschitzWith ℓ (fun x => u (QuotientGroup.mk x)) := by
    simpa only [mul_one, Function.comp_def] using hu.comp
      (quotientMetricSpace_lipschitz_mk (e.baseChange ℝ) (Γ.map realificationHom)
        (realification_subgroup_closed_discrete e Γ l hl hΓ).1)
  obtain ⟨v, hv, hLip, hbound⟩ := exists_ambient_image_reconstruction Φ (Γ.map realificationHom)
    (Λ.map realificationHom) (realification_subgroup_closed_discrete f Λ m hm hΛout).1
    hcover (fun x => u (QuotientGroup.mk x)) hker
    (fun γ hγ x => congrArg u (QuotientGroup.eq.mpr (by
      simpa only [mul_inv_rev, inv_mul_cancel_left, inv_mul_cancel_right] using
        (Γ.map realificationHom).inv_mem hγ)))
    S ℓ K B T⁻¹ ε (inv_pos.mpr (bchLogMetricConstant_pos _ _ _ _)) hε hpull
    (fun x => hub _) hrepS hgap hlift
  let r := generalReconstructionLogBudget C D E F Z p
  obtain ⟨hr, hpr, h18, h48, h24, hZr, hEr, hFr⟩ :=
    generalReconstructionLogBudget_bounds C D E F Z hp
  have hexp : Real.exp p ≤ Real.exp r := Real.exp_le_exp.mpr hpr
  let Asec := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ)
    (rationalKernelHeight (Fintype.card κ) H)
  let Ndim : ℝ≥0 := (Fintype.card κ : ℝ≥0) + 1
  let Den : ℝ≥0 := (matrixDenominator Q * m : ℕ)
  let Row : ℝ≥0 := Ndim * (HQ + 1)
  let Box : ℝ≥0 := ⟨bchBoxCoordinateBound s (Fintype.card κ) H W,
    bchBoxCoordinateBound_nonneg _ _ _ W.coe_nonneg⟩
  have hAsec : (Asec : ℝ) ≤ Real.exp r :=
    (imageSection_bound_le_exp _ _ H hp hι hκ hHp).trans (Real.exp_le_exp.mpr h18)
  have hNdim : (Ndim : ℝ) ≤ Real.exp r := by
    apply le_trans _ hexp
    change (Fintype.card κ : ℝ) + 1 ≤ Real.exp p
    exact (by linarith : (Fintype.card κ : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hT : (T : ℝ) ≤ Real.exp r :=
    (hlog _ H p hp hκ hHp).trans (Real.exp_le_exp.mpr hZr)
  have hDen : (Den : ℝ) ≤ Real.exp r :=
    (imageDefiningDenominator_le_exp Q (Fintype.card ι) H m hQ hp hι hκ hHp hmp).trans
      (Real.exp_le_exp.mpr h48)
  have hRow : (Row : ℝ) ≤ Real.exp r := by
    apply le_trans _ (Real.exp_le_exp.mpr h24)
    exact imageDefiningRow_bound_le_exp _ _ H hp hι hκ hHp
  have hBox : (Box : ℝ) ≤ Real.exp r := by
    have hpqd : p ≤ q + D := hpq.trans (le_add_of_nonneg_right (Nat.cast_nonneg D))
    have hwbound : (W : ℝ) ≤ Real.exp ((q + D + 2) ^ D) := by
      change Real.exp ((q + D) ^ D) ≤ _
      exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) D)
    have hh := (bchBoxCoordinateBound_le_bchBoxMetricConstant s (Fintype.card κ) H W).trans
      (hbox _ H W (q + D) (by positivity) (hκ.trans hpqd)
        (hHp.trans (Real.exp_le_exp.mpr hpqd)) hwbound)
    exact hh.trans (Real.exp_le_exp.mpr hEr)
  have hY : (Kleft : ℝ) ≤ Real.exp r := hKleftBound.trans (Real.exp_le_exp.mpr hFr)
  have hεformula : (ε : ℝ)⁻¹ = (T : ℝ) * Kleft + Den * Row * Box * T * Kleft + 1 := by
    rw [hεinv]
    change _ = (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * Kleft +
      ((matrixDenominator Q * m : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * ((HQ : ℝ) + 1)) *
        bchBoxCoordinateBound s (Fintype.card κ) H W *
        (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * Kleft + 1
    ring
  have htotal := generalReconstructionConstant_le_exp ℓ B Asec Ndim T Den Row Box Kleft ε r hr
    (hℓp.trans hexp) (hBp.trans hexp) hAsec hNdim hT hDen hRow hBox hY hεformula
  exact ⟨v, _, htotal.trans (Real.exp_le_exp.mpr (hbudget p hp)), hLip, hbound, hv⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_controlled_reconstruction (s : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ {ι κ L M : Type*} [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration M s) (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) (Δ : Subgroup F.Group)
      (l m H : ℕ) (hl : 0 < l) (_hm : 0 < m) (_hH : 1 ≤ H)
      (_hΓin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
      (hΓout : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
      (_hΔin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Δ)
      (_hΔout : bchSubgroupCoordinates f Δ ⊆ denominatorGrid m)
      (_hcL : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
      (_hcM : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H)
      (_hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
      (u : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) ⧸
        Γ.map realificationHom) → ℂ)
      (_hker : ∀ k ∈ (realificationMap (hnil := hL) (hM := F.lowerCentralSeries_eq_bot) φ).ker, ∀ x,
        u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x))
      (ℓ B : ℝ≥0)
      (_hu : letI := realificationQuotientMetricSpace e Γ l hl hΓout; LipschitzWith ℓ u)
      (_hub : ∀ x, ‖u x‖ ≤ B)
      (p : ℝ) (_hp : 0 ≤ p) (_hd : (Fintype.card ι : ℝ) ≤ p) (_hn : (Fintype.card κ : ℝ) ≤ p)
      (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p) (_hmp : (m : ℝ) ≤ Real.exp p)
      (_hℓp : (ℓ : ℝ) ≤ Real.exp p) (_hBp : (B : ℝ) ≤ Real.exp p),
      ∃ Λ : Subgroup F.Group, Λ ≤ Δ ∧
        (Λ.subgroupOf Δ).Characteristic ∧ (Λ.subgroupOf Δ).Normal ∧ (Λ.subgroupOf Δ).FiniteIndex ∧
        (Λ.relIndex Δ : ℝ) ≤ Real.exp ((p + N) ^ N) ∧
        ∃ (m' : ℕ) (hm' : 0 < m') (hout : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m'),
          (m' : ℝ) ≤ Real.exp ((p + N) ^ N) ∧ scaledIntegerGrid m' ⊆ bchSubgroupCoordinates f Λ ∧
          letI := realificationQuotientMetricSpace f Λ m' hm' hout
          ∃ (v : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s
            (realification_lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot) ⧸
            Λ.map realificationHom) → ℂ) (K : ℝ≥0),
            (K : ℝ) ≤ Real.exp ((p + N) ^ N) ∧ LipschitzWith K v ∧ (∀ y, ‖v y‖ ≤ 2 * B) ∧
            ∀ x, v (QuotientGroup.mk (realificationMap (hnil := hL)
              (hM := F.lowerCentralSeries_eq_bot) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨C, _, hrec⟩ := exists_controlled_rational_image_reconstruction s
  obtain ⟨N, hN, hbudget⟩ := exists_image_cover_reconstruction_budget (bchIntegralDenominatorBound s) C
  refine ⟨N, hN, ?_⟩
  intro ι κ L M _ _ _ _ _ _ _ _ _ _ _ _ _ _ F hL e f φ Γ Δ l m H hl hm hH
    hΓin hΓout hΔin hΔout hcL hcM hφ u hker ℓ B hu hub p hp hd hn hHp hlp hmp hℓp hBp
  obtain ⟨A, Λ, hA, hAb, hΛ, hchar, hnormal, hfinite, hindex, hin, hout, hcover⟩ :=
    F.exists_image_lattice_cover e f φ Γ Δ l m H hl hm hH hΓin hΔin hΔout hφ hcM
  let a := imageLatticeLogBudget (bchIntegralDenominatorBound s) p
  have ha : 0 ≤ a := imageLatticeLogBudget_nonneg _ hp
  have hAe : (A : ℝ) ≤ Real.exp a :=
    (Nat.cast_le.mpr hAb).trans (imageLatticeBound_le_exp _ _ _ H l m hp hd hn hHp hlp hmp)
  let q := 2 * p + a
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hexp : Real.exp p ≤ Real.exp q := Real.exp_le_exp.mpr hpq
  have hmA : ((m * A : ℕ) : ℝ) ≤ Real.exp (p + a) := by
    rw [Nat.cast_mul, Real.exp_add]
    exact mul_le_mul hmp hAe (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hm' : 0 < (m * A) * m := Nat.mul_pos (Nat.mul_pos hm hA) hm
  have hm'e : (((m * A) * m : ℕ) : ℝ) ≤ Real.exp q := by
    calc
      _ = ((m * A : ℕ) : ℝ) * (m : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp (p + a) * Real.exp p :=
        mul_le_mul hmA hmp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp q := by rw [← Real.exp_add]; dsimp [q]; congr 1; ring
  have hindexe : (Λ.relIndex Δ : ℝ) ≤ Real.exp (p * (p + a)) := by
    apply (Nat.cast_le.mpr hindex).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hmA _).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn (by positivity))
  obtain ⟨hqb, hidxb, hcostb⟩ := hbudget p hp
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite,
    hindexe.trans (Real.exp_le_exp.mpr hidxb), (m * A) * m, hm', hout,
    hm'e.trans (Real.exp_le_exp.mpr hqb), hin, ?_⟩
  obtain ⟨v, K, hKb, hLip, hbound, heq⟩ := hrec hL F.lowerCentralSeries_eq_bot e f φ Γ Λ
    l ((m * A) * m) H hl hm' hH hΓout hin hout hcL hcM hφ hcover u hker ℓ B hu hub q hq
    (hd.trans hpq) (hn.trans hpq) (hHp.trans hexp) hm'e (hℓp.trans hexp) (hBp.trans hexp)
  exact ⟨v, K, hKb.trans (Real.exp_le_exp.mpr hcostb), hLip, hbound, heq⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem exists_rational_image_reconstruction
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Λ)
    (hΛout : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (hcL : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hcM : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H)
    (hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (hcover : Λ.map realificationHom ⊓ (realificationMap (hnil := hL) (hM := hM) φ).range ≤
      (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ))
    (u : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) ⧸
      Γ.map realificationHom) → ℂ)
    (hker : ∀ k ∈ (realificationMap (hnil := hL) (hM := hM) φ).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x))
    (ℓ B : ℝ≥0)
    (hu : letI := realificationQuotientMetricSpace e Γ l hl hΓ; LipschitzWith ℓ u)
    (hub : ∀ x, ‖u x‖ ≤ B)
    (p : ℝ) (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hmp : (m : ℝ) ≤ Real.exp p) :
    letI := realificationQuotientMetricSpace f Λ m hm hΛout
    ∃ (v : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s (realification_lowerCentralSeries_eq_bot hM) ⧸
      Λ.map realificationHom) → ℂ) (K : ℝ≥0),
      LipschitzWith K v ∧ (∀ y, ‖v y‖ ≤ 2 * B) ∧
      ∀ x, v (QuotientGroup.mk (realificationMap (hnil := hL) (hM := hM) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨_, _, hrec⟩ := exists_controlled_rational_image_reconstruction s
  let q : ℝ := p + ℓ + B + 1
  have hpq : p ≤ q := by dsimp [q]; linarith [ℓ.coe_nonneg, B.coe_nonneg]
  have hq : 0 ≤ q := hp.trans hpq
  have hexp : Real.exp p ≤ Real.exp q := Real.exp_le_exp.mpr hpq
  have hℓq : (ℓ : ℝ) ≤ Real.exp q := by
    have hle : (ℓ : ℝ) ≤ q + 1 := by dsimp [q]; linarith [B.coe_nonneg]
    exact hle.trans (Real.add_one_le_exp q)
  have hBq : (B : ℝ) ≤ Real.exp q := by
    have hle : (B : ℝ) ≤ q + 1 := by dsimp [q]; linarith [ℓ.coe_nonneg]
    exact hle.trans (Real.add_one_le_exp q)
  obtain ⟨v, K, _, hLip, hbound, heq⟩ := hrec hL hM e f φ Γ Λ l m H hl hm hH
    hΓ hΛin hΛout hcL hcM hφ hcover u hker ℓ B hu hub q hq
    (hι.trans hpq) (hκ.trans hpq) (hHp.trans hexp) (hmp.trans hexp) hℓq hBq
  exact ⟨v, K, hLip, hbound, heq⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct BigOperators

theorem exists_controlled_product_reconstruction (s : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ {α ι L : Type*} {M : α → Type*} {κ : α → Type*}
      [Fintype α] [Fintype ι] [∀ a, Fintype (κ a)]
      [LieRing L] [LieAlgebra ℚ L] [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ a, M a))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ a, M a))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ a, M a))] [T2Space (ℝ ⊗[ℚ] (∀ a, M a))]
      (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (F : ∀ a, NilpotentLieFiltration (M a) s)
      (e : Basis ι ℚ L) (f : ∀ a, Basis (κ a) ℚ (M a)) (φ : ∀ a, L →ₗ⁅ℚ⁆ M a)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) (Δ : ∀ a, Subgroup (F a).Group)
      (l H : ℕ) (m : α → ℕ) (hl : 0 < l) (_hm : ∀ a, 0 < m a) (_hH : 1 ≤ H)
      (_hΓin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
      (hΓout : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
      (_hΔin : ∀ a, scaledIntegerGrid (m a) ⊆ bchSubgroupCoordinates (f a) (Δ a))
      (_hΔout : ∀ a, bchSubgroupCoordinates (f a) (Δ a) ⊆ denominatorGrid (m a))
      (_hcL : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
      (_hcM : ∀ a i j k, RationalHeightLE (lieStructureConstants (f a) i j k) H)
      (_hφ : ∀ a i j, RationalHeightLE ((f a).repr (φ a (e j)) i) H)
      (u : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) ⧸
        Γ.map realificationHom) → ℂ)
      (_hker : ∀ k, (∀ a, k ∈ (realificationMap (hnil := hL)
        (hM := (F a).lowerCentralSeries_eq_bot) (φ a)).ker) → ∀ x,
        u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x))
      (ℓ B : ℝ≥0)
      (_hu : letI := realificationQuotientMetricSpace e Γ l hl hΓout; LipschitzWith ℓ u)
      (_hub : ∀ x, ‖u x‖ ≤ B)
      (p : ℝ) (_hp : 0 ≤ p) (_hd : (Fintype.card ι : ℝ) ≤ p)
      (_hα : (Fintype.card α : ℝ) ≤ p) (_hκ : ∀ a, (Fintype.card (κ a) : ℝ) ≤ p)
      (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p)
      (_hmp : ∀ a, (m a : ℝ) ≤ Real.exp p)
      (_hℓp : (ℓ : ℝ) ≤ Real.exp p) (_hBp : (B : ℝ) ≤ Real.exp p),
      ∃ Λ : Subgroup (NilpotentLieFiltration.pi F).Group, Λ ≤ piBCHSubgroup F Δ ∧
        (Λ.subgroupOf (piBCHSubgroup F Δ)).Characteristic ∧
        (Λ.subgroupOf (piBCHSubgroup F Δ)).Normal ∧
        (Λ.subgroupOf (piBCHSubgroup F Δ)).FiniteIndex ∧
        (Λ.relIndex (piBCHSubgroup F Δ) : ℝ) ≤ Real.exp ((p + N) ^ N) ∧
        ∃ (m' : ℕ) (hm' : 0 < m')
          (hout : bchSubgroupCoordinates (Pi.basis f) Λ ⊆ denominatorGrid m'),
          (m' : ℝ) ≤ Real.exp ((p + N) ^ N) ∧
          scaledIntegerGrid m' ⊆ bchSubgroupCoordinates (Pi.basis f) Λ ∧
          letI := realificationQuotientMetricSpace (Pi.basis f) Λ m' hm' hout
          ∃ (v : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] (∀ a, M a)) s
            (realification_lowerCentralSeries_eq_bot (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot) ⧸
            Λ.map realificationHom) → ℂ) (K : ℝ≥0),
            (K : ℝ) ≤ Real.exp ((p + N) ^ N) ∧ LipschitzWith K v ∧ (∀ y, ‖v y‖ ≤ 2 * B) ∧
            ∀ x, v (QuotientGroup.mk (realificationMap (hnil := hL)
              (hM := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot) (liePiMap φ) x)) =
              u (QuotientGroup.mk x) := by
  obtain ⟨C, _, hrec⟩ := exists_controlled_reconstruction s
  obtain ⟨N, hN, hbudget⟩ := exists_finiteProductReconstruction_budget C
  refine ⟨N, hN, ?_⟩
  intro α ι L M κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL F e f φ Γ Δ l H m hl hm hH
    hΓin hΓout hΔin hΔout hcL hcM hφ u hker ℓ B hu hub p hp hd hα hκ hHp hlp hmp hℓp hBp
  classical
  let m₀ := ∏ a, m a
  have hm₀ : 0 < m₀ := Finset.prod_pos (fun a _ => hm a)
  have hdvd (a : α) : m a ∣ m₀ := Finset.dvd_prod_of_mem m (Finset.mem_univ a)
  have hin : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) :=
    piBCHSubgroup_inner_grid F f Δ m₀ (fun a => (scaledIntegerGrid_subset_of_dvd (hdvd a)).trans (hΔin a))
  have hout : bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) ⊆ denominatorGrid m₀ :=
    piBCHSubgroup_outer_grid F f Δ m₀ (fun a => (hΔout a).trans (denominatorGrid_subset_of_dvd (hdvd a)))
  let q := p ^ 2 + p + 1
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hp2q : p ^ 2 ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hexp : Real.exp p ≤ Real.exp q := Real.exp_le_exp.mpr hpq
  have hdim : (Fintype.card (Σ a, κ a) : ℝ) ≤ q :=
    (sigma_card_le_budget hp hα hκ).trans hp2q
  have hmp₀ : (m₀ : ℝ) ≤ Real.exp q :=
    (product_denominator_le_budget m hp hα hmp).trans (Real.exp_le_exp.mpr hp2q)
  have hkerπ : ∀ k ∈ (realificationMap (hnil := hL)
      (hM := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot) (liePiMap φ)).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x) := by
    intro k hk
    exact hker k ((mem_realification_liePiMap_ker_iff hL F f φ k).mp hk)
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hidx, m', hm', hgridout, hmb, hgridin,
      v, K, hKb, hLip, hbound, heq⟩ :=
    hrec (NilpotentLieFiltration.pi F) hL e (Pi.basis f) (liePiMap φ) Γ (piBCHSubgroup F Δ)
      l m₀ H hl hm₀ hH hΓin hΓout hin hout hcL (lie_pi_structure_height f hH hcM)
      (liePiMap_height e f φ hφ) u hkerπ ℓ B hu hub q hq (hd.trans hpq) hdim
      (hHp.trans hexp) (hlp.trans hexp) hmp₀ (hℓp.trans hexp) (hBp.trans hexp)
  have hexpN : Real.exp ((q + C) ^ C) ≤ Real.exp ((p + N) ^ N) :=
    Real.exp_le_exp.mpr (hbudget p hp)
  exact ⟨Λ, hΛ, hchar, hnormal, hfinite, hidx.trans hexpN, m', hm', hgridout,
    hmb.trans hexpN, hgridin, v, K, hKb.trans hexpN, hLip, hbound, heq⟩

end Erdos3

end

end OAI
