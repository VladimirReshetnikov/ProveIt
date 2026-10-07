import Mathlib.Algebra.Order.Floor.Ring
import OAI.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

include hφ in

theorem realificationLieHom_layer_surjective
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (j : ℕ) (y : ℝ ⊗[ℚ] M) (hy : y ∈ G.realification.layer j) :
    ∃ x ∈ F.realification.layer j, realificationLieHom φ x = y := by
  have hmap : (F.layer j).map φ.toLinearMap = G.layer j := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hφ j x hx
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hsurj j y hy
      exact ⟨x, hx, hxy⟩
  have hreal : ((F.layer j).baseChange ℝ).map (φ.toLinearMap.baseChange ℝ) =
      (G.layer j).baseChange ℝ := by
    rw [← realification_map, hmap]
  change y ∈ (G.layer j).baseChange ℝ at hy
  rw [← hreal] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨x, hx, hxy⟩

theorem realificationLieHom_top_kernel_eq_zero
    (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (hinj : ∀ x ∈ F.layer s, φ x = 0 → x = 0)
    (x : ℝ ⊗[ℚ] L) (hx : x ∈ F.realification.layer s)
    (hzero : realificationLieHom φ x = 0) : x = 0 := by
  let f := (G.layer s).subtype.comp (φ.toLinearMap.restrict (hφ s))
  have hker : LinearMap.ker f = ⊥ := by
    apply bot_unique
    intro z hz
    change z = 0
    exact Subtype.ext (hinj z z.property hz)
  have hkerReal : LinearMap.ker (f.baseChange ℝ) = ⊥ := by
    rw [← realification_ker, hker, Submodule.baseChange_bot]
  change x ∈ LinearMap.range ((F.layer s).subtype.baseChange ℝ) at hx
  obtain ⟨z, hz⟩ := hx
  have hfz : f.baseChange ℝ z = 0 := by
    rw [show f = φ.toLinearMap.comp (F.layer s).subtype from rfl, LinearMap.baseChange_comp]
    change φ.toLinearMap.baseChange ℝ ((F.layer s).subtype.baseChange ℝ z) = 0
    rw [hz]
    exact hzero
  have hz0 : z = 0 := by
    have hm : z ∈ LinearMap.ker (f.baseChange ℝ) := hfz
    rwa [hkerReal, Submodule.mem_bot] at hm
  rw [← hz, hz0, map_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3
open Module
open scoped TensorProduct BigOperators

theorem realification_fractional_integer_split {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] V) :
    ∃ (e : ℝ ⊗[ℚ] V) (r : V),
      x = e + (1 : ℝ) ⊗ₜ[ℚ] r ∧
      (∀ i, 0 ≤ (b.baseChange ℝ).repr e i ∧ (b.baseChange ℝ).repr e i < 1) ∧
      ∀ i, ∃ z : ℤ, b.repr r i = z := by
  let B := b.baseChange ℝ
  let r := b.equivFun.symm (fun i => (⌊B.repr x i⌋ : ℚ))
  let e := x - (1 : ℝ) ⊗ₜ[ℚ] r
  have hr (i) : b.repr r i = (⌊B.repr x i⌋ : ℚ) := by
    change b.equivFun (b.equivFun.symm _) i = _
    rw [LinearEquiv.apply_symm_apply]
  have he (i) : B.repr e i = Int.fract (B.repr x i) := by
    change B.repr (x - (1 : ℝ) ⊗ₜ[ℚ] r) i = _
    rw [map_sub, Finsupp.sub_apply, Module.Basis.baseChange_repr_tmul (S := ℝ), hr]
    simp only [Rat.smul_def, Rat.cast_intCast, mul_one]
    rfl
  refine ⟨e, r, by dsimp [e]; abel, ?_, fun i => ⟨⌊B.repr x i⌋, hr i⟩⟩
  intro i
  change 0 ≤ B.repr e i ∧ B.repr e i < 1
  rw [he]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem exists_fractional_integer_kernel_correction
    {ι L M : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
    [AddCommGroup M] [Module ℚ M] (φ : L →ₗ[ℚ] M)
    (H : Submodule ℚ L) (b : Basis ι ℚ (LinearMap.ker φ))
    (x : ℝ ⊗[ℚ] L) (hx : φ.baseChange ℝ x ∈ (H.map φ).baseChange ℝ) :
    ∃ (e : ℝ ⊗[ℚ] LinearMap.ker φ) (r : LinearMap.ker φ),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr e i ∧ (b.baseChange ℝ).repr e i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr r i = z) ∧
      x - (LinearMap.ker φ).subtype.baseChange ℝ e -
        (1 : ℝ) ⊗ₜ[ℚ] (r : L) ∈ H.baseChange ℝ := by
  rw [realification_map] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hk : x - y ∈ (LinearMap.ker φ).baseChange ℝ := by
    rw [realification_ker, LinearMap.mem_ker, map_sub, hxy, sub_self]
  obtain ⟨k, hk⟩ := hk
  obtain ⟨e, r, heq, he, hr⟩ := realification_fractional_integer_split b k
  refine ⟨e, r, he, hr, ?_⟩
  have heq' := congrArg ((LinearMap.ker φ).subtype.baseChange ℝ) heq
  rw [hk, map_add, LinearMap.baseChange_tmul] at heq'
  change x - y = (LinearMap.ker φ).subtype.baseChange ℝ e + (1 : ℝ) ⊗ₜ[ℚ] (r : L) at heq'
  have hfinal : x - (LinearMap.ker φ).subtype.baseChange ℝ e -
      (1 : ℝ) ⊗ₜ[ℚ] (r : L) = y := by
    rw [show x = (x - y) + y by abel, heq']
    abel
  rwa [hfinal]

namespace NilpotentLieFiltration

variable {ι L M : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (H : Submodule ℚ L) (hH : F.layer 2 ≤ H)
    (b : Basis ι ℚ (LinearMap.ker φ.toLinearMap))

include hH

theorem exists_kernel_constant_factors (g : F.realification.Group)
    (hg : realificationLieHom φ g.coord ∈ (H.map φ.toLinearMap).baseChange ℝ) :
    ∃ (e : ℝ ⊗[ℚ] LinearMap.ker φ.toLinearMap) (r : LinearMap.ker φ.toLinearMap),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr e i ∧ (b.baseChange ℝ).repr e i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr r i = z) ∧
      let kE : F.realification.Group := ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e⟩
      let kR : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] (r : L)⟩
      NilpotentLieBCHGroup.realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ kE = 1 ∧
      NilpotentLieBCHGroup.realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ kR = 1 ∧
      (kE⁻¹ * g * kR⁻¹).coord ∈ H.baseChange ℝ := by
  obtain ⟨e, r, he, hr, hlin⟩ :=
    exists_fractional_integer_kernel_correction φ.toLinearMap H b g.coord hg
  refine ⟨e, r, he, hr, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    change φ.toLinearMap.baseChange ℝ
      ((LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e) = 0
    have hm : (LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e ∈
        (LinearMap.ker φ.toLinearMap).baseChange ℝ := ⟨e, rfl⟩
    rwa [realification_ker, LinearMap.mem_ker] at hm
  · apply NilpotentLieBCHGroup.ext
    change φ.toLinearMap.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] (r : L)) = 0
    rw [LinearMap.baseChange_tmul, show φ.toLinearMap (r : L) = 0 from r.property,
      TensorProduct.tmul_zero]
  · let a := (LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e
    let c := (1 : ℝ) ⊗ₜ[ℚ] (r : L)
    have hbch := F.realification.bch_triple_sub_sum_mem_next_layer 1 (-a) g.coord (-c)
      (by rw [F.realification.one_eq_top]; trivial)
      (by rw [F.realification.one_eq_top]; trivial)
    have hm : lieBCH s (lieBCH s (-a) g.coord) (-c) - (-a + g.coord + -c) ∈
        H.baseChange ℝ := Submodule.baseChange_mono ℝ hH hbch
    have hlin' : -a + g.coord + -c ∈ H.baseChange ℝ := by
      convert hlin using 1
      dsimp [a, c]
      abel
    have hh := (H.baseChange ℝ).add_mem hm hlin'
    simpa only [sub_add_cancel, NilpotentLieBCHGroup.coord_mul,
      NilpotentLieBCHGroup.coord_inv] using hh

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

section Linear

variable {ι κ V L : Type*} [Fintype κ] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup L] [Module ℚ L]

theorem scalarExtension_coordinate_sum (b : Basis ι ℚ L) (bk : Basis κ ℚ V)
    (f : V →ₗ[ℚ] L) (x : ℝ ⊗[ℚ] V) (i : ι) :
    (b.baseChange ℝ).repr (f.baseChange ℝ x) i =
      ∑ j, (bk.baseChange ℝ).repr x j * (b.repr (f (bk j)) i : ℝ) := by
  classical
  conv_lhs => rw [← (bk.baseChange ℝ).sum_repr x]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, scalarExtension_basis_coordinates]

theorem scalarExtension_fractional_coordinates_bound
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (H : ℝ)
    (hentries : ∀ i j, |(b.repr (f (bk j)) i : ℝ)| ≤ H)
    (x : ℝ ⊗[ℚ] V)
    (hx : ∀ j, 0 ≤ (bk.baseChange ℝ).repr x j ∧ (bk.baseChange ℝ).repr x j < 1)
    (i : ι) :
    |(b.baseChange ℝ).repr (f.baseChange ℝ x) i| ≤ (Fintype.card κ : ℝ) * H := by
  rw [scalarExtension_coordinate_sum b bk f x i]
  calc
    _ ≤ ∑ j, |(bk.baseChange ℝ).repr x j * (b.repr (f (bk j)) i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, H := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hx j).1]
      exact (mul_le_mul (hx j).2.le (hentries i j) (abs_nonneg _) (by norm_num)).trans
        (by rw [one_mul])
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem integral_basis_image_denominatorGrid
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (q : ℕ) (hentries : ∀ j, (fun i => b.repr (f (bk j)) i) ∈ denominatorGrid q)
    (r : V) (hr : ∀ j, ∃ z : ℤ, bk.repr r j = z) :
    (fun i => b.repr (f r) i) ∈ denominatorGrid q := by
  classical
  choose z hz using hr
  choose a ha using hentries
  refine ⟨fun i => ∑ j, z j * a j i, ?_⟩
  intro i
  change (q : ℚ) * b.repr (f r) i = ((∑ j, z j * a j i : ℤ) : ℚ)
  conv_lhs => rw [← bk.sum_repr r]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (q : ℚ) * b.repr (f (bk j)) i = (a j i : ℚ) := ha j i
  rw [hz, ← hj]
  ring

theorem integral_basis_image_realDenominatorGrid
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (q : ℕ) (hentries : ∀ j, (fun i => b.repr (f (bk j)) i) ∈ denominatorGrid q)
    (r : V) (hr : ∀ j, ∃ z : ℤ, bk.repr r j = z) :
    (fun i => (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℚ] f r) i) ∈ realDenominatorGrid q := by
  have h := integral_basis_image_denominatorGrid b bk f q hentries r hr
  have hreal := (real_cast_mem_denominatorGrid_iff q (fun i => b.repr (f r) i)).mpr h
  simpa only [Basis.baseChange_repr_tmul (S := ℝ), Rat.smul_def, mul_one] using hreal

theorem exists_basis_image_bounds_of_height [Fintype ι]
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (H : ℕ) (hentries : ∀ i j, RationalHeightLE (b.repr (f (bk j)) i) H) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ (Fintype.card ι * Fintype.card κ) ∧
      (∀ i j, |(b.repr (f (bk j)) i : ℝ)| ≤ H) ∧
      ∀ j, (fun i => b.repr (f (bk j)) i) ∈ denominatorGrid q := by
  classical
  let A : Matrix ι κ ℚ := fun i j => b.repr (f (bk j)) i
  refine ⟨matrixDenominator A, matrixDenominator_pos A,
    matrixDenominator_le A hentries, fun i j => (hentries i j).abs_real_le, ?_⟩
  intro j
  refine ⟨fun i => clearedMatrix A i j, fun i => ?_⟩
  exact (congrFun (congrFun (clearedMatrix_cast A) i) j).symm

end Linear

namespace NilpotentLieFiltration

variable {ι κ L M : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}

theorem exists_kernel_constant_factors_with_bounds
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (S : Submodule ℚ L) (hS : F.layer 2 ≤ S)
    (b : Basis ι ℚ L) (bk : Basis κ ℚ (LinearMap.ker φ.toLinearMap))
    (H : ℝ) (q : ℕ)
    (hbound : ∀ i j, |(b.repr (bk j : L) i : ℝ)| ≤ H)
    (hgrid : ∀ j, (fun i => b.repr (bk j : L) i) ∈ denominatorGrid q)
    (g : F.realification.Group)
    (hg : realificationLieHom φ g.coord ∈ (S.map φ.toLinearMap).baseChange ℝ) :
    ∃ (e : ℝ ⊗[ℚ] LinearMap.ker φ.toLinearMap) (r : LinearMap.ker φ.toLinearMap),
      (∀ j, 0 ≤ (bk.baseChange ℝ).repr e j ∧ (bk.baseChange ℝ).repr e j < 1) ∧
      (∀ j, ∃ z : ℤ, bk.repr r j = z) ∧
      let kE : F.realification.Group := ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e⟩
      let kR : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] (r : L)⟩
      (∀ i, |(b.baseChange ℝ).repr kE.coord i| ≤ (Fintype.card κ : ℝ) * H) ∧
      (fun i => (b.baseChange ℝ).repr kR.coord i) ∈ realDenominatorGrid q ∧
      NilpotentLieBCHGroup.realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ kE = 1 ∧
      NilpotentLieBCHGroup.realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ kR = 1 ∧
      (kE⁻¹ * g * kR⁻¹).coord ∈ S.baseChange ℝ := by
  obtain ⟨e, r, he, hr, hfac⟩ := F.exists_kernel_constant_factors G φ S hS bk g hg
  refine ⟨e, r, he, hr, ?_⟩
  dsimp only
  refine ⟨?_, ?_, hfac⟩
  · exact scalarExtension_fractional_coordinates_bound b bk
      (LinearMap.ker φ.toLinearMap).subtype H hbound e he
  · exact integral_basis_image_realDenominatorGrid b bk
      (LinearMap.ker φ.toLinearMap).subtype q hgrid r hr

end NilpotentLieFiltration

end Erdos3

end

end OAI
