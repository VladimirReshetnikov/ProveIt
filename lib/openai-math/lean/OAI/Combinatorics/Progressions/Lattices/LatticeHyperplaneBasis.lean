/- Modified for ProveIt: Use older set-comprehension and discrete-subgroup names; statements unchanged. -/
import Mathlib

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeHyperplane (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ) : Submodule ℤ f.ker :=
  ZLattice.comap ℝ Λ f.ker.subtype

@[simp]
theorem mem_latticeHyperplane (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ) (x : f.ker) :
    x ∈ latticeHyperplane Λ f ↔ (x : E) ∈ Λ := Iff.rfl

noncomputable def hyperplaneRetraction (f : E →ₗ[ℝ] ℝ) (w : E) (hw : f w = 1) :
    E →ₗ[ℝ] f.ker where
  toFun x := ⟨x - f x • w, by simp only [LinearMap.mem_ker, map_sub, map_smul, hw, smul_eq_mul, mul_one, sub_self]⟩
  map_add' x y := by
    apply Subtype.ext
    change (x + y) - f (x + y) • w = (x - f x • w) + (y - f y • w)
    rw [map_add, add_smul]
    abel
  map_smul' a x := by
    apply Subtype.ext
    change a • x - f (a • x) • w = a • (x - f x • w)
    rw [map_smul, smul_eq_mul, smul_sub, smul_smul]

@[simp]
theorem hyperplaneRetraction_coe (f : E →ₗ[ℝ] ℝ) (w : E) (hw : f w = 1) (x : E) :
    (hyperplaneRetraction f w hw x : E) = x - f x • w := rfl

@[simp]
theorem hyperplaneRetraction_on_kernel (f : E →ₗ[ℝ] ℝ) (w : E) (hw : f w = 1) (x : f.ker) :
    hyperplaneRetraction f w hw (x : E) = x := by
  apply Subtype.ext
  simp only [hyperplaneRetraction_coe, LinearMap.mem_ker.mp x.property, zero_smul, sub_zero]

theorem hyperplaneRetraction_surjective (f : E →ₗ[ℝ] ℝ) (w : E) (hw : f w = 1) :
    Function.Surjective (hyperplaneRetraction f w hw) :=
  fun x => ⟨x, hyperplaneRetraction_on_kernel f w hw x⟩

theorem hyperplaneRetraction_mem (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) (x : E) (hx : x ∈ Λ) :
    hyperplaneRetraction f w hw x ∈ latticeHyperplane Λ f := by
  change x - f x • w ∈ Λ
  obtain ⟨n, hn⟩ := hint x hx
  rw [hn]
  simpa only [Int.cast_smul_eq_zsmul] using Λ.sub_mem hx (Λ.smul_mem n hwΛ)

theorem latticeHyperplane_span_top (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Λ : Set E) = ⊤)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) :
    Submodule.span ℝ (latticeHyperplane Λ f : Set f.ker) = ⊤ := by
  let S := Submodule.span ℝ (latticeHyperplane Λ f : Set f.ker)
  have hall : ∀ x : E, hyperplaneRetraction f w hw x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span ℝ (Λ : Set E) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hyperplaneRetraction_mem Λ f hint w hwΛ hw x hx)
    | zero => simpa only [map_zero] using S.zero_mem
    | add x y hx hy hpx hpy => simpa only [map_add] using S.add_mem hpx hpy
    | smul a x hx hpx => simpa only [map_smul] using S.smul_mem a hpx
  apply top_le_iff.mp
  intro x hx
  simpa only [hyperplaneRetraction_on_kernel] using hall (x : E)

instance latticeHyperplane_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (f : E →ₗ[ℝ] ℝ) : DiscreteTopology (latticeHyperplane Λ f) :=
  ZLattice.comap_discreteTopology ℝ Λ (by fun_prop) Subtype.val_injective

theorem latticeHyperplane_isZLattice (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) :
    IsZLattice ℝ (latticeHyperplane Λ f) :=
  ⟨latticeHyperplane_span_top Λ f (IsZLattice.span_top (K := ℝ)) hint w hwΛ hw⟩

theorem hyperplane_finrank [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] ℝ)
    (w : E) (hw : f w = 1) : Module.finrank ℝ f.ker + 1 = Module.finrank ℝ E := by
  have hsurj : Function.Surjective f := by
    intro a
    exact ⟨a • w, by simp only [map_smul, hw, smul_eq_mul, mul_one]⟩
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at h
  omega

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def integralLatticeValue (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (x : Λ) : ℤ :=
  (hint x x.property).choose

theorem integralLatticeValue_cast (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (x : Λ) :
    (integralLatticeValue Λ f hint x : ℝ) = f (x : E) :=
  (hint x x.property).choose_spec.symm

noncomputable def integralLatticeCoordinate (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) : Λ →ₗ[ℤ] ℤ where
  toFun := integralLatticeValue Λ f hint
  map_add' x y := by
    apply Int.cast_injective (α := ℝ)
    simp only [Int.cast_add, integralLatticeValue_cast, Submodule.coe_add, map_add]
  map_smul' a x := by
    apply Int.cast_injective (α := ℝ)
    simp only [integralLatticeValue_cast, Submodule.coe_smul, map_zsmul, RingHom.id_apply,
      smul_eq_mul, Int.cast_mul, zsmul_eq_mul]

theorem integralLatticeCoordinate_cast (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (x : Λ) :
    (integralLatticeCoordinate Λ f hint x : ℝ) = f (x : E) :=
  integralLatticeValue_cast Λ f hint x

theorem integralLatticeCoordinate_eq_iff (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (x : Λ) (n : ℤ) :
    integralLatticeCoordinate Λ f hint x = n ↔ f (x : E) = (n : ℝ) := by
  rw [← integralLatticeCoordinate_cast Λ f hint x]
  exact Int.cast_inj.symm

theorem integralLatticeCoordinate_surjective (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) :
    Function.Surjective (integralLatticeCoordinate Λ f hint) := by
  have hw' : integralLatticeCoordinate Λ f hint ⟨w, hwΛ⟩ = 1 :=
    (integralLatticeCoordinate_eq_iff Λ f hint ⟨w, hwΛ⟩ 1).mpr (by simpa using hw)
  intro n
  exact ⟨n • (⟨w, hwΛ⟩ : Λ), by rw [map_smul, hw']; simp⟩

end Erdos3

end

section

namespace Erdos3

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem lattice_gaussian_summable (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) (x : E) :
    Summable (fun m : Λ => Real.exp (-Real.pi * t * ‖x - (m : E)‖ ^ 2)) := by
  let r : ℝ := -(Module.finrank ℤ Λ : ℝ) - 1
  have hr : r < -(Module.finrank ℤ Λ : ℝ) := by dsimp [r]; linarith
  have hs := ZLattice.summable_norm_sub_rpow Λ r hr x
  have hc : IsClosed (Λ : Set E) := @AddSubgroup.isClosed_of_discrete E _ _ _ _
    Λ.toAddSubgroup (inferInstanceAs (DiscreteTopology Λ))
  have he : Topology.IsClosedEmbedding (fun m : Λ => (m : E) - x) := by
    exact (Homeomorph.subRight x).isClosedEmbedding.comp (Λ.isClosedEmbedding_subtype hc)
  have hn : Tendsto (fun m : Λ => ‖(m : E) - x‖) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding he
  have hd := (rexp_neg_quadratic_isLittleO_rpow_atTop
    (show -Real.pi * t < 0 by nlinarith [Real.pi_pos]) 0 r).isBigO.comp_tendsto hn
  have hsum := summable_of_isBigO hs hd
  simpa only [Function.comp_def, zero_mul, add_zero, norm_sub_rev] using hsum

noncomputable def latticeGaussianMass (Λ : Submodule ℤ E) (t : ℝ) (x : E) : ℝ :=
  ∑' m : Λ, Real.exp (-Real.pi * t * ‖x - (m : E)‖ ^ 2)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeGaussianMass_nonneg (Λ : Submodule ℤ E) (t : ℝ) (x : E) :
    0 ≤ latticeGaussianMass Λ t x := tsum_nonneg (fun _ => (Real.exp_pos _).le)

theorem latticeGaussianMass_pos (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) (x : E) : 0 < latticeGaussianMass Λ t x := by
  have h := (lattice_gaussian_summable Λ ht x).le_tsum (0 : Λ) (fun _ _ => (Real.exp_pos _).le)
  exact (Real.exp_pos _).trans_le h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeGaussianMass_add_lattice (Λ : Submodule ℤ E) (t : ℝ) (x : E) (v : Λ) :
    latticeGaussianMass Λ t (x + (v : E)) = latticeGaussianMass Λ t x := by
  have h := (Equiv.addRight v).tsum_eq (fun m : Λ => Real.exp (-Real.pi * t * ‖x + (v : E) - (m : E)‖ ^ 2))
  simpa only [latticeGaussianMass, Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub] using h.symm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeGaussianMass_eq_of_sub_mem (Λ : Submodule ℤ E) (t : ℝ) {x y : E}
    (hxy : x - y ∈ Λ) : latticeGaussianMass Λ t x = latticeGaussianMass Λ t y := by
  have h := latticeGaussianMass_add_lattice Λ t y ⟨x - y, hxy⟩
  simpa only [add_sub_cancel] using h

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeHyperplaneRetraction (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) : Λ →ₗ[ℤ] latticeHyperplane Λ f where
  toFun x := ⟨hyperplaneRetraction f w hw x, hyperplaneRetraction_mem Λ f hint w hwΛ hw x x.property⟩
  map_add' x y := by
    apply Subtype.ext
    change hyperplaneRetraction f w hw ((x : E) + y) = _
    exact map_add (hyperplaneRetraction f w hw) (x : E) (y : E)
  map_smul' n x := by
    apply Subtype.ext
    change hyperplaneRetraction f w hw (n • (x : E)) = n • hyperplaneRetraction f w hw x
    exact map_zsmul (hyperplaneRetraction f w hw) n (x : E)

@[simp]
theorem latticeHyperplaneRetraction_coe (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) (x : Λ) :
    (((latticeHyperplaneRetraction Λ f hint w hwΛ hw x : latticeHyperplane Λ f) : f.ker) : E) =
      (x : E) - f (x : E) • w := rfl

noncomputable def latticeHyperplaneSplit (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) :
    Λ ≃ₗ[ℤ] (latticeHyperplane Λ f × ℤ) :=
  { (latticeHyperplaneRetraction Λ f hint w hwΛ hw).prod (integralLatticeCoordinate Λ f hint) with
    invFun y := ⟨((y.1 : f.ker) : E) + y.2 • w,
      Λ.add_mem ((mem_latticeHyperplane Λ f (y.1 : f.ker)).mp y.1.property) (Λ.smul_mem y.2 hwΛ)⟩
    left_inv x := by
      apply Subtype.ext
      change (x : E) - f (x : E) • w + integralLatticeCoordinate Λ f hint x • w = (x : E)
      rw [← Int.cast_smul_eq_zsmul ℝ, integralLatticeCoordinate_cast]
      exact sub_add_cancel _ _
    right_inv y := by
      apply Prod.ext
      · apply Subtype.ext
        apply Subtype.ext
        change ((y.1 : f.ker) : E) + y.2 • w -
          f (((y.1 : f.ker) : E) + y.2 • w) • w = ((y.1 : f.ker) : E)
        have hy : f ((y.1 : f.ker) : E) = 0 := (y.1 : f.ker).property
        rw [map_add, map_zsmul, hy, hw, zero_add, zsmul_eq_mul, mul_one,
          Int.cast_smul_eq_zsmul]
        exact add_sub_cancel_right _ _
      · apply Int.cast_injective (α := ℝ)
        change (integralLatticeCoordinate Λ f hint _ : ℝ) = (y.2 : ℝ)
        rw [integralLatticeCoordinate_cast]
        change f (((y.1 : f.ker) : E) + y.2 • w) = (y.2 : ℝ)
        have hy : f ((y.1 : f.ker) : E) = 0 := (y.1 : f.ker).property
        simp only [map_add, map_zsmul, hy, hw, zero_add, zsmul_eq_mul, mul_one] }

theorem latticeHyperplaneSplit_symm_coe (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) (y : latticeHyperplane Λ f × ℤ) :
    ((latticeHyperplaneSplit Λ f hint w hwΛ hw).symm y : E) =
      ((y.1 : f.ker) : E) + y.2 • w := rfl

end Erdos3

end

section

namespace Erdos3

theorem integer_functional_image_generator {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : M →ₗ[ℤ] ℤ) (hf : f ≠ 0) :
    ∃ (m : ℤ) (w : M), m ≠ 0 ∧ f w = m ∧ ∀ x, ∃ n : ℤ, f x = n * m := by
  let m := Submodule.IsPrincipal.generator f.range
  have hspan : Submodule.span ℤ {m} = f.range := Submodule.IsPrincipal.span_singleton_generator _
  obtain ⟨w, hw⟩ := Submodule.IsPrincipal.generator_mem f.range
  have hm : m ≠ 0 := by
    intro hm
    have hz : f.range = ⊥ := by rw [← hspan, hm]; simp
    exact hf (LinearMap.range_eq_bot.mp hz)
  refine ⟨m, w, hm, hw, ?_⟩
  intro x
  have hx : f x ∈ Submodule.span ℤ {m} := by rw [hspan]; exact ⟨x, rfl⟩
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨n, (by simpa only [smul_eq_mul] using hn.symm)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integralLatticeCoordinate_ne_zero (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Λ : Set E) = ⊤)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (hf : f ≠ 0) :
    integralLatticeCoordinate Λ f hint ≠ 0 := by
  intro hz
  apply hf
  apply LinearMap.ext_on hspan
  intro x hx
  have h := integralLatticeCoordinate_cast Λ f hint ⟨x, hx⟩
  rw [hz, LinearMap.zero_apply, Int.cast_zero] at h
  exact h.symm

theorem exists_primitive_lattice_functional (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Λ : Set E) = ⊤)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (hf : f ≠ 0) :
    ∃ (m : ℤ) (g : E →ₗ[ℝ] ℝ) (w : E), m ≠ 0 ∧
      f = (m : ℝ) • g ∧ (∀ x ∈ Λ, ∃ n : ℤ, g x = (n : ℝ)) ∧
      w ∈ Λ ∧ g w = 1 ∧ g.ker = f.ker := by
  obtain ⟨m, w, hm, hw, hmult⟩ := integer_functional_image_generator
    (integralLatticeCoordinate Λ f hint) (integralLatticeCoordinate_ne_zero Λ f hspan hint hf)
  let g : E →ₗ[ℝ] ℝ := (m : ℝ)⁻¹ • f
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hg (x : E) : g x = f x / m := by simp only [g, LinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hfw : f (w : E) = (m : ℝ) := by
    rw [← integralLatticeCoordinate_cast Λ f hint w, hw]
  refine ⟨m, g, w, hm, ?_, ?_, w.property, ?_, ?_⟩
  · ext x
    simp only [LinearMap.smul_apply, smul_eq_mul, hg]
    field_simp
  · intro x hx
    obtain ⟨n, hn⟩ := hmult ⟨x, hx⟩
    refine ⟨n, ?_⟩
    rw [hg, ← integralLatticeCoordinate_cast Λ f hint ⟨x, hx⟩, hn, Int.cast_mul]
    exact mul_div_cancel_right₀ (n : ℝ) hmR
  · rw [hg, hfw, div_self hmR]
  · ext x
    simp only [LinearMap.mem_ker, hg, div_eq_zero_iff, hmR, or_false]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem gaussian_translate_bound (t R : ℝ) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (x m : E) (hx : ‖x‖ ≤ R) :
    Real.exp (-Real.pi * t * ‖x - m‖ ^ 2) ≤
      Real.exp (Real.pi * t * R ^ 2) * Real.exp (-Real.pi * (t / 2) * ‖m‖ ^ 2) := by
  have htriangle : ‖m‖ ≤ ‖x - m‖ + ‖x‖ := by
    calc
      ‖m‖ = ‖(m - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖m - x‖ + ‖x‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  have hsquare : ‖m‖ ^ 2 ≤ 2 * ‖x - m‖ ^ 2 + 2 * R ^ 2 := by
    have hx0 := norm_nonneg x
    have hm0 := norm_nonneg m
    have hxm0 := norm_nonneg (x - m)
    nlinarith [sq_nonneg (‖x - m‖ - ‖x‖)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le ht)
    (sub_nonneg.mpr hsquare)]

variable [FiniteDimensional ℝ E]

theorem continuousOn_latticeGaussianMass (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) (R : ℝ) (hR : 0 ≤ R) :
    ContinuousOn (latticeGaussianMass Λ t) (Metric.closedBall 0 R) := by
  have hs := (lattice_gaussian_summable Λ (half_pos ht) 0).mul_left
    (Real.exp (Real.pi * t * R ^ 2))
  apply continuousOn_tsum (fun _ => (by fun_prop : Continuous _).continuousOn) hs
  intro m x hx
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), zero_sub, norm_neg]
  exact gaussian_translate_bound t R ht.le hR x m (by simpa using hx)

theorem continuous_latticeGaussianMass (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) : Continuous (latticeGaussianMass Λ t) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (continuousOn_latticeGaussianMass Λ ht (‖x‖ + 1) (by positivity)).continuousAt
    (Metric.closedBall_mem_nhds_of_mem (by simp))

end Erdos3

end

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeHyperplaneBasis (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1)
    (b : Module.Basis ι ℤ (latticeHyperplane Λ f)) : Module.Basis (ι ⊕ Unit) ℤ Λ :=
  (b.prod (Module.Basis.singleton Unit ℤ)).map
    (latticeHyperplaneSplit Λ f hint w hwΛ hw).symm

@[simp]
theorem latticeHyperplaneBasis_inl (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1)
    (b : Module.Basis ι ℤ (latticeHyperplane Λ f)) (i : ι) :
    (latticeHyperplaneBasis Λ f hint w hwΛ hw b (Sum.inl i) : E) = (b i : f.ker) := by
  simp [latticeHyperplaneBasis, latticeHyperplaneSplit_symm_coe]

@[simp]
theorem latticeHyperplaneBasis_inr (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1)
    (b : Module.Basis ι ℤ (latticeHyperplane Λ f)) (j : Unit) :
    (latticeHyperplaneBasis Λ f hint w hwΛ hw b (Sum.inr j) : E) = w := by
  simp [latticeHyperplaneBasis, latticeHyperplaneSplit_symm_coe]

end Erdos3

end

end OAI
