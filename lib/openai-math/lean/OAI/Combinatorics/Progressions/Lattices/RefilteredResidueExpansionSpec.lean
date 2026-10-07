import OAI.Combinatorics.Progressions.Estimates.LowerRefilteredCyclicExpansion
import OAI.Combinatorics.Progressions.Linear.NativeMarkedKernelRepresentatives

namespace OAI

section

namespace Erdos3

theorem exists_residue_class_lattice_factors {σ G : Type*} [Group G]
    (Γ : Subgroup G) (f : (σ → ℤ) → G) (M : ℕ) (P : G → Prop)
    (hperiod : ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
      ((QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (f y)) ∧
      ((QuotientGroup.mk (f x)⁻¹ : G ⧸ Γ) = QuotientGroup.mk (f y)⁻¹))
    (hrep : ∀ x : σ → ℤ,
      (∃ r : G, P r ∧ ∃ γ ∈ Γ, f x = r * γ) ∧
      (∃ r : G, P r ∧ ∃ γ ∈ Γ, f x = γ * r)) :
    ∃ rR rL : (σ → ZMod M) → G,
      (∀ c, P (rR c) ∧ P (rL c)) ∧
      ∀ x : σ → ℤ,
        (∃ γ ∈ Γ, f x = rR (fun j => (x j : ZMod M)) * γ) ∧
        (∃ γ ∈ Γ, f x = γ * rL (fun j => (x j : ZMod M))) := by
  classical
  let lift : (σ → ZMod M) → σ → ℤ := fun c j => Classical.choose (ZMod.intCast_surjective (c j))
  have hlift (c : σ → ZMod M) (j : σ) : (lift c j : ZMod M) = c j :=
    Classical.choose_spec (ZMod.intCast_surjective (c j))
  choose rR hrR γR hγR heqR using fun c => (hrep (lift c)).1
  choose rL hrL γL hγL heqL using fun c => (hrep (lift c)).2
  refine ⟨rR, rL, fun c => ⟨hrR c, hrL c⟩, ?_⟩
  intro x
  let c := fun j => (x j : ZMod M)
  have hxy (j : σ) : (M : ℤ) ∣ x j - lift c j :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (lift c j) (x j) M).mp (hlift c j)
  have h := hperiod x (lift c) hxy
  have hR : (QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (rR c) := by
    apply h.1.trans
    rw [heqR c]
    exact QuotientGroup.mk_mul_of_mem _ (hγR c)
  have hL : (QuotientGroup.mk (f x)⁻¹ : G ⧸ Γ) = QuotientGroup.mk (rL c)⁻¹ := by
    apply h.2.trans
    rw [heqL c, mul_inv_rev]
    exact QuotientGroup.mk_mul_of_mem _ (Γ.inv_mem (hγL c))
  constructor
  · refine ⟨(rR c)⁻¹ * f x, QuotientGroup.eq.mp hR.symm, ?_⟩
    change f x = rR c * ((rR c)⁻¹ * f x)
    group
  · have hmem : rL c * (f x)⁻¹ ∈ Γ := by
      simpa only [inv_inv] using QuotientGroup.eq.mp hL.symm
    refine ⟨f x * (rL c)⁻¹, ?_, ?_⟩
    · simpa only [mul_inv_rev, inv_inv] using Γ.inv_mem hmem
    · change f x = (f x * (rL c)⁻¹) * rL c
      group

end Erdos3

end

section

namespace Erdos3

theorem exists_residue_class_right_lattice_factors {σ G : Type*} [Group G]
    (Γ : Subgroup G) (f : (σ → ℤ) → G) (M : ℕ) (P : G → Prop)
    (hperiod : ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
      (QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (f y))
    (hrep : ∀ x : σ → ℤ, ∃ r : G, P r ∧ ∃ γ ∈ Γ, f x = r * γ) :
    ∃ r : (σ → ZMod M) → G,
      (∀ c, P (r c)) ∧
      ∀ x : σ → ℤ, ∃ γ ∈ Γ,
        f x = r (fun j => (x j : ZMod M)) * γ := by
  classical
  let lift : (σ → ZMod M) → σ → ℤ :=
    fun c j => Classical.choose (ZMod.intCast_surjective (c j))
  have hlift (c : σ → ZMod M) (j : σ) : (lift c j : ZMod M) = c j :=
    Classical.choose_spec (ZMod.intCast_surjective (c j))
  choose r hr γ hγ heq using fun c => hrep (lift c)
  refine ⟨r, hr, ?_⟩
  intro x
  let c := fun j => (x j : ZMod M)
  have hxy (j : σ) : (M : ℤ) ∣ x j - lift c j :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (lift c j) (x j) M).mp (hlift c j)
  have hR : (QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (r c) := by
    apply (hperiod x (lift c) hxy).trans
    rw [heq c]
    exact QuotientGroup.mk_mul_of_mem _ (hγ c)
  refine ⟨(r c)⁻¹ * f x, QuotientGroup.eq.mp hR.symm, ?_⟩
  change f x = r c * ((r c)⁻¹ * f x)
  group

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_native_residue_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M m : ℕ, 0 < M ∧ 0 < m ∧
        (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
          D.filtration.PolynomialRationalGrid D.basis w q g →
          ∃ rR rL : (σ → ZMod M) → D.RealGroup,
            (∀ c, (∀ i, |(D.basis.baseChange ℝ).repr (rR c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (D.basis.baseChange ℝ).equivFun (rR c).coord ∈ realDenominatorGrid m ∧
              (∀ i, |(D.basis.baseChange ℝ).repr (rL c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (D.basis.baseChange ℝ).equivFun (rL c).coord ∈ realDenominatorGrid m) ∧
            ∀ x : σ → ℤ,
              (∃ γ ∈ D.realLattice,
                D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g =
                  rR (fun j => (x j : ZMod M)) * γ) ∧
              (∃ γ ∈ D.realLattice,
                D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g =
                  γ * rL (fun j => (x j : ZMod M))) := by
  obtain ⟨a, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨b, _, hrep⟩ := exists_native_rational_representatives s
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + (Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ q hq hqp
  obtain ⟨M, hM, hMb, hper⟩ := hperiod D w hw p hp hD hσ q hq hqp
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D p hp hD q hq hqp
  have hsum : (p + a) ^ a + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (p + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) _)).trans hsum
  refine ⟨M, m, hM, hm, hMb.trans (Real.exp_le_exp.mpr haC), hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hg
  let f := fun x : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g
  let A := fun r : D.RealGroup =>
    (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
      (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m
  have hf (x : σ → ℤ) :
      (∃ r : D.RealGroup, A r ∧ ∃ γ ∈ D.realLattice, f x = r * γ) ∧
      (∃ r : D.RealGroup, A r ∧ ∃ γ ∈ D.realLattice, f x = γ * r) := by
    obtain ⟨⟨rR, hR, hRgrid, γR, hγR, heqR⟩, ⟨rL, hL, hLgrid, γL, hγL, heqL⟩⟩ :=
      hreps (f x) (D.filtration.polynomialRationalGrid_value D.basis w q g hg x)
    exact ⟨⟨rR, ⟨fun i => (hR i).trans (Real.exp_le_exp.mpr hbC), hRgrid⟩, γR, hγR, heqR⟩,
      ⟨rL, ⟨fun i => (hL i).trans (Real.exp_le_exp.mpr hbC), hLgrid⟩, γL, hγL, heqL⟩⟩
  obtain ⟨rR, rL, hA, heq⟩ := exists_residue_class_lattice_factors D.realLattice f M A (hper g hg) hf
  exact ⟨rR, rL, fun c => ⟨(hA c).1.1, (hA c).1.2, (hA c).2.1, (hA c).2.2⟩, heq⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_marked_kernel_residue_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
      (w : σ → ℕ), (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M m : ℕ, 0 < M ∧ 0 < m ∧
        (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
          D.filtration.PolynomialRationalGrid D.basis w q g →
          (∀ x : σ → ℤ, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := F.lowerCentralSeries_eq_bot) φ
            (D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g) = 1) →
          ∃ r : (σ → ZMod M) → D.RealGroup,
            (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := F.lowerCentralSeries_eq_bot) φ (r a) = 1 ∧
              (∀ i, |(D.basis.baseChange ℝ).repr (r a).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (D.basis.baseChange ℝ).equivFun (r a).coord ∈ realDenominatorGrid m) ∧
            ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g =
                r (fun j => (x j : ZMod M)) * γ := by
  obtain ⟨a, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨b, _, hrep⟩ := exists_native_marked_kernel_representatives s
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a +
    (Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ d t D F c φ w hw p hp hD hσ hκ hφ q hq hqp
  obtain ⟨M, hM, hMb, hper⟩ := hperiod D w hw p hp hD hσ q hq hqp
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D c φ p hp hD hκ hφ q hq hqp
  have hsum : (p + a) ^ a + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (p + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) _)).trans hsum
  refine ⟨M, m, hM, hm, hMb.trans (Real.exp_le_exp.mpr haC),
    hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hg hmark
  let f := fun x : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g
  let A := fun r : D.RealGroup =>
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ r = 1 ∧
    (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
      (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m
  have hf (x : σ → ℤ) : ∃ r : D.RealGroup, A r ∧ ∃ γ ∈ D.realLattice, f x = r * γ := by
    have hxK := (mem_realificationSubgroup_ker_iff
      (hM := F.lowerCentralSeries_eq_bot) φ (f x)).mpr (hmark x)
    obtain ⟨r, hrK, hr, hrgrid, γ, hγ, hfac⟩ := hreps (f x) hxK
      (D.filtration.polynomialRationalGrid_value D.basis w q g hg x)
    refine ⟨r, ⟨?_, fun i => (hr i).trans (Real.exp_le_exp.mpr hbC), hrgrid⟩, γ, hγ, hfac⟩
    exact (mem_realificationSubgroup_ker_iff (hM := F.lowerCentralSeries_eq_bot) φ r).mp hrK
  obtain ⟨r, hr, hfac⟩ := exists_residue_class_right_lattice_factors D.realLattice f M A
    (fun x y hxy => (hper g hg x y hxy).1) hf
  exact ⟨r, hr, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredResidueExpansionSpec
    (p : ℝ) (q r P : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
    Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
    Q'.GeometryComplexityLE cost ∧
    ∃ Z : RationalFilteredNilmanifold (∀ i : I₀, L i.val) (s + 1)
        (Fintype.card (Σ i : I₀, Fin (d i.val))),
      Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
      Z.GeometryComplexityLE cost ∧
      letI := Z.metricSpace
      let w := fun _ : Unit => 1
      let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
      let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := Z.filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
      ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
          realifyFunctional (piFrequency (freq j)) x = 0) →
        ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
          (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ η : ℝ},
          0 < ρ → 0 ≤ η →
          (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
          (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
          (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
          (∀ i x y, 0 < A i x → 0 < A i y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
          ∀ (S : ZMod N → (D a).Niltest w),
            (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
            (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
              (∀ j, realifyFunctional (freq j a) z.coord = 0) →
              ∀ x, (S h).observable (z • x) = (S h).observable x) →
            ∀ (slow middle rat : ZMod N → ((D a).filtration.realification.adaptedPolynomialFiltration w).Group)
              (κ : ZMod N → (D a).RealGroup)
              (g : ZMod N → E.filtration.realification.PolynomialOrbit w),
              (∀ h, κ h ∈ (D a).realLattice) →
              (∀ h, slow h * middle h * rat h * (D a).filtration.realification.adaptedConstantGroupHom w (κ h) =
                ⟨⟨(S h).orbit.log, (S h).orbit.property⟩⟩) →
              (∀ h, (D a).filtration.PolynomialSlowBound (D a).basis w
                (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
              (∀ h, (D a).filtration.PolynomialRationalGrid (D a).basis w q (rat h)) →
              (∀ h x, (D a).filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (middle h) =
                φ (E.filtration.realification.polynomialOrbitEval w x (g h))) →
              (∀ i j h x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                dist (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
                  (fun _ => (x.val : ℤ)) (g h))) : Z.Space)
                  (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
                    (fun _ => (y.val : ℤ)) (g h)))) ≤ η) →
              ∃ U : I → J → ZMod N → Q'.Niltest w,
                (∀ i j h, (U i j h).UnitIntervalValued) ∧
                (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                  ∀ x, (U i j h).eval x = 0) ∧
                ∃ err : ZMod N → ZMod N → ℝ,
                  (∀ h x, ((S h).evalCyclic N (fun _ => x)).re =
                    (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                  ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (ρ + η) + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

end OAI
