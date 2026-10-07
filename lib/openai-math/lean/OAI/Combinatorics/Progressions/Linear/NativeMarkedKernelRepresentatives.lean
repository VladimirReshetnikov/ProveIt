import Mathlib.Algebra.Lie.Ideal
import Mathlib.LinearAlgebra.Matrix.ToLin
import OAI.Combinatorics.Progressions.Dynamics.QuotientDetectorHeightBudget
import OAI.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization
import OAI.Combinatorics.Progressions.Estimates.NativeBoundedSubalgebraRepresentatives

namespace OAI

section

namespace Erdos3
open Module
open scoped Classical Matrix

section Linear
variable {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

noncomputable def basisMatrixKernelEquiv (b : Basis ι ℚ V) (c : Basis κ ℚ W)
    (T : V →ₗ[ℚ] W) :
    LinearMap.ker (LinearMap.toMatrix b c T).mulVecLin ≃ₗ[ℚ] LinearMap.ker T := by
  have hker : LinearMap.ker (LinearMap.toMatrix b c T).mulVecLin =
      (LinearMap.ker T).comap b.equivFun.symm.toLinearMap := by
    ext x
    have heq : LinearMap.toMatrix b c T *ᵥ x = c.equivFun (T (b.equivFun.symm x)) := by
      simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using
        LinearMap.toMatrix_mulVec_repr b c T (b.equivFun.symm x)
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [heq]
    exact c.equivFun.map_eq_zero_iff
  exact (LinearEquiv.ofEq _ _ hker).trans
    (b.equivFun.symm.ofSubmodule' (LinearMap.ker T))

@[simp] theorem basisMatrixKernelEquiv_repr (b : Basis ι ℚ V) (c : Basis κ ℚ W)
    (T : V →ₗ[ℚ] W) (x : LinearMap.ker (LinearMap.toMatrix b c T).mulVecLin) (i : ι) :
    b.repr (basisMatrixKernelEquiv b c T x : V) i = (x : ι → ℚ) i := by
  change b.repr (b.equivFun.symm (x : ι → ℚ)) i = (x : ι → ℚ) i
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem exists_bounded_linearMap_kernel_basis
    (b : Basis ι ℚ V) (c : Basis κ ℚ W) (T : V →ₗ[ℚ] W)
    {H : ℕ} (hH : 1 ≤ H)
    (hT : ∀ i j, RationalHeightLE (c.repr (T (b j)) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker T),
        ∀ j i, RationalHeightLE (b.repr (bk j : V) i)
          (rationalKernelHeight (Fintype.card κ) H) := by
  let A := LinearMap.toMatrix b c T
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    simpa only [A, LinearMap.toMatrix_apply] using hT
  obtain ⟨t, ht, bk, hbk⟩ := exists_bounded_rational_kernel_basis A hH hA
  refine ⟨Module.finrank ℚ (LinearMap.ker A.mulVecLin), ?_,
    bk.map (basisMatrixKernelEquiv b c T), ?_⟩
  · simpa only [Module.finrank_pi, Module.finrank_self, Nat.mul_one] using
      (LinearMap.ker A.mulVecLin).finrank_le
  · intro j i
    simp only [Basis.map_apply]
    rw [basisMatrixKernelEquiv_repr b c T (bk j) i]
    exact (hbk j i).mono (rationalKernelHeight_mono hH ht)

end Linear

section Lie
variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem exists_bounded_lie_kernel_basis
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {H : ℕ} (hH : 1 ≤ H)
    (hφ : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap),
        ∀ j i, RationalHeightLE (b.repr (bk j : L) i)
          (rationalKernelHeight (Fintype.card κ) H) :=
  exists_bounded_linearMap_kernel_basis b c φ.toLinearMap hH hφ

theorem exists_bounded_lie_kernel_subalgebra_basis
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {H : ℕ} (hH : 1 ≤ H)
    (hφ : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ φ.ker.toLieSubalgebra,
        ∀ j i, RationalHeightLE (b.repr (bk j : L) i)
          (rationalKernelHeight (Fintype.card κ) H) :=
  exists_bounded_lie_kernel_basis b c φ hH hφ

theorem exists_lie_kernel_basis_exp_height
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {H : ℕ} (hHpos : 1 ≤ H)
    (hφ : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap), ∀ j i,
        ((b.repr (bk j : L) i).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
        ((b.repr (bk j : L) i).den : ℝ) ≤ Real.exp ((p + 2) ^ 7) := by
  obtain ⟨r, hr, bk, hbk⟩ := exists_bounded_lie_kernel_basis b c φ hHpos hφ
  have hbudget := rationalKernelHeight_le_budget (Fintype.card κ) H hp hκ hH
  exact ⟨r, hr, bk, fun j i =>
    ⟨(Nat.cast_le.mpr (hbk j i).1).trans hbudget,
      (Nat.cast_le.mpr (hbk j i).2).trans hbudget⟩⟩

theorem exists_lie_kernel_subalgebra_basis_logHeight
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (c.repr (φ (b j)) i) ≤ p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ φ.ker.toLieSubalgebra, ∀ j i,
        ((b.repr (bk j : L) i).num.natAbs : ℝ) ≤ Real.exp ((p + 3) ^ 7) ∧
        ((b.repr (bk j : L) i).den : ℝ) ≤ Real.exp ((p + 3) ^ 7) := by
  obtain ⟨r, hr, bk, hbk⟩ := exists_lie_kernel_basis_exp_height b c φ (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hφ i j))
    (by linarith : 0 ≤ p + 1) (hκ.trans (by linarith))
    (ceil_exp_le_exp_add_one hp)
  refine ⟨r, hr, bk, fun j i => ?_⟩
  rw [show p + 1 + 2 = p + 3 by ring] at hbk
  exact hbk j i

end Lie
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)

theorem exists_topLayer_basis_logHeight (hs : 1 ≤ s) {p : ℝ}
    (hD : D.GeometryComplexityLE p) :
    ∃ r : ℕ, ∃ b : Basis (Fin r) ℚ ((D.filtration.layerIdeal s).toLieSubalgebra),
      ∀ a i, rationalLogHeight (D.basis.repr (b a : L) i) ≤ p := by
  obtain ⟨b, hb⟩ := D.exists_positive_layer_basis s hs hD
  exact ⟨finrank ℚ (D.filtration.layer s), b, hb⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module

noncomputable def markedKernelCommonHeight (p : ℝ) : ℕ :=
  ⌈Real.exp ((p + 3) ^ 7)⌉₊

theorem markedKernelCommonHeight_pos (p : ℝ) :
    1 ≤ markedKernelCommonHeight p :=
  one_le_ceil_exp _

theorem markedKernelCommonHeight_le_exp {p : ℝ} (hp : 0 ≤ p) :
    (markedKernelCommonHeight p : ℝ) ≤ Real.exp ((p + 3) ^ 7 + 1) :=
  ceil_exp_le_exp_add_one (by positivity)

theorem rationalHeightLE_markedKernelCommonHeight {q : ℚ} {p : ℝ}
    (hp : 0 ≤ p) (hq : rationalLogHeight q ≤ p) :
    RationalHeightLE q (markedKernelCommonHeight p) := by
  have hpow : (p + 3) ^ 1 ≤ (p + 3) ^ 7 :=
    pow_le_pow_right₀ (by linarith) (by omega)
  apply rationalHeightLE_ceil_exp
  exact hq.trans (by simpa only [pow_one] using (show p ≤ (p + 3) ^ 7 by
    calc
      p ≤ p + 3 := by linarith
      _ = (p + 3) ^ 1 := (pow_one _).symm
      _ ≤ (p + 3) ^ 7 := hpow))

section Lie

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem exists_marked_kernel_basis_commonHeight
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (c.repr (φ (b j)) i) ≤ p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap),
        ∀ j i, RationalHeightLE (b.repr (bk j : L) i)
          (markedKernelCommonHeight p) := by
  obtain ⟨r, hr, bk, hbk⟩ :=
    exists_lie_kernel_subalgebra_basis_logHeight b c φ hp hκ hφ
  exact ⟨r, hr, bk, fun j i => rationalHeightLE_ceil_exp_of_entries (hbk j i)⟩

theorem exists_marked_kernel_basis_commonHeight_of_dim
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (c.repr (φ (b j)) i) ≤ p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ (r : ℝ) ≤ p ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap),
        ∀ j i, RationalHeightLE (b.repr (bk j : L) i)
          (markedKernelCommonHeight p) := by
  obtain ⟨r, hr, bk, hbk⟩ := exists_marked_kernel_basis_commonHeight b c φ hp hκ hφ
  exact ⟨r, hr, (Nat.cast_le.mpr hr).trans hι, bk, hbk⟩

end Lie
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

theorem exists_nativeTopMarkKernel_spanning_budget :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin e) ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ),
      1 ≤ s → 0 ≤ p → D.GeometryComplexityLE p → (e : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (b.repr (φ (D.basis j)) i) ≤ p) →
      ∃ vP : Fin d → L,
        Submodule.span ℚ (Set.range vP) =
          D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap ∧
        ∀ i j, rationalLogHeight (D.basis.repr (vP i) j) ≤ (p + 2) ^ C := by
  let P : Polynomial ℕ := ((((Polynomial.X + 3) ^ 7 + 4) ^ 2 + 2) ^ 63 + 3)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s d e D b φ p hs hp hD he hφ
  classical
  obtain ⟨r, btop, hbtop⟩ := D.exists_topLayer_basis_logHeight hs hD
  obtain ⟨rk, _, bk, hbk⟩ := exists_lie_kernel_subalgebra_basis_logHeight
    D.basis b φ hp (by simpa only [Fintype.card_fin] using he) hφ
  let q : ℝ := (p + 3) ^ 7
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ p + 3 by linarith)
      (show 1 ≤ (7 : ℕ) by decide)
    have h' : p + 3 ≤ q := by simpa only [pow_one] using h
    linarith
  have htop : ∀ a i, rationalLogHeight (D.basis.repr (btop a : L) i) ≤ q :=
    fun a i => (hbtop a i).trans hpq
  have hk : ∀ a i, rationalLogHeight (D.basis.repr (bk a : L) i) ≤ q :=
    fun a i => (rationalLogHeight_le_iff _ _).mpr (hbk a i)
  let U := (D.filtration.layerIdeal s).toLieSubalgebra
  let V := φ.ker.toLieSubalgebra
  obtain ⟨bP, hbP⟩ := exists_binary_intersection_basis_logHeight
    D.basis U V btop bk hq
    (by simpa only [Fintype.card_fin] using hD.1.trans hpq) htop hk
  let B : ℝ := ((q + 4) ^ 2 + 2) ^ 63 + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hspan := exists_bounded_ambient_spanning D.basis (U ⊓ V) bP bP.span_eq
    (one_le_ceil_exp B) (fun a i => rationalHeightLE_ceil_exp (hbP a i))
  obtain ⟨vP, hvP, hvPh⟩ := hspan
  let indexEquiv : Fin d ≃ Fin (Fintype.card (Fin d)) := finCongr (Fintype.card_fin d).symm
  refine ⟨fun i => vP (indexEquiv i), ?_, ?_⟩
  · have hrange : Set.range (fun i => vP (indexEquiv i)) = Set.range vP := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨indexEquiv i, rfl⟩
      · rintro ⟨i, rfl⟩
        obtain ⟨j, rfl⟩ := indexEquiv.surjective i
        exact ⟨j, rfl⟩
    rw [hrange]
    exact hvP
  intro a i
  have hheight : rationalLogHeight (D.basis.repr (vP (indexEquiv a)) i) ≤ B + 1 :=
    rationalLogHeight_le_of_height (hvPh (indexEquiv a) i) (ceil_exp_le_exp_add_one hB)
  apply hheight.trans
  simpa [P, q, B, Polynomial.eval₂_pow, add_assoc,
    show (2 : ℝ) + 1 = 3 by norm_num] using hbudget p hp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_marked_kernel_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ L M : Type*} [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d)
      (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup,
          g ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
            φ.ker.toLieSubalgebra →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          ∃ r : D.RealGroup,
            r ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
              φ.ker.toLieSubalgebra ∧
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ := by
  obtain ⟨a, _, hrep⟩ := exists_native_bounded_subalgebra_representatives s
  let P : Polynomial ℕ := ((Polynomial.X + 3) ^ 7 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro κ L M _ _ _ _ _ _ _ _ _ d D c φ p hp hD hκ hφ q hq hqp
  obtain ⟨n, hn, bk, hbk⟩ :=
    exists_lie_kernel_subalgebra_basis_logHeight D.basis c φ hp hκ hφ
  let t := (p + 3) ^ 7
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    exact (le_power_budget hp (by decide : 1 ≤ 7)).trans
      (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2) (by linarith : p + 2 ≤ p + 3) 7)
  have hn' : (Fintype.card (Fin n) : ℝ) ≤ t := by
    have hnd : n ≤ d := by simpa only [Fintype.card_fin] using hn
    simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hnd).trans (hD.1.trans hpt)
  have hinc : ∀ i j, rationalLogHeight (D.basis.repr (bk j : L) i) ≤ t :=
    fun i j => (rationalLogHeight_le_iff _ t).mpr (hbk j i)
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D φ.ker.toLieSubalgebra bk t ht
    (GeometryComplexityLE.mono D hD hpt)
    hn' hinc q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  have hb : (t + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hb), ?_⟩
  intro g hgK hg
  obtain ⟨r, hrK, hr, hrgrid, γ, hγ, hfac⟩ := hreps g hgK hg
  exact ⟨r, hrK, fun i => (hr i).trans (Real.exp_le_exp.mpr hb), hrgrid, γ, hγ, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
