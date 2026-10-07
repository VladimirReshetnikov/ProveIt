/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Geometry.RationalModelCoordinates
import OAI.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)
  (h : D.rationalModelCoordinates = E.rationalModelCoordinates)

noncomputable def rationalModelEquiv : L ≃ₗ⁅ℚ⁆ M :=
  { D.basis.repr.trans E.basis.repr.symm with
    map_lie' {x y} := by
      apply E.basis.repr.injective
      ext k
      change E.basis.repr (E.basis.repr.symm (D.basis.repr ⁅x, y⁆)) k = _
      rw [LinearEquiv.apply_symm_apply, lie_coordinate_formula, lie_coordinate_formula]
      apply Finset.sum_congr rfl
      intro ij _
      have hc : lieStructureConstants D.basis ij.1 ij.2 k =
          lieStructureConstants E.basis ij.1 ij.2 k := congrFun h (.inl (ij.1, ij.2, k))
      change lieStructureConstants D.basis ij.1 ij.2 k * D.basis.repr x ij.1 * D.basis.repr y ij.2 =
        lieStructureConstants E.basis ij.1 ij.2 k *
          E.basis.repr (E.basis.repr.symm (D.basis.repr x)) ij.1 *
          E.basis.repr (E.basis.repr.symm (D.basis.repr y)) ij.2
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hc] }

theorem rationalModelEquiv_repr (x : L) :
    E.basis.repr (D.rationalModelEquiv E h x) = D.basis.repr x :=
  E.basis.repr.apply_symm_apply _

theorem rationalModelEquiv_basis (i : Fin d) :
    D.rationalModelEquiv E h (D.basis i) = E.basis i := by
  apply E.basis.repr.injective
  rw [rationalModelEquiv_repr]
  simp only [Basis.repr_self]

theorem rationalModelEquiv_paddedLayerVector (i : Fin (s + 1)) (k : Fin d) :
    D.rationalModelEquiv E h (D.paddedLayerVector i k) = E.paddedLayerVector i k := by
  apply E.basis.repr.injective
  rw [rationalModelEquiv_repr]
  ext j
  exact congrFun h (.inr (i, k, j))

theorem rationalModelEquiv_layer_succ (i : Fin (s + 1)) :
    (D.filtration.layer (i.val + 1)).map (D.rationalModelEquiv E h).toLinearEquiv.toLinearMap =
      E.filtration.layer (i.val + 1) := by
  rw [← D.paddedLayerVector_span i, ← E.paddedLayerVector_span i,
    Submodule.map_span, ← Set.range_comp]
  congr 2
  funext k
  exact D.rationalModelEquiv_paddedLayerVector E h i k

theorem rationalModelEquiv_layer (n : ℕ) :
    (D.filtration.layer n).map (D.rationalModelEquiv E h).toLinearEquiv.toLinearMap =
      E.filtration.layer n := by
  by_cases hn : n = 0
  · subst n
    have hD : D.filtration.layer 0 = ⊤ :=
      top_unique (D.filtration.one_eq_top ▸ D.filtration.antitone (by omega : 0 ≤ 1))
    have hE : E.filtration.layer 0 = ⊤ :=
      top_unique (E.filtration.one_eq_top ▸ E.filtration.antitone (by omega : 0 ≤ 1))
    rw [hD, hE]
    rw [Submodule.map_top]
    apply LinearMap.range_eq_top.mpr
    exact (D.rationalModelEquiv E h).surjective
  · by_cases hns : n ≤ s + 1
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        D.rationalModelEquiv_layer_succ E h ⟨n - 1, by omega⟩
    · have hD : D.filtration.layer n = ⊥ :=
        bot_unique ((D.filtration.antitone (by omega : s + 1 ≤ n)).trans D.filtration.terminal.le)
      have hE : E.filtration.layer n = ⊥ :=
        bot_unique ((E.filtration.antitone (by omega : s + 1 ≤ n)).trans E.filtration.terminal.le)
      rw [hD, hE, Submodule.map_bot]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)
  (h : D.rationalModelCoordinates = E.rationalModelCoordinates)

noncomputable def rationalModelGroupEquiv : D.filtration.Group ≃* E.filtration.Group :=
  { NilpotentLieBCHGroup.map (D.rationalModelEquiv E h).toLieHom with
    invFun := fun g => ⟨(D.rationalModelEquiv E h).symm g.coord⟩
    left_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact (D.rationalModelEquiv E h).symm_apply_apply g.coord
    right_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact (D.rationalModelEquiv E h).apply_symm_apply g.coord }

theorem rationalModelGroupEquiv_coordinates (g : D.filtration.Group) :
    E.basis.equivFun (D.rationalModelGroupEquiv E h g).coord = D.basis.equivFun g.coord := by
  funext k
  exact congrArg (fun v => v k) (D.rationalModelEquiv_repr E h g.coord)

theorem rationalModelGroupEquiv_mem_layer (n : ℕ) (g : D.filtration.Group) :
    D.rationalModelGroupEquiv E h g ∈ E.filtration.subgroup n ↔ g ∈ D.filtration.subgroup n := by
  change D.rationalModelEquiv E h g.coord ∈ E.filtration.layer n ↔ g.coord ∈ D.filtration.layer n
  rw [← D.rationalModelEquiv_layer E h n]
  constructor
  · rintro ⟨x, hx, heq⟩
    have hxg : x = g.coord := (D.rationalModelEquiv E h).injective heq
    change x ∈ D.filtration.layer n at hx
    exact hxg ▸ hx
  · intro hx
    exact ⟨g.coord, hx, rfl⟩

theorem rationalModelGroupEquiv_mem_integral_lattice
    (Λ : Subgroup D.filtration.Group) (Γ : Subgroup E.filtration.Group) (B : ℕ)
    (hΛ : bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B)
    (hΓ : bchSubgroupCoordinates E.basis Γ = scaledIntegerGrid B) (g : D.filtration.Group) :
    D.rationalModelGroupEquiv E h g ∈ Γ ↔ g ∈ Λ := by
  rw [← bchSubgroupCoordinates_repr E.basis Γ (D.rationalModelGroupEquiv E h g),
    ← bchSubgroupCoordinates_repr D.basis Λ g, hΛ, hΓ,
    rationalModelGroupEquiv_coordinates]

theorem rationalModelGroupEquiv_map_integral_lattice
    (Λ : Subgroup D.filtration.Group) (Γ : Subgroup E.filtration.Group) (B : ℕ)
    (hΛ : bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B)
    (hΓ : bchSubgroupCoordinates E.basis Γ = scaledIntegerGrid B) :
    Λ.map (D.rationalModelGroupEquiv E h).toMonoidHom = Γ := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (D.rationalModelGroupEquiv_mem_integral_lattice E h Λ Γ B hΛ hΓ x).mpr hx
  · intro hg
    refine ⟨(D.rationalModelGroupEquiv E h).symm g, ?_,
      (D.rationalModelGroupEquiv E h).apply_symm_apply g⟩
    apply (D.rationalModelGroupEquiv_mem_integral_lattice E h Λ Γ B hΛ hΓ _).mp
    simpa only [MulEquiv.apply_symm_apply] using hg

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)

structure NativeModelEquiv where
  toLieEquiv : L ≃ₗ⁅ℚ⁆ M
  map_basis : ∀ i, toLieEquiv (D.basis i) = E.basis i
  mem_layer : ∀ n x, toLieEquiv x ∈ E.filtration.layer n ↔ x ∈ D.filtration.layer n
  mem_lattice : ∀ g : D.filtration.Group,
    NilpotentLieBCHGroup.map toLieEquiv.toLieHom g ∈ E.lattice ↔ g ∈ D.lattice

namespace NativeModelEquiv

variable {D E} (e : NativeModelEquiv D E)

noncomputable def symm : NativeModelEquiv E D where
  toLieEquiv := e.toLieEquiv.symm
  map_basis i := by
    apply e.toLieEquiv.injective
    change e.toLieEquiv (e.toLieEquiv.symm (E.basis i)) = e.toLieEquiv (D.basis i)
    rw [LieEquiv.apply_symm_apply, e.map_basis]
  mem_layer n x := by
    have h := e.mem_layer n (e.toLieEquiv.symm x)
    rw [LieEquiv.apply_symm_apply] at h
    exact h.symm
  mem_lattice g := by
    have h := e.mem_lattice (⟨e.toLieEquiv.symm g.coord⟩ : D.filtration.Group)
    have heq : NilpotentLieBCHGroup.map (hM := E.filtration.lowerCentralSeries_eq_bot)
        e.toLieEquiv.toLieHom (⟨e.toLieEquiv.symm g.coord⟩ : D.filtration.Group) = g := by
      apply NilpotentLieBCHGroup.ext
      exact e.toLieEquiv.apply_symm_apply g.coord
    rw [heq] at h
    exact h.symm

end NativeModelEquiv

noncomputable def nativeModelEquivOfCoordinates
    (h : D.rationalModelCoordinates = E.rationalModelCoordinates) (B : ℕ)
    (hD : bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B)
    (hE : bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid B) : NativeModelEquiv D E where
  toLieEquiv := D.rationalModelEquiv E h
  map_basis := D.rationalModelEquiv_basis E h
  mem_layer n x := D.rationalModelGroupEquiv_mem_layer E h n ⟨x⟩
  mem_lattice := D.rationalModelGroupEquiv_mem_integral_lattice E h D.lattice E.lattice B hD hE

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3

open scoped TensorProduct

theorem realificationLieEquiv_inverse
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (e : L ≃ₗ⁅ℚ⁆ M) (x : ℝ ⊗[ℚ] L) :
    realificationLieHom e.symm.toLieHom (realificationLieHom e.toLieHom x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    change a ⊗ₜ[ℚ] e.symm (e x) = a ⊗ₜ[ℚ] x
    rw [LieEquiv.symm_apply_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M s d}
  (e : NativeModelEquiv D E)

noncomputable def realGroupEquiv : D.RealGroup ≃* E.RealGroup :=
  { realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) e.toLieEquiv.toLieHom with
    invFun := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) e.toLieEquiv.symm.toLieHom
    left_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact realificationLieEquiv_inverse e.toLieEquiv g.coord
    right_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact realificationLieEquiv_inverse e.toLieEquiv.symm g.coord }

theorem symm_realGroupEquiv_apply (g : D.RealGroup) :
    e.symm.realGroupEquiv (e.realGroupEquiv g) = g :=
  e.realGroupEquiv.symm_apply_apply g

theorem map_real_layer (n : ℕ) (g : D.RealGroup)
    (hg : g ∈ D.filtration.realification.subgroup n) :
    e.realGroupEquiv g ∈ E.filtration.realification.subgroup n :=
  D.filtration.realificationLieHom_mem_layer E.filtration e.toLieEquiv.toLieHom
    (fun j x hx => (e.mem_layer j x).mpr hx) n g.coord hg

theorem real_lattice_le : D.realLattice ≤ E.realLattice.comap e.realGroupEquiv.toMonoidHom := by
  apply realificationMap_subgroup e.toLieEquiv.toLieHom D.lattice E.lattice
  intro g hg
  exact (e.mem_lattice g).mpr hg

noncomputable def spaceMap : D.Space → E.Space :=
  cosetMap D.realLattice E.realLattice e.realGroupEquiv.toMonoidHom e.real_lattice_le

theorem spaceMap_mk (g : D.RealGroup) :
    e.spaceMap (QuotientGroup.mk g) = QuotientGroup.mk (e.realGroupEquiv g) := rfl

theorem spaceMap_smul (g : D.RealGroup) (x : D.Space) :
    e.spaceMap (g • x) = e.realGroupEquiv g • e.spaceMap x :=
  cosetMap_smul D.realLattice E.realLattice e.realGroupEquiv.toMonoidHom e.real_lattice_le g x

theorem symm_spaceMap_apply (x : D.Space) : e.symm.spaceMap (e.spaceMap x) = x := by
  induction x using Quotient.inductionOn with
  | _ g =>
    rw [e.spaceMap_mk, e.symm.spaceMap_mk, e.symm_realGroupEquiv_apply]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

theorem spaceMap_lipschitz :
    letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith (coordinateLipschitzBound d d 1) e.spaceMap := by
  have hmatrix : ∀ k i, RationalHeightLE (E.basis.repr (e.toLieEquiv (D.basis i)) k) 1 := by
    intro k i
    rw [e.map_basis]
    simp only [Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> norm_num [RationalHeightLE]
  have hh :=
    lipschitz_realificationMap_quotient D.basis E.basis e.toLieEquiv.toLieHom
      D.lattice E.lattice (fun g hg => (e.mem_lattice g).mpr hg)
      D.grid E.grid D.grid_pos E.grid_pos D.outer_grid E.outer_grid 1 hmatrix
  simp only [Fintype.card_fin, Nat.cast_one] at hh
  convert hh using 1
  rfl

end Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

end

section

namespace Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

open NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M s d}
  (e : NativeModelEquiv D E) {w : σ → ℕ}

noncomputable def mapOrbit (g : D.filtration.realification.PolynomialOrbit w) :
    E.filtration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (VectorPolynomial.map ((realificationLieHom e.toLieEquiv.toLieHom).toLinearMap.restrictScalars ℚ) g.log)
    (D.filtration.realification.adapted_map E.filtration.realification
      ((realificationLieHom e.toLieEquiv.toLieHom).toLinearMap.restrictScalars ℚ)
      (D.filtration.realificationLieHom_mem_layer E.filtration e.toLieEquiv.toLieHom
        (fun n x hx => (e.mem_layer n x).mpr hx)) w g.adapted)

theorem mapOrbit_log (g : D.filtration.realification.PolynomialOrbit w) :
    (e.mapOrbit g).log =
      VectorPolynomial.map ((realificationLieHom e.toLieEquiv.toLieHom).toLinearMap.restrictScalars ℚ) g.log := rfl

theorem mapOrbit_eval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    E.filtration.realification.polynomialOrbitEval w x (e.mapOrbit g) =
      e.realGroupEquiv (D.filtration.realification.polynomialOrbitEval w x g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval_map (fun i => (x i : ℚ))
    ((realificationLieHom e.toLieEquiv.toLieHom).toLinearMap.restrictScalars ℚ) g.log

theorem mapOrbit_realEval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℝ) :
    E.filtration.realification.polynomialOrbitRealEval w x (e.mapOrbit g) =
      e.realGroupEquiv (D.filtration.realification.polynomialOrbitRealEval w x g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (realificationLieHom e.toLieEquiv.toLieHom).toLinearMap x g.log

end Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

end

end OAI
