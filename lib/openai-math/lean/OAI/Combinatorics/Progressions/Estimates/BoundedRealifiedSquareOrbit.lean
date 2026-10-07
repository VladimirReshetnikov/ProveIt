import OAI.Combinatorics.Progressions.Geometry.RealifiedSquareCoordinates

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareLayerConstraint (j : ℕ) : F.squareLieSubalgebra →ₗ[ℚ]
    ((L ⧸ F.layer j) × (L ⧸ F.layer (j + 1))) :=
  ((F.layer j).mkQ.comp F.squareSnd.toLinearMap).prod
    ((F.layer (j + 1)).mkQ.comp (F.squareFst.toLinearMap - F.squareSnd.toLinearMap))

theorem squareLayer_eq_ker_constraint (j : ℕ) :
    F.squareFiltration.layer j = LinearMap.ker (F.squareLayerConstraint j) := by
  ext x
  rw [F.mem_squareFiltration_layer, F.mem_squareLayer_iff_second_and_difference]
  change (x.val.2 ∈ F.layer j ∧ x.val.1 - x.val.2 ∈ F.layer (j + 1)) ↔
    ((F.layer j).mkQ x.val.2, (F.layer (j + 1)).mkQ (x.val.1 - x.val.2)) = 0
  simp only [Prod.mk_eq_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem realifiedSquareEquiv_mem_layer (j : ℕ) (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    x ∈ F.squareFiltration.realification.layer j ↔
      F.realifiedSquareEquiv x ∈ F.realification.squareFiltration.layer j := by
  change x ∈ (F.squareFiltration.layer j).baseChange ℝ ↔ _
  rw [F.squareLayer_eq_ker_constraint, realification_ker, LinearMap.mem_ker,
    F.realification.mem_squareFiltration_layer,
    F.realification.mem_squareLayer_iff_second_and_difference]
  change (F.squareLayerConstraint j).baseChange ℝ x = 0 ↔
    F.realification.squareSnd (F.realifiedSquareEquiv x) ∈ F.realification.layer j ∧
      F.realification.squareFst (F.realifiedSquareEquiv x) -
        F.realification.squareSnd (F.realifiedSquareEquiv x) ∈ F.realification.layer (j + 1)
  rw [F.realifiedSquareEquiv_snd, F.realifiedSquareEquiv_fst]
  simp only [squareLayerConstraint, realification_prod_eq_zero_iff,
    LinearMap.baseChange_comp, LinearMap.comp_apply, realification_mkQ_eq_zero_iff,
    LinearMap.baseChange_sub, LinearMap.sub_apply]
  rfl

theorem realifiedSquareEquiv_symm_mem_layer (j : ℕ) (x : F.realification.squareLieSubalgebra) :
    F.realifiedSquareEquiv.symm x ∈ F.squareFiltration.realification.layer j ↔
      x ∈ F.realification.squareFiltration.layer j := by
  rw [F.realifiedSquareEquiv_mem_layer, LinearEquiv.apply_symm_apply]

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realifiedSquareGroupEquiv :
    F.squareFiltration.realification.Group ≃* F.realification.squareFiltration.Group where
  toFun g := ⟨F.realifiedSquareEquiv g.coord⟩
  invFun g := ⟨F.realifiedSquareEquiv.symm g.coord⟩
  left_inv g := NilpotentLieBCHGroup.ext (F.realifiedSquareEquiv.symm_apply_apply g.coord)
  right_inv g := NilpotentLieBCHGroup.ext (F.realifiedSquareEquiv.apply_symm_apply g.coord)
  map_mul' g h := NilpotentLieBCHGroup.ext
    (map_lieBCH_of_nilpotent_steps F.realifiedSquareLieEquiv.toLieHom
      F.squareFiltration.realification.lowerCentralSeries_eq_bot
      F.realification.squareFiltration.lowerCentralSeries_eq_bot g.coord h.coord)

noncomputable def realSquareFstHom : F.squareFiltration.realification.Group →* F.realification.Group :=
  realificationMap (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
    (hM := F.lowerCentralSeries_eq_bot) F.squareFst

noncomputable def realSquareSndHom : F.squareFiltration.realification.Group →* F.realification.Group :=
  realificationMap (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
    (hM := F.lowerCentralSeries_eq_bot) F.squareSnd

theorem realifiedSquareGroupEquiv_fst (g : F.squareFiltration.realification.Group) :
    F.realification.squareFstHom (F.realifiedSquareGroupEquiv g) = F.realSquareFstHom g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realifiedSquareEquiv_fst g.coord

theorem realifiedSquareGroupEquiv_snd (g : F.squareFiltration.realification.Group) :
    F.realification.squareSndHom (F.realifiedSquareGroupEquiv g) = F.realSquareSndHom g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realifiedSquareEquiv_snd g.coord

noncomputable def realifiedSquareOrbit {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) :
    F.squareFiltration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap q.log)
    (F.realification.squareFiltration.adapted_map F.squareFiltration.realification
      F.realifiedSquareEquiv.symm.toLinearMap
      (fun j x hx => (F.realifiedSquareEquiv_symm_mem_layer j x).mpr hx) w q.adapted)

theorem realifiedSquareOrbit_eval {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) (x : σ → ℤ) :
    F.realifiedSquareGroupEquiv
      (F.squareFiltration.realification.polynomialOrbitEval w x (F.realifiedSquareOrbit q)) =
        F.realification.squareFiltration.polynomialOrbitEval w x q := by
  apply NilpotentLieBCHGroup.ext
  change F.realifiedSquareEquiv (eval (fun i => (x i : ℚ))
    (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap q.log)) = _
  rw [eval_map]
  exact F.realifiedSquareEquiv.apply_symm_apply _

theorem realifiedSquareOrbit_fst {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) (x : σ → ℤ) :
    F.realSquareFstHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.realifiedSquareOrbit q)) =
        F.realification.squareFstHom (F.realification.squareFiltration.polynomialOrbitEval w x q) := by
  rw [← F.realifiedSquareGroupEquiv_fst, F.realifiedSquareOrbit_eval]

theorem realifiedSquareOrbit_snd {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) (x : σ → ℤ) :
    F.realSquareSndHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.realifiedSquareOrbit q)) =
        F.realification.squareSndHom (F.realification.squareFiltration.polynomialOrbitEval w x q) := by
  rw [← F.realifiedSquareGroupEquiv_snd, F.realifiedSquareOrbit_eval]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem realSquareLattice_le_fst :
    (F.squareLattice Γ).map realificationHom ≤
      (Γ.map realificationHom).comap F.realSquareFstHom := by
  apply realificationMap_subgroup F.squareFst
  exact F.squareLattice_le_fst Γ

theorem realSquareLattice_le_snd :
    (F.squareLattice Γ).map realificationHom ≤
      (Γ.map realificationHom).comap F.realSquareSndHom := by
  apply realificationMap_subgroup F.squareSnd
  exact F.squareLattice_le_snd Γ

noncomputable def realSquareObservable (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) : ℂ :=
  u (ε • cosetMap _ _ F.realSquareFstHom (F.realSquareLattice_le_fst Γ) x) *
    star (u (cosetMap _ _ F.realSquareSndHom (F.realSquareLattice_le_snd Γ) x))

theorem realSquareObservable_mk (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (g : F.squareFiltration.realification.Group) :
    F.realSquareObservable Γ ε u (QuotientGroup.mk g) =
      F.realification.squareObservable (Γ.map realificationHom) ε u
        (QuotientGroup.mk (F.realifiedSquareGroupEquiv g)) := by
  rw [F.realification.squareObservable_mk, F.realifiedSquareGroupEquiv_fst,
    F.realifiedSquareGroupEquiv_snd]
  rfl

theorem realSquareObservable_norm_le (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ x, ‖u x‖ ≤ B)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) :
    ‖F.realSquareObservable Γ ε u x‖ ≤ B ^ 2 := by
  rw [realSquareObservable, norm_mul, norm_star, pow_two]
  exact mul_le_mul (hu _) (hu _) (norm_nonneg _) hB

theorem realSquareObservable_top_invariant (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup s, ∀ x, u (z • x) = character (χ z) * u x)
    (k : F.squareFiltration.realification.Group) (hk : k ∈ F.squareFiltration.realification.subgroup s)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) :
    F.realSquareObservable Γ ε u (k • x) = F.realSquareObservable Γ ε u x := by
  induction x using Quotient.inductionOn with
  | h g =>
    change F.realSquareObservable Γ ε u (QuotientGroup.mk (k * g)) = _
    rw [F.realSquareObservable_mk, F.realSquareObservable_mk, map_mul]
    exact F.realification.squareObservable_top_invariant _ ε u χ hu
      (F.realifiedSquareGroupEquiv k) ((F.realifiedSquareEquiv_mem_layer s k.coord).mp hk)
      (QuotientGroup.mk (F.realifiedSquareGroupEquiv g))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)

theorem exists_realSquare_observable_descent (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x) :
    let I := F.squareFiltration.layerIdeal (s + 1)
    let π := F.squareFiltration.realQuotientStepHom I (t := s) le_rfl
    let Λ := ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom I (t := s) le_rfl)).map
      realificationHom
    ∃! v : F.squareFiltration.quotientTop.realification.Group ⧸ Λ → ℂ,
      ∀ g : F.squareFiltration.realification.Group,
        v (QuotientGroup.mk (π g)) = F.realSquareObservable Γ ε u (QuotientGroup.mk g) := by
  dsimp only
  apply exists_unique_observable_reconstruction _
    (F.squareFiltration.realQuotientStepHom_surjective _ le_rfl)
    ((F.squareLattice Γ).map realificationHom) _
    (F.squareFiltration.realQuotientStepHom_lattice _ le_rfl (F.squareLattice Γ)).le
    (F.realSquareObservable Γ ε u)
  intro k hk x
  exact F.realSquareObservable_top_invariant Γ ε u χ hu k
    ((F.squareFiltration.mem_realQuotientStepHom_ker _ le_rfl k).mp hk)
    (QuotientGroup.mk x)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [TopologicalSpace (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]

theorem exists_lipschitz_realSquare_descent
    (b : Basis ι ℚ F.squareLieSubalgebra)
    (c : Basis κ ℚ (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hin : bchSubgroupCoordinates b (F.squareLattice Γ) ⊆ denominatorGrid l)
    (hout : bchSubgroupCoordinates c ((F.squareLattice Γ).map
      (F.squareFiltration.quotientStepHom (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)) ⊆
        denominatorGrid m)
    (he : ∀ i j, RationalHeightLE
      (c.repr (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) (b j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants c i j k) H)
    (ε : F.realification.Group) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x)
    (A B : ℝ≥0)
    (hLip : letI := realificationQuotientMetricSpace b (F.squareLattice Γ) l hl hin
      LipschitzWith A (F.realSquareObservable Γ ε u))
    (hb : ∀ x, ‖u x‖ ≤ B) :
    let I := F.squareFiltration.layerIdeal (s + 1)
    let Δ := (F.squareLattice Γ).map (F.squareFiltration.quotientStepHom I (t := s) le_rfl)
    letI := realificationQuotientMetricSpace c Δ m hm hout
    ∃ v : F.squareFiltration.quotientTop.realification.Group ⧸ Δ.map realificationHom → ℂ,
      (∀ g, v (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom I (t := s) le_rfl g)) =
        F.realSquareObservable Γ ε u (QuotientGroup.mk g)) ∧
      LipschitzWith (rationalReconstructionLipschitzBound s (Fintype.card ι) (Fintype.card κ) H A (B ^ 2)) v ∧
      ∀ x, ‖v x‖ ≤ (B : ℝ) ^ 2 := by
  dsimp only
  refine exists_lipschitz_realification_reconstruction b c
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))) (lieQuotientMap_surjective _)
    (F.squareLattice Γ) _ le_rfl l m H hl hm hH hin hout he hc
    (F.realSquareObservable Γ ε u) ?_ A (B ^ 2) hLip ?_
  · intro k hk x
    exact F.realSquareObservable_top_invariant Γ ε u χ hu k
      ((F.squareFiltration.mem_realQuotientStepHom_ker _ le_rfl k).mp hk)
      (QuotientGroup.mk x)
  · simpa only [NNReal.coe_pow] using F.realSquareObservable_norm_le Γ ε u B.coe_nonneg hb

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_normalized_square_orbit (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℤ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ q : D.filtration.realification.squareFiltration.PolynomialOrbit w,
          ∀ x : σ → ℤ,
            D.filtration.realification.squareFstHom
              (D.filtration.realification.squareFiltration.polynomialOrbitEval w x q) =
                ε⁻¹ * D.filtration.realification.polynomialOrbitEval w (fun i => x i + h i) f * γ⁻¹ ∧
            D.filtration.realification.squareSndHom
              (D.filtration.realification.squareFiltration.polynomialOrbitEval w x q) =
                D.filtration.realification.polynomialOrbitEval w x f := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_normalized_square s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  obtain ⟨ε, γ, hγ, hε, r, hr, hfst, hsnd⟩ :=
    hnorm D p hp hD w hw (fun i => (h i : ℚ)) f
  let q := NilpotentLieFiltration.polynomialOrbitOfLog r hr
  refine ⟨ε, γ, hγ, hε, q, ?_⟩
  intro x
  constructor
  · rw [mul_assoc]
    apply NilpotentLieBCHGroup.ext
    have hh := congrArg (eval (fun i => (x i : ℚ))) hfst
    rw [eval_map, eval_normalizedShiftLog] at hh
    change (eval (fun i => (x i : ℚ)) r).val.1 = _ at hh
    change (eval (fun i => (x i : ℚ)) r).val.1 =
      lieBCH s (-ε.coord) (lieBCH s (eval (fun i => ((x i + h i : ℤ) : ℚ)) f.log) (-γ.coord))
    simpa only [Int.cast_add] using hh
  · apply NilpotentLieBCHGroup.ext
    have hh := congrArg (eval (fun i => (x i : ℚ))) hsnd
    rw [eval_map] at hh
    exact hh

end Erdos3

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem squareObservable_recovers_product (ε γ a b : F.Group) (hγ : γ ∈ Γ)
    (u : F.Group ⧸ Γ → ℂ) (q : F.squareFiltration.Group)
    (hfst : F.squareFstHom q = ε⁻¹ * a * γ⁻¹) (hsnd : F.squareSndHom q = b) :
    F.squareObservable Γ ε u (QuotientGroup.mk q) =
      u (QuotientGroup.mk a) * star (u (QuotientGroup.mk b)) := by
  rw [F.squareObservable_mk, hfst, hsnd]
  have heq : (QuotientGroup.mk (ε * (ε⁻¹ * a * γ⁻¹)) : F.Group ⧸ Γ) = QuotientGroup.mk a := by
    apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, inv_inv, inv_mul_cancel_left, mul_inv_cancel_left,
      mul_assoc, inv_mul_cancel, mul_one] using hγ
  rw [heq]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_bounded_realified_square_orbit (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℤ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ q : D.filtration.squareFiltration.realification.PolynomialOrbit w,
          ∀ x : σ → ℤ,
            D.filtration.realSquareFstHom
              (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) =
                ε⁻¹ * D.filtration.realification.polynomialOrbitEval w (fun i => x i + h i) f * γ⁻¹ ∧
            D.filtration.realSquareSndHom
              (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) =
                D.filtration.realification.polynomialOrbitEval w x f := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_normalized_square_orbit s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hD w hw h f
  refine ⟨ε, γ, hγ, hε, D.filtration.realifiedSquareOrbit q, ?_⟩
  intro x
  rw [D.filtration.realifiedSquareOrbit_fst, D.filtration.realifiedSquareOrbit_snd]
  exact hq x

end Erdos3

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem realSquareObservable_recovers_product (ε γ a b : F.realification.Group)
    (hγ : γ ∈ Γ.map realificationHom)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (q : F.squareFiltration.realification.Group)
    (hfst : F.realSquareFstHom q = ε⁻¹ * a * γ⁻¹) (hsnd : F.realSquareSndHom q = b) :
    F.realSquareObservable Γ ε u (QuotientGroup.mk q) =
      u (QuotientGroup.mk a) * star (u (QuotientGroup.mk b)) := by
  rw [F.realSquareObservable_mk]
  exact F.realification.squareObservable_recovers_product (Γ.map realificationHom)
    ε γ a b hγ u (F.realifiedSquareGroupEquiv q)
    ((F.realifiedSquareGroupEquiv_fst q).trans hfst)
    ((F.realifiedSquareGroupEquiv_snd q).trans hsnd)

end Erdos3.NilpotentLieFiltration

end

end OAI
