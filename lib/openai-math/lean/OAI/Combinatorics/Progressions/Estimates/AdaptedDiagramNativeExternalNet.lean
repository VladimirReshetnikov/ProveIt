import OAI.Combinatorics.Progressions.Estimates.AntisymmetricPartitionApproximation
import OAI.Combinatorics.Progressions.Estimates.DiagramNativeExternalNetMonotone
import OAI.Combinatorics.Progressions.Linear.RefiltrationLayerBasis

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def nativeRefiltrationLayerEquiv (j : ℕ) (hj : 1 ≤ j) :
    (F.gradedRefiltration W).layer j ≃ₗ[ℚ] F.gradedRefiltrationLayer W j :=
  Submodule.comapSubtypeEquivOfLe (F.gradedRefiltrationLayer_antitone W hj)

theorem exists_native_refiltration_layer_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : Basis ι ℚ L) (b : Basis κ ℚ (F.gradedRefiltrationSubalgebra W))
    (j : ℕ) (hj : 1 ≤ j)
    (a : Basis (Fin (finrank ℚ (F.gradedRefiltrationLayer W j))) ℚ (F.gradedRefiltrationLayer W j))
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i k, RationalHeightLE (e.repr (b i : L) k) H)
    (ha : ∀ i k, RationalHeightLE (e.repr (a i : L) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ a' : Basis (Fin (finrank ℚ ((F.gradedRefiltration W).layer j))) ℚ
        ((F.gradedRefiltration W).layer j),
      ∀ i k, rationalLogHeight (b.repr (a' i : F.gradedRefiltrationSubalgebra W) k) ≤ (p + 2) ^ 8 := by
  let E := F.nativeRefiltrationLayerEquiv W j hj
  let a' := (a.map E.symm).reindex (finCongr E.finrank_eq.symm)
  have hval (i) : ((a' i : F.gradedRefiltrationSubalgebra W) : L) =
      (a ((finCongr E.finrank_eq.symm).symm i) : L) := by
    simp only [a', Basis.reindex_apply, Basis.map_apply, E, nativeRefiltrationLayerEquiv]
    rfl
  refine ⟨a', fun i k => ?_⟩
  apply rationalLogHeight_le_of_height
    (embedding_basis_coordinate_height b e (F.gradedRefiltrationSubalgebra W).incl.toLinearMap
      (fun _ _ h => Subtype.ext h) hH (fun k i => hb i k)
      (a' i : F.gradedRefiltrationSubalgebra W) (K := H) (fun k => by
        change RationalHeightLE (e.repr ((a' i : F.gradedRefiltrationSubalgebra W) : L) k) H
        rw [hval]
        exact ha _ k) k)
  exact embedding_coordinate_height_budget _ _ H H hp hι hκ hHp hHp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_native_refiltration_model_of_bases {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (b : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W))) ℚ
      (D.filtration.gradedRefiltrationSubalgebra W))
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i k, RationalHeightLE (D.basis.repr (b i : L) k) H)
    (hlayers : ∀ j, 1 ≤ j →
      ∃ a : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W j))) ℚ
        (D.filtration.gradedRefiltrationLayer W j),
        ∀ i k, RationalHeightLE (D.basis.repr (a i : L) k) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hgrid : (D.grid : ℝ) ≤ Real.exp p) :
    ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) s
        (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
      E.filtration = D.filtration.gradedRefiltration W ∧ E.basis = b ∧
      E.lattice = D.lattice.comap
        (NilpotentLieBCHGroup.map
          (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
      E.GeometryComplexityLE ((p + 2) ^ 11) := by
  classical
  let K := D.filtration.gradedRefiltrationSubalgebra W
  let F := D.filtration.gradedRefiltration W
  have hr : (finrank ℚ K : ℝ) ≤ p :=
    (Nat.cast_le.mpr (lie_subalgebra_finrank_le D.basis K)).trans (by simpa only [Fintype.card_fin] using hd)
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hd
  have hr' : (Fintype.card (Fin (finrank ℚ K)) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hr
  have hmatrix : ∀ i j, RationalHeightLE (LinearMap.toMatrix b D.basis K.incl.toLinearMap i j) H := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    change RationalHeightLE (D.basis.repr (b j : L) i) H
    exact hb j i
  obtain ⟨N, hN, hNb, hin, hout⟩ := exists_bchSubgroup_comap_grid_exp_bound
    (hM := F.lowerCentralSeries_eq_bot) b D.basis K.incl
    (fun _ _ h => Subtype.ext h) D.lattice hH D.grid_pos hmatrix D.inner_grid D.outer_grid
    hp hd' hr' hHp hgrid
  obtain ⟨_, _, _, hbracket⟩ := exists_bounded_lie_embedding_retraction b D.basis K.incl
    (fun _ _ h => Subtype.ext h) hH hc hmatrix
  have hbracketBudget := rationalLieStructureHeight_inverse_budget d (finrank ℚ K) H hp hd hr hHp
  have hLayer : ∀ i : Fin (s + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (i.val + 1)))) ℚ (F.layer (i.val + 1)),
        ∀ j k, rationalLogHeight (b.repr (a j : K) k) ≤ (p + 2) ^ 8 := by
    intro i
    obtain ⟨a, ha⟩ := hlayers (i.val + 1) (Nat.le_add_left 1 _)
    exact D.filtration.exists_native_refiltration_layer_basis W D.basis b (i.val + 1)
      (Nat.le_add_left 1 _) a hH hb ha hp hd' hr' hHp
  choose a ha using hLayer
  let E : RationalFilteredNilmanifold K s (finrank ℚ K) :=
    { filtration := F
      basis := b
      layerBasis := a
      lattice := D.lattice.comap (NilpotentLieBCHGroup.map (hnil := F.lowerCentralSeries_eq_bot) K.incl)
      grid := N
      grid_pos := hN
      inner_grid := hin
      outer_grid := hout }
  have hp1 : 1 ≤ p + 2 := by linarith
  have h9 : (p + 2) ^ 9 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have h8 : (p + 2) ^ 8 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  refine ⟨E, rfl, rfl, rfl, hr.trans (le_power_budget hp (by decide)),
    hNb.trans (Real.exp_le_exp.mpr h9), ?_, ?_⟩
  · intro i j k
    apply rationalLogHeight_le_of_height (hbracket i j k)
    simpa only [Fintype.card_fin] using hbracketBudget
  · intro i j k
    exact (ha i j k).trans h8

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_controlled_refiltration_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]
      {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v i) k) ≤ p) →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) s
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∀ i k, rationalLogHeight (D.basis.repr (E.basis i : L) k) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 1 + (X + 1 + (X + 1 + 2) ^ 7 + 2) ^ 9
  let P := Q + (Q + 2) ^ 11
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L κ _ _ _ s d D w hF W v hspan p hp hD hκ hv
  let A := ⌈Real.exp p⌉₊
  have hA : 1 ≤ A := one_le_ceil_exp p
  have hAp : (A : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := add_nonneg hp zero_le_one
  have hpp1 : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  obtain ⟨B, hB, hBp, hBases⟩ := D.filtration.exists_uniform_refiltration_layer_bases D.basis w hF
    W v hspan hA (fun i k => rationalHeightLE_ceil_exp (hv i k)) hp1
    (by simpa only [Fintype.card_fin] using hD.1.trans hpp1)
    (hκ.trans hpp1) hAp
  let q := p + 1 + (p + 1 + (p + 1 + 2) ^ 7 + 2) ^ 9
  have hpq : p + 1 ≤ q := le_add_of_nonneg_right (by positivity)
  have hq : 0 ≤ q := hp1.trans hpq
  have hBq : (B : ℝ) ≤ Real.exp q :=
    hBp.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hp1))
  have hAq : (A : ℝ) ≤ Real.exp q := hAp.trans (Real.exp_le_exp.mpr hpq)
  let H := max B A
  have hH : 1 ≤ H := hB.trans (Nat.le_max_left _ _)
  have hHq : (H : ℝ) ≤ Real.exp q := by simpa only [H, Nat.cast_max] using max_le hBq hAq
  obtain ⟨b, hb⟩ := hBases 1
  have hLayers : ∀ j, 1 ≤ j →
      ∃ a : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W j))) ℚ
        (D.filtration.gradedRefiltrationLayer W j),
        ∀ i k, RationalHeightLE (D.basis.repr (a i : L) k) H := by
    intro j _
    obtain ⟨a, ha⟩ := hBases j
    exact ⟨a, fun i k => (ha i k).mono (Nat.le_max_left _ _)⟩
  have hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => (rationalHeightLE_ceil_exp (hD.2.2.1 i j k)).mono (Nat.le_max_right _ _)
  obtain ⟨E, hEF, hEb, hEL, hEc⟩ := exists_native_refiltration_model_of_bases D W b hH
    (fun i k => (hb i k).mono (Nat.le_max_left _ _)) hLayers hc hq
    (hD.1.trans (hpp1.trans hpq)) hHq
    (hD.2.1.trans (Real.exp_le_exp.mpr (hpp1.trans hpq)))
  have hbound : q + (q + 2) ^ 11 ≤ (p + C) ^ C := by
    simpa [P, Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hq (by norm_num)) 11)).trans hbound
  have hcost : (q + 2) ^ 11 ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hbound
  refine ⟨E, hEF, hEL, hEc.mono E hcost, ?_⟩
  intro i k
  rw [hEb]
  exact (rationalLogHeight_le_of_height (hb i k) hBq).trans hqC

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_controlled_adapted_refiltration_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]
      {s d n : ℕ} (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin n) ℚ L) (w : Fin n → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis b w hF).repr (v i) j) ≤ p) →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra U) s
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra U)),
        E.filtration = D.filtration.gradedRefiltration U ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration U).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra U).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∀ i j, rationalLogHeight (D.basis.repr (E.basis i : L) j) ≤ (p + C) ^ C := by
  obtain ⟨A, _, hmodel⟩ := exists_controlled_refiltration_model
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + 4) ^ 11 + X + 1
  let R := T + (T + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + 2) ^ 4)
  refine ⟨C, hC, ?_⟩
  intro L κ _ _ _ s d n D b w hF U v hspan p hp hD hκ hb hv
  obtain ⟨m, hm, hin, hout, hB⟩ := D.exists_prescribed_adapted_model b w hF hp hD
    (fun i j => (hb i j).trans (by linarith))
  let B := D.filtration.ofAdaptedBasis b w hF D.lattice m hm hin hout
  let t := (p + 4) ^ 11 + p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (by linarith : 0 ≤ p + 4) 11]
  have hBt : B.GeometryComplexityLE t := hB.mono B (by dsimp [t]; linarith)
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hmodel B w hF U v hspan ht hBt
    (hκ.trans hpt) (fun i j => (hv i j).trans hpt)
  let r := t + (t + A) ^ A
  have htr : t ≤ r := le_add_of_nonneg_right (by positivity)
  have hr : 0 ≤ r := ht.trans htr
  have hEr : (t + A) ^ A ≤ r := le_add_of_nonneg_left ht
  have hsum : r + (r + 2) ^ 4 ≤ (p + C) ^ C := by
    simpa [T, R, X, t, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hheightC : (r + 2) ^ 4 ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans hsum
  have hn : (Fintype.card (Fin n) : ℝ) ≤ r := by
    rw [← finrank_eq_card_basis b, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1.trans (hpt.trans htr)
  refine ⟨E, hEF, hEL, hE.mono E (hEr.trans hrC), ?_⟩
  intro i j
  exact (linearMap_coordinate_logHeight b D.basis (LinearMap.id : L →ₗ[ℚ] L) hr hn
    (fun a c => (hb a c).trans (hpt.trans htr)) (E.basis i : L)
    (fun k => (hinc i k).trans hEr) j).trans hheightC

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_controlled_refiltered_target :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      {κ : Type*} [Fintype κ] {s : ℕ} {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {k | j ≤ w i k}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i k, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v i) k) ≤ p) →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ b i j, rationalLogHeight ((D b).basis.repr
          (((liePiEval b).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl)
            (E.basis j)) i) ≤ (p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            (optionProduct (Q.raiseStep (Nat.le_succ s))
              (fun i : {i : ι // i ≠ a} => D i.val)).GeometryComplexityLE ((p + C) ^ C) ∧
            ∀ i j, rationalLogHeight ((optionProduct (Q.raiseStep (Nat.le_succ s))
              (fun i : {i : ι // i ≠ a} => D i.val)).basis.repr
              (optionProductMap (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
                (fun i : {i : ι // i ≠ a} =>
                  (liePiEval i.val).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl)
                (E.basis j)) i) ≤ (p + C) ^ C := by
  obtain ⟨A, _, hsource⟩ := exists_controlled_refiltration_model
  obtain ⟨B, _, htarget⟩ := exists_topQuotientOtherTarget
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + 2) ^ 2
  let R := P + (P + Polynomial.C A) ^ A
  let T := R + (R + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ κ _ s d D a w hF W v hspan p hp hι hD hκ hv
  let t := p + (p + 2) ^ 2
  have hpt : p ≤ t := le_add_of_nonneg_right (sq_nonneg _)
  have ht : 0 ≤ t := hp.trans hpt
  have hgeom : (pi D).GeometryComplexityLE t :=
    (pi_geometry D hp hι hD).mono _ (le_add_of_nonneg_left hp)
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hsource (pi D) (productBasisWeight w)
    (pi_layer_span D w hF) W v hspan ht hgeom (hκ.trans hpt) (fun i k => (hv i k).trans hpt)
  let r := t + (t + A) ^ A
  have htr : t ≤ r := le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg A)) _)
  have hr : 0 ≤ r := ht.trans htr
  have hEr : (t + A) ^ A ≤ r := le_add_of_nonneg_left ht
  have hcomp := product_componentMap_logHeight D E.basis
    ((pi D).filtration.gradedRefiltrationSubalgebra W).incl (fun i j => hinc j i)
  have hother : (Fintype.card {i : ι // i ≠ a} : ℝ) ≤ r :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans (hι.trans (hpt.trans htr))
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hT, hmap⟩ := htarget E
    (fun i : {i : ι // i ≠ a} => D i.val)
    (fun i : {i : ι // i ≠ a} =>
      (liePiEval i.val).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl)
    hr (hE.mono E hEr) hother (fun i => (hD i.val).mono _ (hpt.trans htr))
    (fun b i j => (hcomp b.val i j).trans hEr)
  have hsum : r + (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [T, R, P, X, t, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hr (Nat.cast_nonneg B)) _)).trans hsum
  have hTC : (r + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans hsum
  exact ⟨E, hEF, hEL, hE.mono E (hEr.trans hrC),
    fun b i j => (hcomp b i j).trans (hEr.trans hrC),
    n, hn, Q, hQF, hQL, hQ.mono Q hTC, hT.mono _ hTC,
    fun i j => (hmap i j).trans hTC⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_single_refiltered_models :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]
      {s d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v i) k) ≤ p) →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (D.basis.repr
          ((D.filtration.gradedRefiltrationSubalgebra W).incl (E.basis j)) i) ≤ (p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            ∀ i j, rationalLogHeight (Q.basis.repr
              (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ (p + C) ^ C := by
  obtain ⟨A, _, hsource⟩ := exists_controlled_refiltration_model
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + 3) ^ 11)
  refine ⟨C, hC, ?_⟩
  intro L κ _ _ _ s d D w hF W v hspan p hp hD hκ hv
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hsource D w hF W v hspan hp hD hκ hv
  let t := p + (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hproj, _⟩ := E.exists_controlled_top_quotient ht (hE.mono E hAt)
  have hsum : t + (t + 3) ^ 11 ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hQC : (t + 3) ^ 11 ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have h5 : (t + 3) ^ 5 ≤ (t + 3) ^ 11 := pow_le_pow_right₀ (by linarith) (by decide)
  exact ⟨E, hEF, hEL, hE.mono E (hAt.trans htC),
    (fun i j => (hinc j i).trans (hAt.trans htC)), n, hn, Q, hQF, hQL,
    hQ.mono Q hQC, fun i j => (hproj j i).trans (h5.trans hQC)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_adapted_single_refiltered_models :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]
      {s d n : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (b : Basis (Fin n) ℚ L) (w : Fin n → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis b w hF).repr (v i) k) ≤ p) →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (E.basis j : L) i) ≤ (p + C) ^ C) ∧
        ∃ m : ℕ, m ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s m,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            ∀ i j, rationalLogHeight (Q.basis.repr
              (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ (p + C) ^ C := by
  obtain ⟨A, _, hsource⟩ := exists_controlled_adapted_refiltration_model
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + 3) ^ 11)
  refine ⟨C, hC, ?_⟩
  intro L κ _ _ _ s d n D b w hF W v hspan p hp hD hκ hb hv
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hsource D b w hF W v hspan hp hD hκ hb hv
  let t := p + (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  obtain ⟨m, hm, Q, hQF, hQL, hQ, hproj, _⟩ := E.exists_controlled_top_quotient ht (hE.mono E hAt)
  have hsum : t + (t + 3) ^ 11 ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hQC : (t + 3) ^ 11 ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have h5 : (t + 3) ^ 5 ≤ (t + 3) ^ 11 := pow_le_pow_right₀ (by linarith) (by decide)
  exact ⟨E, hEF, hEL, hE.mono E (hAt.trans htC),
    (fun i j => (hinc j i).trans (hAt.trans htC)), m, hm, Q, hQF, hQL,
    hQ.mono Q hQC, fun i j => (hproj j i).trans (h5.trans hQC)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra

theorem exists_antisymmetric_middle_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      {N : ℕ} (V : NativeAntisymmetricOrbitFactors W N p), 0 ≤ p →
      let D := pi (fun _ : Fin 8 => W.model)
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra V.subalgebra)
          (∑ k, mixedCorrelationDegree 1 k)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra V.subalgebra)),
        E.filtration = D.filtration.gradedRefiltration V.subalgebra ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration V.subalgebra).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra V.subalgebra).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (E.basis i : Fin 8 → W.L) j) ≤ (p + C) ^ C) ∧
        ∃ g : E.filtration.realification.PolynomialOrbit (fun _ : Fin 4 => 1),
          ∀ x : Fin 4 → ℤ,
            realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
              (hM := D.filtration.lowerCentralSeries_eq_bot)
              (D.filtration.gradedRefiltrationSubalgebra V.subalgebra).incl
              (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) =
                D.filtration.adaptedPolynomialRealValueHom
                  (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.middle := by
  obtain ⟨A, _, hmodel⟩ := exists_controlled_adapted_refiltration_model
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + 10) ^ 2 + X + 10
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p W N V hp
  let D := pi (fun _ : Fin 8 => W.model)
  let t := (p + 10) ^ 2 + p + 10
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; nlinarith [sq_nonneg (p + 10)]
  have hD : D.GeometryComplexityLE t := by
    have h := pi_geometry (fun _ : Fin 8 => W.model) (by linarith : 0 ≤ p + 8)
      (by norm_num; linarith)
      (fun _ => W.complexity.1.mono W.model (by linarith : p ≤ p + 8))
    exact h.mono D (by dsimp [t]; nlinarith)
  have hdim : (Fintype.card (Fin (finrank ℚ (Fin 8 → W.L))) : ℝ) ≤ t := by
    rw [Fintype.card_fin, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hmodel D V.basis V.weight V.adapted V.subalgebra
    V.generator V.spanning ht hD hdim (fun i j => (V.basis_height i j).trans hpt)
    (fun i j => (V.generator_height i j).trans hpt)
  have hcost : (t + A) ^ A ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨E, hEF, hEL, hE.mono E hcost, fun i j => (hinc i j).trans hcost, ?_⟩
  exact D.filtration.exists_model_refiltered_polynomial V.subalgebra E hEF
    (fun _ : Fin 4 => 1) (fun _ => Nat.zero_lt_one) V.middle
    V.middle_coefficients V.middle_zero

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup

theorem exists_native_middle_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
      {g : (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra R.subalgebra)
          s (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra R.subalgebra)),
        E.filtration = D.filtration.gradedRefiltration R.subalgebra ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration R.subalgebra).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (E.basis i : L) j) ≤ (p + C) ^ C) ∧
        ∃ h : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
          ∀ x : σ → ℤ,
            realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
              (hM := D.filtration.lowerCentralSeries_eq_bot)
              (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
              (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x h) =
                D.filtration.adaptedPolynomialRealValueHom
                  (fun _ : σ => 1) (fun i => (x i : ℝ)) R.middle := by
  obtain ⟨C, hC, hmodel⟩ := exists_controlled_adapted_refiltration_model
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ s d D g eta A p R hp hD
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p := by
    rw [Fintype.card_fin, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hmodel D R.basis R.weight R.adapted R.subalgebra
    R.generator R.spanning hp hD hdim R.basis_height R.generator_height
  refine ⟨E, hEF, hEL, hE, hinc, ?_⟩
  exact D.filtration.exists_model_refiltered_polynomial R.subalgebra E hEF
    (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) R.middle
    R.middle_coefficients R.middle_zero

end Erdos3

end

section

universe u v uO uR uIO

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_adapted_diagram_native_external_net (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {A ι : Type u} {κ : Type v}
      [LieRing A] [LieAlgebra ℚ A] [Fintype ι] [DecidableEq ι] [Fintype κ]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] A)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] A)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] A)] [T2Space (ℝ ⊗[ℚ] A)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d n : ℕ} {dim : ι → ℕ}
      (D : RationalFilteredNilmanifold A (s + 1) d)
      (b : Basis (Fin n) ℚ A) (w : Fin n → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
      (F : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (dim i))
      (χ : ∀ i, A →ₗ⁅ℚ⁆ L i) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card ι : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis b w hF).repr (v i) j) ≤ p) →
      (∀ i, (F i).GeometryComplexityLE p) →
      (∀ a i j, rationalLogHeight ((F a).basis.repr (χ a (D.basis j)) i) ≤ p) →
      (∀ x : A, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) →
        (∀ i, χ i x = 0) → x = 0) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (E.basis j : A) i) ≤ (p + C) ^ C) ∧
        ∃ m : ℕ, m ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s m,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            (∀ i j, rationalLogHeight (Q.basis.repr
              (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ (p + C) ^ C) ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))
             letI := IsModuleTopology.isTopologicalAddGroup ℝ
               (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))
             letI := realification_moduleTopology_t2 E.basis
             letI := moduleTopology ℝ
               (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)))
             letI := IsModuleTopology.isTopologicalAddGroup ℝ
               (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)))
             letI := realification_moduleTopology_t2 Q.basis
             DiagramNativeExternalNetConclusion.{u, uO, uR, uIO} s (s + 1) k E D Q F
               (D.filtration.gradedRefiltrationSubalgebra W).incl
               (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
               (fun i => (χ i).comp (D.filtration.gradedRefiltrationSubalgebra W).incl)
               p ((p + C) ^ C) q) := by
  obtain ⟨a, _, hmodels⟩ := exists_adapted_single_refiltered_models
  obtain ⟨c, _, hnet⟩ := exists_diagram_native_external_net.{u, uO, uR, uIO} s (s + 1) k
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C a) ^ a
  let T := R + (R + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro A ι κ _ _ _ _ _ L _ _ _ _ _ _ _ _ _ _ d n dim D b w hF W v hspan F χ p
    hp hD hκ hι hb hv hFgeom hχ hker q hq hqp
  obtain ⟨E, hEF, hEL, hE, hinc, m, hm, Q, hQF, hQL, hQ, hproj⟩ :=
    hmodels D b w hF W v hspan hp hD hκ hb hv
  let r := p + (p + a) ^ a
  let t := r + (r + 2) ^ 4
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := le_add_of_nonneg_right (by positivity)
  have har : (p + a) ^ a ≤ r := le_add_of_nonneg_left hp
  have hrt : r ≤ t := le_add_of_nonneg_right (by positivity)
  have hfour : (r + 2) ^ 4 ≤ t := le_add_of_nonneg_left hr
  have ht : 0 ≤ t := hr.trans hrt
  have hpt : p ≤ t := hpr.trans hrt
  have hat : (p + a) ^ a ≤ t := har.trans hrt
  have hsum : t + (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [T, R, X, t, r, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hnetC : (t + c) ^ c ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have haC : (p + a) ^ a ≤ (p + C) ^ C := hat.trans htC
  refine ⟨E, hEF, hEL, hE.mono E haC, (fun i j => (hinc i j).trans haC),
    m, hm, Q, hQF, hQL, hQ.mono Q haC, (fun i j => (hproj i j).trans haC), ?_⟩
  let H := D.filtration.gradedRefiltrationSubalgebra W
  let := moduleTopology ℝ (ℝ ⊗[ℚ] H)
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] H)
  let := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q.basis
  have hmarked : ∀ a i j,
      rationalLogHeight ((F a).basis.repr
        (((χ a).comp H.incl) (E.basis j)) i) ≤ t := by
    intro a i j
    apply le_trans ?_ hfour
    exact linearMap_coordinate_logHeight D.basis (F a).basis (χ a).toLinearMap hr
      (by simpa only [Fintype.card_fin] using hD.1.trans hpr)
      (fun j i => (hχ a i j).trans hpr) (E.basis j : A)
      (fun i => (hinc i j).trans har) i
  have hconstructed : DiagramNativeExternalNetConclusion.{u, uO, uR, uIO} s (s + 1) k E D Q F H.incl
      (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
      (fun i => (χ i).comp H.incl) t ((t + c) ^ c) q :=
    hnet E D Q (Nat.le_succ s) F H.incl
      (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
      (fun i => (χ i).comp H.incl) ht (hι.trans hpt)
      (hE.mono E hat) (hD.mono D hpt) (hQ.mono Q hat)
      (fun i => (hFgeom i).mono (F i) hpt)
      (fun i j => (hinc i j).trans hat) (fun i j => (hproj i j).trans hat)
      hmarked (refiltered_markedDiagram_injective D W E hEF χ hker)
      q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  exact DiagramNativeExternalNetConclusion.mono s (s + 1) k E D Q F H.incl
    (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
    (fun i => (χ i).comp H.incl) q hconstructed hp hpt hnetC

end Erdos3.RationalFilteredNilmanifold

end

end OAI
