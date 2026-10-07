/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet

namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

theorem exists_lower_refilteredRecoveryFamily :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {s : ℕ} {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
      (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
      (Q : RationalFilteredNilmanifold
        (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
      {p b : ℝ} {q k : ℕ},
      0 ≤ b → (Fintype.card ι : ℝ) ≤ b → (∀ i, (D i).GeometryComplexityLE b) →
      Q.GeometryComplexityLE b → RefilteredRecoveryFamily D a W E Q p q k b →
      LowerRefilteredRecoveryFamily D a W E Q p q k ((b + C) ^ C) := by
  obtain ⟨C, hC, hsplit⟩ := exists_lowered_split_reconstruction_cover
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ s d D a W e n E Q p b q k hb hι hD hQ hfamily
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I := {i : ι // i ≠ a}
  let A := H ⧸ E.filtration.layerIdeal (s + 1)
  let M := ∀ j : Option I, optionLieSpace A (fun i : I => L i.val) j
  let F := optionFactors (Q.raiseStep (Nat.le_succ s)) (fun i : I => D i.val)
  let T := nativeRefilteredTarget D a W E Q
  let Z₀ := pi (fun i : I => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] A)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] A)
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] M)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] M)
  let := realification_moduleTopology_t2 T.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I, L i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Λ, _, _, _, _, _, m, hm, hΛin, hΛout, hV, hrec⟩ := hfamily
  have hI : (Fintype.card I : ℝ) ≤ b :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hι
  obtain ⟨Δ, N, hN, hin, hout, _, hindex, hQF, hQle, hQgeom, _, hZgeom, hnew⟩ :=
    hsplit Q (Nat.le_succ s) (fun i : I => D i.val) Λ m hm hΛin hΛout
      hb hI hQ (fun i => hD i.val) hV.2.1
  let G := fun i => (F i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  let Q' := Q.loweredCover (Nat.le_succ s) (Δ none) (N none) (hN none) (hin none) (hout none)
  let Z := pi (fun i : I => G (some i))
  have hZle : Z.lattice ≤ Z₀.lattice := by
    intro x hx
    have hmem := (mem_piBCHSubgroup (fun i : I => (G (some i)).filtration)
      (fun i : I => (G (some i)).lattice) x).mp hx
    apply (mem_piBCHSubgroup (fun i : I => (D i.val).filtration)
      (fun i : I => (D i.val).lattice) x).mpr
    intro i
    exact (hindex (some i)).1 (hmem i)
  refine ⟨Q', hQF, rfl, hQle, hQgeom, Z, rfl, rfl, hZle, hZgeom, ?_⟩
  intro J eta hfreq l r hl hr S ℓ hℓ hS hpositive hinvariant
  obtain ⟨u, K₀, hK₀, hu, hunit, _, heval⟩ :=
    hrec eta hfreq l r hl hr S ℓ hℓ hS hpositive hinvariant
  obtain ⟨v, K, hK, hv, hpos, hveval⟩ := hnew u K₀ hK₀ hu hunit
  refine ⟨v, K, hK, hv, hpos, ?_⟩
  intro x
  let φ := optionMaps (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
    (fun i : I => refilteredComponentMap D W i.val)
  let y : (pi G).RealGroup := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (pi G).filtration.lowerCentralSeries_eq_bot) (liePiMap φ) x
  have hfirst := lowered_productProjectionHom_realificationMap E.filtration G Q φ x
  have hsecond := congrArg Prod.snd (optionProductSpaceEquiv_realificationMap E.filtration G φ x)
  have hargs := congrArg₂ Prod.mk
    (congrArg (QuotientGroup.mk : Q'.RealGroup → Q'.Space) hfirst.symm) hsecond.symm
  exact (congrArg v hargs).trans ((hveval y).trans (heval x))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_controlled_refiltered_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + C) ^ C) ∧
            RefilteredRecoveryFamily D a W E Q p q k ((p + C) ^ C) := by
  obtain ⟨A, _, hmodels⟩ := exists_controlled_refiltered_target
  obtain ⟨B, _, hrec⟩ := exists_uniform_refilteredRecoveryFamily s k
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C A) ^ A
  let P := R + (R + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ κ _ d D a w hF W v₀ hspan p hp hι hD hκ hv q hq hqp
  obtain ⟨E, hEF, hEL, hE, hcomp, n, hn, Q, hQF, hQL, hQ, hT, hmap⟩ :=
    hmodels D a w hF W v₀ hspan hp hι hD hκ hv
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg A)) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, R, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg B)) _)).trans hsum
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hfamily := hrec D a W E Q t hEF ht (hE.mono E hAt) ((hD a).mono _ hpt)
    (hT.mono _ hAt) (fun i j => (hcomp a i j).trans hAt) (fun i j => (hmap i j).trans hAt)
    q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  exact ⟨E, hEF, hEL, hE.mono E (hAt.trans htC), n, hn, Q, hQF, hQL,
    hQ.mono Q (hAt.trans htC), hT.mono _ (hAt.trans htC),
    RefilteredRecoveryFamily.mono D a W E Q hfamily hp hpt hcost⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_controlled_lower_refiltered_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + C) ^ C) ∧
            LowerRefilteredRecoveryFamily D a W E Q p q k ((p + C) ^ C) := by
  obtain ⟨A, _, hbase⟩ := exists_controlled_refiltered_reconstruction s k
  obtain ⟨B, _, hlower⟩ := exists_lower_refilteredRecoveryFamily
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let P := T + (T + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ κ _ d D a w hF W v₀ hspan p hp hι hD hκ hv q hq hqp
  obtain ⟨E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, hrec⟩ :=
    hbase D a w hF W v₀ hspan hp hι hD hκ hv q hq hqp
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hrec' := RefilteredRecoveryFamily.mono D a W E Q hrec hp le_rfl hAt
  have hlow := hlower D a W E Q ht (hι.trans hpt) (fun i => (hD i).mono _ hpt)
    (hQ.mono Q hAt) hrec'
  exact ⟨E, hEF, hEL, hE.mono E (hAt.trans htC), n, hn, Q, hQF, hQL,
    hQ.mono Q (hAt.trans htC), htarget.mono _ (hAt.trans htC),
    LowerRefilteredRecoveryFamily.mono_cost D a W E Q hlow hcost⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_controlled_refiltered_cyclic_expansion (s k : ℕ) :
    ∃ A C : ℕ, 2 ≤ A ∧ 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      1 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + A) ^ A) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + A) ^ A) ∧
            (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + A) ^ A) ∧
            LowerRefilteredCyclicExpansionSpec D a W E Q p q k ((p + A) ^ A) C := by
  obtain ⟨A, hA, hmodels⟩ := exists_controlled_lower_refiltered_reconstruction s k
  obtain ⟨C, hC, hexpand⟩ := exists_lower_refiltered_cyclic_expansion s k
  refine ⟨A, C, hA, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ κ _ d D a w hF W v₀ hspan p hp hι hD hκ hv q hq hqp
  obtain ⟨E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, hrec⟩ :=
    hmodels D a w hF W v₀ hspan (by linarith) hι hD hκ hv q hq hqp
  exact ⟨E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget,
    hexpand D a W E Q hp (by positivity) hQF hrec⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
