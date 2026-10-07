import OAI.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent
import OAI.Combinatorics.Progressions.Polynomial.RetainedPhysicalLowerDegree

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

theorem exists_fixed_child_affine_residue_descent (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d),
      ∀ p : ℝ, 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ (P : ℕ) (hP : 0 < P), (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) {e n : ℕ}
        (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
        (Q : RationalFilteredNilmanifold
          ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
        (_hEF : E.filtration = D.filtration.gradedRefiltration W)
        (_hQF : Q.filtration = E.filtration.quotientTop)
        (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) →
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
        ∀ cost : ℝ, 0 ≤ cost → SingleRefilteredRecoveryFamily D W E Q p q C cost →
        let H := D.filtration.gradedRefiltrationSubalgebra W
        let N := H ⧸ E.filtration.layerIdeal (s + 1)
        let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
        let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
        let := realification_moduleTopology_t2 Q.basis
        let T := Q.raiseStep (Nat.le_succ s)
        ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
          (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
          (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (B : ℕ) (hB : 0 < B)
            (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates Q.basis Λ)
            (hout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid B),
            let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
            V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧ V.GeometryComplexityLE cost ∧
            ∃ child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
              DegreeLE (fun _ => 1) s child.log ∧
              FixedAffineResidueDescent D W V b child p q P hP C a (cost + 4) := by
  obtain ⟨C, hC, hfreezing⟩ := Niltest.exists_auxiliary_frozen_discrepancy (s + 1) a
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ _ d D p hp hD hσ q hq hqp
  obtain ⟨P, hP, hPb, hfreeze⟩ := hfreezing D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    p hp hD hσ q hq hqp
  refine ⟨P, hP, hPb, ?_⟩
  intro W e n E Q hEF hQF b hb hb0 cost hcost hfamily H N _ _ _ T
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hVF, hVL, hV,
    child, hdegree, hrealize⟩ :=
    SingleRefilteredRecoveryFamily.exists_fixed_child D W E Q hEF hQF
      (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) b hb hb0 hcost hfamily
  let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hVF, hVL, hV,
    child, hdegree, ?_⟩
  intro scale shift S hS hunit hinvariant slow rational κ hκ hprod hgrid A hA hslow M hM lo length width
    hwidth hwidthN u v J hJ hv hcop δ ε hδ hε hsize hphysical hsmall cells c₀ c₁ F G
  let middle := D.filtration.realification.scalarAffineAdaptedHom (scale : ℚ) (fun i => (shift i : ℚ)) b
  obtain ⟨k, hk₀, hk₁, l₀, r₀, hl₀, hr₀, hgap⟩ :=
    hfreeze S hS hunit slow middle rational κ hκ hprod hgrid A hA hslow
      M hM lo length width hwidth hwidthN u v J hJ hv hcop δ ε hδ hε hsize hphysical hsmall
  have hℓ : (S.lipBound : ℝ) ≤ Real.exp p := by
    linarith [S.observable_budget hS, S.normBound.coe_nonneg]
  have hreal := (hrealize l₀ r₀ hl₀ hr₀ S.observable S.lipBound hℓ S.lipschitz hunit hinvariant).scalarAffine scale shift
  have heq : (fun x : σ → ℤ => S.observable (QuotientGroup.mk
      (l₀ * D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1)
        (fun i => (x i : ℝ)) middle * r₀))) =
      (fun x : σ → ℤ => S.observable (QuotientGroup.mk
        (l₀ * D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1)
          (fun i => ((scale * x i + shift i : ℤ) : ℝ)) b * r₀))) := by
    funext x
    exact congrArg (fun z : D.RealGroup => S.observable (QuotientGroup.mk (l₀ * z * r₀)))
      (D.filtration.scalarAffineAdaptedHom_value_integer (scale : ℚ)
        (fun i => (shift i : ℚ)) x (fun i => scale * x i + shift i)
        (fun i => by push_cast; ring) b)
  rw [← heq] at hreal
  obtain ⟨U, hU, hunitU, hcostU, hgapU⟩ := hreal.transfer_discrepancy
    (partitionCell c₀ k) (partitionCell c₁ k)
    (fun x => commonStrideIndex u M (fun i => (x i).val))
    (fun x => commonStrideIndex u M (fun i => (x i).val)) hgap
  exact ⟨k, hk₀, hk₁, U, hU, hunitU, hcostU, hgapU⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct

noncomputable def HasFixedAffineResidueChild {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (p : ℝ) (q P : ℕ) (hP : 0 < P) (C a : ℕ) (cost : ℝ) : Prop :=
  ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
      (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
    E.filtration = D.filtration.gradedRefiltration W ∧
    ∃ (n : ℕ) (_hn : n ≤ d)
      (Q : RationalFilteredNilmanifold
        ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n),
      Q.filtration = E.filtration.quotientTop ∧
      let H := D.filtration.gradedRefiltrationSubalgebra W
      let N := H ⧸ E.filtration.layerIdeal (s + 1)
      let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
      let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
      let := realification_moduleTopology_t2 Q.basis
      ∃ V : RationalFilteredNilmanifold N s n,
        V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧ V.GeometryComplexityLE cost ∧
        ∃ child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
          DegreeLE (fun _ => 1) s child.log ∧
          FixedAffineResidueDescent D W V b child p q P hP C a cost

theorem exists_controlled_affine_residue_child (s a : ℕ) :
    ∃ C K : ℕ, 2 ≤ C ∧ 2 ≤ K ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ (P : ℕ) (hP : 0 < P), (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
          (v : Fin d → D.filtration.AssociatedGraded),
          Submodule.span ℚ (Set.range v) = W.toSubmodule →
          (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v i) j) ≤ p) →
          ∀ b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
          (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
            D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) →
          coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
          ∃ cost : ℝ, 0 ≤ cost ∧ cost ≤ (p + 2) ^ K ∧
            HasFixedAffineResidueChild D W b p q P hP C a cost := by
  obtain ⟨C, hC, hchild⟩ := exists_fixed_child_affine_residue_descent s a
  obtain ⟨R, _, hmodels⟩ := exists_controlled_single_refiltered_reconstruction s C
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C R) ^ R + 4
  obtain ⟨K, hK, hbudget⟩ := exists_natPolynomial_fixed_power_budget B
  refine ⟨C, K, hC, hK, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ω hF p hp hD hσ q hq hqp
  obtain ⟨P, hP, hPb, hdesc⟩ := hchild D p hp hD hσ q hq hqp
  refine ⟨P, hP, hPb, ?_⟩
  intro W v hspan hv b hb hb0
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hD.1
  obtain ⟨E, hEF, _, _, n, hn, Q, hQF, _, _, hfamily⟩ :=
    hmodels D ω hF W v hspan hp hD hd hv q hq hqp
  have hcost0 : 0 ≤ (p + R) ^ R := by positivity
  have hcost : (p + R) ^ R + 4 ≤ (p + 2) ^ K := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  have hnD : n ≤ d := by
    have hh := lie_subalgebra_finrank_le D.basis (D.filtration.gradedRefiltrationSubalgebra W)
    simpa only [Fintype.card_fin] using hn.trans hh
  have hfixed := hdesc W E Q hEF hQF b hb hb0 ((p + R) ^ R) hcost0 hfamily
  refine ⟨(p + R) ^ R + 4, by positivity, hcost, E, hEF, n, hnD, Q, hQF, ?_⟩
  intro H N _ _ _
  obtain ⟨Λ, _, _, _, _, _, B₀, hB₀, hin, hout, hVF, hVL, hV, child, hdegree, hresidue⟩ := hfixed
  let V := Q.loweredCover (Nat.le_succ s) Λ B₀ hB₀ hin hout
  exact ⟨V, hVF, hVL, hV.mono V (by linarith), child, hdegree, hresidue⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

noncomputable def RetainedAffineResidueEpoch {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ) (p cost : ℝ) (C : ℕ) : Prop :=
  ∃ (v : Fin d → D.filtration.AssociatedGraded) (q P : ℕ) (hP : 0 < P)
      (κ : D.RealGroup)
      (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω W.toSubmodule ∧
    (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v i) j) ≤ p) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp p ∧ (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ κ ∈ D.realLattice ∧
    E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩ ∧
    D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A (Real.exp (p + 2)) E ∧
    (∀ B : σ → ℝ, (∀ i, 0 < B i) → ∀ (r : ℚ) (h : σ → ℚ),
      (∀ i, |(h i : ℝ)| ≤ A i) → (∀ i, |(r : ℝ)| * B i ≤ A i) →
      D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) B (Real.exp (p + 2))
        (D.filtration.realification.scalarAffineAdaptedHom r h E)) ∧
    D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) q R ∧
    coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
    HasFixedAffineResidueChild D W b p q P hP C 1 cost

theorem exists_retained_affine_residue_epoch (s : ℕ) :
    ∃ C K : ℕ, 2 ≤ C ∧ 2 ≤ K ∧ ∀ {σ J L : Type*} [Fintype σ] [DecidableEq σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n aux oldModulus : J → ℕ)
      (M : ℕ) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, 0 < aux j) → (∀ j, 0 < oldModulus j) → 0 < M →
      (∀ j, oldModulus j ∣ M) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      (∀ j, (aux j : ℝ) ≤ Real.exp p) →
      ∀ W A : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ K) ≤ A i) →
      ∀ (T : D.Niltest (fun _ : σ => 1)) (shift : σ → ℚ)
        (oldShift : J → σ → ℚ) (oldSides : J → σ → ℝ),
      (∀ j i, 0 < oldSides j i) → (∀ i, (M : ℝ) * A i ≤ W i) →
      (∀ j i, Real.exp (-p) * W i ≤ ((oldModulus j : ℝ) * aux j) * oldSides j i) →
      (∀ j, D.filtration.SymbolFactorizationIn D.basis ω hF (oldSides j)
        ((T.scalarAffinePullback ((oldModulus j : ℚ) * aux j) (oldShift j)).symbol D.basis ω hF)
        p (n j) (U j)) →
      ∃ work cost : ℝ, p + 16 ≤ work ∧ work ≤ (p + 2) ^ K ∧ 0 ≤ cost ∧ cost ≤ (p + 2) ^ K ∧
        RetainedAffineResidueEpoch D ω hF (⨅ j, U j) (T.scalarAffinePullback (M : ℚ) shift) A work cost C := by
  obtain ⟨F, hFmin, hnormalize⟩ := exists_retained_physical_lower_degree_factorization s
  obtain ⟨S, _, hslow⟩ := exists_scalarAffine_slow_bound (s + 1) ((F + 1) * F)
  obtain ⟨C, D₀, hC, _, hchild⟩ := exists_controlled_affine_residue_child s 1
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C F) ^ F +
    (Polynomial.X + Polynomial.C S) ^ S + 16
  let R : Polynomial ℕ := (Polynomial.X + Polynomial.C F) ^ F + Q + (Q + 2) ^ D₀
  obtain ⟨K, hK, hbudget⟩ := exists_natPolynomial_fixed_power_budget R
  refine ⟨C, K, hC, hK, ?_⟩
  intro σ J L _ _ _ _ _ d _ _ _ _ D ω hF U v n aux oldModulus M p hp hD hσ hJ
    hv hgraded hheight hn haux hOld hM hdiv hnp hauxp W A hA T shift oldShift oldSides
    hSides hcurrent hphysical hold
  let work := p + (p + F) ^ F + (p + S) ^ S + 16
  have hF0 : 0 ≤ (p + F) ^ F := by positivity
  have hS0 : 0 ≤ (p + S) ^ S := by positivity
  have hpwork16 : p + 16 ≤ work := by dsimp only [work]; linarith
  have hpwork : p ≤ work := by linarith
  have hwork0 : 0 ≤ work := hp.trans hpwork
  have hFwork : (p + F) ^ F ≤ work := by dsimp only [work]; linarith
  have hSwork : (p + S) ^ S ≤ work := by dsimp only [work]; linarith
  have htotal : (p + F) ^ F + work + (work + 2) ^ D₀ ≤ (p + 2) ^ K := by
    simpa [R, Q, work, Polynomial.eval₂_pow] using hbudget p hp
  have hpower0 : 0 ≤ (work + 2) ^ D₀ := by positivity
  have hFbound : (p + F) ^ F ≤ (p + 2) ^ K := by linarith
  have hworkbound : work ≤ (p + 2) ^ K := by linarith
  have hchildbound : (work + 2) ^ D₀ ≤ (p + 2) ^ K := by linarith
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  obtain ⟨v₀, m, κ, E, b, R₀, hv₀, hWgraded, hvheight, hm, hmp, _, hκ, hprod,
    hE, hR, hb0, hR0, hcoeff, _, _⟩ :=
    hnormalize D ω hF U v n aux oldModulus M p hp hD hσ hJ hv hgraded hheight
      hn haux hOld hM hdiv hnp hauxp W A
      (fun i => (Real.exp_le_exp.mpr hFbound).trans (hA i))
      T shift oldShift oldSides hSides hcurrent hphysical hold
  have hmpwork : (m : ℝ) ≤ Real.exp work := hmp.trans (Real.exp_le_exp.mpr hFwork)
  obtain ⟨P, hP, hPb, hconstruct⟩ := hchild D ω hF work hwork0 (hD.mono D hpwork)
    (hσ.trans hpwork) m hm hmpwork
  obtain ⟨cost, hcost0, hcost, hfixed⟩ := hconstruct (⨅ j, U j) v₀ hv₀
    (fun i j => (hvheight i j).trans hFwork) b hcoeff hb0
  have hEcoeff := D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hApos
    (Real.exp_le_exp.mpr (shifted_power_le_fixed_base hp F hFmin)) E hE
  refine ⟨work, cost, hpwork16, hworkbound, hcost0, hcost.trans hchildbound,
    v₀, m, P, hP, κ, E, b, R₀, hv₀, hWgraded, fun i j => (hvheight i j).trans hFwork,
    hm, hmpwork, hPb, hκ, hprod, ?_, ?_, hR, hb0, hR0, hcoeff, hfixed⟩
  · exact D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hApos
      (Real.exp_le_exp.mpr (by linarith)) E hE
  · intro B hB r h hh hr
    have hpull := hslow D.filtration D.basis p hp hσ A B hApos hB E hEcoeff r h hh hr
    exact D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) B hB
      (Real.exp_le_exp.mpr (by linarith)) _ hpull

end Erdos3

end

end OAI
