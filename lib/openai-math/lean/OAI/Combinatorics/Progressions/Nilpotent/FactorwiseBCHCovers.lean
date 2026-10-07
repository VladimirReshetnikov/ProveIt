/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import Mathlib.Algebra.Group.Subgroup.Finite
import OAI.Combinatorics.Progressions.Estimates.ControlledSurjectiveReconstruction

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]
  [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}

noncomputable def piBCHSubgroup (F : ∀ a, NilpotentLieFiltration (M a) s)
    (Δ : ∀ a, Subgroup (F a).Group) : Subgroup (NilpotentLieFiltration.pi F).Group :=
  ⨅ a, (Δ a).comap (map (hM := (F a).lowerCentralSeries_eq_bot) (liePiEval a))

theorem mem_piBCHSubgroup (F : ∀ a, NilpotentLieFiltration (M a) s)
    (Δ : ∀ a, Subgroup (F a).Group) (g : (NilpotentLieFiltration.pi F).Group) :
    g ∈ piBCHSubgroup F Δ ↔ ∀ a, (⟨g.coord a⟩ : (F a).Group) ∈ Δ a := by
  simp only [piBCHSubgroup, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

variable [Fintype α] {κ : α → Type*} [∀ a, Fintype (κ a)]

theorem pi_basis_equivFun_symm_apply (f : ∀ a, Basis (κ a) ℚ (M a))
    (x : (Σ a, κ a) → ℚ) (a : α) :
    (Pi.basis f).equivFun.symm x a = (f a).equivFun.symm (fun i => x ⟨a, i⟩) := by
  apply (f a).equivFun.injective
  funext i
  change (Pi.basis f).equivFun ((Pi.basis f).equivFun.symm x) ⟨a, i⟩ = _
  simp only [LinearEquiv.apply_symm_apply]

theorem piBCHSubgroup_coordinates (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group)
    (x : (Σ a, κ a) → ℚ) :
    x ∈ bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) ↔
      ∀ a, (fun i => x ⟨a, i⟩) ∈ bchSubgroupCoordinates (f a) (Δ a) := by
  change (⟨(Pi.basis f).equivFun.symm x⟩ : (NilpotentLieFiltration.pi F).Group) ∈
    piBCHSubgroup F Δ ↔ _
  rw [mem_piBCHSubgroup]
  simp only [pi_basis_equivFun_symm_apply, bchSubgroupCoordinates, Set.mem_ofPred_eq]

theorem piBCHSubgroup_inner_grid (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group) (m : ℕ)
    (hin : ∀ a, scaledIntegerGrid m ⊆ bchSubgroupCoordinates (f a) (Δ a)) :
    scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) := by
  rintro x ⟨z, rfl⟩
  apply (piBCHSubgroup_coordinates F f Δ _).mpr
  intro a
  exact hin a ⟨fun i => z ⟨a, i⟩, rfl⟩

theorem piBCHSubgroup_outer_grid (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group) (m : ℕ)
    (hout : ∀ a, bchSubgroupCoordinates (f a) (Δ a) ⊆ denominatorGrid m) :
    bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) ⊆ denominatorGrid m := by
  intro x hx
  have h := (piBCHSubgroup_coordinates F f Δ x).mp hx
  choose z hz using fun a => hout a (h a)
  exact ⟨fun i => z i.1 i.2, fun i => hz i.1 i.2⟩

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)]
  [DecidableEq α] {s : ℕ}

def liePiSingle (a : α) : M a →ₗ⁅ℚ⁆ (∀ a, M a) where
  toLinearMap := LinearMap.single ℚ M a
  map_lie' {x y} := by
    ext i
    change Pi.single a ⁅x, y⁆ i = ⁅Pi.single a x i, Pi.single a y i⁆
    by_cases hi : i = a
    · subst i
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hi, lie_zero]

noncomputable def bchPiEquiv (F : ∀ a, NilpotentLieFiltration (M a) s) :
    (NilpotentLieFiltration.pi F).Group ≃* (∀ a, (F a).Group) where
  toFun g a := ⟨g.coord a⟩
  invFun g := ⟨fun a => (g a).coord⟩
  left_inv g := by cases g; rfl
  right_inv g := by funext a; exact NilpotentLieBCHGroup.ext rfl
  map_mul' g h := by
    funext a
    exact (map (hnil := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot)
      (hM := (F a).lowerCentralSeries_eq_bot) (liePiEval a)).map_mul g h

noncomputable def bchPiSingle (F : ∀ a, NilpotentLieFiltration (M a) s) (a : α) :
    (F a).Group →* (NilpotentLieFiltration.pi F).Group :=
  map (hnil := (F a).lowerCentralSeries_eq_bot)
    (hM := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot) (liePiSingle a)

theorem bchPiEquiv_single (F : ∀ a, NilpotentLieFiltration (M a) s) (a : α) (g : (F a).Group) :
    bchPiEquiv F (bchPiSingle F a g) = Pi.mulSingle a g := by
  funext i
  apply NilpotentLieBCHGroup.ext
  change Pi.single a g.coord i = ((Pi.mulSingle a g : ∀ i, (F i).Group) i).coord
  by_cases hi : i = a
  · subst i
    simp only [Pi.single_eq_same, Pi.mulSingle_eq_same]
  · simp only [Pi.single_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi, coord_one]

theorem bchPiSingle_eq_symm_mulSingle (F : ∀ a, NilpotentLieFiltration (M a) s)
    (a : α) (g : (F a).Group) :
    bchPiSingle F a g = (bchPiEquiv F).symm (Pi.mulSingle a g) := by
  apply (bchPiEquiv F).injective
  rw [bchPiEquiv_single, MulEquiv.apply_symm_apply]

theorem piBCHSubgroup_le_of_factors [Finite α] (F : ∀ a, NilpotentLieFiltration (M a) s)
    (Δ : ∀ a, Subgroup (F a).Group) (Λ : Subgroup (NilpotentLieFiltration.pi F).Group)
    (h : ∀ a, Δ a ≤ Λ.comap (bchPiSingle F a)) : piBCHSubgroup F Δ ≤ Λ := by
  intro g hg
  let Λ' := Λ.comap (bchPiEquiv F).symm.toMonoidHom
  have hp : bchPiEquiv F g ∈ Λ' := by
    apply Subgroup.pi_mem_of_mulSingle_mem
    intro a
    change (bchPiEquiv F).symm (Pi.mulSingle a (bchPiEquiv F g a)) ∈ Λ
    rw [← bchPiSingle_eq_symm_mulSingle]
    exact h a ((mem_piBCHSubgroup F Δ g).mp hg a)
  simpa only [Λ', Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hp

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

variable {α : Type*} [Fintype α] [DecidableEq α] {M : α → Type*}
  [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}
  (F : ∀ a, NilpotentLieFiltration (M a) s)
  {κ : α → Type*} [∀ a, Fintype (κ a)] (f : ∀ a, Basis (κ a) ℚ (M a))

theorem bchPiSingle_comap_inner_grid (Λ : Subgroup (NilpotentLieFiltration.pi F).Group)
    (m : ℕ) (hΛ : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis f) Λ) (a : α) :
    scaledIntegerGrid m ⊆ bchSubgroupCoordinates (f a) (Λ.comap (bchPiSingle F a)) := by
  classical
  rintro x ⟨z, rfl⟩
  change bchPiSingle F a ⟨(f a).equivFun.symm ((m : ℚ) • fun i => (z i : ℚ))⟩ ∈ Λ
  apply (bchSubgroupCoordinates_repr (Pi.basis f) Λ _).mp
  apply hΛ
  refine ⟨fun i : Σ a, κ a => (Pi.single a z : ∀ a, κ a → ℤ) i.1 i.2, ?_⟩
  ext ⟨i, j⟩
  change (f i).repr (Pi.single a ((f a).equivFun.symm ((m : ℚ) • fun k => (z k : ℚ))) i) j = _
  by_cases hi : i = a
  · subst i
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    change (f a).equivFun ((f a).equivFun.symm ((m : ℚ) • fun k => (z k : ℚ))) j = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · simp only [Pi.single_eq_of_ne hi, map_zero, Finsupp.zero_apply, Pi.zero_apply,
      Int.cast_zero, Pi.smul_apply, smul_eq_mul, mul_zero]

theorem exists_factorwise_bch_covers (Γ : ∀ a, Subgroup (F a).Group) (l : α → ℕ)
    (hl : ∀ a, 0 < l a)
    (hΓin : ∀ a, scaledIntegerGrid (l a) ⊆ bchSubgroupCoordinates (f a) (Γ a))
    (hΓout : ∀ a, bchSubgroupCoordinates (f a) (Γ a) ⊆ denominatorGrid (l a))
    (Λ : Subgroup (NilpotentLieFiltration.pi F).Group) (m : ℕ) (hm : 0 < m)
    (hΛ : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis f) Λ)
    {p : ℝ} (hp : 0 ≤ p) (hd : ∀ a, (Fintype.card (κ a) : ℝ) ≤ p)
    (hlp : ∀ a, (l a : ℝ) ≤ Real.exp p) (hmp : (m : ℝ) ≤ Real.exp p) :
    ∃ (Δ : ∀ a, Subgroup (F a).Group) (N : α → ℕ),
      (∀ a, Δ a ≤ Γ a ∧ ((Δ a).subgroupOf (Γ a)).Characteristic ∧
        ((Δ a).subgroupOf (Γ a)).Normal ∧ ((Δ a).subgroupOf (Γ a)).FiniteIndex ∧
        ((Δ a).relIndex (Γ a) : ℝ) ≤ Real.exp (2 * p ^ 2) ∧
        0 < N a ∧ (N a : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
        scaledIntegerGrid (N a) ⊆ bchSubgroupCoordinates (f a) (Δ a) ∧
        bchSubgroupCoordinates (f a) (Δ a) ⊆ denominatorGrid (N a)) ∧
      piBCHSubgroup F Δ ≤ Λ := by
  have h := fun a => (F a).exists_normal_cover_exp_quadratic (f a) (Γ a)
    (Λ.comap (bchPiSingle F a)) (l a) m (hl a) hm (hΓin a) (hΓout a)
    (bchPiSingle_comap_inner_grid F f Λ m hΛ a) hp (hd a) (hlp a) hmp
  choose Δ htarget hΔ hchar hnormal hfinite hindex N hN hNb hin hout using h
  exact ⟨Δ, N, fun a => ⟨hΔ a, hchar a, hnormal a, hfinite a, hindex a,
    hN a, hNb a, hin a, hout a⟩, piBCHSubgroup_le_of_factors F Δ Λ htarget⟩

end Erdos3

end

end OAI
