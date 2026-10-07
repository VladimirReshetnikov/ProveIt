import OAI.Combinatorics.Progressions.Linear.NativeRankBudget
import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def realLayer (d i : ℕ) : LieIdeal ℝ (ℝ ⊗[ℚ] L) :=
  (F.layerIdeal d i).baseChange ℝ

theorem realLayer_lex_antitone {d e i j : ℕ} (h : d < e ∨ d = e ∧ i ≤ j) :
    F.realLayer e j ≤ F.realLayer d i := Submodule.baseChange_mono ℝ (F.lex_antitone h)

theorem realLayer_congr {d e i j : ℕ} (h : F.layer d i = F.layer e j) :
    F.realLayer d i = F.realLayer e j :=
  le_antisymm (Submodule.baseChange_mono ℝ h.le) (Submodule.baseChange_mono ℝ h.ge)

theorem realLayer_one : F.realLayer 1 0 = ⊤ := by
  have h : F.layerIdeal 1 0 = ⊤ := by
    ext x
    change x ∈ F.layer 1 0 ↔ x ∈ (⊤ : Submodule ℚ L)
    rw [F.one_eq_top]
  simp only [realLayer, h, LieSubmodule.baseChange_top]

theorem realLayer_rank_zero_eq_one (d : ℕ) : F.realLayer d 0 = F.realLayer d 1 :=
  F.realLayer_congr (F.rank_zero_eq_one d)

theorem realLayer_overshoot (d i : ℕ) (h : d < i) : F.realLayer d i = F.realLayer (d + 1) 0 :=
  F.realLayer_congr (F.overshoot d i h)

theorem realLayer_terminal : F.realLayer s (r + 1) = ⊥ := by
  have h : F.layerIdeal s (r + 1) = ⊥ := by
    ext x
    change x ∈ F.layer s (r + 1) ↔ x ∈ (⊥ : Submodule ℚ L)
    rw [F.terminal]
  simp only [realLayer, h, LieSubmodule.baseChange_bot]

theorem lie_realLayer_le (d e i j : ℕ) :
    ⁅F.realLayer d i, F.realLayer e j⁆ ≤ F.realLayer (d + e) (i + j) := by
  have h : ⁅F.layerIdeal d i, F.layerIdeal e j⁆ ≤ F.layerIdeal (d + e) (i + j) := by
    rw [LieSubmodule.lie_le_iff]
    exact fun x hx y hy => F.lie_mem hx hy
  rw [realLayer, realLayer, ← LieSubmodule.lie_baseChange]
  exact Submodule.baseChange_mono ℝ h

theorem realLayer_lie_mem {d e i j : ℕ} {x y : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realLayer d i) (hy : y ∈ F.realLayer e j) :
    ⁅x, y⁆ ∈ F.realLayer (d + e) (i + j) :=
  F.lie_realLayer_le d e i j (LieSubmodule.lie_mem_lie hx hy)

noncomputable def realification : DegreeRankLieFiltration (ℝ ⊗[ℚ] L) s r where
  rank_le_degree := F.rank_le_degree
  layer d i := (F.realLayer d i).toSubmodule.restrictScalars ℚ
  lex_antitone := F.realLayer_lex_antitone
  one_eq_top := by rw [F.realLayer_one]; rfl
  rank_zero_eq_one d := by rw [F.realLayer_rank_zero_eq_one]
  overshoot d i h := by rw [F.realLayer_overshoot d i h]
  lie_mem := F.realLayer_lie_mem
  terminal := by rw [F.realLayer_terminal]; rfl

theorem realification_associatedDegree :
    F.realification.associatedDegree = F.associatedDegree.realification := rfl

theorem realification_subgroup_eq_realificationSubgroup (d i : ℕ) :
    F.realification.subgroup d i =
      NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.associatedDegree.lowerCentralSeries_eq_bot) (F.layerIdeal d i).toLieSubalgebra := by
  ext x
  rfl

theorem rational_inclusion_mem_realLayer {d i : ℕ} {x : L} (hx : x ∈ F.layer d i) :
    rationalLieInclusion x ∈ F.realLayer d i := LieSubmodule.tmul_mem_baseChange_of_mem 1 hx

theorem realificationHom_mem_subgroup {d i : ℕ} {x : F.Group} (hx : x ∈ F.subgroup d i) :
    NilpotentLieBCHGroup.realificationHom x ∈ F.realification.subgroup d i :=
  F.rational_inclusion_mem_realLayer hx

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem realLayer_eq_span {κ : Type*} (d i : ℕ) (b : Basis κ ℚ (F.layer d i)) :
    (F.realLayer d i).toSubmodule =
      Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (b j : L))) := by
  change (F.layer d i).baseChange ℝ = _
  exact (real_span_rational_family (F.layer d i) (fun j => (b j : L))
    (span_submodule_basis _ b)).symm

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem realification_subgroup_closed {ι : Type*} [Fintype ι] (e : Basis ι ℚ L) (d i : ℕ) :
    IsClosed (F.realification.subgroup d i : Set F.realification.Group) := by
  rw [F.realification_subgroup_eq_realificationSubgroup]
  exact NilpotentLieBCHGroup.realificationSubgroup_closed e (F.layerIdeal d i).toLieSubalgebra

omit [T2Space (ℝ ⊗[ℚ] L)] in
theorem realification_subgroup_connected_simplyConnected (d i : ℕ) :
    ConnectedSpace (F.realification.subgroup d i) ∧
      SimplyConnectedSpace (F.realification.subgroup d i) := by
  rw [F.realification_subgroup_eq_realificationSubgroup]
  exact NilpotentLieBCHGroup.realificationSubgroup_connected_simplyConnected
    (F.layerIdeal d i).toLieSubalgebra

theorem realification_layer_lattice_closed_discrete {ι : Type*} [Fintype ι] (e : Basis ι ℚ L)
    (Γ : Subgroup F.Group) (l : ℕ) (hl : 0 < l)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (d i : ℕ) :
    let Λ := (Γ.map NilpotentLieBCHGroup.realificationHom).comap (F.realification.subgroup d i).subtype
    IsClosed (Λ : Set (F.realification.subgroup d i)) ∧
      IsDiscrete (Λ : Set (F.realification.subgroup d i)) := by
  rw [F.realification_subgroup_eq_realificationSubgroup]
  exact NilpotentLieBCHGroup.realificationSubgroup_lattice_closed_discrete e
    (F.layerIdeal d i).toLieSubalgebra Γ l hl houter

omit [T2Space (ℝ ⊗[ℚ] L)] in
theorem realification_layer_lattice_cocompact {ι : Type*} [Fintype ι] (e : Basis ι ℚ L)
    (Γ : Subgroup F.Group) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (d i : ℕ) :
    CompactSpace (F.realification.subgroup d i ⧸
      (Γ.map NilpotentLieBCHGroup.realificationHom).comap (F.realification.subgroup d i).subtype) := by
  rw [F.realification_subgroup_eq_realificationSubgroup]
  exact NilpotentLieBCHGroup.realificationSubgroup_lattice_cocompact e
    (F.layerIdeal d i).toLieSubalgebra Γ l hl hinner houter

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}

structure DegreeRankStructure (D : RationalFilteredNilmanifold L s d) (r : ℕ) where
  filtration : DegreeRankLieFiltration L s r
  associated : filtration.associatedDegree = D.filtration
  basis : ∀ i j : Fin (s + 1),
    Basis (Fin (finrank ℚ (filtration.layer i.val j.val))) ℚ (filtration.layer i.val j.val)

namespace DegreeRankStructure

variable {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

def ComplexityLE (p : ℝ) : Prop :=
  D.GeometryComplexityLE p ∧ ∀ i j a k, rationalLogHeight (D.basis.repr (R.basis i j a : L) k) ≤ p

theorem ComplexityLE.mono {p q : ℝ} (hR : R.ComplexityLE p) (hpq : p ≤ q) : R.ComplexityLE q :=
  ⟨GeometryComplexityLE.mono D hR.1 hpq, fun i j a k => (hR.2 i j a k).trans hpq⟩

theorem real_associated : R.filtration.realification.associatedDegree = D.filtration.realification := by
  rw [R.filtration.realification_associatedDegree, R.associated]

noncomputable def realSubgroup (i j : ℕ) : Subgroup D.RealGroup := R.filtration.realification.subgroup i j

theorem realSubgroup_zero (i : ℕ) : R.realSubgroup i 0 = D.filtration.realification.subgroup i := by
  ext x
  change x.coord ∈ R.filtration.realification.associatedDegree.layer i ↔
    x.coord ∈ D.filtration.realification.layer i
  rw [R.real_associated]

theorem realSubgroup_le_degree (i j : ℕ) : R.realSubgroup i j ≤ D.filtration.realification.subgroup i := by
  intro x hx
  have h := R.filtration.realification.subgroup_le_associatedDegree i j hx
  change x.coord ∈ R.filtration.realification.associatedDegree.layer i at h
  change x.coord ∈ D.filtration.realification.layer i
  rwa [R.real_associated] at h

theorem realSubgroup_lex_antitone {i j a b : ℕ} (h : i < j ∨ i = j ∧ a ≤ b) :
    R.realSubgroup j b ≤ R.realSubgroup i a := R.filtration.realification.subgroup_lex_antitone h

theorem realSubgroup_commutator_mem {i j a b : ℕ} {x y : D.RealGroup}
    (hx : x ∈ R.realSubgroup i a) (hy : y ∈ R.realSubgroup j b) :
    x * y * x⁻¹ * y⁻¹ ∈ R.realSubgroup (i + j) (a + b) :=
  R.filtration.realification.subgroup_commutator_mem hx hy

theorem realSubgroup_terminal : R.realSubgroup s (r + 1) = ⊥ :=
  R.filtration.realification.subgroup_terminal

noncomputable def orbitEquiv {σ : Type*} (w : σ → ℕ) :
    D.filtration.realification.PolynomialOrbit w ≃*
      R.filtration.realification.associatedDegree.PolynomialOrbit w :=
  D.filtration.realification.orbitEquivOfEq R.real_associated.symm w

theorem orbitEquiv_eval {σ : Type*} (w : σ → ℕ)
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    R.filtration.realification.associatedDegree.polynomialOrbitEval w x (R.orbitEquiv w g) =
      D.filtration.realification.polynomialOrbitEval w x g :=
  D.filtration.realification.orbitEquivOfEq_eval R.real_associated.symm w g x

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem realSubgroup_closed (i j : ℕ) : IsClosed (R.realSubgroup i j : Set D.RealGroup) :=
  R.filtration.realification_subgroup_closed D.basis i j

omit [T2Space (ℝ ⊗[ℚ] L)] in
theorem realSubgroup_connected_simplyConnected (i j : ℕ) :
    ConnectedSpace (R.realSubgroup i j) ∧ SimplyConnectedSpace (R.realSubgroup i j) :=
  R.filtration.realification_subgroup_connected_simplyConnected i j

theorem realSubgroup_lattice_closed_discrete (i j : ℕ) :
    let Λ := D.realLattice.comap (R.realSubgroup i j).subtype
    IsClosed (Λ : Set (R.realSubgroup i j)) ∧ IsDiscrete (Λ : Set (R.realSubgroup i j)) :=
  R.filtration.realification_layer_lattice_closed_discrete D.basis D.lattice D.grid D.grid_pos
    D.outer_grid i j

omit [T2Space (ℝ ⊗[ℚ] L)] in
theorem realSubgroup_lattice_cocompact (i j : ℕ) :
    CompactSpace (R.realSubgroup i j ⧸ D.realLattice.comap (R.realSubgroup i j).subtype) :=
  R.filtration.realification_layer_lattice_cocompact D.basis D.lattice D.grid D.grid_pos
    D.inner_grid D.outer_grid i j

end DegreeRankStructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

namespace DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r t : ℕ}

def withRank (F : DegreeRankLieFiltration L s r) (ht : t ≤ s)
    (hterminal : F.layer s (t + 1) = ⊥) : DegreeRankLieFiltration L s t where
  rank_le_degree := ht
  layer := F.layer
  lex_antitone := F.lex_antitone
  one_eq_top := F.one_eq_top
  rank_zero_eq_one := F.rank_zero_eq_one
  overshoot := F.overshoot
  lie_mem := F.lie_mem
  terminal := hterminal

end DegreeRankLieFiltration

namespace RationalFilteredNilmanifold.DegreeRankStructure

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r t d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

noncomputable def withRank (R : D.DegreeRankStructure r) (ht : t ≤ s)
    (hterminal : R.filtration.layer s (t + 1) = ⊥) : D.DegreeRankStructure t where
  filtration := R.filtration.withRank ht hterminal
  associated := R.associated
  basis := R.basis

theorem withRank_complexity (R : D.DegreeRankStructure r) (ht : t ≤ s)
    (hterminal : R.filtration.layer s (t + 1) = ⊥) {p : ℝ} (hR : R.ComplexityLE p) :
    (R.withRank ht hterminal).ComplexityLE p := hR

end RationalFilteredNilmanifold.DegreeRankStructure

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_native_degree_rank_structure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ R : D.DegreeRankStructure s, R.filtration = D.filtration.canonicalDegreeRank ∧
        R.ComplexityLE ((p + C) ^ C) := by
  obtain ⟨a, _, hbasis⟩ := exists_canonical_rank_basis_budget s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hcost : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hex : ∀ i j : Fin (s + 1),
      ∃ b : Basis (Fin (finrank ℚ (D.filtration.rankLayer i.val j.val))) ℚ
          (D.filtration.rankLayer i.val j.val),
        ∀ k l, rationalLogHeight (D.basis.repr (b k : L) l) ≤ (p + a) ^ a := by
    intro i j
    obtain ⟨b, _, hb⟩ := hbasis D hp hD i.val j.val (Nat.le_of_lt_succ i.isLt)
    exact ⟨b, hb⟩
  choose b hb using hex
  let R : D.DegreeRankStructure s := {
    filtration := D.filtration.canonicalDegreeRank
    associated := D.filtration.canonicalDegreeRank_associatedDegree_eq
    basis := b }
  refine ⟨R, rfl, hD.mono D (by linarith), ?_⟩
  intro i j k l
  exact (hb i j k l).trans (by linarith)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t r d : ℕ}

theorem raiseStep_rankSubgroup_eq_bot (D : RationalFilteredNilmanifold L t d)
    (hts : t < s) (R : (D.raiseStep hts.le).DegreeRankStructure r) (j : ℕ) :
    R.realSubgroup s j = ⊥ := by
  apply bot_unique
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply NilpotentLieBCHGroup.ext
  change x.coord = 0
  have hm := R.realSubgroup_le_degree s j hx
  change x.coord ∈ D.filtration.realification.layer s at hm
  simpa only [D.filtration.realification.layer_eq_bot_above_step hts, Submodule.mem_bot] using hm

theorem exists_raised_degree_rank_structure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {t r d : ℕ}
      (D : RationalFilteredNilmanifold L t d) (hts : t < s), r ≤ s →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∃ R : (D.raiseStep hts.le).DegreeRankStructure r,
        R.ComplexityLE ((p + C) ^ C) ∧ R.realSubgroup s r = ⊥ := by
  obtain ⟨C, hC, hcanonical⟩ := exists_native_degree_rank_structure s
  refine ⟨C, hC, ?_⟩
  intro L _ _ t r d D hts hrs p hp hD
  obtain ⟨A, _, hA⟩ := hcanonical (D.raiseStep hts.le) hp (D.raiseStep_geometry hts.le hD)
  have hzero (j : ℕ) : A.filtration.layer s j = ⊥ := by
    apply bot_unique
    have h := A.filtration.layer_le_associatedDegree s j
    rw [A.associated] at h
    exact h.trans (D.filtration.layer_eq_bot_above_step hts).le
  let R := A.withRank hrs (hzero (r + 1))
  exact ⟨R, A.withRank_complexity hrs (hzero (r + 1)) hA,
    D.raiseStep_rankSubgroup_eq_bot hts R r⟩

namespace Niltest

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {σ : Type*} {w : σ → ℕ} {D : RationalFilteredNilmanifold L t d}

theorem raiseStep_rank_vertical (T : D.Niltest w) (hts : t < s)
    (R : (D.raiseStep hts.le).DegreeRankStructure r)
    (z : (D.raiseStep hts.le).RealGroup) (hz : z ∈ R.realSubgroup s r)
    (x : (D.raiseStep hts.le).Space) :
    (T.raiseStep hts.le).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
          (T.raiseStep hts.le).observable x := by
  rw [D.raiseStep_rankSubgroup_eq_bot hts R r] at hz
  have hz' : z = 1 := Subgroup.mem_bot.mp hz
  subst z
  simp

end Niltest

end Erdos3.RationalFilteredNilmanifold

end

end OAI
