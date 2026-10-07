/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartBudgetedTreeBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

theorem exists_finite_children_of_stage_bounds {n : ℕ} (H : State n)
    {cap cumulative : ℕ → ℝ} (hH : StageBounds cap cumulative H)
    (hcap : cap n ≤ Bphase)
    {p : ℝ} (hp : 0 ≤ p) (hpast : cumulative n ≤ p) (hbudget : cap n ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : (((n + 1) * (Fintype.card η * m) : ℕ) : ℝ) ≤ p)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ children : Finset (State (n + 1)),
      (children.card : ℝ) ≤ Real.exp
        ((Fintype.card η : ℝ) * cap n + (p + 8) ^ 8 +
          (p + fullChartStageCountConstant (n + 1) 254) ^
            fullChartStageCountConstant (n + 1) 254) ∧
      (∀ Hnext ∈ children, AdmissibleChildAt F b ω hF J fast basis lift Z
        Utag poly N Bphase (cap n) H Hnext) ∧
      ∀ q K' pair, FullChartAdmissibleStageCorrection F b ω hF J (n + 1)
        fast basis lift Z H.outer.1 H.outer.2 H.K Utag poly N (cap n) q K' pair →
        ∃ Hnext ∈ children, RepresentsCorrection F b ω hF J fast basis lift Z
          Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨count, hcount, candidate, hgood, hcover⟩ :=
    exists_full_chart_finite_stage_branches F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N (cap n) 254 (by omega)
      hH.certificate hp hpast hbudget hX hm hJ hη
      (by simpa only [Nat.succ_mul] using hblocks)
      (fun point hpoint => H.retained point (Set.mem_univ _) hpoint) hpoly hN
  let next (i : Fin count) : State (n + 1) :=
    H.append_admissible (cap n) hcap (candidate i).1.1 (candidate i).1.2
      (candidate i).2 (hgood i)
  refine ⟨Finset.univ.image next, ?_, ?_, ?_⟩
  · exact (Nat.cast_le.mpr ((Finset.card_image_le).trans_eq
      (Finset.card_fin count))).trans hcount
  · intro Hnext hmem
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
    exact append_admissible_is_child_at H (cap n) hcap _ _ _ (hgood i)
  · intro q K' pair hpair
    obtain ⟨i, hlabel, heval⟩ := hcover q K' pair hpair
    refine ⟨next i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    have hentry := append_admissible_entry H (cap n) hcap
      (candidate i).1.1 (candidate i).1.2 (candidate i).2 (hgood i)
    refine ⟨hentry.2.2.trans (congrArg Prod.fst hlabel), ?_, ?_⟩
    · exact (append_admissible_K H (cap n) hcap _ _ _ (hgood i)).trans
        (congrArg Prod.snd hlabel)
    · intro t ht
      change eval₂ t ((next i).slow n) = _ ∧ _
      dsimp only [next]
      rw [hentry.1, hentry.2.1]
      with_reducible exact heval t ht

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical BigOperators

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

noncomputable def stageBranchLog (dim n : ℕ) (cap p : ℝ) : ℝ :=
  (dim : ℝ) * cap + (p + 8) ^ 8 +
    (p + fullChartStageCountConstant (n + 1) 254) ^
      fullChartStageCountConstant (n + 1) 254

theorem stageBranchLog_mono (dim n : ℕ) (cap : ℝ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) : stageBranchLog dim n cap p ≤ stageBranchLog dim n cap q := by
  unfold stageBranchLog
  have hfirst : (p + 8) ^ 8 ≤ (q + 8) ^ 8 := by gcongr
  have hlast : (p + fullChartStageCountConstant (n + 1) 254) ^
      fullChartStageCountConstant (n + 1) 254 ≤
      (q + fullChartStageCountConstant (n + 1) 254) ^
        fullChartStageCountConstant (n + 1) 254 := by gcongr
  exact add_le_add (add_le_add le_rfl hfirst) hlast

theorem stageBranchLog_nonneg (dim n : ℕ) {cap p : ℝ}
    (hcap : 0 ≤ cap) (hp : 0 ≤ p) : 0 ≤ stageBranchLog dim n cap p := by
  unfold stageBranchLog
  positivity

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

theorem exists_prefix_counted_budgeted_branch_tree (depth : ℕ)
    (cap cumulative pCount : ℕ → ℝ) (pTree : ℝ)
    (hpTree : 0 ≤ pTree) (hstorage : Bphase ≤ pTree)
    (hcaps : ∀ n < depth, cap n ≤ Bphase)
    (hmono : ∀ n < depth, cumulative n ≤ cumulative (n + 1))
    (hcap : ∀ n < depth, cap n ≤ cumulative (n + 1))
    (hcount : ∀ n < depth, 0 ≤ pCount n)
    (hpast : ∀ n < depth, cumulative n ≤ pCount n)
    (hbudget : ∀ n < depth, cap n ≤ pCount n)
    (hcountTree : ∀ n < depth, pCount n ≤ pTree)
    (hX : (Fintype.card X : ℝ) ≤ pTree) (hm : (m : ℝ) ≤ pTree)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ pTree)
    (hη : (Fintype.card η : ℝ) ≤ pTree)
    (hblocks : ((depth * (Fintype.card η * m) : ℕ) : ℝ) ≤ pTree)
    (hXlocal : ∀ n < depth, (Fintype.card X : ℝ) ≤ pCount n)
    (hmlocal : ∀ n < depth, (m : ℝ) ≤ pCount n)
    (hJlocal : ∀ n < depth, (Fintype.card (Σ j, J j) : ℝ) ≤ pCount n)
    (hηlocal : ∀ n < depth, (Fintype.card η : ℝ) ≤ pCount n)
    (hblockslocal : ∀ n < depth, (((n + 1) * (Fintype.card η * m) : ℕ) : ℝ) ≤ pCount n)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase cap depth pTree,
      ∀ n, n < depth → ∀ history ∈ T.level n,
        ((T.children n history).card : ℝ) ≤
          Real.exp (stageBranchLog (Fintype.card η) n (cap n) (pCount n)) := by
  have hchildren (n : ℕ) (hn : n < depth) (history : State n) :
      ∃ children : Finset (State (n + 1)),
        (children.card : ℝ) ≤ Real.exp (stageBranchLog (Fintype.card η) n (cap n) pTree) ∧
        (∀ next ∈ children, AdmissibleChildAt F b ω hF J fast basis lift Z
          Utag poly N Bphase (cap n) history next) ∧
        (∀ q K pair, FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
          Z history.outer.1 history.outer.2 history.K Utag poly N (cap n) q K pair →
          ∃ next ∈ children, RepresentsCorrection F b ω hF J fast basis lift Z
            Utag poly N Bphase next q K pair) ∧
        (StageBounds cap cumulative history → (children.card : ℝ) ≤
          Real.exp (stageBranchLog (Fintype.card η) n (cap n) (pCount n))) := by
    by_cases hvalid : StageBounds cap cumulative history
    · obtain ⟨children, hcard, hadmissible, hcomplete⟩ :=
        exists_finite_children_of_stage_bounds history hvalid (hcaps n hn)
          (hcount n hn) (hpast n hn) (hbudget n hn) (hXlocal n hn) (hmlocal n hn)
          (hJlocal n hn) (hηlocal n hn) (hblockslocal n hn) hpoly hN
      refine ⟨children, ?_, hadmissible, hcomplete, fun _ => hcard⟩
      exact hcard.trans (Real.exp_le_exp.mpr
        (stageBranchLog_mono _ _ _ (hcount n hn) (hcountTree n hn)))
    · obtain ⟨children, hcard, hadmissible, hcomplete⟩ :=
        exists_finite_children_at_budget history (cap n) (hcaps n hn) hpTree hstorage
          ((hcaps n hn).trans hstorage) hX hm hJ hη
          ((Nat.cast_le.mpr (Nat.mul_le_mul_right (Fintype.card η * m)
            (Nat.succ_le_of_lt hn))).trans hblocks) hpoly hN
      exact ⟨children, hcard, hadmissible, hcomplete, fun h => (hvalid h).elim⟩
  let children : ∀ n, State n → Finset (State (n + 1)) := fun n history =>
    if hn : n < depth then Classical.choose (hchildren n hn history) else ∅
  let T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase cap depth pTree := {
    children := children
    card := by
      intro n hn history
      dsimp only [children]
      rw [dite_eq_left hn]
      exact_mod_cast (Classical.choose_spec (hchildren n hn history)).1.trans (Nat.le_ceil _)
    admissible := by
      intro n hn history next hmem
      have hm' : next ∈ Classical.choose (hchildren n hn history) := by
        simpa only [children, dite_eq_left hn] using hmem
      exact (Classical.choose_spec (hchildren n hn history)).2.1 next hm'
    complete := by
      intro n hn history q K pair hpair
      obtain ⟨next, hmem, hrep⟩ :=
        (Classical.choose_spec (hchildren n hn history)).2.2.1 q K pair hpair
      exact ⟨next, by simpa only [children, dite_eq_left hn] using hmem, hrep⟩ }
  refine ⟨T, ?_⟩
  intro n hn history hmem
  have hvalid := T.stage_bounds hmono hcap n (Nat.le_of_lt hn) history hmem
  have hsharp := (Classical.choose_spec (hchildren n hn history)).2.2.2 hvalid
  simpa only [T, children, dite_eq_left hn] using hsharp

omit [Fintype X] in

theorem BudgetedBranchTree.card_level_le_prefix_exp
    {cap : ℕ → ℝ} {depth : ℕ} {pTree : ℝ}
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase cap depth pTree)
    (pCount : ℕ → ℝ)
    (hsharp : ∀ n, n < depth → ∀ history ∈ T.level n,
      ((T.children n history).card : ℝ) ≤
        Real.exp (stageBranchLog (Fintype.card η) n (cap n) (pCount n)))
    (n : ℕ) (hn : n ≤ depth) :
    ((T.level n).card : ℝ) ≤ Real.exp
      (∑ j ∈ Finset.range n, stageBranchLog (Fintype.card η) j (cap j) (pCount j)) :=
  finiteGradedBranchLevel_card_le_exp_sum _ T.children depth
    (fun j => stageBranchLog (Fintype.card η) j (cap j) (pCount j)) hsharp n hn

omit [Fintype X] in

theorem BudgetedBranchTree.card_vertices_le_prefix_exp
    {cap : ℕ → ℝ} {depth : ℕ} {pTree : ℝ}
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase cap depth pTree)
    (pCount : ℕ → ℝ)
    (hsharp : ∀ n, n < depth → ∀ history ∈ T.level n,
      ((T.children n history).card : ℝ) ≤
        Real.exp (stageBranchLog (Fintype.card η) n (cap n) (pCount n)))
    (hcap : ∀ j < depth, 0 ≤ cap j) (hp : ∀ j < depth, 0 ≤ pCount j) :
    (T.vertices.card : ℝ) ≤ ((depth + 1 : ℕ) : ℝ) * Real.exp
      (∑ j ∈ Finset.range depth, stageBranchLog (Fintype.card η) j (cap j) (pCount j)) :=
  finiteGradedBranchVertices_card_le_mul_exp_sum _ T.children depth
    (fun j => stageBranchLog (Fintype.card η) j (cap j) (pCount j)) hsharp
    (fun j hj => stageBranchLog_nonneg _ _ (hcap j hj) (hp j hj)) depth le_rfl

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical BigOperators

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}
  {depth : ℕ} {pTree : ℝ}

local notation "Cstage" => fun n => fullChartStageCountConstant (n + 1) 254

theorem BudgetedBranchTree.card_level_le_forward_prefix
    (A : ℕ) {x : ℝ} (hx : 0 ≤ x) (hd : (Fintype.card η : ℝ) ≤ x)
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase
      (fun n => preparedFiniteForwardCap A Cstage n x) depth pTree)
    (hsharp : ∀ n, n < depth → ∀ history ∈ T.level n,
      ((T.children n history).card : ℝ) ≤ Real.exp
        (stageBranchLog (Fintype.card η) n (preparedFiniteForwardCap A Cstage n x)
          (preparedFiniteForwardCount A Cstage n x)))
    (n : ℕ) (hn : n ≤ depth) :
    ((T.level n).card : ℝ) ≤ Real.exp (preparedFiniteForwardPrefixLog A Cstage n x) := by
  apply (T.card_level_le_prefix_exp
    (fun j => preparedFiniteForwardCount A Cstage j x) hsharp n hn).trans
  apply Real.exp_le_exp.mpr
  exact Finset.sum_le_sum (fun j _ =>
    preparedFiniteForward_branch_count_log A Cstage j hx hd)

theorem BudgetedBranchTree.card_reached_type_le_forward_prefix
    (A : ℕ) {x : ℝ} (hx : 0 ≤ x) (hd : (Fintype.card η : ℝ) ≤ x)
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase
      (fun n => preparedFiniteForwardCap A Cstage n x) depth pTree)
    (hsharp : ∀ n, n < depth → ∀ history ∈ T.level n,
      ((T.children n history).card : ℝ) ≤ Real.exp
        (stageBranchLog (Fintype.card η) n (preparedFiniteForwardCap A Cstage n x)
          (preparedFiniteForwardCount A Cstage n x)))
    (n : ℕ) (hn : n ≤ depth) :
    (Fintype.card {history // history ∈ T.level n} : ℝ) ≤
      Real.exp (preparedFiniteForwardPrefixLog A Cstage n x) := by
  simpa only [Fintype.card_coe] using T.card_level_le_forward_prefix A hx hd hsharp n hn

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical BigOperators

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

variable (depth scheduleExponent : ℕ) (x : ℝ)
    (hx : 0 ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hm : (m : ℝ) ≤ x)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ x)
    (hη : (Fintype.card η : ℝ) ≤ x)
    (hblocks : ((depth * (Fintype.card η * m) : ℕ) : ℝ) ≤ x)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i)

local notation "cap" => fun n => preparedFiniteForwardCap scheduleExponent countConstants n x
local notation "cumulative" => fun n => preparedFiniteForwardCumulative scheduleExponent countConstants n x
local notation "count" => fun n => preparedFiniteForwardCount scheduleExponent countConstants n x
local notation "storage" => preparedFiniteForwardParameter scheduleExponent countConstants depth x
local notation "Tree" => BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N
  (cumulative depth) cap depth storage

include hx hX hm hJ hη hblocks hpoly hN

theorem exists_early_forward_branch_tree :
    ∃ T : Tree,
      (∀ n, n < depth → ∀ history ∈ T.level n,
        ((T.children n history).card : ℝ) ≤
          Real.exp (stageBranchLog (Fintype.card η) n (cap n) (count n))) ∧
      (∀ n, n ≤ depth → ((T.level n).card : ℝ) ≤
        Real.exp (preparedFiniteForwardPrefixLog scheduleExponent countConstants n x)) := by
  have hstorage0 := preparedFiniteForwardParameter_nonneg scheduleExponent countConstants depth hx
  have hstorage := (preparedFiniteForward_prefix_bounds scheduleExponent countConstants depth hx).1.2
  have hxtoStorage := le_preparedFiniteForwardParameter scheduleExponent countConstants depth hx
  have hxtoCount (n : ℕ) : x ≤ count n :=
    le_preparedFiniteForwardCount scheduleExponent countConstants n hx
  have hcountTree (n : ℕ) (hn : n < depth) : count n ≤ storage :=
    preparedFiniteForwardCount_le_parameter scheduleExponent countConstants hx hn
  obtain ⟨T, hsharp⟩ := exists_prefix_counted_budgeted_branch_tree
    (F := F) (b := b) (ω := ω) (hF := hF) (J := J)
    (fast := fast) (basis := basis) (lift := lift) (Z := Z)
    depth cap cumulative count storage hstorage0 hstorage
    (fun _ hn => preparedFiniteForwardCap_le_cumulative scheduleExponent countConstants hx hn)
    (fun n _ => preparedFiniteForwardCumulative_le_succ scheduleExponent countConstants n hx)
    (fun n _ => preparedFiniteForwardCap_le_cumulative_succ scheduleExponent countConstants n hx)
    (fun n _ => preparedFiniteForwardCount_nonneg scheduleExponent countConstants n hx)
    (fun n _ => ((preparedFiniteForward_prefix_bounds scheduleExponent countConstants n hx).1.2).trans
      (preparedFiniteForwardParameter_le_count scheduleExponent countConstants n hx))
    (fun n _ => preparedFiniteForwardCap_le_count scheduleExponent countConstants n hx)
    hcountTree (hX.trans hxtoStorage) (hm.trans hxtoStorage) (hJ.trans hxtoStorage)
    (hη.trans hxtoStorage) (hblocks.trans hxtoStorage)
    (fun n _ => hX.trans (hxtoCount n)) (fun n _ => hm.trans (hxtoCount n))
    (fun n _ => hJ.trans (hxtoCount n)) (fun n _ => hη.trans (hxtoCount n))
    (fun n hn => (Nat.cast_le.mpr (Nat.mul_le_mul_right (Fintype.card η * m)
      (Nat.succ_le_of_lt hn))).trans (hblocks.trans (hxtoCount n))) hpoly hN
  exact ⟨T, hsharp, fun n hn =>
    T.card_level_le_forward_prefix scheduleExponent hx hη hsharp n hn⟩

noncomputable def earlyForwardBranchTree : Tree :=
  Classical.choose (exists_early_forward_branch_tree F b ω hF J fast basis lift Z Utag poly N
    depth scheduleExponent x hx hX hm hJ hη hblocks hpoly hN)

local notation "earlyTree" => earlyForwardBranchTree F b ω hF J fast basis lift Z Utag poly N
  depth scheduleExponent x hx hX hm hJ hη hblocks hpoly hN

theorem earlyForwardBranchTree_sharp (n : ℕ) (hn : n < depth)
    (history) (hmem : history ∈ (earlyTree).level n) :
    (((earlyTree).children n history).card : ℝ) ≤
      Real.exp (stageBranchLog (Fintype.card η) n (cap n) (count n)) :=
  (Classical.choose_spec (exists_early_forward_branch_tree F b ω hF J fast basis lift Z Utag poly N
    depth scheduleExponent x hx hX hm hJ hη hblocks hpoly hN)).1 n hn history hmem

theorem earlyForwardBranchTree_card_level (n : ℕ) (hn : n ≤ depth) :
    (((earlyTree).level n).card : ℝ) ≤
      Real.exp (preparedFiniteForwardPrefixLog scheduleExponent countConstants n x) :=
  (Classical.choose_spec (exists_early_forward_branch_tree F b ω hF J fast basis lift Z Utag poly N
    depth scheduleExponent x hx hX hm hJ hη hblocks hpoly hN)).2 n hn

noncomputable abbrev earlyForwardReached (n : ℕ) :=
  {history // history ∈ (earlyTree).level n}

theorem earlyForwardReached_card (n : ℕ) (hn : n ≤ depth) :
    (Fintype.card (earlyForwardReached F b ω hF J fast basis lift Z Utag poly N
      depth scheduleExponent x hx hX hm hJ hη hblocks hpoly hN n) : ℝ) ≤
      Real.exp (preparedFiniteForwardPrefixLog scheduleExponent countConstants n x) := by
  simpa only [earlyForwardReached, Fintype.card_coe] using
    earlyForwardBranchTree_card_level F b ω hF J fast basis lift Z Utag poly N
      depth scheduleExponent x hx hX hm hJ hη hblocks hpoly hN n hn

noncomputable abbrev earlyForwardBranches (stage : Fin (depth + 1)) :=
  earlyForwardReached F b ω hF J fast basis lift Z Utag poly N
    depth scheduleExponent x hx hX hm hJ hη hblocks hpoly hN stage.val

theorem earlyForwardBranches_card (stage : Fin (depth + 1)) :
    (Fintype.card (earlyForwardBranches F b ω hF J fast basis lift Z Utag poly N
      depth scheduleExponent x hx hX hm hJ hη hblocks hpoly hN stage) : ℝ) ≤
      Real.exp (preparedFiniteForwardPrefixLog scheduleExponent countConstants stage.val x) :=
  earlyForwardReached_card F b ω hF J fast basis lift Z Utag poly N
    depth scheduleExponent x hx hX hm hJ hη hblocks hpoly hN stage.val
    (Nat.le_of_lt_succ stage.isLt)

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI
