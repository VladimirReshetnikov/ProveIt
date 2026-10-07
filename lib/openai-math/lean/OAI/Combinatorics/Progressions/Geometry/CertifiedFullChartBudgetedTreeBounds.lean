/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.CeilingExponentialTreeBudget
import OAI.Combinatorics.Progressions.Estimates.FiniteClassifiedRepresentatives
import OAI.Combinatorics.Progressions.Estimates.FiniteGradedBranchPrefixLog
import OAI.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeQuotientPolynomial realSymbolGradeEvaluation restrictedMajorCorrection
  fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (budget : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "Good" => FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
  Z left right K₀ Utag poly N budget

private theorem stage_branch_numeric {p budget : ℝ} {r a : ℕ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) (hb : budget ≤ p) (ha : 254 ≤ a) :
    (r : ℝ) * budget ≤ (p + a) ^ a ∧ budget ≤ (p + a) ^ a := by
  have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 2 ≤ a by omega)
  have hbase : 1 ≤ p + a := by linarith
  have hshift : p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg a)
  have hpower : p ^ 2 ≤ (p + a) ^ a :=
    (pow_le_pow_left₀ hp hshift 2).trans (pow_le_pow_right₀ hbase (by omega))
  have hprod : (r : ℝ) * budget ≤ p * p :=
    (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg r)).trans
      (mul_le_mul_of_nonneg_right hr hp)
  refine ⟨hprod.trans (by simpa only [pow_two] using hpower), ?_⟩
  exact hb.trans (hshift.trans (by simpa only [pow_one] using
    (pow_le_pow_right₀ hbase (show 1 ≤ a by omega))))

private theorem exists_full_chart_optional_stage_branch
    (q : ℕ) (K' : Set Point) (p : ℝ) (blocks a : ℕ) (ha : 254 ≤ a)
    (hcert : RationalTaggedConstraintCertificate J Set.univ K' p blocks)
    (hp : 0 ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p) (hblocks : (blocks : ℝ) ≤ p)
    (hretained : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ Utag j) → point ∈ K₀)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) (hq : 0 < q)
    (hqcap : (q : ℝ) ≤ Real.exp ((p + a) ^ a)) (hbudget : budget ≤ (p + a) ^ a) :
    ∃ c : ℕ, (c : ℝ) ≤ Real.exp
        ((p + fullChartStageCountConstant k a) ^ fullChartStageCountConstant k a) ∧
      ∃ candidate : Fin c → VP × VP, (∀ j, Good q K' (candidate j)) ∧
        ∀ pair, Good q K' pair → ∃ j, ∀ t ∈ K',
          eval₂ t (candidate j).1 = eval₂ t pair.1 ∧
          eval₂ t (candidate j).2 = eval₂ t pair.2 ∧
          eval₂ t (realChartSubstitute chart (candidate j).1) =
            eval₂ t (realChartSubstitute chart pair.1) := by
  by_cases hex : ∃ pair, Good q K' pair
  · obtain ⟨pair, hpair⟩ := hex
    have hret : ∀ point, (∀ j, (fun z => point (Sum.inr ⟨j, z⟩)) ∈ Utag j) →
        point ∈ K' := by
      unfold FullChartAdmissibleStageCorrection at hpair
      rcases hpair with ⟨_, _, _, _, _, _, _, _, hretain, _⟩
      intro point hpoint
      exact hretain point (hretained point hpoint) hpoint
    exact exists_full_chart_finite_stage_representatives F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget q K' p blocks a ha hcert hp hX hJ hη hblocks
      hret hpoly hN hq hqcap hbudget
  · refine ⟨0, by simpa using Real.exp_nonneg _, Fin.elim0, ?_, ?_⟩
    · intro j; exact Fin.elim0 j
    · intro pair hpair; exact (hex ⟨pair, hpair⟩).elim

theorem exists_full_chart_finite_stage_branches
    {past p : ℝ} {blocks : ℕ}
    (a : ℕ) (ha : 254 ≤ a)
    (hprevious : RationalTaggedConstraintCertificate J Set.univ K₀ past blocks)
    (hp : 0 ≤ p) (hpast : past ≤ p) (hbudget : budget ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : ((blocks + Fintype.card η * m : ℕ) : ℝ) ≤ p)
    (hretained : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ Utag j) → point ∈ K₀)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ count : ℕ, (count : ℝ) ≤ Real.exp
        ((Fintype.card η : ℝ) * budget + (p + 8) ^ 8 +
          (p + fullChartStageCountConstant k a) ^ fullChartStageCountConstant k a) ∧
      ∃ candidate : Fin count → (ℕ × Set Point) × (VP × VP),
        (∀ i, Good (candidate i).1.1 (candidate i).1.2 (candidate i).2) ∧
        ∀ q K' pair, Good q K' pair → ∃ i,
          (candidate i).1 = (q, K') ∧ ∀ t ∈ K',
            eval₂ t (candidate i).2.1 = eval₂ t pair.1 ∧
            eval₂ t (candidate i).2.2 = eval₂ t pair.2 ∧
            eval₂ t (realChartSubstitute chart (candidate i).2.1) =
              eval₂ t (realChartSubstitute chart pair.1) := by
  obtain ⟨n, hn, branches, hbranches, hcover⟩ :=
    exists_fullChart_admissible_stage_branches F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget hprevious hp hpast hbudget hm hJ hblocks
  let validLabel := fun (l : ℕ × Set Point) (pair : VP × VP) => Good l.1 l.2 pair
  let relLabel := fun (l : ℕ × Set Point) (pair pair' : VP × VP) => ∀ t ∈ l.2,
    eval₂ t pair.1 = eval₂ t pair'.1 ∧ eval₂ t pair.2 = eval₂ t pair'.2 ∧
    eval₂ t (realChartSubstitute chart pair.1) = eval₂ t (realChartSubstitute chart pair'.1)
  let valid := fun i => validLabel (branches i)
  let rel := fun i => relLabel (branches i)
  have hnum := stage_branch_numeric hp hη hbudget ha
  have hbranch : ∀ i : Fin n, ∃ c : ℕ,
      (c : ℝ) ≤ Real.exp ((p + fullChartStageCountConstant k a) ^ fullChartStageCountConstant k a) ∧
      ∃ candidate : Fin c → VP × VP, (∀ j, valid i (candidate j)) ∧
        ∀ pair, valid i pair → ∃ j, rel i (candidate j) pair := by
    intro i
    dsimp only [valid, rel, validLabel, relLabel]
    exact exists_full_chart_optional_stage_branch F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget (branches i).1 (branches i).2
      p (blocks + Fintype.card η * m) a ha (hbranches i).2.2 hp hX hJ hη hblocks
      hretained hpoly hN (hbranches i).1
      (((Nat.cast_le.mpr (hbranches i).2.1).trans (Nat.floor_le (Real.exp_nonneg _))).trans
        (Real.exp_le_exp.mpr hnum.1)) hnum.2
  obtain ⟨count, hcount, candidate, hvalid, hcomplete⟩ :=
    exists_finite_classified_representatives branches validLabel relLabel
      (fun l pair => hcover l.1 l.2 pair) hbranch
  refine ⟨count, ?_, candidate, hvalid, fun q K' pair => hcomplete (q, K') pair⟩
  exact (hcount.trans (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _))).trans_eq
    (Real.exp_add _ _).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteStageTreeLogBound (depth : ℕ) (Cstage : ℕ → ℕ) (p : ℝ) : ℝ :=
  p ^ 2 + (p + 8) ^ 8 +
    ∑ n ∈ Finset.range depth, (p + Cstage (n + 1)) ^ Cstage (n + 1)

theorem finiteStageTreeLogBound_nonneg (depth : ℕ) (Cstage : ℕ → ℕ)
    {p : ℝ} (hp : 0 ≤ p) : 0 ≤ finiteStageTreeLogBound depth Cstage p := by
  unfold finiteStageTreeLogBound
  exact add_nonneg (add_nonneg (sq_nonneg _) (by positivity))
    (Finset.sum_nonneg (fun _ _ => pow_nonneg (by positivity) _))

theorem finiteStageTree_stage_log_le (depth : ℕ) (Cstage : ℕ → ℕ)
    {p budget : ℝ} {r n : ℕ} (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p)
    (hbudget : budget ≤ p) (hn : n < depth) :
    (r : ℝ) * budget + (p + 8) ^ 8 +
        (p + Cstage (n + 1)) ^ Cstage (n + 1) ≤
      finiteStageTreeLogBound depth Cstage p := by
  have hprod : (r : ℝ) * budget ≤ p ^ 2 := by
    simpa only [pow_two] using
      (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg r)).trans
        (mul_le_mul_of_nonneg_right hr hp)
  have hterm : (p + Cstage (n + 1)) ^ Cstage (n + 1) ≤
      ∑ j ∈ Finset.range depth, (p + Cstage (j + 1)) ^ Cstage (j + 1) :=
    Finset.single_le_sum (f := fun j => (p + Cstage (j + 1)) ^ Cstage (j + 1))
      (fun _ _ => pow_nonneg (by positivity) _) (Finset.mem_range.mpr hn)
  exact add_le_add (add_le_add hprod le_rfl) hterm

theorem exists_finite_stage_tree_budget (depth : ℕ) (Cstage : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      finiteStageTreeLogBound depth Cstage p ≤ (p + C) ^ C ∧
      ((((depth + 1) * (max 1 ⌈Real.exp (finiteStageTreeLogBound depth Cstage p)⌉₊) ^ depth : ℕ) : ℝ)) ≤
        Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let P := X ^ 2 + (X + 8) ^ 8 +
    ∑ n ∈ Finset.range depth,
      (X + Polynomial.C (Cstage (n + 1))) ^ Cstage (n + 1)
  let Q := P + Polynomial.C (depth + 1) + Polynomial.C depth * (P + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro p hp
  let b := finiteStageTreeLogBound depth Cstage p
  have hb : 0 ≤ b := finiteStageTreeLogBound_nonneg depth Cstage hp
  have hsum : b + ((depth : ℝ) + 1) + (depth : ℝ) * (b + 1) ≤ (p + C) ^ C := by
    simpa [Q, P, X, b, finiteStageTreeLogBound, Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum] using hbudget p hp
  have hrest : 0 ≤ ((depth : ℝ) + 1) + (depth : ℝ) * (b + 1) := by positivity
  refine ⟨by dsimp only [b] at *; linarith, ?_⟩
  exact (ceiling_exp_tree_vertices_le depth hb).trans
    (Real.exp_le_exp.mpr (by linarith))

namespace NilpotentLieFiltration

noncomputable def fullChartFiniteTreeLogBound (depth : ℕ) (p : ℝ) : ℝ :=
  finiteStageTreeLogBound depth (fun k => fullChartStageCountConstant k 254) p

noncomputable def fullChartFiniteTreeBranching (depth : ℕ) (p : ℝ) : ℕ :=
  ⌈Real.exp (fullChartFiniteTreeLogBound depth p)⌉₊

theorem fullChartFiniteTree_branch_count_le (depth : ℕ)
    {p budget : ℝ} {r n count : ℕ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) (hbudget : budget ≤ p) (hn : n < depth)
    (hcount : (count : ℝ) ≤ Real.exp
      ((r : ℝ) * budget + (p + 8) ^ 8 +
        (p + fullChartStageCountConstant (n + 1) 254) ^
          fullChartStageCountConstant (n + 1) 254)) :
    count ≤ fullChartFiniteTreeBranching depth p := by
  apply ceil_exp_branch_count
  exact hcount.trans (Real.exp_le_exp.mpr
    (finiteStageTree_stage_log_le depth (fun k => fullChartStageCountConstant k 254)
      hp hr hbudget hn))

theorem exists_fullChartFiniteTree_budget (depth : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      fullChartFiniteTreeLogBound depth p ≤ (p + C) ^ C ∧
      ((((depth + 1) * (max 1 (fullChartFiniteTreeBranching depth p)) ^ depth : ℕ) : ℝ)) ≤
        Real.exp ((p + C) ^ C) :=
  exists_finite_stage_tree_budget depth (fun k => fullChartStageCountConstant k 254)

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

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
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def AdmissibleChild {n : ℕ} (H : State n) (Hnext : State (n + 1)) : Prop :=
  FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N Bphase (Hnext.q n) Hnext.K
      (Hnext.slow n, Hnext.rat n) ∧
  ∀ j < n, Hnext.slow j = H.slow j ∧ Hnext.rat j = H.rat j ∧ Hnext.q j = H.q j

def RepresentsCorrection {n : ℕ} (Hnext : State (n + 1)) (q : ℕ)
    (K' : Set Point) (pair : VP × VP) : Prop :=
  Hnext.q n = q ∧ Hnext.K = K' ∧ ∀ t ∈ K',
    eval₂ t (Hnext.slow n) = eval₂ t pair.1 ∧
    eval₂ t (Hnext.rat n) = eval₂ t pair.2 ∧
    eval₂ t (realChartSubstitute chart (Hnext.slow n)) =
      eval₂ t (realChartSubstitute chart pair.1)

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}

omit [Fintype X] in
theorem append_admissible_is_child {n : ℕ} (H : State n) (q : ℕ)
    (K' : Set Point) (pair : VP × VP)
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N Bphase q K' pair) :
    AdmissibleChild F b ω hF J fast basis lift Z Utag poly N Bphase H
      (H.append_admissible Bphase le_rfl q K' pair hpair) := by
  refine ⟨?_, fun j hj => append_admissible_prefix H Bphase le_rfl q K' pair hpair j hj⟩
  rw [append_admissible_K, (append_admissible_entry H Bphase le_rfl q K' pair hpair).1,
    (append_admissible_entry H Bphase le_rfl q K' pair hpair).2.1,
    (append_admissible_entry H Bphase le_rfl q K' pair hpair).2.2]
  exact hpair

theorem exists_finite_children {n : ℕ} (H : State n)
    {p : ℝ} (hp : 0 ≤ p) (hbudget : Bphase ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : (((n + 1) * (Fintype.card η * m) : ℕ) : ℝ) ≤ p)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ children : Finset (State (n + 1)),
      (children.card : ℝ) ≤ Real.exp
        ((Fintype.card η : ℝ) * Bphase + (p + 8) ^ 8 +
          (p + fullChartStageCountConstant (n + 1) 254) ^
            fullChartStageCountConstant (n + 1) 254) ∧
      (∀ Hnext ∈ children, AdmissibleChild F b ω hF J fast basis lift Z
        Utag poly N Bphase H Hnext) ∧
      ∀ q K' pair, FullChartAdmissibleStageCorrection F b ω hF J (n + 1)
        fast basis lift Z H.outer.1 H.outer.2 H.K Utag poly N Bphase q K' pair →
        ∃ Hnext ∈ children, RepresentsCorrection F b ω hF J fast basis lift Z
          Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨count, hcount, candidate, hgood, hcover⟩ :=
    exists_full_chart_finite_stage_branches F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N Bphase 254 (by omega)
      H.certificate hp hbudget hbudget hX hm hJ hη
      (by simpa only [Nat.succ_mul] using hblocks)
      (fun point hpoint => H.retained point (Set.mem_univ _) hpoint) hpoly hN
  let next (i : Fin count) : State (n + 1) :=
    H.append_admissible Bphase le_rfl (candidate i).1.1 (candidate i).1.2
      (candidate i).2 (hgood i)
  refine ⟨Finset.univ.image next, ?_, ?_, ?_⟩
  · exact (Nat.cast_le.mpr ((Finset.card_image_le).trans_eq
      (Finset.card_fin count))).trans hcount
  · intro Hnext hmem
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
    exact append_admissible_is_child H _ _ _ (hgood i)
  · intro q K' pair hpair
    obtain ⟨i, hlabel, heval⟩ := hcover q K' pair hpair
    refine ⟨next i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    have hentry := append_admissible_entry H Bphase le_rfl
      (candidate i).1.1 (candidate i).1.2 (candidate i).2 (hgood i)
    refine ⟨hentry.2.2.trans (congrArg Prod.fst hlabel), ?_, ?_⟩
    · exact (append_admissible_K H Bphase le_rfl _ _ _ (hgood i)).trans
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
open scoped TensorProduct Classical

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
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

structure FiniteBranchTree (depth : ℕ) (p : ℝ) where
  children : ∀ n, State n → Finset (State (n + 1))
  card : ∀ n, n < depth → ∀ H, (children n H).card ≤
    ⌈Real.exp ((Fintype.card η : ℝ) * Bphase + (p + 8) ^ 8 +
      (p + fullChartStageCountConstant (n + 1) 254) ^
        fullChartStageCountConstant (n + 1) 254)⌉₊
  admissible : ∀ n, n < depth → ∀ H Hnext, Hnext ∈ children n H →
    AdmissibleChild F b ω hF J fast basis lift Z Utag poly N Bphase H Hnext
  complete : ∀ n, n < depth → ∀ H q K' pair,
    FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N Bphase q K' pair →
    ∃ Hnext ∈ children n H, RepresentsCorrection F b ω hF J fast basis lift Z
      Utag poly N Bphase Hnext q K' pair

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}

theorem exists_finite_branch_tree (depth : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hbudget : Bphase ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : ((depth * (Fintype.card η * m) : ℕ) : ℝ) ≤ p)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    Nonempty (FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p) := by
  have hstage (n : ℕ) (hn : n < depth) (H : State n) :=
    exists_finite_children H hp hbudget hX hm hJ hη
      ((Nat.cast_le.mpr (Nat.mul_le_mul_right (Fintype.card η * m)
        (Nat.succ_le_of_lt hn))).trans hblocks) hpoly hN
  let children : ∀ n, State n → Finset (State (n + 1)) := fun n H =>
    if hn : n < depth then Classical.choose (hstage n hn H) else ∅
  refine ⟨{ children := children, card := ?_, admissible := ?_, complete := ?_ }⟩
  · intro n hn H
    dsimp only [children]
    rw [dite_eq_left hn]
    exact_mod_cast (Classical.choose_spec (hstage n hn H)).1.trans (Nat.le_ceil _)
  · intro n hn H Hnext hmem
    have hm' : Hnext ∈ Classical.choose (hstage n hn H) := by
      simpa only [children, dite_eq_left hn] using hmem
    exact (Classical.choose_spec (hstage n hn H)).2.1 Hnext hm'
  · intro n hn H q K' pair hpair
    obtain ⟨Hnext, hmem, hrep⟩ := (Classical.choose_spec (hstage n hn H)).2.2 q K' pair hpair
    exact ⟨Hnext, by simpa only [children, dite_eq_left hn] using hmem, hrep⟩

variable (F b ω hF J fast basis lift Z Utag poly N Bphase)

noncomputable def univInitialHistory : State 0 :=
  initial F b ω hF J fast basis lift Z Set.univ Utag poly N Bphase
    (fun _ _ _ => Set.mem_univ _)

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}
variable {depth : ℕ} {p : ℝ}

noncomputable def FiniteBranchTree.level
    (T : FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p)
    (n : ℕ) : Finset (State n) :=
  finiteGradedBranchLevel (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children n

noncomputable def FiniteBranchTree.vertices
    (T : FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p) :
    Finset (Σ n : Fin (depth + 1), State n.val) :=
  finiteGradedBranchVertices (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children depth

noncomputable def fullChartTreeBranchCap (depth : ℕ) (dim : ℕ) (Bphase p : ℝ) : ℕ :=
  (Finset.range depth).sup (fun n =>
    ⌈Real.exp ((dim : ℝ) * Bphase + (p + 8) ^ 8 +
      (p + fullChartStageCountConstant (n + 1) 254) ^
        fullChartStageCountConstant (n + 1) 254)⌉₊)

omit [Fintype X] in
theorem FiniteBranchTree.card_children_le
    (T : FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p)
    (n : ℕ) (hn : n < depth) (H : State n) :
    (T.children n H).card ≤ fullChartTreeBranchCap depth (Fintype.card η) Bphase p :=
by
  apply (T.card n hn H).trans
  exact Finset.le_sup (f := fun n => ⌈Real.exp ((Fintype.card η : ℝ) * Bphase + (p + 8) ^ 8 +
    (p + fullChartStageCountConstant (n + 1) 254) ^
      fullChartStageCountConstant (n + 1) 254)⌉₊) (Finset.mem_range.mpr hn)

omit [Fintype X] in
theorem FiniteBranchTree.card_level_le
    (T : FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p)
    (n : ℕ) (hn : n ≤ depth) :
    (T.level n).card ≤ (fullChartTreeBranchCap depth (Fintype.card η) Bphase p) ^ n :=
  finiteGradedBranchLevel_card_le_pow _ T.children depth _
    (fun n hn H _ => T.card_children_le n hn H) n hn

omit [Fintype X] in
theorem FiniteBranchTree.card_vertices_le
    (T : FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p) :
    T.vertices.card ≤ (depth + 1) *
      (max 1 (fullChartTreeBranchCap depth (Fintype.card η) Bphase p)) ^ depth :=
  finiteGradedBranchVertices_card_le _ T.children depth _
    (fun n hn H _ => T.card_children_le n hn H)

omit [Fintype X] in

theorem FiniteBranchTree.exists_representative_child
    (T : FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p)
    {n : ℕ} (hn : n < depth) {H : State n} (hH : H ∈ T.level n)
    (q : ℕ) (K' : Set Point) (pair : VP × VP)
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N Bphase q K' pair) :
    ∃ Hnext ∈ T.level (n + 1),
      AdmissibleChild F b ω hF J fast basis lift Z Utag poly N Bphase H Hnext ∧
      RepresentsCorrection F b ω hF J fast basis lift Z Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨Hnext, hmem, hrep⟩ := T.complete n hn H q K' pair hpair
  exact ⟨Hnext, finiteGradedBranchLevel_child_mem _ T.children hH hmem,
    T.admissible n hn H Hnext hmem, hrep⟩

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

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
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def AdmissibleChildAt (budget : ℝ) {n : ℕ} (H : State n) (Hnext : State (n + 1)) : Prop :=
  FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget (Hnext.q n) Hnext.K
      (Hnext.slow n, Hnext.rat n) ∧
  ∀ j < n, Hnext.slow j = H.slow j ∧ Hnext.rat j = H.rat j ∧ Hnext.q j = H.q j

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}

omit [Fintype X] in
theorem append_admissible_is_child_at {n : ℕ} (H : State n)
    (budget : ℝ) (hcap : budget ≤ Bphase) (q : ℕ)
    (K' : Set Point) (pair : VP × VP)
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    AdmissibleChildAt F b ω hF J fast basis lift Z Utag poly N Bphase budget H
      (H.append_admissible budget hcap q K' pair hpair) := by
  refine ⟨?_, fun j hj => append_admissible_prefix H budget hcap q K' pair hpair j hj⟩
  rw [append_admissible_K, (append_admissible_entry H budget hcap q K' pair hpair).1,
    (append_admissible_entry H budget hcap q K' pair hpair).2.1,
    (append_admissible_entry H budget hcap q K' pair hpair).2.2]
  exact hpair

theorem exists_finite_children_at_budget {n : ℕ} (H : State n)
    (budget : ℝ) (hcap : budget ≤ Bphase)
    {p : ℝ} (hp : 0 ≤ p) (hpast : Bphase ≤ p) (hbudget : budget ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : (((n + 1) * (Fintype.card η * m) : ℕ) : ℝ) ≤ p)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ children : Finset (State (n + 1)),
      (children.card : ℝ) ≤ Real.exp
        ((Fintype.card η : ℝ) * budget + (p + 8) ^ 8 +
          (p + fullChartStageCountConstant (n + 1) 254) ^
            fullChartStageCountConstant (n + 1) 254) ∧
      (∀ Hnext ∈ children, AdmissibleChildAt F b ω hF J fast basis lift Z
        Utag poly N Bphase budget H Hnext) ∧
      ∀ q K' pair, FullChartAdmissibleStageCorrection F b ω hF J (n + 1)
        fast basis lift Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair →
        ∃ Hnext ∈ children, RepresentsCorrection F b ω hF J fast basis lift Z
          Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨count, hcount, candidate, hgood, hcover⟩ :=
    exists_full_chart_finite_stage_branches F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N budget 254 (by omega)
      H.certificate hp hpast hbudget hX hm hJ hη
      (by simpa only [Nat.succ_mul] using hblocks)
      (fun point hpoint => H.retained point (Set.mem_univ _) hpoint) hpoly hN
  let next (i : Fin count) : State (n + 1) :=
    H.append_admissible budget hcap (candidate i).1.1 (candidate i).1.2
      (candidate i).2 (hgood i)
  refine ⟨Finset.univ.image next, ?_, ?_, ?_⟩
  · exact (Nat.cast_le.mpr ((Finset.card_image_le).trans_eq
      (Finset.card_fin count))).trans hcount
  · intro Hnext hmem
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
    exact append_admissible_is_child_at H budget hcap _ _ _ (hgood i)
  · intro q K' pair hpair
    obtain ⟨i, hlabel, heval⟩ := hcover q K' pair hpair
    refine ⟨next i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    have hentry := append_admissible_entry H budget hcap
      (candidate i).1.1 (candidate i).1.2 (candidate i).2 (hgood i)
    refine ⟨hentry.2.2.trans (congrArg Prod.fst hlabel), ?_, ?_⟩
    · exact (append_admissible_K H budget hcap _ _ _ (hgood i)).trans
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
open scoped TensorProduct Classical

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
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

noncomputable def fullChartTreeExponent (depth : ℕ) : ℕ :=
  Classical.choose (exists_fullChartFiniteTree_budget depth)

theorem fullChartTreeExponent_ge_two (depth : ℕ) : 2 ≤ fullChartTreeExponent depth :=
  (Classical.choose_spec (exists_fullChartFiniteTree_budget depth)).1

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}
variable {depth : ℕ} {p : ℝ}

omit [Fintype X] in
theorem FiniteBranchTree.card_children_le_uniform
    (T : FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p)
    (hp : 0 ≤ p) (hη : (Fintype.card η : ℝ) ≤ p) (hbudget : Bphase ≤ p)
    (n : ℕ) (hn : n < depth) (H : State n) :
    (T.children n H).card ≤ fullChartFiniteTreeBranching depth p := by
  apply (T.card n hn H).trans
  apply Nat.ceil_mono
  exact Real.exp_le_exp.mpr (finiteStageTree_stage_log_le depth
    (fun k => fullChartStageCountConstant k 254) hp hη hbudget hn)

omit [Fintype X] in
theorem FiniteBranchTree.card_vertices_le_exp
    (T : FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p)
    (hp : 0 ≤ p) (hη : (Fintype.card η : ℝ) ≤ p) (hbudget : Bphase ≤ p) :
    (T.vertices.card : ℝ) ≤ Real.exp ((p + fullChartTreeExponent depth) ^ fullChartTreeExponent depth) := by
  have hcard := finiteGradedBranchVertices_card_le
    (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children depth (fullChartFiniteTreeBranching depth p)
    (fun n hn H _ => T.card_children_le_uniform hp hη hbudget n hn H)
  exact (Nat.cast_le.mpr hcard).trans
    ((Classical.choose_spec (exists_fullChartFiniteTree_budget depth)).2 p hp).2

theorem exists_bounded_finite_branch_tree (depth : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hbudget : Bphase ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : ((depth * (Fintype.card η * m) : ℕ) : ℝ) ≤ p)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ T : FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p,
      (T.vertices.card : ℝ) ≤
        Real.exp ((p + fullChartTreeExponent depth) ^ fullChartTreeExponent depth) := by
  obtain ⟨T⟩ := exists_finite_branch_tree (F := F) (b := b) (ω := ω) (hF := hF)
    (J := J) (fast := fast) (basis := basis) (lift := lift) (Z := Z)
    depth hp hbudget hX hm hJ hη hblocks hpoly hN
  exact ⟨T, T.card_vertices_le_exp hp hη hbudget⟩

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer

theorem exists_reached_child_of_major_correlation_witness (m n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
        [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
        (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
        (J : Fin m → Type) [∀ j, Fintype (J j)]
        (fast : Submodule ℚ F.AssociatedGraded)
        (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
        (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast →
      (∀ y, fast.mkQ (lift y) = y) →
      ∀ (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
        (Bphase pTree pPhase Rrank : ℝ) (depth : ℕ)
        (T : FiniteBranchTree F b ω hF J fast basis lift Z U poly N Bphase depth pTree)
        (H : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
          Set.univ U poly N Bphase n),
      n < depth → H ∈ T.level n → (pPhase + C) ^ C ≤ Bphase →
      Nonempty (FullChartMajorCorrelationWitness F b ω hF J (n + 1) fast basis
        Z H.outer.1 H.outer.2 N poly U pPhase Rrank C) →
      ∃ (q : ℕ) (K : Set ((X ⊕ (Σ j, J j)) → ℝ))
        (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
          VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))),
        FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
          Z H.outer.1 H.outer.2 H.K U poly N ((pPhase + C) ^ C) q K pair ∧
        ∃ Hnext ∈ T.level (n + 1),
          AdmissibleChild F b ω hF J fast basis lift Z U poly N Bphase H Hnext ∧
          RepresentsCorrection F b ω hF J fast basis lift Z U poly N Bphase Hnext q K pair := by
  obtain ⟨C, hC, hsource⟩ :=
    exists_certified_full_chart_decomposition_of_major_correlation_witness m (n + 1) (by omega)
  refine ⟨C, hC, ?_⟩
  intro X L ι η _ _ _ _ _ s F b ω hF J _ fast basis lift hfast hsection
    Z U poly N Bphase pTree pPhase Rrank depth T H hn hH hbudget hcorrelation
  have hlower : ∀ t ∈ H.K, ∀ j < n + 1,
      F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
        (H.outer.1⁻¹ * Z * H.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
    intro t ht j hj
    exact H.invariant_outer t ht j (by omega)
  have hdecomposition := hsource F b ω hF J fast basis lift hfast hsection
    Z H.outer.1 H.outer.2 H.K H.dilation hlower N poly U pPhase Rrank hcorrelation
  obtain ⟨q, K, pair, hpair⟩ :=
    CertifiedFullChartDetectedDecomposition.exists_admissible_stage
      F b ω hF J (n + 1) fast basis lift Z H.outer.1 H.outer.2 H.K U poly N
      ((pPhase + C) ^ C) hdecomposition
  refine ⟨q, K, pair, hpair, ?_⟩
  have hpairB := FullChartAdmissibleStageCorrection.mono_budget hpair hbudget
  exact T.exists_representative_child hn hH q K pair hpairB

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

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
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

variable (stageBudget : ℕ → ℝ)

structure BudgetedBranchTree (depth : ℕ) (p : ℝ) where
  children : ∀ n, State n → Finset (State (n + 1))
  card : ∀ n, n < depth → ∀ H, (children n H).card ≤
    ⌈Real.exp ((Fintype.card η : ℝ) * stageBudget n + (p + 8) ^ 8 +
      (p + fullChartStageCountConstant (n + 1) 254) ^
        fullChartStageCountConstant (n + 1) 254)⌉₊
  admissible : ∀ n, n < depth → ∀ H Hnext, Hnext ∈ children n H →
    AdmissibleChildAt F b ω hF J fast basis lift Z Utag poly N Bphase (stageBudget n) H Hnext
  complete : ∀ n, n < depth → ∀ H q K' pair,
    FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N (stageBudget n) q K' pair →
    ∃ Hnext ∈ children n H, RepresentsCorrection F b ω hF J fast basis lift Z
      Utag poly N Bphase Hnext q K' pair

variable {F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget}

theorem exists_budgeted_branch_tree (depth : ℕ)
    (hcaps : ∀ n, n < depth → stageBudget n ≤ Bphase)
    {p : ℝ} (hp : 0 ≤ p) (hbudget : Bphase ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : ((depth * (Fintype.card η * m) : ℕ) : ℝ) ≤ p)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    Nonempty (BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p) := by
  have hstage (n : ℕ) (hn : n < depth) (H : State n) :=
    exists_finite_children_at_budget H (stageBudget n) (hcaps n hn) hp hbudget
      ((hcaps n hn).trans hbudget) hX hm hJ hη
      ((Nat.cast_le.mpr (Nat.mul_le_mul_right (Fintype.card η * m)
        (Nat.succ_le_of_lt hn))).trans hblocks) hpoly hN
  let children : ∀ n, State n → Finset (State (n + 1)) := fun n H =>
    if hn : n < depth then Classical.choose (hstage n hn H) else ∅
  refine ⟨{ children := children, card := ?_, admissible := ?_, complete := ?_ }⟩
  · intro n hn H
    dsimp only [children]
    rw [dite_eq_left hn]
    exact_mod_cast (Classical.choose_spec (hstage n hn H)).1.trans (Nat.le_ceil _)
  · intro n hn H Hnext hmem
    have hm' : Hnext ∈ Classical.choose (hstage n hn H) := by
      simpa only [children, dite_eq_left hn] using hmem
    exact (Classical.choose_spec (hstage n hn H)).2.1 Hnext hm'
  · intro n hn H q K' pair hpair
    obtain ⟨Hnext, hmem, hrep⟩ := (Classical.choose_spec (hstage n hn H)).2.2 q K' pair hpair
    exact ⟨Hnext, by simpa only [children, dite_eq_left hn] using hmem, hrep⟩

variable {depth : ℕ} {p : ℝ}

noncomputable def BudgetedBranchTree.level
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    (n : ℕ) : Finset (State n) :=
  finiteGradedBranchLevel (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children n

noncomputable def BudgetedBranchTree.vertices
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p) :
    Finset (Σ n : Fin (depth + 1), State n.val) :=
  finiteGradedBranchVertices (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children depth

omit [Fintype X] in

theorem BudgetedBranchTree.exists_representative_child
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    {n : ℕ} (hn : n < depth) {H : State n} (hH : H ∈ T.level n)
    (q : ℕ) (K' : Set Point) (pair : VP × VP)
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N (stageBudget n) q K' pair) :
    ∃ Hnext ∈ T.level (n + 1),
      AdmissibleChildAt F b ω hF J fast basis lift Z Utag poly N Bphase (stageBudget n) H Hnext ∧
      RepresentsCorrection F b ω hF J fast basis lift Z Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨Hnext, hmem, hrep⟩ := T.complete n hn H q K' pair hpair
  exact ⟨Hnext, finiteGradedBranchLevel_child_mem _ T.children hH hmem,
    T.admissible n hn H Hnext hmem, hrep⟩

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

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
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}
variable {stageBudget cumulative : ℕ → ℝ} {depth : ℕ} {p : ℝ}

omit [Fintype X] in

theorem BudgetedBranchTree.stage_bounds
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    (hmono : ∀ n < depth, cumulative n ≤ cumulative (n + 1))
    (hcap : ∀ n < depth, stageBudget n ≤ cumulative (n + 1)) :
    ∀ n, n ≤ depth → ∀ H ∈ T.level n, StageBounds stageBudget cumulative H := by
  apply finiteGradedBranchLevel_all_valid
    (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children depth (fun _ H => StageBounds stageBudget cumulative H)
  · unfold univInitialHistory
    exact StageBounds.initial stageBudget cumulative (fun _ _ _ => Set.mem_univ _)
  · intro n hn H _ hH Hnext hnext
    have hadmissible := T.admissible n hn H Hnext hnext
    exact hH.of_admissible_child Hnext hadmissible.2 hadmissible.1
      (hmono n hn) (hcap n hn)

omit [Fintype X] in

theorem BudgetedBranchTree.exists_reached_smaller_budget
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    (hmono : ∀ n < depth, cumulative n ≤ cumulative (n + 1))
    (hcap : ∀ n < depth, stageBudget n ≤ cumulative (n + 1))
    {n : ℕ} (hn : n ≤ depth) {H : State n} (hH : H ∈ T.level n)
    (hprefix : ∀ j < n, stageBudget j ≤ cumulative n) :
    ∃ Hsmall : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
        Set.univ Utag poly N (cumulative n) n,
      Hsmall.K = H.K ∧
      outer F b ω hF J fast basis lift Z Set.univ Utag poly N (cumulative n) Hsmall = H.outer := by
  have hbounds := T.stage_bounds hmono hcap n hn H hH
  exact ⟨hbounds.to_budget hprefix, hbounds.to_budget_K hprefix, hbounds.to_budget_outer hprefix⟩

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI
