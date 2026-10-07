/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Compat.TensorProduct
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Order.Interval.Finset.Fin
import OAI.Combinatorics.Progressions.Estimates.RealifiedMultidegree
import OAI.Combinatorics.Progressions.Linear.SpanningFlagSelection
import OAI.Combinatorics.Progressions.Linear.WeightedFlagBasis

namespace OAI

section

namespace Erdos3

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem span_inter_eq_of_spanning_family {η : Type*} (P : Submodule K V)
    (v : η → P) (hspan : Submodule.span K (Set.range v) = ⊤)
    (S : Set V) (hv : ∀ i, (v i : V) ∈ S) :
    Submodule.span K (S ∩ (P : Set V)) = P := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ hx => hx.2)
  · have hmap := congrArg (Submodule.map P.subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap
    conv_lhs => rw [← hmap]
    apply Submodule.span_mono
    rintro x ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨hv i, (v i).property⟩

theorem exists_sorted_flag_basis_from_spanning_set [FiniteDimensional K V] {n : ℕ}
    (P : Fin n → Submodule K V) (hP : Antitone P) (S : Set V)
    (hS : Submodule.span K S = ⊤)
    (hspan : ∀ i, Submodule.span K (S ∩ (P i : Set V)) = P i) :
    ∃ (e : Basis (Fin (finrank K V)) K V) (w : Fin (finrank K V) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ n) ∧ (∀ j, e j ∈ S) ∧
      ∀ i, P i = Submodule.span K (e '' {j | i.val < w j}) := by
  classical
  obtain ⟨B, hBS, hBli, hBspan, T, hT, hTB, hTspan⟩ :=
    exists_nested_independent_spanning_sets n P S hP hspan
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : B → V)) := by
    simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hBspan, hS, le_refl]
  let b : Basis B K V := Basis.mk hBli.linearIndependent_restrict hsp
  let : Finite B := Module.Finite.finite_basis b
  let : Fintype B := Fintype.ofFinite B
  let ρ : B ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  let u : Fin (finrank K V) → ℕ := fun j => nestedSupportWeight T (ρ.symm j).val
  let σ := Tuple.sort u
  let e := b.reindex (ρ.trans σ.symm)
  let w : Fin (finrank K V) → ℕ := fun j => u (σ j)
  have he (j : Fin (finrank K V)) : e j = (ρ.symm (σ j)).val := by
    simp [e, b, Basis.reindex_apply]
  refine ⟨e, w, Tuple.monotone_sort u, fun j => nestedSupportWeight_le T _, ?_, ?_⟩
  · intro j
    rw [he]
    exact hBS (ρ.symm (σ j)).property
  · intro i
    rw [← hTspan i]
    congr 1
    ext x
    constructor
    · intro hx
      let k : B := ⟨x, hTB i hx⟩
      refine ⟨σ.symm (ρ k), ?_, ?_⟩
      · simpa only [Set.mem_ofPred_eq, w, u, Equiv.apply_symm_apply,
          Equiv.symm_apply_apply] using (mem_nestedSupport_iff T hT i x).mp hx
      · simp only [he, Equiv.apply_symm_apply, Equiv.symm_apply_apply, k]
    · rintro ⟨j, hj, rfl⟩
      rw [he]
      exact (mem_nestedSupport_iff T hT i _).mpr hj

end Erdos3

end

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

def basisTail (e : Basis (Fin d) ℚ L) (i : ℕ) : Submodule ℚ L where
  carrier := {x | ∀ j : Fin d, j.val < i → e.repr x j = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro j hj
    simp only [map_add, Finsupp.add_apply, hx j hj, hy j hj, zero_add]
  smul_mem' c x hx := by
    intro j hj
    simp only [map_smul, Finsupp.smul_apply, hx j hj, smul_zero]

theorem basisTail_antitone (e : Basis (Fin d) ℚ L) : Antitone (basisTail e) :=
  fun _ _ hij _ hx k hk => hx k (lt_of_lt_of_le hk hij)

theorem basisTail_zero (e : Basis (Fin d) ℚ L) : basisTail e 0 = ⊤ := by
  apply top_unique
  intro x _ j hj
  omega

theorem basisTail_terminal (e : Basis (Fin d) ℚ L) : basisTail e d = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply e.repr.injective
  ext j
  simpa only [map_zero, Finsupp.zero_apply] using hx j j.isLt

theorem basisTail_eq_span (e : Basis (Fin d) ℚ L) (i : ℕ) :
    basisTail e i = Submodule.span ℚ (e '' {j : Fin d | i ≤ j.val}) := by
  ext x
  rw [e.mem_span_image]
  constructor
  · intro hx j hj
    by_contra h
    exact (Finsupp.mem_support_iff.mp hj) (hx j (Nat.lt_of_not_ge h))
  · intro hx j hj
    by_contra h
    exact (not_le_of_gt hj) (hx (Finsupp.mem_support_iff.mpr h))

theorem basis_mem_tail (e : Basis (Fin d) ℚ L) (j : Fin d) {i : ℕ} (hij : i ≤ j.val) :
    e j ∈ basisTail e i := by
  rw [basisTail_eq_span]
  exact Submodule.subset_span ⟨j, hij, rfl⟩

theorem mem_basisTail_succ_iff (e : Basis (Fin d) ℚ L) (j : Fin d) (x : L) :
    x ∈ basisTail e (j.val + 1) ↔ x ∈ basisTail e j.val ∧ e.repr x j = 0 := by
  constructor
  · intro hx
    exact ⟨basisTail_antitone e (Nat.le_succ j.val) hx, hx j (Nat.lt_succ_self j.val)⟩
  · rintro ⟨hx, hj⟩ k hk
    by_cases hkj : k = j
    · simpa only [hkj] using hj
    · apply hx k
      have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      omega

theorem sub_coordinate_mem_tail (e : Basis (Fin d) ℚ L) (j : Fin d) {x : L}
    (hx : x ∈ basisTail e j.val) :
    x - e.repr x j • e j ∈ basisTail e (j.val + 1) := by
  classical
  intro k hk
  by_cases hkj : k = j
  · subst k
    simp
  · have hlt : k.val < j.val := by
      have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      omega
    simp only [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply,
      hx k hlt, Basis.repr_self, Finsupp.single_eq_of_ne hkj, smul_zero, sub_zero]

def IsCentralLieBasis (e : Basis (Fin d) ℚ L) : Prop :=
  ∀ (j : Fin d) (a : L), ⁅a, e j⁆ ∈ basisTail e (j.val + 1)

namespace IsCentralLieBasis

variable {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
include he

theorem lie_mem_tail_succ (i : ℕ) (a : L) {b : L} (hb : b ∈ basisTail e i) :
    ⁅a, b⁆ ∈ basisTail e (i + 1) := by
  classical
  rw [← e.sum_repr b, lie_sum]
  apply Submodule.sum_mem
  intro j _
  rw [lie_smul]
  by_cases hj : j.val < i
  · rw [hb j hj, zero_smul]
    exact (basisTail e (i + 1)).zero_mem
  · exact (basisTail e (i + 1)).smul_mem _
      (basisTail_antitone e (Nat.add_le_add_right (Nat.le_of_not_gt hj) 1) (he j a))

def tailIdeal (i : ℕ) : LieIdeal ℚ L :=
  { basisTail e i with
    lie_mem := by
      intro a b hb
      exact basisTail_antitone e (Nat.le_succ i) (he.lie_mem_tail_succ i a hb) }

theorem coordinate_lie_eq_zero (i j k : Fin d) (hkj : k.val ≤ j.val) :
    e.repr ⁅e i, e j⁆ k = 0 := he j (e i) k (Nat.lt_succ_of_le hkj)

end IsCentralLieBasis

theorem centralLieBasis_of_sorted_filtration {s : ℕ} (F : NilpotentLieFiltration L s)
    (e : Basis (Fin d) ℚ L) (w : Fin d → ℕ) (hw : Monotone w)
    (hlayer : ∀ i, F.layer i = Submodule.span ℚ (e '' {j | i ≤ w j})) :
    IsCentralLieBasis e := by
  intro j a
  have ha : a ∈ F.layer 1 := by simp [F.one_eq_top]
  have hj : e j ∈ F.layer (w j) := by
    rw [hlayer]
    exact Submodule.subset_span ⟨j, by simp, rfl⟩
  have hbr := F.lie_mem ha hj
  rw [hlayer] at hbr
  rw [basisTail_eq_span]
  apply Submodule.span_mono (Set.image_mono ?_) hbr
  intro k hk
  change j.val + 1 ≤ k.val
  change 1 + w j ≤ w k at hk
  by_contra h
  have hkj : k ≤ j := by change k.val ≤ j.val; omega
  have hweight := hw hkj
  omega

end Erdos3

end

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d n : ℕ}

theorem finite_flag_weight_le (P : ℕ → Submodule ℚ L) (e : Basis (Fin d) ℚ L)
    (w : Fin d → ℕ) (hn : P n = ⊥)
    (hspan : P n = Submodule.span ℚ (e '' {j | n < w j})) (j : Fin d) : w j ≤ n := by
  by_contra h
  have hj : e j ∈ P n := by
    rw [hspan]
    exact Submodule.subset_span ⟨j, Nat.lt_of_not_ge h, rfl⟩
  rw [hn] at hj
  exact e.ne_zero j (by simpa only [Submodule.mem_bot] using hj)

theorem centralLieBasis_of_finite_flag (P : ℕ → Submodule ℚ L)
    (e : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
    (hzero : P 0 = ⊤) (hterminal : P n = ⊥)
    (hstep : ∀ i, ∀ {x y : L}, y ∈ P i → ⁅x, y⁆ ∈ P (i + 1))
    (hw : Monotone w)
    (hspan : ∀ i : Fin (n + 1), P i.val = Submodule.span ℚ (e '' {j | i.val < w j})) :
    IsCentralLieBasis e := by
  intro j a
  have hjn : w j ≤ n := finite_flag_weight_le P e w hterminal (hspan ⟨n, by omega⟩) j
  have hbr : ⁅a, e j⁆ ∈ P (w j) := by
    cases hweight : w j with
    | zero => simp only [hzero, Submodule.mem_top]
    | succ k =>
        apply hstep k
        rw [hspan ⟨k, by omega⟩]
        exact Submodule.subset_span ⟨j, by change k < w j; omega, rfl⟩
  rw [hspan ⟨w j, by omega⟩] at hbr
  rw [basisTail_eq_span]
  apply Submodule.span_mono (Set.image_mono ?_) hbr
  intro k hk
  change j.val + 1 ≤ k.val
  change w j < w k at hk
  by_contra h
  have hkj : k ≤ j := by change k.val ≤ j.val; omega
  exact (not_lt_of_ge (hw hkj)) hk

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

include F

omit [FiniteDimensional ℚ L] in
theorem layer_eq_span_of_weighted_flag {d : ℕ} (e : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
    (hbound : ∀ j, w j ≤ s + 1)
    (hlayer : ∀ i : Fin (s + 1),
      F.layer (i.val + 1) = Submodule.span ℚ (e '' {j | i.val < w j})) :
    ∀ i, F.layer i = Submodule.span ℚ (e '' {j | i ≤ w j}) := by
  intro i
  cases i with
  | zero =>
      have hzero : F.layer 0 = ⊤ := by
        apply top_unique
        rw [← F.one_eq_top]
        exact F.antitone (by omega)
      simp only [hzero, Nat.zero_le, Set.ofPred_true, Set.image_univ, e.span_eq]
  | succ i =>
      by_cases hi : i < s + 1
      · simpa only [Nat.succ_le_iff] using hlayer ⟨i, hi⟩
      · have htail : F.layer (i + 1) = ⊥ := by
          apply bot_unique
          simpa only [F.terminal] using F.antitone (show s + 1 ≤ i + 1 by omega)
        have hempty : {j | i + 1 ≤ w j} = (∅ : Set (Fin d)) := by
          ext j
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          have := hbound j
          omega
        rw [htail, hempty, Set.image_empty, Submodule.span_empty]

theorem exists_sorted_adapted_basis :
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ s + 1) ∧
      ∀ i, F.layer i = Submodule.span ℚ (e '' {j | i ≤ w j}) := by
  let P : Fin (s + 1) → Submodule ℚ L := fun i => F.layer (i.val + 1)
  have hP : Antitone P := fun i j hij => F.antitone (Nat.add_le_add_right hij 1)
  obtain ⟨e, w, hw, hbound, hlayer⟩ := exists_sorted_weighted_flag_basis P hP
  exact ⟨e, w, hw, hbound, F.layer_eq_span_of_weighted_flag e w hbound hlayer⟩

theorem exists_central_basis :
    ∃ e : Basis (Fin (finrank ℚ L)) ℚ L, IsCentralLieBasis e := by
  obtain ⟨e, w, hw, _, hlayer⟩ := F.exists_sorted_adapted_basis
  exact ⟨e, centralLieBasis_of_sorted_filtration F e w hw hlayer⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

noncomputable def weightCut {d : ℕ} (w : Fin d → ℕ) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => w j ≤ k)).card

theorem weightCut_le {d : ℕ} (w : Fin d → ℕ) (k : ℕ) : weightCut w k ≤ d := by
  classical
  simpa only [weightCut, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin d))) (p := fun j => w j ≤ k))

theorem weight_gt_iff_cut_le {d : ℕ} (w : Fin d → ℕ) (hw : Monotone w) (k : ℕ) (j : Fin d) :
    k < w j ↔ weightCut w k ≤ j.val := by
  classical
  let A := Finset.univ.filter (fun i => w i ≤ k)
  constructor
  · intro hj
    have hA : A ⊆ Finset.Iio j := by
      intro i hi
      apply Finset.mem_Iio.mpr
      have hiw : w i ≤ k := (Finset.mem_filter.mp hi).2
      by_contra h
      have := hw (le_of_not_gt h)
      omega
    have hcard := Finset.card_le_card hA
    simpa only [A, Fin.card_Iio, weightCut] using hcard
  · intro hj
    by_contra h
    have hjw : w j ≤ k := le_of_not_gt h
    have hA : Finset.Iic j ⊆ A := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hw (Finset.mem_Iic.mp hi)).trans hjw⟩
    have hcard := Finset.card_le_card hA
    rw [Fin.card_Iic] at hcard
    change j.val + 1 ≤ weightCut w k at hcard
    omega

theorem span_weight_gt_eq_basisTail {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ) (hw : Monotone w) (k : ℕ) :
    Submodule.span ℚ (b '' {j | k < w j}) = basisTail b (weightCut w k) := by
  rw [basisTail_eq_span]
  apply congrArg (Submodule.span ℚ)
  apply congrArg (fun S : Set (Fin d) => b '' S)
  ext j
  exact weight_gt_iff_cut_le w hw k j

end Erdos3

end

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {d : ℕ}

def realBasisTail (e : Basis (Fin d) ℝ L) (i : ℕ) : Submodule ℝ L where
  carrier := {x | ∀ j : Fin d, j.val < i → e.repr x j = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro j hj
    simp only [map_add, Finsupp.add_apply, hx j hj, hy j hj, zero_add]
  smul_mem' c x hx := by
    intro j hj
    simp only [map_smul, Finsupp.smul_apply, hx j hj, smul_zero]

theorem realBasisTail_antitone (e : Basis (Fin d) ℝ L) : Antitone (realBasisTail e) :=
  fun _ _ hij _ hx k hk => hx k (lt_of_lt_of_le hk hij)

theorem realBasisTail_zero (e : Basis (Fin d) ℝ L) : realBasisTail e 0 = ⊤ := by
  apply top_unique
  intro x _ j hj
  omega

theorem realBasisTail_terminal (e : Basis (Fin d) ℝ L) : realBasisTail e d = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply e.repr.injective
  ext j
  simpa only [map_zero, Finsupp.zero_apply] using hx j j.isLt

theorem realBasisTail_eq_span (e : Basis (Fin d) ℝ L) (i : ℕ) :
    realBasisTail e i = Submodule.span ℝ (e '' {j : Fin d | i ≤ j.val}) := by
  ext x
  rw [e.mem_span_image]
  constructor
  · intro hx j hj
    by_contra h
    exact (Finsupp.mem_support_iff.mp hj) (hx j (Nat.lt_of_not_ge h))
  · intro hx j hj
    by_contra h
    exact (not_le_of_gt hj) (hx (Finsupp.mem_support_iff.mpr h))

theorem real_basis_mem_tail (e : Basis (Fin d) ℝ L) (j : Fin d) {i : ℕ} (hij : i ≤ j.val) :
    e j ∈ realBasisTail e i := by
  rw [realBasisTail_eq_span]
  exact Submodule.subset_span ⟨j, hij, rfl⟩

theorem mem_realBasisTail_succ_iff (e : Basis (Fin d) ℝ L) (j : Fin d) (x : L) :
    x ∈ realBasisTail e (j.val + 1) ↔ x ∈ realBasisTail e j.val ∧ e.repr x j = 0 := by
  constructor
  · intro hx
    exact ⟨realBasisTail_antitone e (Nat.le_succ j.val) hx, hx j (Nat.lt_succ_self j.val)⟩
  · rintro ⟨hx, hj⟩ k hk
    by_cases hkj : k = j
    · simpa only [hkj] using hj
    · apply hx k
      have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      omega

theorem real_sub_coordinate_mem_tail (e : Basis (Fin d) ℝ L) (j : Fin d) {x : L}
    (hx : x ∈ realBasisTail e j.val) :
    x - e.repr x j • e j ∈ realBasisTail e (j.val + 1) := by
  classical
  intro k hk
  by_cases hkj : k = j
  · subst k
    simp
  · have hlt : k.val < j.val := by
      have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      omega
    simp only [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply,
      hx k hlt, Basis.repr_self, Finsupp.single_eq_of_ne hkj, smul_zero, sub_zero]

def IsRealCentralLieBasis (e : Basis (Fin d) ℝ L) : Prop :=
  ∀ (j : Fin d) (a : L), ⁅a, e j⁆ ∈ realBasisTail e (j.val + 1)

namespace IsRealCentralLieBasis

variable {e : Basis (Fin d) ℝ L} (he : IsRealCentralLieBasis e)
include he

theorem lie_mem_tail_succ (i : ℕ) (a : L) {b : L} (hb : b ∈ realBasisTail e i) :
    ⁅a, b⁆ ∈ realBasisTail e (i + 1) := by
  classical
  rw [← e.sum_repr b, lie_sum]
  apply Submodule.sum_mem
  intro j _
  rw [lie_smul]
  by_cases hj : j.val < i
  · rw [hb j hj, zero_smul]
    exact (realBasisTail e (i + 1)).zero_mem
  · exact (realBasisTail e (i + 1)).smul_mem _
      (realBasisTail_antitone e (Nat.add_le_add_right (Nat.le_of_not_gt hj) 1) (he j a))

noncomputable def tailIdeal [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L] (i : ℕ) : LieIdeal ℚ L :=
  { (realBasisTail e i).restrictScalars ℚ with
    lie_mem := by
      intro a b hb
      exact realBasisTail_antitone e (Nat.le_succ i) (he.lie_mem_tail_succ i a hb) }

theorem coordinate_lie_eq_zero (i j k : Fin d) (hkj : k.val ≤ j.val) :
    e.repr ⁅e i, e j⁆ k = 0 := he j (e i) k (Nat.lt_succ_of_le hkj)

end IsRealCentralLieBasis

end Erdos3

namespace Erdos3

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

theorem IsCentralLieBasis.real_baseChange {e : Basis (Fin d) ℚ L}
    (he : IsCentralLieBasis e) : IsRealCentralLieBasis (e.baseChange ℝ) := by
  intro j a
  induction a using TensorProduct.inductionOn with
  | tmul r a =>
      intro k hk
      simp only [Basis.baseChange_apply, LieAlgebra.ExtendScalars.bracket_tmul,
        mul_one, Basis.baseChange_repr_tmul, he j a k hk, zero_smul]
  | add a b ha hb =>
      rw [add_lie]
      exact (realBasisTail (e.baseChange ℝ) (j.val + 1)).add_mem ha hb

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L)

theorem exists_bounded_sorted_adapted_basis {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤) {H : ℕ}
    (hv : ∀ i j k, RationalHeightLE (e.repr (v i j : L) k) H) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ s + 1) ∧ IsCentralLieBasis b ∧
      (∀ j k, RationalHeightLE (e.repr (b j) k) H) ∧
      ∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j}) := by
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  let S : Set L := {x | ∀ k, RationalHeightLE (e.repr x k) H}
  let P : Fin (s + 1) → Submodule ℚ L := fun i => F.layer (i.val + 1)
  have hP : Antitone P := fun i j hij => F.antitone (Nat.add_le_add_right hij 1)
  have hSP (i : Fin (s + 1)) : Submodule.span ℚ (S ∩ (P i : Set L)) = P i :=
    span_inter_eq_of_spanning_family (P i) (v i) (hspan i) S (hv i)
  have hS : Submodule.span ℚ S = ⊤ := by
    apply top_unique
    calc
      ⊤ = P 0 := F.one_eq_top.symm
      _ = Submodule.span ℚ (S ∩ (P 0 : Set L)) := (hSP 0).symm
      _ ≤ Submodule.span ℚ S := Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, w, hw, hbound, hbS, hbP⟩ :=
    exists_sorted_flag_basis_from_spanning_set P hP S hS hSP
  have hlayer := F.layer_eq_span_of_weighted_flag b w hbound hbP
  exact ⟨b, w, hw, hbound, centralLieBasis_of_sorted_filtration F b w hw hlayer, hbS, hlayer⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
