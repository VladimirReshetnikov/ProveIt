/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Sampling.FrozenPartitionScore

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def truncatedProgressionLength (N a q H : ℕ) : ℕ :=
  if a < N then min H ((N - 1 - a) / q + 1) else 0

theorem lt_truncatedProgressionLength_iff {N a q H j : ℕ} (hq : 0 < q) :
    j < truncatedProgressionLength N a q H ↔ j < H ∧ a + q * j < N := by
  by_cases ha : a < N
  · simp only [truncatedProgressionLength, ite_eq_left ha, lt_min_iff]
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hq, Nat.mul_comm j q]
    omega
  · simp only [truncatedProgressionLength, ite_eq_right ha, Nat.not_lt_zero, false_iff,
      not_and]
    omega

def progressionBlockLabel {N : ℕ} (q H : ℕ) (hq : 0 < q) (n : Fin N) :
    Fin q × Fin (N / q / H + 1) :=
  (⟨n.val % q, Nat.mod_lt _ hq⟩,
    ⟨n.val / q / H, Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.div_le_div_right (Nat.le_of_lt n.isLt)))⟩)

def progressionBlockStart {N q H : ℕ} (i : Fin q × Fin (N / q / H + 1)) : ℕ :=
  i.1.val + q * (H * i.2.val)

theorem progressionBlock_reconstruct {N q H : ℕ} (hq : 0 < q) (n : Fin N) :
    progressionBlockStart (progressionBlockLabel q H hq n) + q * (n.val / q % H) =
      n.val := by
  dsimp [progressionBlockStart, progressionBlockLabel]
  calc
    _ = n.val % q + q * (n.val / q % H + H * (n.val / q / H)) := by ring
    _ = n.val := by rw [Nat.mod_add_div, Nat.mod_add_div]

theorem progressionBlockLabel_of_point {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (i : Fin q × Fin (N / q / H + 1)) {j : ℕ} (hj : j < H)
    (hpoint : progressionBlockStart i + q * j < N) :
    progressionBlockLabel q H hq ⟨progressionBlockStart i + q * j, hpoint⟩ = i := by
  apply Prod.ext <;> apply Fin.ext
  · simp [progressionBlockLabel, progressionBlockStart, Nat.add_mod,
      Nat.mod_eq_of_lt i.1.isLt]
  · change (i.1.val + q * (H * i.2.val) + q * j) / q / H = i.2.val
    rw [show i.1.val + q * (H * i.2.val) + q * j =
      i.1.val + q * (H * i.2.val + j) by ring]
    rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt i.1.isLt, zero_add]
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hH, Nat.div_eq_of_lt hj, zero_add]

theorem progressionBlockLabel_eq_iff {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (i : Fin q × Fin (N / q / H + 1)) (n : Fin N) :
    progressionBlockLabel q H hq n = i ↔
      ∃ j < truncatedProgressionLength N (progressionBlockStart i) q H,
        n.val = progressionBlockStart i + q * j := by
  constructor
  · intro hi
    have heq := progressionBlock_reconstruct (H := H) hq n
    rw [hi] at heq
    exact ⟨n.val / q % H,
      (lt_truncatedProgressionLength_iff hq).mpr
        ⟨Nat.mod_lt _ hH, lt_of_eq_of_lt heq n.isLt⟩,
      heq.symm⟩
  · rintro ⟨j, hj, hn⟩
    have hj' := (lt_truncatedProgressionLength_iff hq).mp hj
    have heq := progressionBlockLabel_of_point hq hH i hj'.1 hj'.2
    have hfin : n = ⟨progressionBlockStart i + q * j, hj'.2⟩ := Fin.ext hn
    rwa [← hfin] at heq

noncomputable def progressionBlockEquiv {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (i : Fin q × Fin (N / q / H + 1)) :
    Fin (truncatedProgressionLength N (progressionBlockStart i) q H) ≃
      ↥(partitionCell (progressionBlockLabel q H hq) i) := by
  let point (j : Fin (truncatedProgressionLength N (progressionBlockStart i) q H)) :
      ↥(partitionCell (progressionBlockLabel q H hq) i) :=
    ⟨⟨progressionBlockStart i + q * j.val,
        ((lt_truncatedProgressionLength_iff hq).mp j.isLt).2⟩,
      (mem_partitionCell _ _ _).mpr
        (progressionBlockLabel_of_point hq hH i
          ((lt_truncatedProgressionLength_iff hq).mp j.isLt).1 _)⟩
  apply Equiv.ofBijective point
  constructor
  · intro j k hjk
    apply Fin.ext
    have heq : progressionBlockStart i + q * j.val =
        progressionBlockStart i + q * k.val := congrArg (fun n => n.val.val) hjk
    exact mul_left_cancel₀ hq.ne' (Nat.add_left_cancel heq)
  · intro n
    obtain ⟨j, hj, hn⟩ := (progressionBlockLabel_eq_iff hq hH i n.val).mp
      ((mem_partitionCell _ _ _).mp n.property)
    exact ⟨⟨j, hj⟩, Subtype.ext (Fin.ext hn.symm)⟩

theorem progressionBlock_card {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (i : Fin q × Fin (N / q / H + 1)) :
    (partitionCell (progressionBlockLabel q H hq) i).card =
      truncatedProgressionLength N (progressionBlockStart i) q H := by
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    (Fintype.card_congr (progressionBlockEquiv hq hH i)).symm

theorem progressionBlock_expect {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (i : Fin q × Fin (N / q / H + 1)) (f : ℕ → ℝ) :
    (𝔼 n ∈ partitionCell (progressionBlockLabel q H hq) i, f n.val) =
      𝔼 j : Fin (truncatedProgressionLength N (progressionBlockStart i) q H),
        f (progressionBlockStart i + q * j.val) := by
  classical
  have he := Fintype.expect_equiv (progressionBlockEquiv hq hH i)
    (fun j => f (progressionBlockStart i + q * j.val))
    (fun n => f n.val.val) (fun _ => rfl)
  have hcoe : (𝔼 n : ↥(partitionCell (progressionBlockLabel q H hq) i), f n.val.val) =
      𝔼 n ∈ partitionCell (progressionBlockLabel q H hq) i, f n.val := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe]
    rw [Finset.sum_coe_sort (partitionCell (progressionBlockLabel q H hq) i)
      (fun n : Fin N => f n.val)]
  exact hcoe.symm.trans he.symm

theorem progressionBlock_label_count (N q H : ℕ) :
    Fintype.card (Fin q × Fin (N / q / H + 1)) ≤ N / H + q := by
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_add, Nat.mul_one]
  apply Nat.add_le_add_right
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm q H, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

theorem progressionBlock_label_count_mul (N q H : ℕ) :
    Fintype.card (Fin q × Fin (N / q / H + 1)) * H ≤ N + q * H := by
  calc
    _ ≤ (N / H + q) * H := Nat.mul_le_mul_right H (progressionBlock_label_count N q H)
    _ = N / H * H + q * H := Nat.add_mul _ _ _
    _ ≤ N + q * H := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

theorem progressionBlock_label_count_mul_le_twice {N q H : ℕ} (hfit : q * H ≤ N) :
    Fintype.card (Fin q × Fin (N / q / H + 1)) * H ≤ 2 * N := by
  have h := progressionBlock_label_count_mul N q H
  omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

structure FiniteProgressionPartition (N : ℕ) where
  Label : Type
  labelFintype : Fintype Label
  start : Label → ℕ
  step : Label → ℕ
  length : Label → ℕ
  step_pos : ∀ i, 0 < step i
  equiv : (Σ i : Label, Fin (length i)) ≃ Fin N
  equiv_val : ∀ i (j : Fin (length i)), (equiv ⟨i, j⟩).val = start i + step i * j.val

attribute [instance] FiniteProgressionPartition.labelFintype

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

def point (i : P.Label) (j : Fin (P.length i)) : Fin N := P.equiv ⟨i, j⟩

@[simp] theorem point_val (i : P.Label) (j : Fin (P.length i)) :
    (P.point i j).val = P.start i + P.step i * j.val := P.equiv_val i j

theorem point_lt (i : P.Label) {j : ℕ} (hj : j < P.length i) :
    P.start i + P.step i * j < N := by
  simpa only [P.point_val] using (P.point i ⟨j, hj⟩).isLt

def cell (n : Fin N) : P.Label := (P.equiv.symm n).1

def offset (n : Fin N) : Fin (P.length (P.cell n)) := (P.equiv.symm n).2

@[simp] theorem cell_point (i : P.Label) (j : Fin (P.length i)) :
    P.cell (P.point i j) = i := by simp [cell, point]

@[simp] theorem point_cell_offset (n : Fin N) : P.point (P.cell n) (P.offset n) = n := by
  exact P.equiv.apply_symm_apply n

noncomputable def pointEquiv (i : P.Label) :
    Fin (P.length i) ≃ ↥(partitionCell P.cell i) := by
  let f (j : Fin (P.length i)) : ↥(partitionCell P.cell i) :=
    ⟨P.point i j, (mem_partitionCell P.cell i _).mpr (P.cell_point i j)⟩
  apply Equiv.ofBijective f
  constructor
  · intro j k h
    have he : P.equiv ⟨i, j⟩ = P.equiv ⟨i, k⟩ := congrArg Subtype.val h
    exact sigma_mk_injective (β := fun i : P.Label => Fin (P.length i)) (P.equiv.injective he)
  · intro n
    have hi : P.cell n.val = i := (mem_partitionCell P.cell i n.val).mp n.property
    rcases hx : P.equiv.symm n.val with ⟨k, j⟩
    have hki : k = i := by simpa only [cell, hx] using hi
    subst k
    refine ⟨j, Subtype.ext ?_⟩
    have he := congrArg P.equiv hx
    simpa only [f, point, Equiv.apply_symm_apply] using he.symm

theorem card_cell (i : P.Label) : (partitionCell P.cell i).card = P.length i := by
  simpa only [Fintype.card_coe, Fintype.card_fin] using (Fintype.card_congr (P.pointEquiv i)).symm

theorem expect_cell (i : P.Label) (f : ℕ → ℝ) :
    (𝔼 n ∈ partitionCell P.cell i, f n.val) =
      𝔼 j : Fin (P.length i), f (P.start i + P.step i * j.val) := by
  classical
  have he := Fintype.expect_equiv (P.pointEquiv i)
    (fun j => f (P.start i + P.step i * j.val)) (fun n => f n.val.val)
    (fun j => by simp [pointEquiv, point, P.equiv_val])
  have hcoe : (𝔼 n : ↥(partitionCell P.cell i), f n.val.val) =
      𝔼 n ∈ partitionCell P.cell i, f n.val := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe]
    rw [Finset.sum_coe_sort (partitionCell P.cell i) (fun n : Fin N => f n.val)]
  exact hcoe.symm.trans he.symm

def whole (N : ℕ) : FiniteProgressionPartition N where
  Label := Unit
  labelFintype := inferInstance
  start := fun _ => 0
  step := fun _ => 1
  length := fun _ => N
  step_pos := fun _ => by decide
  equiv := {
    toFun := fun x => x.2
    invFun := fun n => ⟨(), n⟩
    left_inv := fun ⟨i, j⟩ => by cases i; rfl
    right_inv := fun _ => rfl }
  equiv_val := fun _ _ => by simp

noncomputable def blocks (N q H : ℕ) (hq : 0 < q) (hH : 0 < H) :
    FiniteProgressionPartition N where
  Label := Fin q × Fin (N / q / H + 1)
  labelFintype := inferInstance
  start := progressionBlockStart
  step := fun _ => q
  length := fun i => truncatedProgressionLength N (progressionBlockStart i) q H
  step_pos := fun _ => hq
  equiv := (Equiv.sigmaCongrRight (fun i => (progressionBlockEquiv hq hH i).trans
    (Equiv.subtypeEquivRight (fun n => mem_partitionCell (progressionBlockLabel q H hq) i n)))).trans
    (Equiv.sigmaFiberEquiv (progressionBlockLabel q H hq))
  equiv_val := fun _ _ => rfl

end FiniteProgressionPartition
end Erdos3

end

section

namespace Erdos3

def mergedIntervalLength (N H k : ℕ) : ℕ :=
  if k + 1 = N / H then N - H * k else H

theorem mergedInterval_start_le {N H k : ℕ} (hk : k < N / H) : H * k ≤ N := by
  have hq : H * (N / H) ≤ N := by simpa only [mul_comm] using Nat.div_mul_le_self N H
  exact (Nat.mul_le_mul_left H hk.le).trans hq

theorem mergedInterval_length_bounds {N H k : ℕ} (hH : 0 < H) (hk : k < N / H) :
    H ≤ mergedIntervalLength N H k ∧ mergedIntervalLength N H k < 2 * H := by
  by_cases hlast : k + 1 = N / H
  · have hstart := mergedInterval_start_le hk
    have hcancel := Nat.sub_add_cancel hstart
    have hq : H * (N / H) ≤ N := by simpa only [mul_comm] using Nat.div_mul_le_self N H
    have hdiv := Nat.mod_add_div N H
    have hrem := Nat.mod_lt N hH
    rw [← hlast] at hq hdiv
    simp only [mergedIntervalLength, hlast, ite_true]
    constructor <;> nlinarith
  · simp only [mergedIntervalLength, hlast, ite_false]
    exact ⟨le_rfl, by omega⟩

theorem mergedInterval_point_lt {N H k j : ℕ} (hk : k < N / H)
    (hj : j < mergedIntervalLength N H k) : H * k + j < N := by
  by_cases hlast : k + 1 = N / H
  · have hstart := mergedInterval_start_le hk
    simp only [mergedIntervalLength, hlast, ite_true] at hj
    omega
  · have hjH : j < H := by simpa only [mergedIntervalLength, hlast, ite_false] using hj
    have hstep := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hk)
    have hq : H * (N / H) ≤ N := by simpa only [mul_comm] using Nat.div_mul_le_self N H
    nlinarith

theorem mergedInterval_index_unique {N H k l j t : ℕ}
    (hk : k < N / H) (hl : l < N / H)
    (hj : j < mergedIntervalLength N H k) (ht : t < mergedIntervalLength N H l)
    (heq : H * k + j = H * l + t) : k = l := by
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · have hlast : k + 1 ≠ N / H := by omega
    have hjH : j < H := by simpa only [mergedIntervalLength, hlast, ite_false] using hj
    have hstep := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hkl)
    nlinarith
  · exact hkl
  · have hlast : l + 1 ≠ N / H := by omega
    have htH : t < H := by simpa only [mergedIntervalLength, hlast, ite_false] using ht
    have hstep := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hlk)
    nlinarith

theorem exists_mergedInterval_coordinate {N H y : ℕ} (hH : 0 < H) (hHN : H ≤ N) (hy : y < N) :
    ∃ k < N / H, ∃ j < mergedIntervalLength N H k, H * k + j = y := by
  have hq : 0 < N / H := Nat.div_pos hHN hH
  let k := min (y / H) (N / H - 1)
  have hkleft : k ≤ y / H := Nat.min_le_left _ _
  have hkright : k ≤ N / H - 1 := Nat.min_le_right _ _
  have hk : k < N / H := by omega
  have hdivy : H * (y / H) ≤ y := by simpa only [mul_comm] using Nat.div_mul_le_self y H
  have hstart : H * k ≤ y := (Nat.mul_le_mul_left H hkleft).trans hdivy
  have hj : y - H * k < mergedIntervalLength N H k := by
    by_cases hlast : k + 1 = N / H
    · simp only [mergedIntervalLength, hlast, ite_true]
      omega
    · have hkeq : k = y / H := by
        by_cases hle : y / H ≤ N / H - 1
        · exact min_eq_left hle
        · have heq : k = N / H - 1 := min_eq_right (le_of_not_ge hle)
          omega
      have hdiv := Nat.mod_add_div y H
      have hrem := Nat.mod_lt y hH
      rw [← hkeq] at hdiv
      simp only [mergedIntervalLength, hlast, ite_false]
      omega
  exact ⟨k, hk, y - H * k, hj, by omega⟩

end Erdos3

end

section

namespace Erdos3

theorem truncatedProgressionLength_le (N a q H : ℕ) :
    truncatedProgressionLength N a q H ≤ H := by
  unfold truncatedProgressionLength
  split_ifs
  · exact min_le_left _ _
  · exact Nat.zero_le _

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

noncomputable def restrict (M : ℕ) (hMN : M ≤ N) : FiniteProgressionPartition M := by
  let len (i : P.Label) := truncatedProgressionLength M (P.start i) (P.step i) (P.length i)
  have hlen (i : P.Label) : len i ≤ P.length i := truncatedProgressionLength_le _ _ _ _
  let emb : (Σ i : P.Label, Fin (len i)) → Σ i : P.Label, Fin (P.length i) :=
    Sigma.map id (fun i j => ⟨j.val, j.isLt.trans_le (hlen i)⟩)
  have hemb : Function.Injective emb := by
    apply Function.injective_id.sigma_map
    intro i x y h
    apply Fin.ext
    exact congrArg (fun z : Fin (P.length i) => z.val) h
  let f (x : Σ i : P.Label, Fin (len i)) : Fin M :=
    ⟨P.start x.1 + P.step x.1 * x.2.val,
      ((lt_truncatedProgressionLength_iff (P.step_pos x.1)).mp x.2.isLt).2⟩
  have hrel (x : Σ i : P.Label, Fin (len i)) : (P.equiv (emb x)).val = (f x).val :=
    P.equiv_val x.1 _
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply hemb
      apply P.equiv.injective
      apply Fin.ext
      rw [hrel, hrel, h]
    · intro n
      let y := P.equiv.symm ⟨n.val, n.isLt.trans_le hMN⟩
      have hy : P.start y.1 + P.step y.1 * y.2.val = n.val := by
        rw [← P.equiv_val]
        exact congrArg Fin.val (P.equiv.apply_symm_apply _)
      have hj : y.2.val < len y.1 :=
        (lt_truncatedProgressionLength_iff (P.step_pos y.1)).mpr ⟨y.2.isLt, by rw [hy]; exact n.isLt⟩
      exact ⟨⟨y.1, ⟨y.2.val, hj⟩⟩, Fin.ext hy⟩
  exact {
    Label := P.Label
    labelFintype := P.labelFintype
    start := P.start
    step := P.step
    length := len
    step_pos := P.step_pos
    equiv := Equiv.ofBijective f hf
    equiv_val := fun _ _ => rfl }

theorem restrict_length_le (M : ℕ) (hMN : M ≤ N) (i : P.Label) :
    (P.restrict M hMN).length i ≤ P.length i := truncatedProgressionLength_le _ _ _ _

@[simp] theorem restrict_start (M : ℕ) (hMN : M ≤ N) (i : P.Label) :
    (P.restrict M hMN).start i = P.start i := rfl

@[simp] theorem restrict_step (M : ℕ) (hMN : M ≤ N) (i : P.Label) :
    (P.restrict M hMN).step i = P.step i := rfl

@[simp] theorem restrict_card (M : ℕ) (hMN : M ≤ N) :
    Fintype.card (P.restrict M hMN).Label = Fintype.card P.Label := rfl

end FiniteProgressionPartition
end Erdos3

end

section

namespace Erdos3.FiniteProgressionPartition

noncomputable def mergedIntervals (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) :
    FiniteProgressionPartition N := by
  let len : Fin (N / H) → ℕ := fun k => mergedIntervalLength N H k.val
  let f : (Σ k : Fin (N / H), Fin (len k)) → Fin N := fun x =>
    ⟨H * x.1.val + x.2.val, mergedInterval_point_lt x.1.isLt x.2.isLt⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨k, j⟩ ⟨l, t⟩ heq
      have he : H * k.val + j.val = H * l.val + t.val := congrArg Fin.val heq
      have hkl : k = l := Fin.ext (mergedInterval_index_unique k.isLt l.isLt j.isLt t.isLt he)
      cases hkl
      have hjt : j = t := Fin.ext (Nat.add_left_cancel he)
      cases hjt
      rfl
    · intro y
      obtain ⟨k, hk, j, hj, heq⟩ := exists_mergedInterval_coordinate hH hHN y.isLt
      exact ⟨⟨⟨k, hk⟩, ⟨j, hj⟩⟩, Fin.ext heq⟩
  exact {
    Label := Fin (N / H)
    labelFintype := inferInstance
    start := fun k => H * k.val
    step := fun _ => 1
    length := len
    step_pos := fun _ => Nat.zero_lt_one
    equiv := Equiv.ofBijective f hf
    equiv_val := fun _ _ => by simp only [Equiv.ofBijective_apply, f, one_mul] }

theorem mergedIntervals_length_bounds (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (k : (mergedIntervals N H hH hHN).Label) :
    H ≤ (mergedIntervals N H hH hHN).length k ∧
      (mergedIntervals N H hH hHN).length k < 2 * H :=
  mergedInterval_length_bounds hH k.isLt

@[simp] theorem mergedIntervals_start (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (k : (mergedIntervals N H hH hHN).Label) :
    (mergedIntervals N H hH hHN).start k = H * k.val := rfl

@[simp] theorem mergedIntervals_step (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (k : (mergedIntervals N H hH hHN).Label) :
    (mergedIntervals N H hH hHN).step k = 1 := rfl

@[simp] theorem mergedIntervals_card (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) :
    Fintype.card (mergedIntervals N H hH hHN).Label = N / H := Fintype.card_fin _

theorem cell_eq_iff_of_step_one {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (n : Fin N) (k : P.Label) :
    P.cell n = k ↔ P.start k ≤ n.val ∧ n.val < P.start k + P.length k := by
  constructor
  · intro hn
    subst k
    have heq := congrArg Fin.val (P.point_cell_offset n)
    rw [P.point_val, hstep, one_mul] at heq
    have hj := (P.offset n).isLt
    omega
  · rintro ⟨hlo, hhi⟩
    let j : Fin (P.length k) := ⟨n.val - P.start k, by omega⟩
    have heq : P.point k j = n := by
      apply Fin.ext
      rw [P.point_val, hstep, one_mul]
      dsimp only [j]
      omega
    rw [← heq, P.cell_point]

theorem end_le_of_step_one {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (k : P.Label) (hpos : 0 < P.length k) :
    P.start k + P.length k ≤ N := by
  have h := P.point_lt k (j := P.length k - 1) (by omega)
  rw [hstep, one_mul] at h
  omega

end Erdos3.FiniteProgressionPartition

end

section

namespace Erdos3.FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

noncomputable def bind (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i)) :
    FiniteProgressionPartition N where
  Label := Σ i : P.Label, (Q i).Label
  labelFintype := inferInstance
  start := fun x => P.start x.1 + P.step x.1 * (Q x.1).start x.2
  step := fun x => P.step x.1 * (Q x.1).step x.2
  length := fun x => (Q x.1).length x.2
  step_pos := fun x => Nat.mul_pos (P.step_pos x.1) ((Q x.1).step_pos x.2)
  equiv := (Equiv.sigmaAssoc (fun i j => Fin ((Q i).length j))).trans
    ((Equiv.sigmaCongrRight (fun i => (Q i).equiv)).trans P.equiv)
  equiv_val := by
    intro x j
    change (P.equiv ⟨x.1, (Q x.1).equiv ⟨x.2, j⟩⟩).val = _
    rw [P.equiv_val, (Q x.1).equiv_val]
    ring

@[simp] theorem bind_start (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i))
    (i : P.Label) (j : (Q i).Label) :
    (P.bind Q).start ⟨i, j⟩ = P.start i + P.step i * (Q i).start j := rfl

@[simp] theorem bind_step (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i))
    (i : P.Label) (j : (Q i).Label) :
    (P.bind Q).step ⟨i, j⟩ = P.step i * (Q i).step j := rfl

@[simp] theorem bind_length (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i))
    (i : P.Label) (j : (Q i).Label) : (P.bind Q).length ⟨i, j⟩ = (Q i).length j := rfl

theorem bind_card (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i)) :
    Fintype.card (P.bind Q).Label = ∑ i : P.Label, Fintype.card (Q i).Label := Fintype.card_sigma

theorem bind_card_mul_le (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i))
    (H B : ℕ) (hQ : ∀ i, Fintype.card (Q i).Label * H ≤ B) :
    Fintype.card (P.bind Q).Label * H ≤ Fintype.card P.Label * B := by
  classical
  rw [P.bind_card, Finset.sum_mul]
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset P.Label)) => hQ i)

end Erdos3.FiniteProgressionPartition

end

end OAI
