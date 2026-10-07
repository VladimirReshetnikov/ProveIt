import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Geometry.BoxBlockBudget
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
import OAI.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid

namespace OAI

section

namespace Erdos3

structure ResidueBoxSlice {ι : Type*} (N : ι → ℕ) (q : ℕ) where
  start : ι → ℕ
  length : ι → ℕ
  inside : ∀ i j, j < length i → start i + q * j < N i

namespace ResidueBoxSlice

variable {ι : Type*} {N : ι → ℕ} {q : ℕ}

def point (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) : ∀ i, Fin (N i) :=
  fun i => ⟨A.start i + q * (j i).val, A.inside i _ (j i).isLt⟩

noncomputable def center (A : ResidueBoxSlice N q) : ι → ℝ :=
  fun i => (A.start i : ℝ) / N i

theorem point_residue (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) (i : ι) :
    (A.point j i).val % q = A.start i % q := by
  simp [point, Nat.add_mod]

noncomputable abbrev ofBlocks (H : ι → ℕ) (hq : 0 < q) (hH : ∀ i, 0 < H i)
    (a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label) :
    ResidueBoxSlice N q where
  start i := (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).start (a i)
  length i := (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).length (a i)
  inside i _j hj := (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).point_lt (a i) hj

theorem ofBlocks_point (H : ι → ℕ) (hq : 0 < q) (hH : ∀ i, 0 < H i)
    (a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label)
    (j : ∀ i, Fin ((ofBlocks H hq hH a).length i)) :
    (ofBlocks H hq hH a).point j =
      BoxProgressionPartition.point (fun i => FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)) a j := by
  funext i
  apply Fin.ext
  rfl

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3

namespace FiniteProgressionPartition

theorem entireResidue_length_ge {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (blocks N q (N + 1) hq (Nat.succ_pos N)).Label) :
    H ≤ (blocks N q (N + 1) hq (Nat.succ_pos N)).length i := by
  have hdiv : N / q / (N + 1) = 0 :=
    Nat.div_eq_of_lt ((Nat.div_le_self N q).trans_lt (Nat.lt_succ_self N))
  have hi : i.2.val = 0 := by
    have hi := i.2.isLt
    omega
  have hHN : H ≤ N := (Nat.le_mul_of_pos_left H hq).trans hfit
  have hlast : i.1.val + q * (H - 1) < N := by
    calc
      _ < q + q * (H - 1) := Nat.add_lt_add_right i.1.isLt _
      _ = q * ((H - 1) + 1) := by ring
      _ = q * H := by rw [Nat.sub_add_cancel hH]
      _ ≤ N := hfit
  have hlen : H - 1 < truncatedProgressionLength N (progressionBlockStart i) q (N + 1) := by
    apply (lt_truncatedProgressionLength_iff hq).mpr
    refine ⟨by omega, ?_⟩
    simpa only [progressionBlockStart, hi, Nat.mul_zero, Nat.add_zero] using hlast
  change H ≤ truncatedProgressionLength N (progressionBlockStart i) q (N + 1)
  omega

noncomputable def comparableResidues (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) : FiniteProgressionPartition N :=
  (blocks N q (N + 1) hq (Nat.succ_pos N)).bind
    (fun i => mergedIntervals _ H hH (entireResidue_length_ge hq hH hfit i))

theorem comparableResidues_step (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidues N q H hq hH hfit).Label) :
    (comparableResidues N q H hq hH hfit).step i = q := by
  change q * 1 = q
  exact mul_one q

theorem comparableResidues_length (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidues N q H hq hH hfit).Label) :
    H ≤ (comparableResidues N q H hq hH hfit).length i ∧
      (comparableResidues N q H hq hH hfit).length i < 2 * H :=
  mergedIntervals_length_bounds _ H hH (entireResidue_length_ge hq hH hfit i.1) i.2

end FiniteProgressionPartition

open scoped BigOperators

theorem exists_partition_cell_average {Ω K : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype K] (cell : Ω → K) (f : Ω → ℝ) :
    ∃ k, (partitionCell cell k).Nonempty ∧
      (𝔼 x, f x) ≤ 𝔼 x ∈ partitionCell cell k, f x := by
  classical
  by_contra! hnone
  have hstrict (k : K) (hk : (partitionCell cell k).Nonempty) :
      (∑ x ∈ partitionCell cell k, f x) < (partitionCell cell k).card * (𝔼 x, f x) := by
    have hcard : (0 : ℝ) < (partitionCell cell k).card := by exact_mod_cast hk.card_pos
    have h := mul_lt_mul_of_pos_left (hnone k hk) hcard
    rwa [Finset.card_mul_expect] at h
  have hle (k : K) : (∑ x ∈ partitionCell cell k, f x) ≤
      (partitionCell cell k).card * (𝔼 x, f x) := by
    by_cases hk : (partitionCell cell k).Nonempty
    · exact (hstrict k hk).le
    · simp [Finset.not_nonempty_iff_eq_empty.mp hk]
  obtain ⟨x₀⟩ := ‹Nonempty Ω›
  have hk : (partitionCell cell (cell x₀)).Nonempty :=
    ⟨x₀, (mem_partitionCell cell (cell x₀) x₀).mpr rfl⟩
  have hsum := Finset.sum_lt_sum (fun k (_ : k ∈ (Finset.univ : Finset K)) => hle k)
    ⟨cell x₀, Finset.mem_univ _, hstrict _ hk⟩
  rw [sum_partitionCell, ← Finset.sum_mul, card_partitionCell_sum,
    Fintype.expect_eq_sum_div_card] at hsum
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_div_cancel₀ _ hcard] at hsum
  exact lt_irrefl _ hsum

theorem exists_comparable_residueBoxSlice {I : Type*} [Fintype I] [DecidableEq I]
    (N H : I → ℕ) {q : ℕ} (hq : 0 < q) (hH : ∀ i, 0 < H i)
    (hfit : ∀ i, q * H i ≤ N i) (f : (∀ i, Fin (N i)) → ℝ) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, H i ≤ A.length i ∧ A.length i < 2 * H i) ∧
      (𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (A.length i)), f (A.point j) := by
  classical
  let P := fun i => FiniteProgressionPartition.comparableResidues (N i) q (H i) hq (hH i) (hfit i)
  let : ∀ i, NeZero (N i) := fun i => ⟨ne_of_gt ((Nat.mul_pos hq (hH i)).trans_le (hfit i))⟩
  obtain ⟨k, _, hk⟩ := exists_partition_cell_average (BoxProgressionPartition.cell P) f
  let A : ResidueBoxSlice N q := {
    start := fun i => (P i).start (k i)
    length := fun i => (P i).length (k i)
    inside := fun i j hj => by
      have hp := (P i).point_lt (k i) hj
      rwa [FiniteProgressionPartition.comparableResidues_step] at hp }
  refine ⟨A, ?_, ?_⟩
  · intro i
    exact FiniteProgressionPartition.comparableResidues_length (N i) q (H i) hq (hH i) (hfit i) (k i)
  · rw [BoxProgressionPartition.expect_cell] at hk
    convert hk using 1
    apply Finset.expect_congr rfl
    intro j _
    congr 1
    ext i
    simp only [ResidueBoxSlice.point, BoxProgressionPartition.point_val,
      FiniteProgressionPartition.comparableResidues_step, A, P]

theorem exists_narrow_residueBoxSlice {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) {q : ℕ} (hq : 0 < q) {ρ : ℝ} (_hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hlarge : ∀ i, 4 * (q : ℝ) ≤ ρ * N i) (f : (∀ i, Fin (N i)) → ℝ) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, 0 < A.length i ∧ ρ * N i ≤ 4 * q * A.length i ∧
        (q : ℝ) * A.length i ≤ ρ * N i) ∧
      (𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (A.length i)), f (A.point j) := by
  let H : I → ℕ := fun i => ⌊ρ * N i / (2 * q)⌋₊
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htwoq : (0 : ℝ) < 2 * q := by positivity
  have harg (i : I) : 2 ≤ ρ * N i / (2 * q) :=
    (le_div_iff₀ htwoq).mpr (by nlinarith [hlarge i])
  have hH (i : I) : 0 < H i := Nat.floor_pos.mpr (by linarith [harg i])
  have hupper (i : I) : (H i : ℝ) * (2 * q) ≤ ρ * N i :=
    (le_div_iff₀ htwoq).mp (Nat.floor_le (by linarith [harg i]))
  have hlower (i : I) : ρ * N i ≤ 4 * q * H i := by
    have hn : ρ * N i / (2 * q) < (H i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hh : 1 ≤ (H i : ℝ) := by exact_mod_cast hH i
    have hquot : ρ * N i / (2 * q) ≤ 2 * H i := by linarith
    have hm := (div_le_iff₀ htwoq).mp hquot
    nlinarith
  have hfit (i : I) : q * H i ≤ N i := by
    have hn : ρ * (N i : ℝ) ≤ N i := mul_le_of_le_one_left (Nat.cast_nonneg _) hρ1
    have hm : (q : ℝ) * H i ≤ N i := by
      nlinarith [hupper i, mul_nonneg (Nat.cast_nonneg (α := ℝ) q) (Nat.cast_nonneg (α := ℝ) (H i))]
    exact_mod_cast hm
  obtain ⟨A, hA, hscore⟩ := exists_comparable_residueBoxSlice N H hq hH hfit f
  refine ⟨A, ?_, hscore⟩
  intro i
  have hlow : (H i : ℝ) ≤ A.length i := by exact_mod_cast (hA i).1
  have hhigh : (A.length i : ℝ) < 2 * H i := by exact_mod_cast (hA i).2
  refine ⟨(hH i).trans_le (hA i).1, ?_, ?_⟩
  · exact (hlower i).trans (mul_le_mul_of_nonneg_left hlow (by positivity))
  · have hm := mul_le_mul_of_nonneg_left hhigh.le hqR.le
    nlinarith [hupper i]

end Erdos3

end

section

namespace Erdos3

theorem denseResidueMeshInterval (b len M : ℕ) (hM : 0 < M) (hlen : 2 * M < len) :
    let lo := b / M + 1
    let hi := (b + len) / M
    lo < hi ∧ b ≤ M * lo ∧ M * hi ≤ b + len ∧
      len - (M * hi - M * lo) ≤ 2 * M := by
  dsimp only
  have hb := Nat.mod_add_div b M
  have he := Nat.mod_add_div (b + len) M
  have hbm := Nat.mod_lt b hM
  have hem := Nat.mod_lt (b + len) hM
  have hstart : b < M * (b / M + 1) := by nlinarith
  have hstartUpper : M * (b / M + 1) ≤ b + M := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hend : M * ((b + len) / M) ≤ b + len := by omega
  have hendLower : b + len < M * ((b + len) / M) + M := by omega
  have hlt : b / M + 1 < (b + len) / M := by nlinarith
  refine ⟨hlt, hstart.le, hend, ?_⟩
  have hmul : M * (b / M + 1) ≤ M * ((b + len) / M) :=
    Nat.mul_le_mul_left M hlt.le
  omega

theorem denseResidueMeshInterval_code_bound (b len M K : ℕ)
    (hM : 0 < M) (hlen : 2 * M < len) (hbox : b + len ≤ K * M) :
    b / M + 1 ≤ K ∧ (b + len) / M ≤ K := by
  have h := denseResidueMeshInterval b len M hM hlen
  dsimp only at h
  have hhi : (b + len) / M ≤ K := by nlinarith [h.2.2.1]
  exact ⟨h.1.le.trans hhi, hhi⟩

namespace ResidueBoxSlice
variable {X : Type*} {N : X → ℕ} {q : ℕ}

theorem residueIndex_endpoint_le (S : ResidueBoxSlice N q) (hq : 0 < q)
    (hlen : ∀ i, 0 < S.length i) (i : X) :
    S.start i / q + S.length i ≤ N i := by
  have hi := S.inside i (S.length i - 1) (by have := hlen i; omega)
  have hmul : S.length i - 1 ≤ q * (S.length i - 1) := by nlinarith
  have hdiv : S.start i / q ≤ S.start i := Nat.div_le_self _ _
  omega

def meshRounded (S : ResidueBoxSlice N q) (_hq : 0 < q) (M : ℕ)
    (hM : 0 < M) (hlen : ∀ i, 2 * M < S.length i) : ResidueBoxSlice N q where
  start i := S.start i % q + q * (M * (S.start i / q / M + 1))
  length i := M * ((S.start i / q + S.length i) / M) - M * (S.start i / q / M + 1)
  inside i j hj := by
    have h := denseResidueMeshInterval (S.start i / q) (S.length i) M hM (hlen i)
    dsimp only at h
    let offset := M * (S.start i / q / M + 1) - S.start i / q
    have ho : offset + j < S.length i := by dsimp [offset]; omega
    have he := S.inside i (offset + j) ho
    have hmod := Nat.mod_add_div (S.start i) q
    have hstart := h.2.1
    have hoff : offset + S.start i / q = M * (S.start i / q / M + 1) := by
      dsimp [offset]
      omega
    nlinarith

theorem meshRounded_length_pos (S : ResidueBoxSlice N q) (hq : 0 < q) (M : ℕ)
    (hM : 0 < M) (hlen : ∀ i, 2 * M < S.length i) (i : X) :
    0 < (S.meshRounded hq M hM hlen).length i := by
  have h := (denseResidueMeshInterval (S.start i / q) (S.length i) M hM (hlen i)).1
  change 0 < M * ((S.start i / q + S.length i) / M) - M * (S.start i / q / M + 1)
  have := Nat.mul_lt_mul_of_pos_left h hM
  omega

theorem meshRounded_contained (S : ResidueBoxSlice N q) (hq : 0 < q) (M : ℕ)
    (hM : 0 < M) (hlen : ∀ i, 2 * M < S.length i) :
    ∃ offset : X → ℕ,
      (∀ i, (S.meshRounded hq M hM hlen).start i = S.start i + q * offset i) ∧
      (∀ i, offset i + (S.meshRounded hq M hM hlen).length i ≤ S.length i) ∧
      ∀ i, S.length i - (S.meshRounded hq M hM hlen).length i ≤ 2 * M := by
  refine ⟨fun i => M * (S.start i / q / M + 1) - S.start i / q, ?_, ?_, ?_⟩
  · intro i
    have h := (denseResidueMeshInterval (S.start i / q) (S.length i) M hM (hlen i)).2.1
    have he : M * (S.start i / q / M + 1) - S.start i / q + S.start i / q =
        M * (S.start i / q / M + 1) := by omega
    have hmod := Nat.mod_add_div (S.start i) q
    change _ + _ * _ = _ + _ * _
    nlinarith
  · intro i
    have h := denseResidueMeshInterval (S.start i / q) (S.length i) M hM (hlen i)
    dsimp only at h
    dsimp only [meshRounded]
    have hstart := h.2.1
    have hend := h.2.2.1
    have hmul := Nat.mul_le_mul_left M h.1.le
    omega
  · intro i
    exact (denseResidueMeshInterval (S.start i / q) (S.length i) M hM (hlen i)).2.2.2

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {ι : Type*} {N : ι → ℕ} {q : ℕ}

theorem log_side_loss (A : ResidueBoxSlice N q) (hN : ∀ i, 0 < N i)
    {η : ℝ} (hη : 0 < η) (hlength : ∀ i, η * N i ≤ (A.length i : ℝ)) (i : ι) :
    Real.log (N i) - Real.log (A.length i) ≤ -Real.log η := by
  have hNi : (0 : ℝ) < N i := by exact_mod_cast hN i
  have h := Real.log_le_log (mul_pos hη hNi) (hlength i)
  rw [Real.log_mul hη.ne' hNi.ne'] at h
  linarith

theorem log_volume_loss [Fintype ι] (A : ResidueBoxSlice N q) (hN : ∀ i, 0 < N i)
    {η : ℝ} (hη : 0 < η) (hlength : ∀ i, η * N i ≤ (A.length i : ℝ)) :
    (∑ i, Real.log (N i)) - ∑ i, Real.log (A.length i) ≤
      (Fintype.card ι : ℝ) * (-Real.log η) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => A.log_side_loss hN hη hlength i)
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

theorem spatial_freezing_log_side_loss [Fintype ι] (A : ResidueBoxSlice N q)
    (hN : ∀ i, 0 < N i) (hq : 0 < q) {θ ρ : ℝ} (hθ : 0 < θ) (hρ : 0 < ρ)
    (hlength : ∀ i, θ * ρ * N i / (4 * q * (Fintype.card ι + 1)) ≤ (A.length i : ℝ)) (i : ι) :
    Real.log (N i) - Real.log (A.length i) ≤
      Real.log (4 * q * ((Fintype.card ι : ℝ) + 1)) - Real.log θ - Real.log ρ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hden : (0 : ℝ) < 4 * q * ((Fintype.card ι : ℝ) + 1) := by positivity
  have h := A.log_side_loss hN (div_pos (mul_pos hθ hρ) hden)
    (fun i => by simpa only [div_mul_eq_mul_div] using hlength i) i
  rw [Real.log_div (mul_pos hθ hρ).ne' hden.ne', Real.log_mul hθ.ne' hρ.ne'] at h
  linarith

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open MvPolynomial

variable {ι : Type*} {N : ι → ℕ} {q s d : ℕ}

noncomputable def parameters (A : ResidueBoxSlice N q) (i : ι) : MvPolynomial ι ℝ :=
  C (A.start i : ℝ) + (q : ℝ) • X i

theorem parameters_degree (A : ResidueBoxSlice N q) (i : ι) :
    A.parameters i ∈ weightedSupportLE (fun _ : ι => 1) 1 :=
  (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    ((weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ i))

noncomputable def reparamPatch (A : ResidueBoxSlice N q) (P : PolynomialPatch ι s d) :
    PolynomialPatch ι s d := P.reparam A.parameters A.parameters_degree

@[simp] theorem reparamPatch_kernel (A : ResidueBoxSlice N q) (P : PolynomialPatch ι s d) :
    (A.reparamPatch P).kernel = P.kernel := rfl

theorem reparamPatch_value (A : ResidueBoxSlice N q) (P : PolynomialPatch ι s d)
    (j : ∀ i, Fin (A.length i)) :
    (A.reparamPatch P).value (fun i => ((j i).val : ℝ)) =
      P.value (fun i => ((A.point j i).val : ℝ)) := by
  rw [reparamPatch, PolynomialPatch.reparam_value]
  congr 1
  funext i
  simp [parameters, point]

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

theorem exists_normalized_cell_of_coordinate_intervals {ι : Type*}
    (T lo hi : ι → ℝ) (hT : ∀ i, 0 < T i) {Q : ℕ} (hQ : 0 < Q)
    (hlo : ∀ i, |lo i| ≤ T i) (hhi : ∀ i, |hi i| ≤ T i)
    (hwidth : ∀ i, hi i - lo i ≤ 2 * T i / Q) :
    ∃ a : ι → Fin (Q + 1), ∀ v : ι → ℝ,
      (∀ i, lo i ≤ v i ∧ v i ≤ hi i) →
      ∀ i, |v i - normalizedRealBoxGrid T Q a i| ≤ T i * (2 / Q) := by
  let mid := fun i => (lo i + hi i) / 2
  have hm (i) : |mid i| ≤ T i := by
    apply abs_le.mpr
    have hl := abs_le.mp (hlo i)
    have hh := abs_le.mp (hhi i)
    dsimp only [mid]
    constructor <;> linarith
  obtain ⟨a, ha⟩ := exists_normalizedRealBoxGrid_half_cell T hT hQ mid hm
  refine ⟨a, ?_⟩
  intro v hv i
  have hd : |v i - mid i| ≤ T i / Q := by
    apply abs_le.mpr
    have hw := hwidth i
    rw [mul_div_assoc] at hw
    have hh := hv i
    dsimp only [mid]
    constructor <;> linarith
  calc
    _ ≤ |v i - mid i| + |mid i - normalizedRealBoxGrid T Q a i| := abs_sub_le _ _ _
    _ ≤ T i / Q + T i / Q := add_le_add hd (ha i)
    _ = T i * (2 / Q) := by ring

namespace ResidueBoxSlice

theorem exists_affine_normalized_cell {ι : Type*} {N : ι → ℕ} {q Q : ℕ}
    (A : ResidueBoxSlice N q) (hlen : ∀ i, 0 < A.length i)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) (hQ : 0 < Q)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hwidth : ∀ i, step * q * A.length i ≤ 2 * T i / Q) :
    ∃ a : ι → Fin (Q + 1), ∀ j : ∀ i, Fin (A.length i), ∀ i,
      |origin i + step * (A.point j i).val - normalizedRealBoxGrid T Q a i| ≤
        T i * (2 / Q) := by
  let lo := fun i => origin i + step * A.start i
  let hi := fun i => origin i + step * (A.start i + q * (A.length i - 1) : ℕ)
  have hlo (i) : |lo i| ≤ T i := by
    apply hparent i (A.start i)
    simpa only [Nat.mul_zero, Nat.add_zero] using A.inside i 0 (hlen i)
  have hhi (i) : |hi i| ≤ T i :=
    hparent i _ (A.inside i _ (Nat.sub_lt (hlen i) (by decide)))
  have hw (i) : hi i - lo i ≤ 2 * T i / Q := by
    have hs : step * (q : ℝ) * (A.length i - 1 : ℕ) ≤ step * q * A.length i :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.sub_le _ _)) (by positivity)
    dsimp only [hi, lo]
    push_cast
    nlinarith [hwidth i]
  obtain ⟨a, ha⟩ := exists_normalized_cell_of_coordinate_intervals T lo hi hT hQ hlo hhi hw
  refine ⟨a, fun j => ha (fun i => origin i + step * (A.point j i).val) ?_⟩
  intro i
  have hj : (j i).val ≤ A.length i - 1 := by have := (j i).isLt; omega
  have hs := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj : ((j i).val : ℝ) ≤ _)
    (show 0 ≤ step * (q : ℝ) by positivity)
  dsimp only [lo, hi, point]
  push_cast
  constructor
  · have hn : 0 ≤ step * (q : ℝ) * ((j i).val : ℝ) := by positivity
    nlinarith
  · nlinarith

end ResidueBoxSlice
end Erdos3

end

end OAI
