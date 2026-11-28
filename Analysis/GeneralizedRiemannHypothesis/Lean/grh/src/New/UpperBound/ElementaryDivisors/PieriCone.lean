import Lib.Base

/-!
# The Pieri cone, the step map and the slab: interlacing and volume of the cone

Vectors `ν` are real functions on pairs `(b, j)`, with `b` in `Fin k` and `j` a letter (in `ZMod N`
for the final volume formula). The step map `New.permStep` sends `ν` to signed gaps between
consecutive letters, twisted by permutations. The cone `New.pieriCone v P` is cut out by Pieri's
inequalities, one half of the interlacing inequalities between `ν` and `P` times its shift. The slab
`New.degreeSlab k D` is the set of nonnegative vectors whose sum at each letter `j` lies in the unit
interval `[D j - 1, D j]`, a product of slices of orthants.

## Main definitions and results

* `New.detOneSubPerm`: the determinant `det (1 - τ / q)` for a permutation `τ` of coordinates.
* `New.det_interlacing_indicator`: interlacing of two decreasing sequences is the determinant of a
  matrix of indicators.
* `New.volume_real_inter_degreeSlab_eq_signed_sum`, `New.prod_mul_volume_real_inter_degreeSlab`: for
  `P > 1`, a set whose preimage under `New.permStep` (with trivial permutations) is the cone fills a
  fraction of the slab given by a signed sum over permutations, equal to
  `∏ l < k, (q - 1) / (q ^ (l + 1) - 1)` with `q = P ^ N`.

The result serves the dimension bounds mod `p` from flags in
`New.UpperBound.ElementaryDivisors.DefectCount`.

## Notation

The Boolean `v j` selects the sign of the steps at the letter `j`: `+` for true, `-` for false. In
the application `v j` is true for even `j`.

## Relation to the literature

See `New.UpperBound.ElementaryDivisors.DefectCount` for related work.
-/

namespace New

section SignedCount

open Finset Matrix MeasureTheory Measure Equiv Fintype Set Bornology Tuple LinearMap Fin Perm List

variable {k m : ℕ}

section StepMap

variable {T : Type} [Add T] [One T] (v : T → Bool) (P : ℝ)

/-- The step map. For permutations `σ j` of `Fin k`, one for each letter `j`, it is the linear map
`ν ↦ β` with `β (b, j) = ± (P * ν (b, j + 1) - ν (σ j b, j))`, the sign being `+` if `v j` is true
and `-` otherwise. The entries of `β` are the steps of `ν`. -/
@[simps!]
def permStep (σ : T → Equiv.Perm (Fin k)) : Module.End ℝ (Fin k × T → ℝ) :=
  LinearMap.pi fun x : Fin k × T ↦
    (if v x.2 then (1 : ℝ) else -1) • (P • .proj (x.1, x.2 + 1) - .proj (σ x.2 x.1, x.2))

/-- The slab: the vectors `β ≥ 0` whose degree `∑ b, β (b, j)` lies in `[D j - 1, D j]` for every
letter `j`. -/
def degreeSlab (k : ℕ) (D : T → ℝ) : Set (Fin k × T → ℝ) :=
  {β : Fin k × T → ℝ | 0 ≤ β ∧ ∀ j : T, ∑ b : Fin k, β (b, j) ∈ Set.Icc (D j - 1) (D j)}

/-- The Pieri cone: the vectors `ν` such that, for all `j` and `b`,
`P * ν (b + 1, j + 1) ≤ ν (b, j)` if `v j` is true, and `ν (b + 1, j) ≤ P * ν (b, j + 1)`
otherwise. -/
def pieriCone : Set (Fin k × T → ℝ) :=
  {ν : Fin k × T → ℝ |
    ∀ (j : T) (b b' : Fin k), b.val + 1 = b' →
      permStep v P 1 ν ((if v j then b' else b), j) ≤ ν (b, j) - ν (b', j)}

/-- The set of `ν` whose steps have degrees `∑ b, permStep v P 1 ν (b, j)` in `[D j - 1, D j]` and
such that, after block `j` of `ν` is rearranged by `τ j`, the image under `permStep v P σ` has
positive entries and lies in `Y`. -/
def positiveStepSet (D : T → ℝ) (σ τ : T → Perm (Fin k)) (Y : Set (Fin k × T → ℝ)) :
    Set (Fin k × T → ℝ) :=
  {ν : Fin k × T → ℝ |
    (∀ j : T, ∑ b : Fin k, permStep v P 1 ν (b, j) ∈ Icc (D j - 1) (D j)) ∧
      (∀ (j : T) (b : Fin k), 0 < permStep v P σ (ν ∘ prodCongrLeft τ) (b, j)) ∧
        permStep v P σ (ν ∘ prodCongrLeft τ) ∈ Y}

/-- For weakly decreasing `x` and `y` in `ℝ ^ k`, the matrix with `(b, c)` entry `1` if `y c < x b`
and `0` otherwise has determinant `1` if the two interlace, `x 0 > y 0 ≥ x 1 > y 1 ≥ ⋯`, and `0`
otherwise. -/
lemma det_interlacing_indicator {x y : Fin k → ℝ} (hx : Antitone x) (hy : Antitone y) :
    det (of fun b c : Fin k ↦ if y c < x b then (1 : ℝ) else 0) =
      if (∀ b : Fin k, y b < x b) ∧ ∀ b c : Fin k, b.val + 1 = c.val → x c ≤ y b then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨b, hb⟩ | h_none := exists_or_forall_not fun b : Fin k ↦ y 0 < x b.succ
    · -- If `y 0 < x b.succ`, rows `0` and `b.succ` consist of ones, and interlacing fails.
      have h_row_succ (c : Fin (k + 1)) : y c < x b.succ := (hy c.zero_le).trans_lt hb
      have h_row_zero (c : Fin (k + 1)) : y c < x 0 := (h_row_succ c).trans_le (hx b.succ.zero_le)
      rw [ite_eq_right fun ⟨_, h_le⟩ ↦ (h_row_succ b.castSucc).not_ge (h_le b.castSucc b.succ rfl)]
      exact det_zero_of_row_eq b.succ_ne_zero (funext fun c ↦ by simp [h_row_succ, h_row_zero])
    · -- Otherwise column `0` vanishes below the top: expand along it.
      have h_expand : det (of fun b c : Fin (k + 1) ↦ if y c < x b then (1 : ℝ) else 0) =
          (if y 0 < x 0 then 1 else 0) *
            det (of fun b c : Fin k ↦ if y c.succ < x b.succ then (1 : ℝ) else 0) := by
        simp [det_succ_column_zero, sum_univ_succ, h_none]
        rfl
      rw [h_expand, ih (x := fun b ↦ x b.succ) (y := fun b ↦ y b.succ)
        (hx.comp_monotone strictMono_succ.monotone) (hy.comp_monotone strictMono_succ.monotone)]
      -- As every `x b.succ ≤ y 0`, interlacing is `y 0 < x 0` and interlacing of the tails.
      have h_split : ((∀ b : Fin (k + 1), y b < x b) ∧
            ∀ b c : Fin (k + 1), b.val + 1 = c.val → x c ≤ y b) ↔
          y 0 < x 0 ∧ (∀ b : Fin k, y b.succ < x b.succ) ∧
            ∀ b c : Fin k, b.val + 1 = c.val → x c.succ ≤ y b.succ := by
        simp [forall_fin_succ, fun b : Fin k ↦ not_lt.1 (h_none b), and_assoc]
      simp only [h_split, ite_zero_mul_ite_zero, mul_one]

omit [Add T] [One T] in
/-- The slab `degreeSlab k D` is bounded, where `D j` is a real number for each letter `j` of a
finite set `T`. -/
lemma isBounded_degreeSlab [Fintype T] (D : T → ℝ) : IsBounded (degreeSlab k D) := by
  -- A nonnegative entry is at most the degree of its block.
  refine (Metric.isBounded_Icc 0 fun x : Fin k × T ↦ D x.2).subset ?_
  rintro β ⟨h_nonneg, h_deg⟩
  exact ⟨h_nonneg, fun ⟨b, j⟩ ↦
    (single_le_sum (fun b' _ ↦ h_nonneg (b', j)) (Finset.mem_univ b)).trans (h_deg j).2⟩

omit [Add T] [One T] in
/-- The part of any set `Y` that lies in the slab `degreeSlab k D` is bounded. -/
lemma isBounded_inter_degreeSlab [Fintype T] (D : T → ℝ) (Y : Set (Fin k × T → ℝ)) :
    IsBounded (Y ∩ degreeSlab k D) :=
  (isBounded_degreeSlab D).subset inter_subset_right

end StepMap

/-- The determinant `det (1 - τ / q)`, where the permutation `τ` acts on `Fin k → ℝ` by permuting
coordinates, `x ↦ x ∘ τ`. -/
noncomputable def detOneSubPerm (q : ℝ) (τ : Perm (Fin k)) : ℝ :=
  (1 - q⁻¹ • funLeft ℝ ℝ τ : Module.End ℝ (Fin k → ℝ)).det

variable (P : ℝ)

/-- For linear maps `A : ℝ^ι → ℝ^κ` and `B : ℝ^κ → ℝ^ι`, the endomorphisms `1 - A B` and
`1 - B A` have the same determinant. -/
lemma det_one_sub_comp_comm {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : (ι → ℝ) →ₗ[ℝ] κ → ℝ) (B : (κ → ℝ) →ₗ[ℝ] ι → ℝ) :
    (1 - A ∘ₗ B).det = (1 - B ∘ₗ A).det := by
  rw [← det_toMatrix', ← det_toMatrix', map_sub, map_sub, toMatrix'_one, toMatrix'_one,
    toMatrix'_comp, toMatrix'_comp, det_one_sub_mul_comm]

/-- For `P > 1` the step map `permStep v P σ` has nonzero determinant. -/
lemma det_permStep_ne_zero (v : Fin (m + 1) → Bool) (hP : 1 < P)
    (σ : Fin (m + 1) → Equiv.Perm (Fin k)) :
    (permStep v P σ).det ≠ 0 := by
  intro h_det
  obtain ⟨ν, hν, h_ne⟩ := (Submodule.ne_bot_iff _).1 (bot_lt_ker_of_det_eq_zero h_det).ne'
  -- In the kernel `P • ν` only rearranges the entries of `ν`, so `P ‖ν‖ ≤ ‖ν‖`.
  have h_step (b : Fin k) (j : Fin (m + 1)) : P * ν (b, j + 1) = ν (σ j b, j) := by
    have h_entry : permStep v P σ ν (b, j) = 0 := congrFun (mem_ker.1 hν) (b, j)
    rw [permStep_apply] at h_entry; split_ifs at h_entry <;> linarith
  have h_eq : P • ν = ν ∘ fun x : Fin k × Fin (m + 1) ↦ (σ (x.2 - 1) x.1, x.2 - 1) := by
    ext ⟨b, j⟩
    simpa using h_step b (j - 1)
  have h_le : P * ‖ν‖ ≤ ‖ν‖ :=
    calc P * ‖ν‖ = ‖P • ν‖ := by rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hP.le)]
      _ ≤ ‖ν‖ := (congrArg norm h_eq).trans_le (pi_norm_comp_le ν _)
  nlinarith [norm_pos_iff.2 h_ne]

/-- Let `P > 1`. The step map `permStep v P σ` takes `ν` to the vector with entries
`± (P * ν (b, j + 1) - ν (σ j b, j))`, with `+` where `v j` is true, `-` where it is false, and
`j + 1` taken in `Fin (m + 1)`. Up to a constant that does not depend on `σ`, its determinant is
`detOneSubPerm (P ^ (m + 1)) σ̄ = det (1 - σ̄ / P ^ (m + 1))`, where `σ̄ = (ofFn σ).prod` is the
product `σ 0 * ⋯ * σ m`, acting by permuting coordinates. -/
lemma exists_det_permStep_eq (v : Fin (m + 1) → Bool) (hP : 1 < P) :
    ∃ c : ℝ, ∀ σ : Fin (m + 1) → Equiv.Perm (Fin k),
      (permStep v P σ).det = c * detOneSubPerm (P ^ (m + 1)) (ofFn σ).prod := by
  -- Factor the step map. `E` is the signed shift `ν_j ↦ ± ν_(j+1)` and `N` the triangular map
  -- `ν_j ↦ P ν_j - ν_(j-1)` with `ν_(-1) = 0`; neither depends on `σ`.
  let E : Module.End ℝ (Fin k × Fin (m + 1) → ℝ) := permStep v 1 1 - permStep v 0 1
  let N : Module.End ℝ (Fin k × Fin (m + 1) → ℝ) :=
    P • 1 - .pi fun x : Fin k × Fin (m + 1) ↦
      Fin.cases 0 (fun j : Fin m ↦ proj (x.1, j.castSucc)) x.2
  refine ⟨E.det * N.det, fun σ ↦ ?_⟩
  -- `G` permutes block `j` by `σ_0 ⋯ σ_(j-1)`, which moves all the twist to the last step. There
  -- `A` reads the last block through `σ̄`, and `N ∘ B` places a vector in block `0`.
  let π : Perm (Fin k × Fin (m + 1)) := prodCongrLeft fun j ↦ partialProd σ j.castSucc
  let G : Module.End ℝ (Fin k × Fin (m + 1) → ℝ) := toLin' (permMatrix ℝ π)
  let A : (Fin k × Fin (m + 1) → ℝ) →ₗ[ℝ] Fin k → ℝ :=
    funLeft ℝ ℝ fun b ↦ (partialProd σ (last (m + 1)) b, last m)
  let B : (Fin k → ℝ) →ₗ[ℝ] Fin k × Fin (m + 1) → ℝ := pi fun x ↦ P⁻¹ ^ x.2.val.succ • proj x.1
  have h_E (ν : Fin k × Fin (m + 1) → ℝ) (b : Fin k) (j : Fin (m + 1)) :
      E ν (b, j) = (if v j then 1 else -1) * ν (b, j + 1) := by
    cases hv : v j <;> simp [E, hv]
  have h_G (ν : Fin k × Fin (m + 1) → ℝ) (b : Fin k) (j : Fin (m + 1)) :
      G ν (b, j) = ν (partialProd σ j.castSucc b, j) := by simp [G, π, permMatrix_mulVec]
  -- After `1 - B ∘ₗ A`, the map `N` subtracts the preceding block, read cyclically through `σ̄`.
  have h_N (ν : Fin k × Fin (m + 1) → ℝ) (b : Fin k) (i : Fin (m + 1)) :
      N ((1 - B ∘ₗ A) ν) (b, i) =
        P * ν (b, i) - Fin.cases (ν (partialProd σ (last (m + 1)) b, last m))
          (fun j : Fin m ↦ ν (b, j.castSucc)) i := by
    cases i using Fin.cases <;>
      simp [N, A, B, mul_sub, (zero_lt_one.trans hP).ne', pow_succ, mul_assoc]
  have h_factor : permStep v P σ * G = E * G * N * (1 - B ∘ₗ A) := by
    refine LinearMap.ext fun ν ↦ funext fun ⟨b, j⟩ ↦ ?_
    simp only [Module.End.mul_apply, permStep_apply, h_E, h_G, h_N]
    -- Compare the entries by `partialProd σ j.succ = partialProd σ j.castSucc * σ j`.
    cases j using lastCases <;> simp [← succ_last, partialProd_succ]
  have h_AB : (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ (ofFn σ).prod = A ∘ₗ B :=
    LinearMap.ext fun x ↦ funext fun b ↦ by simp [A, B, partialProd, take_of_length_le]
  -- Cancel `det G = ± 1` and use `det (1 - B A) = det (1 - A B)`.
  have h_det : (permStep v P σ).det * G.det = E.det * G.det * N.det * (1 - B ∘ₗ A).det := by
    simp only [← map_mul, h_factor]
  rw [detOneSubPerm, h_AB, det_one_sub_comp_comm A B]
  exact mul_right_cancel₀ (show G.det ≠ 0 by simp [G]) (by linear_combination h_det)

/-- Change of variables for `P > 1`. The degree of a vector `β` at a letter `j` is `∑ b, β (b, j)`,
and `degreeSlab k D` is the set of `β ≥ 0` whose degree at each `j` lies in `[D j - 1, D j]`. The
set `positiveStepSet v P D σ τ Y` consists of the `ν` such that `permStep v P 1 ν` has its degrees
in these intervals and `permStep v P σ` sends `ν`, with block `j` rearranged by `τ j`, to a vector
of `Y` with positive entries. Its volume is the volume of `Y ∩ degreeSlab k D` divided by
`|det (permStep v P σ)|`. -/
lemma volume_positiveStepSet (v : Fin (m + 1) → Bool) (hP : 1 < P) (D : Fin (m + 1) → ℝ)
    (σ τ : Fin (m + 1) → Perm (Fin k)) (Y : Set (Fin k × Fin (m + 1) → ℝ)) :
    volume (positiveStepSet v P D σ τ Y) =
      ENNReal.ofReal |(permStep v P σ).det|⁻¹ * volume (Y ∩ degreeSlab k D) := by
  let L : Module.End ℝ (Fin k × Fin (m + 1) → ℝ) :=
    permStep v P σ * toLin' (permMatrix ℝ (prodCongrLeft τ))
  have hL (ν : Fin k × Fin (m + 1) → ℝ) : L ν = permStep v P σ (ν ∘ prodCongrLeft τ) := by
    simp [L, permMatrix_mulVec]
  have hL_det : L.det ≠ 0 := by simpa [L] using det_permStep_ne_zero P v hP σ
  -- The degrees do not see `σ` and `τ`.
  have h_deg (ν : Fin k × Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
      ∑ b : Fin k, L ν (b, j) = ∑ b : Fin k, permStep v P 1 ν (b, j) := by
    have h_sum (e : Perm (Fin k)) (i : Fin (m + 1)) : ∑ b, ν (e b, i) = ∑ b, ν (b, i) :=
      Equiv.sum_comp e fun b ↦ ν (b, i)
    have h_sum_mul : ∑ b, ν (τ j (σ j b), j) = ∑ b, ν (b, j) := h_sum (τ j * σ j) j
    cases hv : v j <;> simp [hL, hv, ← mul_sum, h_sum, h_sum_mul]
  have h_pre : positiveStepSet v P D σ τ Y = L ⁻¹' (Y ∩ degreeSlab k D ∩ {β | ∀ x, β x ≠ 0}) := by
    ext ν
    simp only [positiveStepSet, degreeSlab, ← hL, ← h_deg, Set.mem_preimage, Set.mem_inter_iff,
      mem_ofPred_eq, Pi.le_def, Pi.zero_apply, Prod.forall]
    exact ⟨fun ⟨h_sum, h_pos, h_mem⟩ ↦
        ⟨⟨h_mem, fun b j ↦ (h_pos j b).le, h_sum⟩, fun b j ↦ (h_pos j b).ne'⟩,
      fun ⟨⟨h_mem, h_nonneg, h_sum⟩, h_ne⟩ ↦
        ⟨h_sum, fun j b ↦ (h_nonneg b j).lt_of_ne' (h_ne b j), h_mem⟩⟩
  -- The walls `β x = 0` are null.
  have h_walls : ∀ᵐ β : Fin k × Fin (m + 1) → ℝ, ∀ x, β x ≠ 0 :=
    ae_all_iff.2 fun x ↦ ae_eval_ne _ x 0
  rw [h_pre, addHaar_preimage_linearMap _ hL_det, measure_inter_conull h_walls]
  simp [L, abs_unit_intCast, abs_inv]

open Classical in
/-- Let `P ≥ 0` and let `τ j` sort block `j` of `ν` decreasingly, giving `ν'`. The step
`permStep v P σ ν (b, j)` is `± (P * ν (b, j + 1) - ν (σ j b, j))`, with `+` where `v j` is true,
`-` where it is false, and `j + 1` taken in `Fin (m + 1)`. The signs of `σ 0 * ⋯ * σ m`, summed over
the `σ` with all these steps positive, add up to `1` if the steps `permStep v P 1 ν'` are positive
and `ν'` lies in `pieriCone v P`, and to `0` otherwise. -/
lemma sum_sign_indicator_pos_eq_indicator_pieriCone (v : Fin (m + 1) → Bool) (hP : 0 ≤ P)
    {ν : Fin k × Fin (m + 1) → ℝ} {τ : Fin (m + 1) → Perm (Fin k)}
    (h_anti : ∀ j : Fin (m + 1), Antitone fun b : Fin k ↦ ν (τ j b, j)) :
    ∑ σ : Fin (m + 1) → Perm (Fin k),
        (if ∀ (j : Fin (m + 1)) (b : Fin k), 0 < permStep v P σ ν (b, j) then
          (sign (ofFn σ).prod : ℝ) else 0) =
      if (∀ (j : Fin (m + 1)) (b : Fin k), 0 < permStep v P 1 (ν ∘ prodCongrLeft τ) (b, j)) ∧
        ν ∘ prodCongrLeft τ ∈ pieriCone v P then 1 else 0 := by
  -- Both sides are the product over `j` of the determinants of the indicators of positive steps.
  -- `M j b' b` indicates that the step at `(b, j)` is positive if `σ j b = b'` (the transposition
  -- serves only as some permutation sending `b` to `b'`).
  let M (j : Fin (m + 1)) : Matrix (Fin k) (Fin k) ℝ :=
    of fun b' b ↦ if 0 < permStep v P (fun _ ↦ .swap b b') ν (b, j) then 1 else 0
  trans ∏ j, ((M j).reindex (τ j).symm (τ (j + 1)).symm).det
  · -- Expand the determinants; the signs of the `τ j` occur twice and cancel.
    have h_entries (σ : Fin (m + 1) → Perm (Fin k)) : ∏ j, ∏ b, M j (σ j b) b =
        if ∀ (j : Fin (m + 1)) (b : Fin k), 0 < permStep v P σ ν (b, j) then 1 else 0 := by
      simp [M, Fintype.prod_ite_zero]
    have h_sign (σ : Fin (m + 1) → Perm (Fin k)) :
        (sign (ofFn σ).prod : ℝ) = ∏ j, (sign (σ j) : ℝ) := by
      simp [map_list_prod, List.map_ofFn, List.prod_ofFn, prod_univ_succ]
    have h_cancel : ∏ j, (sign (τ j) : ℝ) * sign (τ (j + 1)) = 1 := by
      rw [prod_mul_distrib,
        (AddGroup.addRight_bijective 1).prod_comp fun j ↦ (sign (τ j) : ℝ), ← prod_mul_distrib]
      simp [← Int.cast_mul, ← Units.val_mul]
    calc
      _ = ∑ σ : Fin (m + 1) → Perm (Fin k),
            ∏ j, (sign (σ j) : ℝ) * ∏ b, M j (σ j b) b := by
          simp only [prod_mul_distrib, h_entries, h_sign, mul_ite, mul_one, mul_zero]
      _ = ∏ j, (M j).det := by simp only [det_apply', prod_univ_sum, piFinset_univ]
      _ = ∏ j, ((sign (τ j) : ℝ) * sign (τ (j + 1))) * (M j).det := by
          rw [prod_mul_distrib, h_cancel, one_mul]
      _ = ∏ j, ((M j).reindex (τ j).symm (τ (j + 1)).symm).det := by
          exact prod_congr rfl fun j _ ↦ by rw [Matrix.det_reindex]; simp
  · -- After sorting, each factor is an interlacing determinant.
    let ν' : Fin k × Fin (m + 1) → ℝ := ν ∘ prodCongrLeft τ
    have h_det (j : Fin (m + 1)) : ((M j).reindex (τ j).symm (τ (j + 1)).symm).det =
        if ∀ b : Fin k, 0 < permStep v P 1 ν' (b, j) ∧ ∀ b' : Fin k, b.val + 1 = b' →
            permStep v P 1 ν' ((if v j then b' else b), j) ≤ ν' (b, j) - ν' (b', j) then 1
        else 0 := by
      have h_anti_mul : Antitone fun b ↦ P * ν (τ (j + 1) b, j + 1) := (h_anti (j + 1)).const_mul hP
      by_cases hv : v j
      · have h_matrix : (M j).reindex (τ j).symm (τ (j + 1)).symm =
            (of fun b c : Fin k ↦
              if ν (τ j c, j) < P * ν (τ (j + 1) b, j + 1) then (1 : ℝ) else 0)ᵀ := by
          simp [M, ← ext_iff, hv]
        rw [h_matrix, det_transpose, det_interlacing_indicator h_anti_mul (h_anti j)]
        simp [ν', hv, forall_and]
      · have h_matrix : (M j).reindex (τ j).symm (τ (j + 1)).symm =
            of fun b c : Fin k ↦
              if P * ν (τ (j + 1) c, j + 1) < ν (τ j b, j) then (1 : ℝ) else 0 := by
          simp [M, ← ext_iff, hv]
        rw [h_matrix, det_interlacing_indicator (h_anti j) h_anti_mul]
        simp [ν', hv, forall_and, sub_add]
    simp only [h_det, Fintype.prod_boole]
    congr! 1
    simp only [ν', pieriCone, mem_ofPred_eq, forall_and]

/-- Counting in two ways at a point `ν`, for `P ≥ 0`. The cone `pieriCone v P` requires
`P * ν (b + 1, j + 1) ≤ ν (b, j)` where `v j` is true and `ν (b + 1, j) ≤ P * ν (b, j + 1)`
elsewhere. Let `Ω` pull back to this cone under `permStep v P 1`. The set
`positiveStepSet v P D σ τ Y` consists of the `ν` with `∑ b, permStep v P 1 ν (b, j)` in
`[D j - 1, D j]` for all `j` such that `permStep v P σ` sends `ν`, with each block `j` rearranged by
`τ j`, to a vector of `Y` with positive entries. Then the number of `τ` with `ν` in
`positiveStepSet v P D 1 τ Ω` equals the number of `σ` with `ν` in `positiveStepSet v P D σ 1 univ`,
each `σ` counted with the sign of `σ 0 * ⋯ * σ m`. -/
lemma sum_indicator_positiveStepSet {v : Fin (m + 1) → Bool} (hP : 0 ≤ P) (D : Fin (m + 1) → ℝ)
    {Ω : Set (Fin k × Fin (m + 1) → ℝ)}
    (hΩ : ∀ ν : Fin k × Fin (m + 1) → ℝ, permStep v P 1 ν ∈ Ω ↔ ν ∈ pieriCone v P)
    (ν : Fin k × Fin (m + 1) → ℝ) :
    ∑ τ : Fin (m + 1) → Perm (Fin k), (positiveStepSet v P D 1 τ Ω).indicator (fun _ ↦ (1 : ℝ)) ν =
      ∑ σ : Fin (m + 1) → Perm (Fin k),
        (positiveStepSet v P D σ 1 univ).indicator (fun _ ↦ (sign (ofFn σ).prod : ℝ)) ν := by
  classical
  -- Only the `τ` that sorts every block of `ν` decreasingly can contribute on the left.
  let τ (j : Fin (m + 1)) : Perm (Fin k) := sort fun b ↦ -ν (b, j)
  have h_anti (j : Fin (m + 1)) : Antitone fun b : Fin k ↦ ν (τ j b, j) := fun b b' h_le ↦
    neg_le_neg_iff.1 (monotone_sort (fun b ↦ -ν (b, j)) h_le)
  have h_sort (τ' : Fin (m + 1) → Perm (Fin k)) (hτ' : ν ∈ positiveStepSet v P D 1 τ' Ω) :
      τ' = τ := by
    obtain ⟨-, h_pos, h_mem⟩ := hτ'
    -- A positive step bounded by `ν (τ' j b, j) - ν (τ' j b', j)` makes that difference positive.
    have h_desc (j : Fin (m + 1)) (b b' : Fin k) (h_succ : b.val + 1 = b') :
        ν (τ' j b', j) < ν (τ' j b, j) :=
      sub_pos.1 ((h_pos j (if v j then b' else b)).trans_le ((hΩ _).1 h_mem j b b' h_succ))
    exact funext fun j ↦ eq_sort_iff'.2 ((strictMono_iff_forall_covBy _).2 fun b b' h_cov ↦
      Prod.Lex.left _ _ (neg_lt_neg (h_desc j b b' h_cov.coe_fin.succ_eq)))
  rw [sum_eq_single τ fun τ' h_ne ↦ indicator_of_notMem (mt (h_sort τ') h_ne) _]
  by_cases h_deg : ∀ j, ∑ b, permStep v P 1 ν (b, j) ∈ Icc (D j - 1) (D j)
  · have h_left : ν ∈ positiveStepSet v P D 1 τ Ω ↔
        (∀ (j : Fin (m + 1)) (b : Fin k), 0 < permStep v P 1 (ν ∘ prodCongrLeft τ) (b, j)) ∧
          ν ∘ prodCongrLeft τ ∈ pieriCone v P := by
      simp only [positiveStepSet, mem_ofPred_eq, h_deg, hΩ, implies_true, true_and]
    have h_right (σ : Fin (m + 1) → Perm (Fin k)) : ν ∈ positiveStepSet v P D σ 1 univ ↔
        ∀ (j : Fin (m + 1)) (b : Fin k), 0 < permStep v P σ ν (b, j) := by
      simp only [positiveStepSet, mem_ofPred_eq, h_deg, implies_true, true_and, Set.mem_univ,
        and_true, show ν ∘ prodCongrLeft (1 : Fin (m + 1) → Perm (Fin k)) = ν from rfl]
    simp only [indicator_apply, h_left, h_right]
    simpa using (sum_sign_indicator_pos_eq_indicator_pieriCone P v hP h_anti).symm
  · simp only [indicator_apply, positiveStepSet, mem_ofPred_eq, h_deg, false_and, ite_false,
      sum_const_zero]

/-- For `f` on permutations of `Fin k`, the sum of `f (σ 0 * ⋯ * σ m)` over all families `σ` is
`k ! ^ m` times the sum of `f`: choose `σ 1, …, σ m` and solve for `σ 0`. -/
lemma sum_comp_prod_ofFn (f : Perm (Fin k) → ℝ) :
    ∑ σ : Fin (m + 1) → Perm (Fin k), f (ofFn σ).prod =
      k.factorial ^ m * ∑ τ : Perm (Fin k), f τ := by
  let e : Perm (Fin k) × (Fin m → Perm (Fin k)) ≃ (Fin (m + 1) → Perm (Fin k)) :=
    (prodCongrLeft fun g ↦ .mulRight (ofFn g).prod⁻¹).trans (consEquiv fun _ ↦ Perm (Fin k))
  rw [← e.sum_comp]
  simp [e, sum_prod_type_right, card_perm]

/-- Let `P > 1` and `q = P ^ (m + 1)`. Let `Ω` be a set whose preimage under the step map is the
cone. Then `Ω` fills the fraction `|det (1 - id / q)| / k ! * ∑ τ, sign τ / |det (1 - τ / q)|` of
the volume of the slab `degreeSlab k D` of vectors `β ≥ 0` with `∑ b, β (b, j)` in `[D j - 1, D j]`
for all `j`. -/
lemma volume_real_inter_degreeSlab_eq_signed_sum {v : Fin (m + 1) → Bool} (hP : 1 < P)
    (D : Fin (m + 1) → ℝ) {Ω : Set (Fin k × Fin (m + 1) → ℝ)}
    (hΩ : ∀ ν : Fin k × Fin (m + 1) → ℝ, permStep v P 1 ν ∈ Ω ↔ ν ∈ pieriCone v P) :
    volume.real (Ω ∩ degreeSlab k D) =
      |detOneSubPerm (P ^ (m + 1)) (1 : Perm (Fin k))| / k.factorial *
        (∑ τ : Perm (Fin k), τ.sign / |detOneSubPerm (P ^ (m + 1)) τ|) *
          volume.real (degreeSlab k D) := by
  -- Integrate the pointwise count `sum_indicator_positiveStepSet` over `ν`: each set is a linear
  -- preimage of a part of the slab, and the determinants are known up to a common constant.
  let Δ (τ : Perm (Fin k)) : ℝ := |detOneSubPerm (P ^ (m + 1)) τ|
  show _ = Δ 1 / k.factorial * (∑ τ : Perm (Fin k), τ.sign / Δ τ) * volume.real (degreeSlab k D)
  obtain ⟨c, hc⟩ := exists_det_permStep_eq (k := k) P v hP
  obtain ⟨hc_ne, hΔ_ne⟩ : c ≠ 0 ∧ Δ 1 ≠ 0 := by
    simpa [hc, Δ] using det_permStep_ne_zero (k := k) P v hP 1
  have h_fin (σ τ : Fin (m + 1) → Perm (Fin k)) (Y : Set (Fin k × Fin (m + 1) → ℝ)) :
      volume (positiveStepSet v P D σ τ Y) ≠ ⊤ := by
    rw [volume_positiveStepSet P v hP]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (isBounded_inter_degreeSlab D Y).measure_lt_top.ne
  have h_vol (σ τ : Fin (m + 1) → Perm (Fin k)) (Y : Set (Fin k × Fin (m + 1) → ℝ)) :
      volume.real (positiveStepSet v P D σ τ Y) =
        (|c| * Δ (ofFn σ).prod)⁻¹ * volume.real (Y ∩ degreeSlab k D) := by
    simp [Measure.real, volume_positiveStepSet P v hP, hc, abs_mul, Δ, abs_nonneg]
  have h_meas_univ (σ : Fin (m + 1) → Perm (Fin k)) :
      MeasurableSet (positiveStepSet v P D σ 1 univ) := by
    simp only [positiveStepSet, measurableSet_setOfPred, Set.mem_Icc, Set.mem_univ]; fun_prop
  have h_meas_Ω (τ : Fin (m + 1) → Perm (Fin k)) :
      MeasurableSet (positiveStepSet v P D 1 τ Ω) := by
    simp only [positiveStepSet, hΩ, pieriCone, mem_ofPred_eq, measurableSet_setOfPred, Set.mem_Icc]
    fun_prop
  have h_int : ∑ τ : Fin (m + 1) → Perm (Fin k), volume.real (positiveStepSet v P D 1 τ Ω) =
      ∑ σ : Fin (m + 1) → Perm (Fin k),
        volume.real (positiveStepSet v P D σ 1 univ) * sign (ofFn σ).prod := by
    have h_count : ∫ ν, ∑ τ, (positiveStepSet v P D 1 τ Ω).indicator (fun _ ↦ (1 : ℝ)) ν =
        ∫ ν, ∑ σ : Fin (m + 1) → Perm (Fin k),
          (positiveStepSet v P D σ 1 univ).indicator (fun _ ↦ (sign (ofFn σ).prod : ℝ)) ν := by
      simp_rw [sum_indicator_positiveStepSet P (zero_le_one.trans hP.le) D hΩ]
    rw [integral_finsetSum, integral_finsetSum] at h_count
    · simpa [h_meas_univ, h_meas_Ω] using h_count
    · exact fun σ _ ↦ (integrableOn_const (h_fin σ 1 univ)).integrable_indicator (h_meas_univ σ)
    · exact fun τ _ ↦ (integrableOn_const (h_fin 1 τ Ω)).integrable_indicator (h_meas_Ω τ)
  have h_eq : (k.factorial : ℝ) ^ (m + 1) * ((|c| * Δ 1)⁻¹ * volume.real (Ω ∩ degreeSlab k D)) =
      k.factorial ^ m * ∑ τ : Perm (Fin k),
        (|c| * Δ τ)⁻¹ * volume.real (degreeSlab k D) * sign τ := by
    simpa [← sum_comp_prod_ofFn, h_vol, card_perm] using h_int
  have h_sum : ∑ τ : Perm (Fin k), (|c| * Δ τ)⁻¹ * volume.real (degreeSlab k D) * sign τ =
      |c|⁻¹ * (∑ τ : Perm (Fin k), τ.sign / Δ τ) * volume.real (degreeSlab k D) := by
    rw [mul_sum, sum_mul]
    exact sum_congr rfl fun τ _ ↦ by ring
  rw [h_sum, pow_succ] at h_eq
  field_simp at h_eq ⊢
  linear_combination h_eq

end SignedCount

section InterlacingCone

open Finset Matrix MeasureTheory Equiv LinearMap ENNReal

/-- The slab of one letter, the nonnegative vectors of `ℝ ^ k` with sum at most `1`, has positive
volume. -/
lemma volume_real_degreeSlab_one_pos (k : ℕ) : 0 < volume.real (degreeSlab k (1 : Fin 1 → ℝ)) := by
  let a : Fin k × Fin 1 → ℝ := fun _ ↦ (k : ℝ)⁻¹
  have h_box : Set.Icc 0 a ⊆ degreeSlab k (1 : Fin 1 → ℝ) := fun β ⟨h_low, h_up⟩ ↦
    ⟨h_low, fun j ↦ ⟨by simpa using sum_nonneg fun b _ ↦ h_low (b, j),
      (sum_le_sum fun b _ ↦ h_up (b, j)).trans (by simp [a, mul_inv_le_one])⟩⟩
  have h_box_pos : 0 < volume.real (Set.Icc 0 a) :=
    toReal_pos (by simp [a, Real.volume_Icc_pi]) measure_Icc_lt_top.ne
  exact h_box_pos.trans_le (measureReal_mono h_box (isBounded_degreeSlab 1).measure_lt_top.ne)

/-- The case of one letter, the only element of `Fin 1`, with sign `+` (`⊤` is the constant function
`true`). For `q > 1` the cone `pieriCone ⊤ q` of vectors with `q * β (b + 1) ≤ β b` fills the
fraction `∏ b < k, (q - 1) / (q ^ (b + 1) - 1)` of `degreeSlab k 1`, the simplex of vectors `β ≥ 0`
in `ℝ ^ k` with `∑ b, β b` in `[0, 1]`. -/
lemma volume_real_pieriCone_inter_degreeSlab_one (k : ℕ) {q : ℝ} (hq : 1 < q) :
    volume.real (pieriCone ⊤ q ∩ degreeSlab k (1 : Fin 1 → ℝ)) =
      (∏ b : Fin k, (q ^ (b.val + 1) - 1) / (q - 1))⁻¹ *
        volume.real (degreeSlab k (1 : Fin 1 → ℝ)) := by
  -- The nonnegative part of the cone is an orthant in the coordinates `β b - q β (b + 1)`. Rescaled
  -- by `d b`, they define a triangular map `F` that keeps the degree `∑ b, β b`.
  let d (i : ℕ) : ℝ := (q ^ (i + 1) - 1) / (q - 1)
  have hd_pos (i : ℕ) : 0 < d i := by simp [d, one_lt_pow₀, hq]
  have hd_zero : d 0 = 1 := by simp [d, sub_ne_zero, hq.ne']
  have hd_succ (i : ℕ) : d (i + 1) - 1 = q * d i := by
    simp only [d]; field_simp [sub_ne_zero.2 hq.ne']; ring
  let coord (b : ℕ) : (Fin k × Fin 1 → ℝ) →ₗ[ℝ] ℝ := if h : b < k then .proj (⟨b, h⟩, 0) else 0
  have h_coord (b : Fin k) (β : Fin k × Fin 1 → ℝ) : coord b β = β (b, 0) := by simp [coord]
  let F : Module.End ℝ (Fin k × Fin 1 → ℝ) := pi fun x ↦ d x.1 • (coord x.1 - q • coord (x.1 + 1))
  have hF (β : Fin k × Fin 1 → ℝ) (b : Fin k) :
      F β (b, 0) = d b * (β (b, 0) - q * coord (b + 1) β) := by simp [F, h_coord]
  have h_det : F.det = ∏ b : Fin k, d b := by
    have h_tri : ((toMatrix' F).reindex (prodUnique _ _) (prodUnique _ _)).IsUpperTriangular := by
      intro b b' h_lt
      have h_ne : b.val ≠ b'.val ∧ b.val + 1 ≠ b'.val :=
        ⟨(Fin.lt_def.1 h_lt).ne', (Nat.lt_succ_of_lt (Fin.lt_def.1 h_lt)).ne'⟩
      simp [Fin.ext_iff, F, coord, DFunLike.dite_apply, h_ne]
    rw [← det_toMatrix', ← det_reindex_self (prodUnique _ _), det_of_isUpperTriangular h_tri]
    simp [Fin.ext_iff, F, coord, DFunLike.dite_apply]
  have h_det_pos : 0 < F.det := by simp [prod_pos, h_det, hd_pos]
  have h_deg (β : Fin k × Fin 1 → ℝ) : ∑ b, F β (b, 0) = ∑ b, β (b, 0) := by
    rw [← sub_eq_zero, ← sum_sub_distrib]
    calc ∑ b : Fin k, (F β (b, 0) - β (b, 0))
        = ∑ b ∈ range k, ((d b - 1) * coord b β - (d (b + 1) - 1) * coord (b + 1) β) := by
          rw [sum_range]
          exact sum_congr rfl fun b _ ↦ by rw [hF, hd_succ, h_coord]; ring
      _ = 0 := by rw [sum_range_sub' fun b ↦ (d b - 1) * coord b β]; simp [hd_zero, coord]
  have h_pre : pieriCone ⊤ q ∩ degreeSlab k 1 = F ⁻¹' degreeSlab k 1 := by
    ext β
    have h_nonneg : 0 ≤ F β ↔ ∀ b : Fin k, q * coord (b + 1) β ≤ β (b, 0) := by
      simp [Pi.le_def, hF, hd_pos]
    suffices h_orthant :
        (∀ b b' : Fin k, b.val + 1 = b' → q * β (b', 0) ≤ β (b, 0)) ∧ 0 ≤ β ↔ 0 ≤ F β by
      simp [pieriCone, degreeSlab, h_deg, ← and_assoc, ← h_orthant]
    rw [h_nonneg]
    refine ⟨fun ⟨h_step, hβ⟩ b ↦ ?_, fun h_step ↦
      ⟨fun b b' h_succ ↦ by simpa [h_succ, h_coord] using h_step b, fun ⟨b, j⟩ ↦ ?_⟩⟩
    · by_cases hb : b.val + 1 < k
      · simpa [coord, hb] using h_step b ⟨b + 1, hb⟩ rfl
      · simpa [coord, hb] using hβ (b, 0)
    · -- `0 ≤ β b` for the last `b`; descend to all `b`.
      obtain rfl : j = 0 := Subsingleton.elim j 0
      induction b using WellFoundedGT.induction with
      | ind b ih =>
        refine (mul_nonneg (zero_le_one.trans hq.le) ?_).trans (h_step b)
        by_cases hb : b.val + 1 < k
        · simpa [coord, hb] using ih ⟨b + 1, hb⟩ (Nat.lt_succ_self b)
        · simp [coord, hb]
  rw [h_pre, Measure.real, volume.addHaar_preimage_linearMap h_det_pos.ne', toReal_mul,
    toReal_ofReal (abs_nonneg _), abs_inv, abs_of_pos h_det_pos, h_det, Measure.real]

/-- Volume of the image of the cone in a slab. Let `P > 1` and `q = P ^ N`, and let `Ω` be a set
whose preimage under the step map is the cone. Then the volume of `Ω ∩ degreeSlab k D`, multiplied
by `∏ l < k, (q ^ (l + 1) - 1) / (q - 1)`, equals the volume of the slab. -/
theorem prod_mul_volume_real_inter_degreeSlab {k N : ℕ} [NeZero N] {v : ZMod N → Bool} {P : ℝ}
    (hP : 1 < P) (D : ZMod N → ℝ) {Ω : Set (Fin k × ZMod N → ℝ)}
    (hΩ : ∀ ν : Fin k × ZMod N → ℝ, permStep v P 1 ν ∈ Ω ↔ ν ∈ pieriCone v P) :
    (∏ l : Fin k, ((P ^ N) ^ (l.val + 1) - 1) / (P ^ N - 1)) * volume.real (Ω ∩ degreeSlab k D) =
      volume.real (degreeSlab k D) := by
  -- By `volume_real_inter_degreeSlab_eq_signed_sum` the share `c` of `Ω` in the slab depends only
  -- on `k` and `q = P ^ N`. So it can be computed for one letter with the sign `+` and `q` in place
  -- of `P`.
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = m + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  set q : ℝ := P ^ (m + 1)
  have hq : 1 < q := one_lt_pow₀ hP m.succ_ne_zero
  let c : ℝ := |detOneSubPerm q (1 : Perm (Fin k))| / k.factorial *
    ∑ τ : Perm (Fin k), τ.sign / |detOneSubPerm q τ|
  -- `ZMod (m + 1)` is `Fin (m + 1)` by definition.
  have h_share : volume.real (Ω ∩ degreeSlab k D) = c * volume.real (degreeSlab k D) :=
    volume_real_inter_degreeSlab_eq_signed_sum P hP D hΩ
  have h_block : volume.real (pieriCone ⊤ q ∩ degreeSlab k (1 : Fin 1 → ℝ)) =
      c * volume.real (degreeSlab k (1 : Fin 1 → ℝ)) := by
    -- For one letter the step map is the homothety of ratio `q - 1 > 0`.
    have h_cone (ν : Fin k × Fin 1 → ℝ) :
        permStep ⊤ q 1 ν ∈ pieriCone ⊤ q ↔ ν ∈ pieriCone ⊤ q := by
      have h_pos : 0 < q - 1 := sub_pos.2 hq
      simp [pieriCone, field]
    simpa only [zero_add, pow_one] using volume_real_inter_degreeSlab_eq_signed_sum (m := 0) q hq 1
      h_cone
  have hc : (∏ l : Fin k, (q ^ (l.val + 1) - 1) / (q - 1))⁻¹ = c :=
    mul_right_cancel₀ (volume_real_degreeSlab_one_pos k).ne'
      ((volume_real_pieriCone_inter_degreeSlab_one k hq).symm.trans h_block)
  rw [h_share, ← hc, mul_inv_cancel_left₀ (prod_pos fun l _ ↦ by simp [one_lt_pow₀, hq]).ne']

end InterlacingCone

end New
