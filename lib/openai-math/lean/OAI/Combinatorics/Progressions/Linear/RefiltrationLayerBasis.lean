/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.GradedUnitEvaluation

namespace OAI

section

namespace Erdos3

open Module

theorem span_selected_basis {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (S : Set ι) [DecidablePred (· ∈ S)] :
    Submodule.span ℚ (Set.range (fun i => if i ∈ S then b i else 0)) =
      Submodule.span ℚ (b '' S) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (if i ∈ S then b i else 0) ∈ Submodule.span ℚ (b '' S)
    split_ifs with hi
    · exact Submodule.subset_span ⟨i, hi, rfl⟩
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    simpa only [ite_eq_left hi] using
      (Submodule.subset_span (s := Set.range (fun i => if i ∈ S then b i else 0)) ⟨i, rfl⟩)

namespace NilpotentLieFiltration

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem exists_refiltration_layer_basis_of_quotient
    {κ : Type*} [Fintype κ] (W : LieSubalgebra ℚ F.AssociatedGraded)
    (f : Basis κ ℚ (F.AssociatedGraded ⧸ W.toSubmodule)) {H : ℕ} (hH : 1 ≤ H)
    (hf : ∀ i k, RationalHeightLE
      (f.repr (W.toSubmodule.mkQ (F.associatedGradedBasis b w hlayers i)) k) H) (j : ℕ) :
    ∃ r : ℕ, r ≤ Fintype.card κ ∧
      ∃ e : Basis (Fin (finrank ℚ (F.gradedRefiltrationLayer W j))) ℚ (F.gradedRefiltrationLayer W j),
        ∀ i k, RationalHeightLE (b.repr (e i : L) k)
          ((Fintype.card ι + 1) * rationalKernelHeight r H ^ Fintype.card ι) := by
  classical
  let v : ι → L := fun i => if j ≤ w i then b i else 0
  let P := W.toSubmodule.mkQ.comp (F.gradedPieceProjection b w hlayers j)
  have hv : ∀ i k, RationalHeightLE (b.repr (v i) k) 1 := by
    intro i k
    dsimp [v]
    split_ifs
    · exact basis_repr_height_one b i k
    · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero (by decide : 1 ≤ 1)
  have hPv : ∀ i k, RationalHeightLE (f.repr (P (v i)) k) H := by
    intro i k
    dsimp only [P, v, LinearMap.comp_apply]
    split_ifs
    · rw [F.gradedPieceProjection_basis]
      split_ifs
      · exact hf i k
      · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
    · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  have hspan : Submodule.span ℚ (Set.range v) = F.layer j := by
    rw [hlayers j]
    exact span_selected_basis b {i | j ≤ w i}
  have hker : F.layer j ⊓ LinearMap.ker P = F.gradedRefiltrationLayer W j := by
    rw [F.gradedRefiltrationLayer_eq_inf_comap b w hlayers W j]
    dsimp only [P]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  obtain ⟨r, hr, z, hz, hheight⟩ := exists_bounded_span_kernel_generators b f P v hH hv hPv
  rw [hspan, hker] at hz
  have hh : ∀ i k, RationalHeightLE (b.repr (z i) k)
      ((Fintype.card ι + 1) * rationalKernelHeight r H ^ Fintype.card ι) := by
    simpa only [mul_one] using hheight
  obtain ⟨e, he⟩ := exists_bounded_submodule_basis_from_spanning b _ z hz hh
  exact ⟨r, hr, e, he⟩

theorem exists_uniform_refiltration_layer_bases
    {κ : Type*} [Fintype κ] (W : LieSubalgebra ℚ F.AssociatedGraded)
    (v : κ → F.AssociatedGraded) (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i k, RationalHeightLE ((F.associatedGradedBasis b w hlayers).repr (v i) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ B : ℕ, 1 ≤ B ∧ (B : ℝ) ≤ Real.exp ((p + (p + 2) ^ 7 + 2) ^ 9) ∧
      ∀ j, ∃ e : Basis (Fin (finrank ℚ (F.gradedRefiltrationLayer W j))) ℚ (F.gradedRefiltrationLayer W j),
        ∀ i k, RationalHeightLE (b.repr (e i : L) k) B := by
  obtain ⟨A, hA, hAp, d, hdim, f, hf⟩ := exists_submodule_quotient_basis_exp
    (F.associatedGradedBasis b w hlayers) W.toSubmodule v hspan hH hv hp hκ hHp
  let B := (Fintype.card ι + 1) * rationalKernelHeight (Fintype.card ι) A ^ Fintype.card ι
  have hB : 1 ≤ B := by
    exact Nat.mul_le_mul (Nat.le_add_left 1 _) (one_le_pow₀ (rationalKernelHeight_pos _ hA))
  let q := p + (p + 2) ^ 7
  have hpq : p ≤ q := le_add_of_nonneg_right (by positivity)
  have hq : 0 ≤ q := hp.trans hpq
  have hAq : (A : ℝ) ≤ Real.exp q := hAp.trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  have hBp : (B : ℝ) ≤ Real.exp ((q + 2) ^ 9) :=
    stepDrop_basis_height_budget _ _ A hq (hd.trans hpq) (hd.trans hpq) hAq
  refine ⟨B, hB, hBp, ?_⟩
  intro j
  obtain ⟨r, hr, e, he⟩ := F.exists_refiltration_layer_basis_of_quotient b w hlayers W f hA
    (fun i k => hf k i) j
  have hrd : r ≤ d := by simpa only [Fintype.card_fin] using hr
  have hrι : r ≤ Fintype.card ι := hrd.trans hdim
  refine ⟨e, fun i k => (he i k).mono ?_⟩
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (rationalKernelHeight_mono hA hrι) _)

end NilpotentLieFiltration
end Erdos3

end

end OAI
