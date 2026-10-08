/-
Modified for ProveIt: this file is an extract of upstream
`OAI/Combinatorics/Progressions/Lattices/NativeProperAffineRecovery.lean`
(openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0).
It keeps only `exists_dense_cyclic_model_of_integer_vectors` (upstream lines
190-261) and `exists_bounded_affine_box_of_cyclic_model` (upstream lines
452-512), with verbatim statements and proof bodies, in the distinct
`OAI.Erdos3.FreimanModel.ProveItExtract` namespace so the extract can coexist
with the full upstream module. Only the needed imports are retained; the
rest of the upstream file and its large import closure are omitted.
-/
import OAI.Combinatorics.Progressions.Estimates.CyclicProgressionHom
import OAI.Combinatorics.Progressions.Estimates.DenseCyclicFreimanModel
import OAI.Combinatorics.Progressions.Estimates.DenseTranslate
import OAI.Combinatorics.Progressions.Estimates.FreimanFivefoldCardinality
import OAI.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
import OAI.Combinatorics.Progressions.Lattices.IntegerVectorFreimanEmbedding

namespace OAI

section

namespace Erdos3.FreimanModel.ProveItExtract

open scoped Pointwise

theorem exists_dense_cyclic_model_of_integer_vectors {I : Type*} [Fintype I]
    (A : Finset (I → ℤ)) (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) (s : ℕ) (hs : 0 < s) :
    ∃ (N : ℕ) (J : Finset (I → ℤ)) (B : Finset (ZMod N)) (f : (I → ℤ) → ZMod N),
      0 < N ∧ J.Nonempty ∧ J ⊆ A ∧ A.card ≤ (2 * s) * J.card ∧
      B.Nonempty ∧ B = J.image f ∧ B.card = J.card ∧
      IsAddFreimanIso s (J : Set _) (B : Set _) f ∧
      (N : ℝ) ≤ 2 * K ^ (2 * s) * A.card ∧
      (4 * (s : ℝ) * K ^ (2 * s))⁻¹ ≤ (B.card : ℝ) / N := by
  classical
  obtain ⟨e, he⟩ := exists_integer_freiman_embedding A s
  let X := A.image e
  have hX : X.Nonempty := hA.image e
  have hXcard : X.card = A.card := Finset.card_image_of_injOn he.bijOn.injOn
  have hXsmall : ((X - X).card : ℝ) ≤ K * X.card := by
    have hdiff : X - X = (A - A).image e := by
      ext z
      simp only [X, Finset.mem_sub, Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨x - y, ⟨x, hx, y, hy, rfl⟩, e.map_sub x y⟩
      · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
        exact ⟨e x, ⟨x, hx, rfl⟩, e y, ⟨y, hy, rfl⟩, (e.map_sub x y).symm⟩
    rw [hdiff, hXcard]
    exact (show (((A - A).image e).card : ℝ) ≤ (A - A).card by
      exact_mod_cast Finset.card_image_le).trans hsmall
  obtain ⟨N, X', B, g, hN, hX'ne, hX'sub, hsize, hBne, hB, hBcard,
      hg, hNsize, hdensity⟩ := exists_dense_cyclic_model X hX hK hXsmall s hs
  let J := A.filter fun x => e x ∈ X'
  have hJA : J ⊆ A := Finset.filter_subset _ _
  have hJimage : J.image e = X' := by
    ext z
    constructor
    · rintro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hX'sub hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  have heJ : IsAddFreimanIso s (J : Set _) (X' : Set ℤ) e := by
    apply he.subset hJA
    refine ⟨?_, he.bijOn.injOn.mono hJA, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro z hz
      rw [← hJimage] at hz
      exact Finset.mem_image.mp hz
  have hJcard : X'.card = J.card := by
    rw [← hJimage]
    exact Finset.card_image_of_injOn heJ.bijOn.injOn
  have hJne : J.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hJcard]
    exact hX'ne.card_pos
  have hJsize : A.card ≤ (2 * s) * J.card := by
    simpa only [hXcard, hJcard] using hsize
  have hBimage : B = J.image (g ∘ e) := by
    rw [hB, ← hJimage, Finset.image_image]
  have hNsize' : (N : ℝ) ≤ 2 * K ^ (2 * s) * A.card := by
    simpa only [hXcard] using hNsize
  exact ⟨N, J, B, g ∘ e, hN, hJne, hJA, hJsize, hBne, hBimage,
    hBcard.trans hJcard, hg.comp heJ, hNsize', hdensity⟩

end Erdos3.FreimanModel.ProveItExtract

end

section

namespace Erdos3.FreimanModel.ProveItExtract

open scoped Pointwise BigOperators
open CyclicCrootSisask

theorem exists_bounded_affine_box_of_cyclic_model {G : Type*} [AddCommGroup G] [DecidableEq G]
    {Q : ℕ} [NeZero Q] (A : Finset G) (hA : A.Nonempty) (B : Finset (ZMod Q))
    (hB : B.Nonempty) (f : G → ZMod Q) (hf : IsAddFreimanIso 8 (A : Set _) (B : Set _) f)
    {p : ℝ} (hp : 0 ≤ p) (hdensity : Real.exp (-p) * Q ≤ (B.card : ℝ)) :
    ∃ F ⊆ A, F.Nonempty ∧
      Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * A.card ≤ (F.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ G) (base : G),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
        (∏ i, (2 * R i + 1)) ≤ Q ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ a ∈ F, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ a = base + Φ x := by
  classical
  obtain ⟨T, hrank, hT, hTsub, hTsize⟩ := exists_quartic_bogolyubov_progression B hp hdensity
  obtain ⟨L, hmap, hinj, hzero, hadd⟩ := exists_fourfold_lift_of_eight_iso A B hB f hf
  have hpair (x y z t : T.Param) (h : T.eval x + T.eval y = T.eval z + T.eval t) :
      L (T.eval x) + L (T.eval y) = L (T.eval z) + L (T.eval t) :=
    (hadd _ (hTsub (T.eval_mem_carrier x)) _ (hTsub (T.eval_mem_carrier y))
      _ (hTsub (T.eval_mem_carrier z)) _ (hTsub (T.eval_mem_carrier t))).mpr h
  let Φ := T.freimanHom L
  let S := T.coefficientBox.image Φ
  have hS : S ⊆ 2 • A - 2 • A := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, rfl⟩ := T.mem_coefficientBox.mp hx
    change T.freimanHom L (T.coeff y) ∈ _
    rw [T.freimanHom_coeff L hzero hpair]
    exact hmap (hTsub (T.eval_mem_carrier y))
  have hScard : S.card = T.carrier.card := by
    change (T.coefficientBox.image (T.freimanHom L)).card = T.carrier.card
    rw [T.image_freimanHom L hzero hpair]
    exact Finset.card_image_of_injOn (hinj.mono hTsub)
  have hbound : ((A - S).card : ℝ) ≤ (Q : ℝ) := by
    have h := card_sub_le_of_fourfold_subset A S f (hf.mono (hmn := by decide)) hS
    have h' : (A - S).card ≤ Q := by simpa only [ZMod.card] using h
    exact_mod_cast h'
  have hsize : Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * Q ≤
      (S.card : ℝ) := by rw [hScard]; exact hTsize
  obtain ⟨base, _hbase, F, hFA, hF, hFsize, hFsub⟩ := exists_dense_translate A S hA
    (Real.exp_pos _) (by exact_mod_cast NeZero.pos Q) hbound hsize
  refine ⟨F, hFA, hF, hFsize, T.rank, T.radius, Φ, base, hrank, ?_, ?_, ?_⟩
  · rw [← T.card_carrier_of_proper hT]
    simpa only [ZMod.card] using Finset.card_le_univ T.carrier
  · intro x hx y hy hxy
    exact T.freimanHom_injOn hT L (hinj.mono hTsub) hzero hpair
      (T.mem_coefficientBox_iff_abs_le.mpr hx) (T.mem_coefficientBox_iff_abs_le.mpr hy) hxy
  · intro a ha
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp (hFsub a ha)
    refine ⟨x, T.mem_coefficientBox_iff_abs_le.mp hx, ?_⟩
    rw [heq]
    abel

end Erdos3.FreimanModel.ProveItExtract

end

end OAI
