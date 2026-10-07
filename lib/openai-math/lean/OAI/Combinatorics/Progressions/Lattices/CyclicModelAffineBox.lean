import OAI.Combinatorics.Progressions.Estimates.CyclicProgressionHom
import OAI.Combinatorics.Progressions.Estimates.DenseTranslate
import OAI.Combinatorics.Progressions.Estimates.FreimanFivefoldCardinality
import OAI.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods

namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise
open CyclicCrootSisask

theorem exists_affine_box_of_cyclic_model {G : Type*} [AddCommGroup G] [DecidableEq G]
    {Q : ℕ} [NeZero Q] (A : Finset G) (hA : A.Nonempty) (B : Finset (ZMod Q))
    (hB : B.Nonempty) (f : G → ZMod Q) (hf : IsAddFreimanIso 8 (A : Set _) (B : Set _) f)
    {p : ℝ} (hp : 0 ≤ p) (hdensity : Real.exp (-p) * Q ≤ (B.card : ℝ)) :
    ∃ F ⊆ A, F.Nonempty ∧
      Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * A.card ≤ (F.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ G) (base : G),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
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
  refine ⟨F, hFA, hF, hFsize, T.rank, T.radius, Φ, base, hrank, ?_, ?_⟩
  · intro x hx y hy hxy
    exact T.freimanHom_injOn hT L (hinj.mono hTsub) hzero hpair
      (T.mem_coefficientBox_iff_abs_le.mpr hx) (T.mem_coefficientBox_iff_abs_le.mpr hy) hxy
  · intro a ha
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp (hFsub a ha)
    refine ⟨x, T.mem_coefficientBox_iff_abs_le.mp hx, ?_⟩
    rw [heq]
    abel

end Erdos3.FreimanModel

end

end OAI
