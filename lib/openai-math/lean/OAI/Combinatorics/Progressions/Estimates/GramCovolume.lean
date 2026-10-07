import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.InnerProductSpace.GramMatrix

namespace OAI

section

namespace Erdos3

open Module RealInnerProductSpace

theorem zspan_covolume_sq_eq_det_gram {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {r : ℕ} (b : Basis (Fin r) ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ^ 2 = (Matrix.gram ℝ b).det := by
  let b₀ : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  have hrank : Module.finrank ℝ E = r := by simpa using Module.finrank_eq_card_basis b
  let e : Fin (Module.finrank ℝ E) ≃ Fin r := Fin.castOrderIso hrank
  let o : OrthonormalBasis (Fin r) ℝ E := b₀.reindex e
  have hoVolume : MeasureTheory.volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [MeasureTheory.measureReal_def]
    have hfd : MeasureTheory.volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
      rw [MeasureTheory.measure_congr
        (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis MeasureTheory.volume)]
      exact o.volume_parallelepiped
    rw [hfd]
    simp
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |o.toBasis.det b| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain
      (Submodule.span ℤ (Set.range b)) MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b MeasureTheory.volume),
      ZSpan.measureReal_fundamentalDomain b MeasureTheory.volume o.toBasis, hoVolume, mul_one]
  rw [hcov, sq_abs, o.toBasis.det_apply]
  rw [Matrix.gram_eq_conjTranspose_mul o b, Matrix.det_mul, Matrix.det_conjTranspose]
  have hm : o.toBasis.toMatrix b = Matrix.of fun i j => o.repr (b j) i := by
    ext i j
    rfl
  rw [hm]
  simp [pow_two]

end Erdos3

end

end OAI
