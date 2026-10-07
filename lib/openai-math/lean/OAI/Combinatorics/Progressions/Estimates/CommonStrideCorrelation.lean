import OAI.Combinatorics.Progressions.Geometry.CommonStrideCoordinates

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteCorrelation_commonStrideBox {I : Type*} [Fintype I] [DecidableEq I]
    (b : I → ℤ) {d : ℕ} (hd : 0 < d) (K : I → ℕ) (f g : (I → ℤ) → ℂ) :
    finiteCorrelation (commonStrideBox b d K) f g =
      finiteCorrelation (integerBox K) (fun x => f (commonStridePoint b d x))
        (fun x => g (commonStridePoint b d x)) := by
  rw [commonStrideBox_eq_image]
  unfold finiteCorrelation
  exact Finset.expect_image (commonStridePoint_injective b hd).injOn

end Erdos3

end

end OAI
