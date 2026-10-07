import Mathlib.LinearAlgebra.Basis.Prod
import OAI.Combinatorics.Progressions.Estimates.RationalRowReduction
import OAI.Combinatorics.Progressions.Geometry.DilationPairCoordinates

namespace OAI

section

namespace Erdos3

open Module

theorem exists_scaledPair_basis_height {ι α β L : Type*} [Fintype α] [Fintype β]
    [AddCommGroup L] [Module ℚ L] (e : Basis ι ℚ L)
    (P Q : Submodule ℚ L) (hQP : Q ≤ P) (a : Basis α ℚ Q) (b : Basis β ℚ P)
    (q : ℚ) {H K : ℕ} (hH : 1 ≤ H) (hK : 1 ≤ K) (hq : RationalHeightLE q K)
    (ha : ∀ j k, RationalHeightLE (e.repr (a j : L) k) H)
    (hb : ∀ j k, RationalHeightLE (e.repr (b j : L) k) H) :
    ∃ c : Basis (Fin (finrank ℚ (scaledPairLayer P Q q))) ℚ (scaledPairLayer P Q q),
      ∀ j k, RationalHeightLE (e.repr (c j).val.1 k) (H * K) ∧
        RationalHeightLE (e.repr (c j).val.2 k) (H * K) := by
  classical
  let c := (a.prod b).map (scaledPairLayerEquiv P Q hQP q)
  have hHK : H ≤ H * K := Nat.le_mul_of_pos_right H (by omega)
  have hz (k : ι) : RationalHeightLE (e.repr 0 k) (H * K) := by
    simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero (hH.trans hHK)
  have hc (j : α ⊕ β) (k : ι) :
      RationalHeightLE (e.repr (c j).val.1 k) (H * K) ∧
        RationalHeightLE (e.repr (c j).val.2 k) (H * K) := by
    rcases j with j | j
    · simpa [c, Basis.prod_apply, scaledPairLayerEquiv, scaledPairAssemble] using
        (show RationalHeightLE (e.repr (a j : L) k) (H * K) ∧
          RationalHeightLE (e.repr 0 k) (H * K) from ⟨(ha j k).mono hHK, hz k⟩)
    · have hmul : RationalHeightLE (q * e.repr (b j : L) k) (H * K) := by
        simpa only [Nat.mul_comm K H] using hq.mul (hb j k)
      simpa [c, Basis.prod_apply, scaledPairLayerEquiv, scaledPairAssemble, smul_eq_mul] using
        (show RationalHeightLE (q * e.repr (b j : L) k) (H * K) ∧
          RationalHeightLE (e.repr (b j : L) k) (H * K) from ⟨hmul, (hb j k).mono hHK⟩)
  let c' := c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)
  exact ⟨c', fun j k => by simpa only [c', Basis.reindex_apply] using hc _ k⟩

end Erdos3

end

end OAI
