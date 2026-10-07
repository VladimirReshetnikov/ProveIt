import Mathlib.Algebra.Lie.Prod
import OAI.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (P : LieSubalgebra ℚ (VectorPolynomial σ ℚ L))

noncomputable def restrictedOutsideDownsetIdeal
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) : LieIdeal ℚ P :=
  LieIdeal.comap P.incl (outsideDownsetIdeal J hJ)

@[simp] theorem mem_restrictedOutsideDownsetIdeal
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (p : P) :
    p ∈ restrictedOutsideDownsetIdeal P J hJ ↔ ∀ a ∈ J, coefficients p.val a = 0 :=
  mem_outsideDownsetIdeal J hJ p.val

theorem restrictedOutsideDownsetIdeal_inf_eq_bot
    (J K : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (hK : IsLowerSet K)
    (hcover : ∀ p : P, p.val ∈ coefficientSupport (J ∪ K)) :
    restrictedOutsideDownsetIdeal P J hJ ⊓ restrictedOutsideDownsetIdeal P K hK = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply Subtype.ext
  apply coefficients.injective
  ext a
  change coefficients p.val a = 0
  by_cases haJ : a ∈ J
  · exact (mem_restrictedOutsideDownsetIdeal P J hJ p).mp hp.1 a haJ
  · by_cases haK : a ∈ K
    · exact (mem_restrictedOutsideDownsetIdeal P K hK p).mp hp.2 a haK
    · exact hcover p a (fun h => h.elim haJ haK)

noncomputable def downsetPairQuotientMap
    (J K : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (hK : IsLowerSet K) :
    P →ₗ⁅ℚ⁆ (P ⧸ restrictedOutsideDownsetIdeal P J hJ) ×
      (P ⧸ restrictedOutsideDownsetIdeal P K hK) :=
  (lieQuotientMap (restrictedOutsideDownsetIdeal P J hJ)).prod
    (lieQuotientMap (restrictedOutsideDownsetIdeal P K hK))

theorem downsetPairQuotientMap_injective
    (J K : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (hK : IsLowerSet K)
    (hcover : ∀ p : P, p.val ∈ coefficientSupport (J ∪ K)) :
    Function.Injective (downsetPairQuotientMap P J K hJ hK) := by
  intro p q hpq
  apply sub_eq_zero.mp
  have hzero : downsetPairQuotientMap P J K hJ hK (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  have hmem : p - q ∈ restrictedOutsideDownsetIdeal P J hJ ⊓
      restrictedOutsideDownsetIdeal P K hK := by
    constructor
    · exact (lieQuotientMap_eq_zero _ _).mp (congrArg Prod.fst hzero)
    · exact (lieQuotientMap_eq_zero _ _).mp (congrArg Prod.snd hzero)
  rw [restrictedOutsideDownsetIdeal_inf_eq_bot P J K hJ hK hcover] at hmem
  exact (LieSubmodule.mem_bot _).mp hmem

end Erdos3.VectorPolynomial

end

end OAI
