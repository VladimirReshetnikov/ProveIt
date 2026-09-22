import Surreal.HahnSeries.PolynomialFiniteFactorSupport
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Lifting simple residue roots in a Hahn field

The binary coprime factor lift supplies the existence part of
`polynomial:cor:simpleroot`. The complementary factor has nonzero residue
at the prescribed simple root, which proves uniqueness among all finite
roots with that residue. The positive-order correction has support in the
original error monoid with zero removed. The explicit first-coefficient
formula is a separate obligation. No algebraic closedness or divisibility
of the exponent group is assumed.
-/

namespace Surreal.HahnSeries

open Polynomial
open scoped _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- A simple residue root has a supported lift, unique among all finite roots
with that residue, independently of any support restriction. -/
theorem exists_supported_root_of_simple_standardPart
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic) (c : K)
    (hc : (H.map (standardPart Γ K)).IsRoot c)
    (hd : (H.map (standardPart Γ K)).derivative.eval c ≠ 0) :
    ∃ z : nonnegativeSubring Γ K, H.IsRoot z ∧ standardPart Γ K z = c ∧
      (z : K⟦Γ⟧).support ⊆ residueErrorSupport H ∧
      ∀ y, H.IsRoot y ∧ standardPart Γ K y = c → y = z := by
  let P₀ := H.map (standardPart Γ K)
  let q := P₀ /ₘ (X - C c)
  have heq : P₀ = (X - C c) * q :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hc |>.symm
  have hq : q.Monic := (monic_X_sub_C c).of_mul_monic_left (heq ▸ hH.map _)
  have hcop : IsCoprime (X - C c) q :=
    isCoprime_of_is_root_of_eval_derivative_ne_zero P₀ c hd
  have hqc : q.eval c ≠ 0 := by
    have h := congrArg (fun P : K[X] => P.eval c)
      (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative P₀ c)
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self,
      zero_mul, add_zero] at h
    exact h.trans_ne hd
  obtain ⟨⟨F, G⟩, hF, hG, hFd, _, hF₀, hG₀, _, hFG, hFs, _⟩ :=
    exists_monic_factorization_with_support_of_standardPart (X - C c) q
      (monic_X_sub_C c) hq hcop H hH heq
  have hFlin : F = X + C (F.coeff 0) := hF.eq_X_add_C (by simpa using hFd)
  let z : nonnegativeSubring Γ K := -F.coeff 0
  have hFz : F.IsRoot z := by
    rw [IsRoot.def, hFlin, eval_add, eval_X, eval_C]
    exact neg_add_cancel (F.coeff 0)
  have hz : H.IsRoot z := by
    rw [← hFG, IsRoot.def, eval_mul, hFz.eq_zero, zero_mul]
  have hzc : standardPart Γ K z = c := by
    have h := congrArg (fun P : K[X] => P.coeff 0) hF₀
    simpa [z] using congrArg Neg.neg h
  have hzS : (z : K⟦Γ⟧).support ⊆ residueErrorSupport H := by
    change (-((F.coeff 0 : nonnegativeSubring Γ K) : K⟦Γ⟧)).support ⊆ _
    rw [_root_.HahnSeries.support_neg]
    exact hFs 0
  refine ⟨z, hz, hzc, hzS, ?_⟩
  rintro y ⟨hy, hyc⟩
  have hGy : G.eval y ≠ 0 := by
    intro hzero
    apply hqc
    have h := congrArg (standardPart Γ K) hzero
    rw [map_zero] at h
    have heval := (Polynomial.eval₂_at_apply (p := G) (standardPart Γ K) y).symm
    rw [← eval_map, hG₀, hyc] at heval
    exact heval.symm.trans h
  have hFy : F.eval y = 0 := by
    have h := hy.eq_zero
    rw [← hFG, eval_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hGy
  rw [hFlin, eval_add, eval_X, eval_C] at hFy
  exact eq_neg_iff_add_eq_zero.mpr hFy

/-- Every simple residue root has a unique lift in the nonnegative-order Hahn ring. -/
theorem existsUnique_root_of_simple_standardPart
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic) (c : K)
    (hc : (H.map (standardPart Γ K)).IsRoot c)
    (hd : (H.map (standardPart Γ K)).derivative.eval c ≠ 0) :
    ∃! z : nonnegativeSubring Γ K, H.IsRoot z ∧ standardPart Γ K z = c := by
  obtain ⟨z, hz, hzc, _, huniq⟩ := exists_supported_root_of_simple_standardPart H hH c hc hd
  exact ⟨z, ⟨hz, hzc⟩, huniq⟩

/-- The simple-root lift expressed as an actual positive-order correction
to the prescribed ordinary coefficient, with uniqueness among all such corrections. -/
theorem existsUnique_infinitesimal_root_correction
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic) (c : K)
    (hc : (H.map (standardPart Γ K)).IsRoot c)
    (hd : (H.map (standardPart Γ K)).derivative.eval c ≠ 0) :
    ∃! η : K⟦Γ⟧, 0 < η.orderTop ∧
      (H.map (nonnegativeSubring Γ K).subtype).IsRoot (_root_.HahnSeries.single 0 c + η) := by
  obtain ⟨z, ⟨hz, hzc⟩, huniq⟩ := existsUnique_root_of_simple_standardPart H hH c hc hd
  let η : K⟦Γ⟧ := z.1 - _root_.HahnSeries.single 0 c
  have hη : 0 < η.orderTop := by
    simpa only [hzc] using orderTop_sub_standardPart_pos z
  refine ⟨η, ⟨hη, ?_⟩, ?_⟩
  · simpa only [η, add_sub_cancel] using! hz.map (f := (nonnegativeSubring Γ K).subtype)
  · rintro ε ⟨hε, hroot⟩
    let y : nonnegativeSubring Γ K :=
      ⟨_root_.HahnSeries.single 0 c + ε,
        (le_min _root_.HahnSeries.orderTop_single_le hε.le).trans
          _root_.HahnSeries.min_orderTop_le_orderTop_add⟩
    have hy : H.IsRoot y :=
      hroot.of_map (f := (nonnegativeSubring Γ K).subtype) Subtype.val_injective
    have hyc : standardPart Γ K y = c := by
      change (_root_.HahnSeries.single 0 c + ε).coeff 0 = c
      rw [_root_.HahnSeries.coeff_add, _root_.HahnSeries.coeff_single_same,
        _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop hε, add_zero]
    have heq := congrArg Subtype.val (huniq y ⟨hy, hyc⟩)
    change ε = z.1 - _root_.HahnSeries.single 0 c
    rw [← heq]
    exact (add_sub_cancel_left _ _).symm

/-- The simple-root correction lies in the original error monoid with zero
removed. The unrestricted uniqueness theorem above applies to all corrections. -/
theorem existsUnique_supported_root_correction
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic) (c : K)
    (hc : (H.map (standardPart Γ K)).IsRoot c)
    (hd : (H.map (standardPart Γ K)).derivative.eval c ≠ 0) :
    ∃! η : K⟦Γ⟧, (0 < η.orderTop ∧
      (H.map (nonnegativeSubring Γ K).subtype).IsRoot (_root_.HahnSeries.single 0 c + η)) ∧
      η.support ⊆ (residueErrorSupport H : Set Γ) \ {0} := by
  obtain ⟨z, hz, hzc, hzS, _⟩ := exists_supported_root_of_simple_standardPart H hH c hc hd
  let η : K⟦Γ⟧ := z.1 - _root_.HahnSeries.single 0 c
  have hη : 0 < η.orderTop := by simpa only [hzc] using orderTop_sub_standardPart_pos z
  have hroot : (H.map (nonnegativeSubring Γ K).subtype).IsRoot
      (_root_.HahnSeries.single 0 c + η) := by
    simpa only [η, add_sub_cancel] using! hz.map (f := (nonnegativeSubring Γ K).subtype)
  have hS : η.support ⊆ (residueErrorSupport H : Set Γ) \ {0} := by
    simpa only [hzc] using support_sub_constant_standardPart_subset z _ hzS
  obtain ⟨ζ, _, huniq⟩ := existsUnique_infinitesimal_root_correction H hH c hc hd
  refine ⟨η, ⟨⟨hη, hroot⟩, hS⟩, ?_⟩
  intro ε hε
  exact (huniq ε hε.1).trans (huniq η ⟨hη, hroot⟩).symm

end

end Surreal.HahnSeries
