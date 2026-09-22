import Surreal.HahnSeries.Binomial
import Surreal.HahnSeries.StandardPart

/-!
# Uniqueness of binomial roots near one

The binomial root used in the proof of `b:ramification` is the unique root
whose difference from one has positive Hahn order. The algebraic reason is
that the finite geometric factor in `y ^ m - z ^ m` has standard part `m`,
which is nonzero in characteristic zero.

This is uniqueness in the valuation neighborhood of one, without an order
on the coefficient field. In particular it does not identify the root with
a positive square root or prove the analytic ramification theorem.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K] [CharZero K]

/-- Positive natural powers are injective on series whose difference
from one has positive order. This supplies the uniqueness needed for the
binomial root construction in the proof of `b:ramification`. -/
theorem pow_injective_near_one (m : ℕ) (hm : m ≠ 0) :
    Set.InjOn (fun y : K⟦Γ⟧ => y ^ m) {y | 0 < (y - 1).orderTop} := by
  intro y hy z hz hpow
  have hyo := ((orderTop_self_sub_one_pos_iff y).mp hy).1
  have hzo := ((orderTop_self_sub_one_pos_iff z).mp hz).1
  let Y : nonnegativeSubring Γ K := ⟨y, (mem_nonnegativeSubring _).mpr hyo.ge⟩
  let Z : nonnegativeSubring Γ K := ⟨z, (mem_nonnegativeSubring _).mpr hzo.ge⟩
  have hY : standardPart Γ K Y = 1 := by
    change y.coeff 0 = 1
    have h := coeff_eq_zero_of_lt_orderTop hy
    simpa [sub_eq_zero] using h
  have hZ : standardPart Γ K Z = 1 := by
    change z.coeff 0 = 1
    have h := coeff_eq_zero_of_lt_orderTop hz
    simpa [sub_eq_zero] using h
  let S : nonnegativeSubring Γ K := ∑ i ∈ Finset.range m, Y ^ i * Z ^ (m - 1 - i)
  have hS : standardPart Γ K S = (m : K) := by
    simp only [S, map_sum, map_mul, map_pow, hY, hZ, one_pow, mul_one,
      Finset.sum_const, Finset.card_range, nsmul_one]
  have hS0 : S ≠ 0 := by
    intro hzero
    have hc := congrArg (standardPart Γ K) hzero
    rw [hS, map_zero] at hc
    exact (Nat.cast_ne_zero.mpr hm) hc
  have hpow' : Y ^ m = Z ^ m := Subtype.ext hpow
  have hprod : S * (Y - Z) = 0 := by
    dsimp only [S]
    rw [geom_sum₂_mul, hpow', sub_self]
  have heq : Y = Z := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hS0)
  exact congrArg Subtype.val heq

/-- The rational binomial root is the unique `m`th root of `1 + x`
near one. This identifies the branch furnished by the formal binomial
series in the proof of `b:ramification`. -/
theorem binomialPower_rat_root_unique (x : K⟦Γ⟧) (hx : 0 < x.orderTop)
    (m : ℕ) (hm : m ≠ 0) (y : K⟦Γ⟧)
    (hy : 0 < (y - 1).orderTop) (hpow : y ^ m = 1 + x) :
    y = binomialPower x hx (1 / (m : ℚ)) :=
  pow_injective_near_one m hm hy (orderTop_binomialPower_sub_one_pos x hx _)
    (hpow.trans (binomialPower_rat_root x hx m hm).symm)

/-- Existence and uniqueness of the root near one, with existence supplied
by the admissible Hahn binomial sum rather than algebraic closedness. -/
theorem exists_unique_root_near_one (x : K⟦Γ⟧) (hx : 0 < x.orderTop)
    (m : ℕ) (hm : m ≠ 0) :
    ∃! y : K⟦Γ⟧, y ^ m = 1 + x ∧ 0 < (y - 1).orderTop := by
  refine ⟨binomialPower x hx (1 / (m : ℚ)),
    ⟨binomialPower_rat_root x hx m hm, orderTop_binomialPower_sub_one_pos x hx _⟩, ?_⟩
  intro y hy
  exact binomialPower_rat_root_unique x hx m hm y hy.2 hy.1

end
end Surreal.HahnSeries
