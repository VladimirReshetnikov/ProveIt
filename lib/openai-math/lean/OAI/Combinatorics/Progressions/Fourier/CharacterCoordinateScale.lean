/- Modified for ProveIt: use Mathlib v4.32.0's generic prod_le_prod'
for product comparisons. Mathematical statements unchanged. -/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Max
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def latticeCharacterCoordinates {I : Type*} [DecidableEq I] (χ : AddChar (I → ℤ) ℂ) (i : I) : ℂ :=
  χ (Pi.single i 1)

theorem integerVector_sum_single {I : Type*} [Fintype I] [DecidableEq I] (v : I → ℤ) :
    v = ∑ i, v i • (Pi.single i 1 : I → ℤ) := by
  ext i
  simp [Pi.single_apply]

theorem latticeCharacter_eval {I : Type*} [Fintype I] [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (v : I → ℤ) :
    χ v = ∏ i, latticeCharacterCoordinates χ i ^ (v i : ℤ) := by
  have hsum (s : Finset I) : χ (∑ i ∈ s, v i • (Pi.single i 1 : I → ℤ)) =
      ∏ i ∈ s, latticeCharacterCoordinates χ i ^ (v i : ℤ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, χ.map_add_eq_mul, ih]
      rw [χ.map_zsmul_eq_zpow]
      rfl
  rw [integerVector_sum_single v]
  convert hsum Finset.univ using 1
  apply Finset.prod_congr rfl
  intro i _
  simp [Pi.single_apply]

theorem latticeCharacterCoordinates_injective {I : Type*} [Fintype I] [DecidableEq I] :
    Function.Injective (latticeCharacterCoordinates (I := I)) := by
  intro χ ψ h
  ext v
  rw [latticeCharacter_eval, latticeCharacter_eval, h]

theorem latticeCharacterCoordinates_pow {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (n : ℕ) (i : I) :
    latticeCharacterCoordinates (χ ^ n) i = latticeCharacterCoordinates χ i ^ n := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem latticeCharacter_coordinate_order_dvd {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (a : ℕ) (hχ : χ ^ a = 1) (i : I) :
    orderOf (latticeCharacterCoordinates χ i) ∣ a :=
  orderOf_dvd_iff_pow_eq_one.mpr
    (congrArg (fun ψ : AddChar (I → ℤ) ℂ => ψ (Pi.single i 1)) hχ)

theorem latticeCharacter_coordinate_order_pos {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) (i : I) :
    0 < orderOf (latticeCharacterCoordinates χ i) :=
  Nat.pos_of_dvd_of_pos
    (latticeCharacter_coordinate_order_dvd χ (orderOf χ) (pow_orderOf_eq_one χ) i) hχ

theorem latticeCharacter_order_le_product {I : Type*} [Fintype I] [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    orderOf χ ≤ ∏ i, orderOf (latticeCharacterCoordinates χ i) := by
  have hpos : 0 < ∏ i, orderOf (latticeCharacterCoordinates χ i) :=
    Finset.prod_pos (fun i _ => latticeCharacter_coordinate_order_pos χ hχ i)
  apply Nat.le_of_dvd hpos
  apply orderOf_dvd_iff_pow_eq_one.mpr
  apply latticeCharacterCoordinates_injective
  funext i
  rw [latticeCharacterCoordinates_pow]
  change (latticeCharacterCoordinates χ i) ^ (∏ j, orderOf (latticeCharacterCoordinates χ j)) = 1
  apply orderOf_dvd_iff_pow_eq_one.mp
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem exists_coordinate_order_power_ge {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    ∃ i, 0 < orderOf (latticeCharacterCoordinates χ i) ∧
      orderOf χ ≤ orderOf (latticeCharacterCoordinates χ i) ^ Fintype.card I := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => orderOf (latticeCharacterCoordinates χ i)) Finset.univ_nonempty
  refine ⟨i, latticeCharacter_coordinate_order_pos χ hχ i, (latticeCharacter_order_le_product χ hχ).trans ?_⟩
  calc
    _ ≤ ∏ _j : I, orderOf (latticeCharacterCoordinates χ i) :=
      Finset.prod_le_prod' (fun coordinate hcoordinate => hi coordinate hcoordinate)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

abbrev TorsionLatticeCharacter (I : Type*) (a : ℕ) :=
  {χ : AddChar (I → ℤ) ℂ // χ ^ a = 1}

noncomputable def torsionCharacterCoordinates {I : Type*} [DecidableEq I] {a : ℕ} [NeZero a]
    (χ : TorsionLatticeCharacter I a) (i : I) : rootsOfUnity a ℂ :=
  rootsOfUnity.mkOfPowEq (latticeCharacterCoordinates χ.val i)
    (congrArg (fun ψ : AddChar (I → ℤ) ℂ => ψ (Pi.single i 1)) χ.property)

theorem torsionCharacterCoordinates_injective {I : Type*} [Fintype I] [DecidableEq I]
    {a : ℕ} [NeZero a] :
    Function.Injective (torsionCharacterCoordinates (I := I) (a := a)) := by
  intro χ ψ h
  apply Subtype.ext
  apply latticeCharacterCoordinates_injective
  funext i
  exact congrArg (fun z : rootsOfUnity a ℂ => (z.val : ℂ)) (congrFun h i)

noncomputable instance torsionLatticeCharacterFintype (I : Type*) [Fintype I] (a : ℕ) [NeZero a] :
    Fintype (TorsionLatticeCharacter I a) := by
  classical
  let _ : Fintype (rootsOfUnity a ℂ) := Fintype.ofFinite _
  exact Fintype.ofInjective torsionCharacterCoordinates torsionCharacterCoordinates_injective

theorem torsionLatticeCharacter_card_le (I : Type*) [Fintype I] (a : ℕ) [NeZero a] :
    Fintype.card (TorsionLatticeCharacter I a) ≤ a ^ Fintype.card I := by
  classical
  let _ : Fintype (rootsOfUnity a ℂ) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective torsionCharacterCoordinates
    (torsionCharacterCoordinates_injective (I := I) (a := a))
  have hc : Fintype.card (rootsOfUnity a ℂ) = a := by
    rw [← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]
  rw [Fintype.card_fun, hc] at h
  exact h

end Erdos3

end

section

namespace Erdos3

theorem exists_coordinate_order_rpow_ge {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    ∃ i, 0 < orderOf (latticeCharacterCoordinates χ i) ∧
      (orderOf χ : ℝ) ^ (1 / (Fintype.card I : ℝ)) ≤ orderOf (latticeCharacterCoordinates χ i) := by
  obtain ⟨i, hi, hpow⟩ := exists_coordinate_order_power_ge χ hχ
  refine ⟨i, hi, ?_⟩
  have hq : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos (α := I)
  have hpowR : (orderOf χ : ℝ) ≤ (orderOf (latticeCharacterCoordinates χ i) : ℝ) ^ Fintype.card I := by
    exact_mod_cast hpow
  have hb : (0 : ℝ) ≤ orderOf (latticeCharacterCoordinates χ i) := Nat.cast_nonneg _
  calc
    _ ≤ ((orderOf (latticeCharacterCoordinates χ i) : ℝ) ^ Fintype.card I) ^
        (1 / (Fintype.card I : ℝ)) := Real.rpow_le_rpow (Nat.cast_nonneg _) hpowR (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb, mul_one_div_cancel hq.ne', Real.rpow_one]

end Erdos3

end

end OAI
