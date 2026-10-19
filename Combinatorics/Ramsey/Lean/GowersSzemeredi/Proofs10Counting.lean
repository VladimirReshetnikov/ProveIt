import GowersSzemeredi.ProofInfrastructure
import GowersSzemeredi.Section10
import Mathlib.Algebra.Order.Chebyshev

/-!
# Counting proofs for Gowers's Section 10

This module proves the elementary difference-popularity estimates collected
in Lemma 10.1.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

lemma countWhere_cast_eq_sum_ite {T : Type*} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    (countWhere P : Real) = ∑ x : T, if P x then 1 else 0 := by
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  simp

private lemma differenceWeight_eq_sum_fibre {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (x y : X) :
    (domainDifferenceWeight D x y : Real) =
      ∑ z : X, ((D.fibre (D.index z + (D.index y - D.index x))).card : Real) := by
  unfold domainDifferenceWeight
  rw [countWhere_cast_eq_sum_ite, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  have hcond (w : X) :
      D.index w - D.index z = D.index y - D.index x ↔
        D.index w = D.index z + (D.index y - D.index x) := by
    constructor <;> intro h <;> linear_combination h
  simp_rw [hcond]
  unfold MultifunctionDomain.fibre
  rw [Finset.filter_congr_decidable]
  simp

private lemma differenceWeight_le {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (alpha : Real) (M : Nat) (hcard : (Fintype.card X : Real) = alpha * M * N)
    (hfibre : ∀ s, (D.fibre s).card ≤ M) (x y : X) :
    (domainDifferenceWeight D x y : Real) ≤ alpha * M ^ 2 * N := by
  rw [differenceWeight_eq_sum_fibre]
  calc
    ∑ z : X, ((D.fibre (D.index z + (D.index y - D.index x))).card : Real) ≤
        ∑ _z : X, (M : Real) := by
      apply Finset.sum_le_sum
      intro z _
      exact_mod_cast hfibre (D.index z + (D.index y - D.index x))
    _ = (Fintype.card X : Real) * M := by simp
    _ = alpha * M ^ 2 * N := by rw [hcard]; ring

private lemma totalWeight_le {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (alpha : Real) (M : Nat) (hcard : (Fintype.card X : Real) = alpha * M * N)
    (hfibre : ∀ s, (D.fibre s).card ≤ M) (x : X) :
    (domainTotalWeight D x : Real) ≤ alpha ^ 2 * M ^ 3 * N ^ 2 := by
  unfold domainTotalWeight
  rw [Nat.cast_sum]
  calc
    ∑ y : X, (domainDifferenceWeight D x y : Real) ≤
        ∑ _y : X, alpha * M ^ 2 * N := by
      exact Finset.sum_le_sum fun y _ => differenceWeight_le D alpha M hcard hfibre x y
    _ = (Fintype.card X : Real) * (alpha * M ^ 2 * N) := by simp
    _ = alpha ^ 2 * M ^ 3 * N ^ 2 := by rw [hcard]; ring

/-- The number of ordered pairs with a prescribed index difference. -/
private noncomputable def differenceMultiplicity {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] (D : MultifunctionDomain N X) (d : ZMod N) : Nat :=
  countWhere fun zw : X × X => D.index zw.2 - D.index zw.1 = d

private lemma differenceWeight_eq_multiplicity {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (x y : X) :
    domainDifferenceWeight D x y = differenceMultiplicity D (D.index y - D.index x) := rfl

private lemma sum_differenceMultiplicity {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] (D : MultifunctionDomain N X) :
    ∑ d : ZMod N, (differenceMultiplicity D d : Real) =
      (Fintype.card X : Real) ^ 2 := by
  simp_rw [differenceMultiplicity, countWhere_cast_eq_sum_ite]
  rw [Finset.sum_comm]
  simp [pow_two]

private lemma sum_differenceWeight_eq_sum_sq {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) :
    (∑ x : X, ∑ y : X, (domainDifferenceWeight D x y : Real)) =
      ∑ d : ZMod N, (differenceMultiplicity D d : Real) ^ 2 := by
  simp_rw [differenceWeight_eq_multiplicity]
  rw [← Fintype.sum_prod_type', ← Finset.sum_fiberwise' _
    (fun xy : X × X => D.index xy.2 - D.index xy.1) fun d => (differenceMultiplicity D d : Real)]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Finset.sum_const, nsmul_eq_mul, sq, differenceMultiplicity,
    countWhere_cast_eq_sum_ite, Finset.natCast_card_filter]

private lemma card_fourth_le_total_differenceWeight {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) :
    (Fintype.card X : Real) ^ 4 ≤
      (N : Real) * ∑ x : X, ∑ y : X, (domainDifferenceWeight D x y : Real) := by
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (ZMod N)))
    (f := fun d : ZMod N => (differenceMultiplicity D d : Real))
  have hcs' :
      (∑ d : ZMod N, (differenceMultiplicity D d : Real)) ^ 2 ≤
        (N : Real) * ∑ d : ZMod N, (differenceMultiplicity D d : Real) ^ 2 := by
    simpa [ZMod.card] using hcs
  calc
    (Fintype.card X : Real) ^ 4 =
        ((Fintype.card X : Real) ^ 2) ^ 2 := by ring
    _ = (∑ d : ZMod N, (differenceMultiplicity D d : Real)) ^ 2 := by
      rw [sum_differenceMultiplicity]
    _ ≤ (N : Real) * ∑ d : ZMod N,
        (differenceMultiplicity D d : Real) ^ 2 := hcs'
    _ = (N : Real) * ∑ x : X, ∑ y : X,
        (domainDifferenceWeight D x y : Real) := by
      rw [sum_differenceWeight_eq_sum_sq]

private lemma total_differenceWeight_lower {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (alpha : Real) (M : Nat)
    (hcard : (Fintype.card X : Real) = alpha * M * N) :
    alpha ^ 4 * M ^ 4 * N ^ 3 ≤
      ∑ x : X, ∑ y : X, (domainDifferenceWeight D x y : Real) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply le_of_mul_le_mul_left (a := (N : Real)) (by
    calc
    (N : Real) * (alpha ^ 4 * M ^ 4 * N ^ 3) =
        (Fintype.card X : Real) ^ 4 := by rw [hcard]; ring
    _ ≤ (N : Real) * ∑ x : X, ∑ y : X,
        (domainDifferenceWeight D x y : Real) :=
      card_fourth_le_total_differenceWeight D) hN

/-- **Gowers, Lemma 10.1.** -/
theorem lemma_10_1_holds : lemma_10_1 := by
  intro N _ X _ _ D alpha M hbounds
  rcases hbounds with ⟨_halpha, _halpha_one, _hM, hcard, hfibre⟩
  exact ⟨
    fun x y => differenceWeight_le D alpha M hcard hfibre x y,
    fun x => totalWeight_le D alpha M hcard hfibre x,
    total_differenceWeight_lower D alpha M hcard⟩

/-- **Gowers, Lemma 10.4.** -/
theorem lemma_10_4_holds : lemma_10_4 := by
  intro N _ X _ _ D phi B alpha M sigma eta hsetup x y z hd
  obtain ⟨⟨-, -, -, hcard, -⟩, -, -, -, -, hinvariant, -⟩ := hsetup
  rw [differenceWeight_eq_sum_fibre, differenceWeight_eq_sum_fibre, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _t : X, sigma * M := Finset.sum_le_sum fun t _ => by
        have h := hinvariant (D.index t + (D.index y - D.index x)) _ hd
        rwa [add_assoc, sub_add_sub_cancel'] at h
    _ = sigma * alpha * M ^ 2 * N := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring

end LeanProofs.GowersSzemeredi
