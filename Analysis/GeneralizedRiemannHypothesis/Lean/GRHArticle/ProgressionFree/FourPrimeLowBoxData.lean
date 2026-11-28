import GRHArticle.ProgressionFree.FiniteGPBranchCertificate
import GRHArticle.ProgressionFree.FourPrimeHighDigitNumerics
import GRHArticle.ProgressionFree.Rankin
import GRHArticle.ProgressionFree.RectangularPrefixWeights
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Finite weighted data for a four-prime box

Each exponent vector is encoded by its integer value at the base primes.
Integer weights clear the common denominator and multiply nongreedy
weights by the article's factor `21/20`.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- The integer represented by an exponent vector at the base primes. -/
def fourPrimeBoxValue (q a : Fin 4 → ℕ) : ℕ :=
  q 0 ^ a 0 * (q 1 ^ a 1 * (q 2 ^ a 2 * q 3 ^ a 3))

theorem fourPrimeBoxValue_eq_prod (q a : Fin 4 → ℕ) : fourPrimeBoxValue q a = ∏ i, q i ^ a i := by
  simp [fourPrimeBoxValue,Fin.prod_univ_succ]

theorem fourPrimeBoxValue_pos (q a : Fin 4 → ℕ) (hq : ∀ i, (q i).Prime) :
    0 < fourPrimeBoxValue q a :=
  (fourPrimeBoxValue_eq_prod q a).symm ▸ Finset.prod_pos (fun i _ ↦ pow_pos (hq i).pos _)

theorem fourPrimeBoxValue_factorization (q a : Fin 4 → ℕ) (hq : ∀ i, (q i).Prime)
    (hInj : Function.Injective q) (i : Fin 4) :
    (fourPrimeBoxValue q a).factorization (q i) = a i := by
  rw [fourPrimeBoxValue_eq_prod]
  rw [Nat.factorization_prod_apply (fun j _ ↦ pow_ne_zero _ (hq j).ne_zero)]
  rw [sum_eq_single i]
  · exact Nat.factorization_pow_self (hq i)
  · intro j _ hj
    rw [(hq j).factorization_pow,Finsupp.single_eq_of_ne (fun he ↦ hj (hInj he.symm))]
  · simp

theorem fourPrimeBoxValue_injective (q : Fin 4 → ℕ) (hq : ∀ i, (q i).Prime)
    (hInj : Function.Injective q) : Function.Injective (fourPrimeBoxValue q) := by
  intro a c he
  funext i
  exact (fourPrimeBoxValue_factorization q a hq hInj i).symm.trans
    ((congrArg (fun n : ℕ ↦ n.factorization (q i)) he).trans
      (fourPrimeBoxValue_factorization q c hq hInj i))

/-- The decidable test for coordinatewise ternary digits at most one. -/
def fourPrimeBoxGood (a : Fin 4 → ℕ) : Bool :=
  (List.finRange 4).all fun i ↦ (Nat.digits 3 (a i)).all (fun t ↦ decide (t ≤ 1))

theorem fourPrimeBoxGood_iff (a : Fin 4 → ℕ) :
    fourPrimeBoxGood a = true ↔ ∀ i, a i ∈ greedyExponents := by
  simp [fourPrimeBoxGood,greedyExponents,List.all_eq_true]

/-- Common-denominator numerator of the reciprocal weight, before inflation. -/
def fourPrimeBoxWeightNumerator (q a : Fin 4 → ℕ) : ℕ :=
  fourPrimeBoxValue q (fun i ↦ fourPrimeLowBoxLimit i-a i)

theorem fourPrimeBoxWeightNumerator_eq_prod (q a : Fin 4 → ℕ) :
    fourPrimeBoxWeightNumerator q a = ∏ i, q i ^ (fourPrimeLowBoxLimit i-a i) :=
  fourPrimeBoxValue_eq_prod q _

/-- Integer score for comparing greedy and nongreedy entries. -/
def fourPrimeBoxScore (q a : Fin 4 → ℕ) : ℕ :=
  (if fourPrimeBoxGood a then 20 else 21) * fourPrimeBoxWeightNumerator q a

/-- An entry of the branch checker carries its exponent vector, ordering key,
and integer score. -/
abbrev FourPrimeBoxEntry := (Fin 4 → ℕ) × ℕ × ℕ

private def exponentTupleToVector (a : ℕ × ℕ × ℕ × ℕ) : Fin 4 → ℕ :=
  ![a.1,a.2.1,a.2.2.1,a.2.2.2]

private theorem exponentTupleToVector_injective : Function.Injective exponentTupleToVector := by
  intro a b h
  exact Prod.ext (congrFun h 0)
    (Prod.ext (congrFun h 1) (Prod.ext (congrFun h 2) (congrFun h 3)))

private def fourPrimeExponentList (r : Fin 4 → ℕ) : List (Fin 4 → ℕ) :=
  ((List.range (r 0+1)) ×ˢ ((List.range (r 1+1)) ×ˢ
    ((List.range (r 2+1)) ×ˢ (List.range (r 3+1))))).map exponentTupleToVector

private theorem mem_fourPrimeExponentList (r a : Fin 4 → ℕ) :
    a ∈ fourPrimeExponentList r ↔ a ∈ exponentBox r := by
  rw [fourPrimeExponentList,List.mem_map,mem_exponentBox]
  constructor
  · rintro ⟨⟨a₀,a₁,a₂,a₃⟩,ha,rfl⟩ i
    simp only [List.mem_product,List.mem_range,Nat.lt_succ_iff] at ha
    fin_cases i
    · exact ha.1
    · exact ha.2.1
    · exact ha.2.2.1
    · exact ha.2.2.2
  · intro ha
    refine ⟨(a 0,a 1,a 2,a 3),?_,?_⟩
    · simp only [List.mem_product,List.mem_range,Nat.lt_succ_iff]
      exact ⟨ha 0,ha 1,ha 2,ha 3⟩
    · funext i
      fin_cases i <;> rfl

private theorem fourPrimeExponentList_nodup (r : Fin 4 → ℕ) :
    (fourPrimeExponentList r).Nodup :=
  List.Nodup.map exponentTupleToVector_injective
    (List.nodup_range.product (List.nodup_range.product (List.nodup_range.product List.nodup_range)))

/-- The exponent vectors enumerated in increasing order of their base value. -/
def fourPrimeSortedExponents (q r : Fin 4 → ℕ) : List (Fin 4 → ℕ) :=
  List.insertionSort (fun a c ↦ fourPrimeBoxValue q a ≤ fourPrimeBoxValue q c) (fourPrimeExponentList r)

theorem fourPrimeSortedExponents_coe (q r : Fin 4 → ℕ) :
    (fourPrimeSortedExponents q r : Multiset (Fin 4 → ℕ)) = (exponentBox r).val := by
  have hPerm : (fourPrimeSortedExponents q r).Perm (fourPrimeExponentList r) := List.perm_insertionSort _ _
  have hN := hPerm.nodup_iff.mpr (fourPrimeExponentList_nodup r)
  have h : (fourPrimeSortedExponents q r).toFinset = exponentBox r := by
    ext a
    rw [List.mem_toFinset,hPerm.mem_iff,mem_fourPrimeExponentList]
  exact congrArg Finset.val ((List.toFinset_eq hN).trans h)

/-- Exact entries for a rectangular prefix of the low-digit box. -/
def fourPrimeBoxEntries (q r : Fin 4 → ℕ) : List FourPrimeBoxEntry :=
  (fourPrimeSortedExponents q r).map fun a ↦ (a,fourPrimeBoxValue q a,fourPrimeBoxScore q a)

/-- As in the article's test, an earlier pair forbids its increasing
geometric completion. -/
def fourPrimeBoxForbidden (a b c : FourPrimeBoxEntry) : Bool :=
  decide (a.2.1 < b.2.1 ∧ b.2.1 < c.2.1 ∧ a.2.1 * c.2.1 = b.2.1 * b.2.1)

/-- The target is the integer mass of the greedy vectors in the prefix. -/
def fourPrimeBoxTarget (q r : Fin 4 → ℕ) : ℕ :=
  (((fourPrimeBoxEntries q r).filter fun x ↦ fourPrimeBoxGood x.1).map (fun x ↦ x.2.2)).sum

/-- Execute the branch check on a specified base and prefix. -/
def fourPrimeBoxCheck (q r : Fin 4 → ℕ) : Bool :=
  let L := fourPrimeBoxEntries q r
  finiteGPBranchCheck (fun x ↦ x.2.2) fourPrimeBoxForbidden
    (fourPrimeBoxTarget q r) (L.length+1) 0 [] L

end GRHArticle.ProgressionFree
