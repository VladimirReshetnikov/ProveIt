import CoarseDegrees.Limit

/-!
# The dyadic code

`Rc A` is the set whose value at `n` is `A (col n)`: the bits of `A` replicated along the
dyadic columns (synthesis, Section 6; report 10, Theorem 1.4).  It has the same Turing degree
as `A`, but its *coarse descriptions* are much weaker objects, and the criterion below says
exactly how weak:

  `B` computes a coarse description of `Rc A`  ↔  `A` is the limit of a `B`-computable
  approximation,

which under Shoenfield's limit lemma is `A ≤ᵀ B'`.  The limit form is used so that no jump
operator is needed.

This file proves the definition, the degree, and the direction from limit computability to a
description; the converse, by majority decoding, is in `CoarseDegrees.Majority`.
Everything here is proved.
-/

noncomputable section

open scoped Computability
open TuringDegrees
open scoped SetTuring

namespace CoarseDegrees

/-- The dyadic code: `n ∈ Rc A` exactly when the column index of `n` lies in `A`. -/
def Rc (A : Set ℕ) : Set ℕ := {n | col n ∈ A}

@[simp] theorem mem_Rc {A : Set ℕ} {n : ℕ} : n ∈ Rc A ↔ col n ∈ A := Iff.rfl

/-- The `k`-th column contains `2^k - 1`. -/
theorem col_two_pow_sub_one (k : ℕ) : col (2 ^ k - 1) = k := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hsucc : 2 ^ k - 1 + 1 = 2 ^ k := by omega
  have hle : k ≤ col (2 ^ k - 1) := by
    rw [← pow_dvd_iff_le_col, hsucc]
  have hlt : col (2 ^ k - 1) < k + 1 := by
    by_contra hcon
    have : 2 ^ (k + 1) ∣ (2 ^ k - 1 + 1) := pow_dvd_iff_le_col.mpr (by omega)
    rw [hsucc] at this
    have hle2 : 2 ^ (k + 1) ≤ 2 ^ k := Nat.le_of_dvd hpos this
    have : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_succ (by norm_num)
    omega
  omega

/-- The code has the Turing degree of the coded set. -/
theorem Rc_reducible (A : Set ℕ) : Rc A ≤ᵀₛ A :=
  recursiveIn_precomp (RecursiveIn.oracle _ (Set.mem_singleton _)) computable_col

theorem reducible_Rc (A : Set ℕ) : A ≤ᵀₛ Rc A := by
  have hcomp : Computable (fun k : ℕ => 2 ^ k - 1) :=
    (Primrec.nat_sub.comp ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp
      (Primrec.const 2) Primrec.id) (Primrec.const 1)).to_comp
  have h := recursiveIn_precomp
    (RecursiveIn.oracle (characteristic (Rc A)) (Set.mem_singleton _)) hcomp
  refine h.of_eq fun k => ?_
  simp only [characteristic, characteristicValue, Rc, Set.mem_setOf_eq]
  by_cases hk : k ∈ A
  · have h2 : col (2 ^ k - 1) ∈ A := by rwa [col_two_pow_sub_one]
    rw [if_pos h2, if_pos hk]
  · have h2 : col (2 ^ k - 1) ∉ A := by rwa [col_two_pow_sub_one]
    rw [if_neg h2, if_neg hk]

theorem Rc_equivalent (A : Set ℕ) : Rc A ≡ᵀₛ A := ⟨Rc_reducible A, reducible_Rc A⟩

/-! ## From a limit approximation to a coarse description -/

/-- **The easy direction of the criterion.**  If `A` is the limit of a `B`-computable
approximation, then `B` computes a coarse description of `Rc A`: read the approximation at
stage `n` on the column of `n`.  Each column then carries only finitely many errors, so the
error set has density zero. -/
theorem exists_description_of_limit {B A : Set ℕ} (h : LimitComputableIn B A) :
    ∃ D : Set ℕ, D ≤ᵀₛ B ∧ SetCoarseEq D (Rc A) := by
  obtain ⟨L, hL, hlim⟩ := h
  refine ⟨{n | Nat.pair (col n) n ∈ L}, ?_, ?_⟩
  · -- the description is computable from `B`
    have hpair : Computable₂ (Nat.pair) := Primrec₂.natPair.to_comp
    have hq : Computable (fun n : ℕ => Nat.pair (col n) n) :=
      hpair.comp computable_col Computable.id
    have hred : {n | Nat.pair (col n) n ∈ L} ≤ᵀₛ L :=
      recursiveIn_precomp (RecursiveIn.oracle _ (Set.mem_singleton _)) hq
    exact hred.trans hL
  · -- the errors are bounded on every column
    refine densityZero_of_bounded_columns fun k => ?_
    obtain ⟨s, hs⟩ := hlim k
    refine ⟨s, fun n hn hcol => ?_⟩
    by_contra hns
    have hsn : s ≤ n := by omega
    have hiff : n ∈ {n | Nat.pair (col n) n ∈ L} ↔ n ∈ Rc A := by
      rw [Set.mem_setOf_eq, mem_Rc, hcol]
      exact hs n hsn
    rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hiff.mp h1)
    · exact h2 (hiff.mpr h1)

end CoarseDegrees
