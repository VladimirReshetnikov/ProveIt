import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Associated

open Finset Nat

/-- A prime divides a truncated descending product exactly when the least residue lies in its interval. -/
theorem prime_dvd_descendingProduct_iff {p a u : ℕ} (hp : p.Prime) :
    p ∣ ∏ t ∈ range (u + 1), (a - t) ↔ a % p ≤ u := by
  constructor
  · intro h
    obtain ⟨t, ht, hpt⟩ := hp.prime.exists_mem_finset_dvd h
    have heq : a % p = min a t % p :=
      (modEq_sub (min_le_left ..)).of_dvd (Nat.sub_eq_sub_min .. ▸ hpt)
    calc
      a % p = min a t % p := heq
      _ ≤ min a t := Nat.mod_le _ _
      _ ≤ t := min_le_right _ _
      _ ≤ u := Nat.le_of_lt_succ (mem_range.mp ht)
  · intro h
    exact (Nat.dvd_sub_mod a).trans
      (dvd_prod_of_mem _ (mem_range_succ_iff.mpr h))

#print axioms prime_dvd_descendingProduct_iff
