import IPRADerivations.Probability.ConditionalAveraging
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The finite Euler–Poincaré formula, Euler additivity and collapses

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`:

* A03 (`thm:euler-poincare`, "The preceding proposition gives `c_k = b_k + r_k + r_{k+1}`. Substitute this in
  the alternating sum … They cancel for `1 ≤ j ≤ d`, and the two endpoint terms are zero because
  `r_0 = r_{d+1} = 0`"):
  - `euler_poincare_ring`: `∑_{k ≤ d} (−1)^k c_k = ∑_{k ≤ d} (−1)^k b_k` in every commutative ring, through the
    telescoping identity `alt_telescope`;
  - `euler_poincare`: the same for natural iPRA terms, as the sign-free equation
    `∑_{k even} c_k + ∑_{k odd} b_k = ∑_{k odd} c_k + ∑_{k even} b_k`, from derived equations
    `c_k = b_k + r_k + r_{k+1}`, `r_0 = 0`, `r_{d+1} = 0`;
* A06 (Euler additivity, "Counting this partition proves the first assertion after taking alternating sums"):
  `euler_additivity`, `χ(A ∪ B) + χ(A ∩ B) = χ(A) + χ(B)` for finite sets of simplices graded by a dimension;
* A05 (elementary collapse, the Euler half: "the Euler characteristic changes by deleting exactly one
  `k`-simplex and one `(k+1)`-simplex, whose signed contributions sum to zero"): `euler_collapse`.
-/

namespace LeanProofs.IPRA.Topology.EulerCharacteristic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.ErrorBudget (nsum toG_nsum)
open LeanProofs.IPRA.Probability.ConditionalAveraging (toG_ite)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

/-! ## A03 in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- `∑_{k ≤ d} (−1)^k (r_k + r_{k+1}) = r_0 + (−1)^d r_{d+1}`. -/
theorem alt_telescope (r : ℕ → R) : ∀ d,
    ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * (r k + r (k + 1)) = r 0 + (-1) ^ d * r (d + 1)
  | 0 => by simp
  | d + 1 => by
    rw [Finset.sum_range_succ, alt_telescope r d, _root_.pow_succ]
    ring

/-- A03: `∑_{k ≤ d} (−1)^k c_k = ∑_{k ≤ d} (−1)^k b_k`. -/
theorem euler_poincare_ring (c b r : ℕ → R) (d : ℕ) (hc : ∀ k ≤ d, c k = b k + r k + r (k + 1))
    (h0 : r 0 = 0) (hd : r (d + 1) = 0) :
    ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * c k = ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * b k := by
  have e : ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * c k =
      ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * b k +
        ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * (r k + r (k + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hc k (by simpa [Nat.lt_succ_iff] using hk)]
    ring
  rw [e, alt_telescope, h0, hd]
  ring

/-- The sign-free form of an alternating identity. -/
theorem sign_free (C B : ℕ → R) (d : ℕ)
    (h : ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * C k = ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * B k) :
    (∑ k : Fin (d + 1), if Even k.val then C k else 0) + (∑ k : Fin (d + 1), if Even k.val then 0 else B k) =
      (∑ k : Fin (d + 1), if Even k.val then 0 else C k) + ∑ k : Fin (d + 1), if Even k.val then B k else 0 := by
  have h' : ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * (C k - B k) = 0 := by
    have : ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * (C k - B k) =
        ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * C k - ∑ k ∈ Finset.range (d + 1), (-1 : R) ^ k * B k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, h, sub_self]
  rw [← sub_eq_zero]
  have e : (∑ k : Fin (d + 1), if Even k.val then C k else 0) + (∑ k : Fin (d + 1), if Even k.val then 0 else B k) -
      ((∑ k : Fin (d + 1), if Even k.val then 0 else C k) + ∑ k : Fin (d + 1), if Even k.val then B k else 0) =
      ∑ k : Fin (d + 1), (-1 : R) ^ k.val * (C k - B k) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : Even k.val
    · simp only [hk, ↓reduceIte, Even.neg_one_pow hk]
      ring
    · simp only [hk, ↓reduceIte, Odd.neg_one_pow (Nat.not_even_iff_odd.mp hk)]
      ring
  rw [e, Fin.sum_univ_eq_sum_range (fun k => (-1 : R) ^ k * (C k - B k))]
  exact h'

end Ring

/-! ## A03 for iPRA terms -/

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem toG_ite' (c : Prop) [Decidable c] (a : PTm n) :
    Groth.ι (Q.mk Γ (if c then zero else a)) = if c then 0 else Groth.ι (Q.mk Γ a) := by
  split_ifs <;> simp [Q.mk_zero]

/-- `∑_{k ≤ d, k even} f_k`. -/
def evenSum (f : ℕ → PTm n) (d : ℕ) : PTm n := nsum fun k : Fin (d + 1) => if Even k.val then f k else zero

/-- `∑_{k ≤ d, k odd} f_k`. -/
def oddSum (f : ℕ → PTm n) (d : ℕ) : PTm n := nsum fun k : Fin (d + 1) => if Even k.val then zero else f k

/-- A03, sign-free: `∑_{even} c + ∑_{odd} b = ∑_{odd} c + ∑_{even} b`. -/
theorem euler_poincare (c b r : ℕ → PTm n) (d : ℕ)
    (hc : ∀ k ≤ d, Γ ⊢[PRAAx] c k ≐ b k + r k + r (k + 1))
    (h0 : Γ ⊢[PRAAx] r 0 ≐ zero) (hd : Γ ⊢[PRAAx] r (d + 1) ≐ zero) :
    Γ ⊢[PRAAx] evenSum c d + oddSum b d ≐ oddSum c d + evenSum b d := by
  have key := euler_poincare_ring (fun k => Groth.ι (Q.mk Γ (c k))) (fun k => Groth.ι (Q.mk Γ (b k)))
    (fun k => Groth.ι (Q.mk Γ (r k))) d
    (fun k hk => by have e := natEq (hc k hk); simpa using e)
    (by have e := natEq h0; simpa using e)
    (by have e := natEq hd; simpa using e)
  apply deriveNat
  simp only [evenSum, oddSum, Q.mk_add, map_add, toG_nsum, toG_ite, toG_ite']
  exact sign_free _ _ d key

/-! ## A06 and A05 -/

/-- The Euler characteristic of a finite set of graded simplices. -/
def chi {σ : Type*} (dim : σ → ℕ) (S : Finset σ) : ℤ := ∑ s ∈ S, (-1 : ℤ) ^ dim s

/-- A06: `χ(A ∪ B) + χ(A ∩ B) = χ(A) + χ(B)`. -/
theorem euler_additivity {σ : Type*} [DecidableEq σ] (dim : σ → ℕ) (A B : Finset σ) :
    chi dim (A ∪ B) + chi dim (A ∩ B) = chi dim A + chi dim B :=
  Finset.sum_union_inter

/-- A05, Euler half: deleting a `k`-simplex and a `(k+1)`-simplex preserves `χ`. -/
theorem euler_collapse {σ : Type*} [DecidableEq σ] (dim : σ → ℕ) (S : Finset σ) {s t : σ} (hs : s ∈ S)
    (ht : t ∈ S) (hst : s ≠ t) (hdim : dim t = dim s + 1) :
    chi dim ((S.erase s).erase t) = chi dim S := by
  unfold chi
  have ht' : t ∈ S.erase s := Finset.mem_erase.mpr ⟨Ne.symm hst, ht⟩
  rw [← Finset.add_sum_erase _ _ hs, ← Finset.add_sum_erase _ _ ht', hdim, _root_.pow_succ]
  ring

end LeanProofs.IPRA.Topology.EulerCharacteristic
