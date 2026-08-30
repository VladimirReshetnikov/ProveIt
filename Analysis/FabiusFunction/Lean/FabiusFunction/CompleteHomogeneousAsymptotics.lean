import FabiusFunction.CompleteHomogeneous
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Asymptotic bounds for complete homogeneous evaluations

This module records the finite-family asymptotic estimate behind evaluated
complete homogeneous symmetric polynomials.  If every coordinate of a fixed
finite family is `O(g)` along a filter, then its degree-`n` complete
homogeneous evaluation is `O(g ^ n)`.

The proof uses the explicit `Sym`-indexed formula.  Every summand is a product
of exactly `n` coordinate functions, so multiplicativity of `IsBigO` gives the
required power bound term by term; closure under finite sums completes the
argument.  The statement includes degree zero and permits the evaluated
polynomial and the comparison scale to have different normed codomains.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped BigOperators

namespace Fabius

noncomputable section

private theorem multiset_prod_apply_isBigO_pow
    {α ι R S : Type*} [SeminormedCommRing R]
    [NormedRing S] [NormMulClass S] [NormOneClass S]
    (l : Filter α) (a : ι → α → R) (g : α → S)
    (t : Multiset ι) (h : ∀ i, a i =O[l] g) :
    (fun x => (t.map fun i => a i x).prod) =O[l]
      (fun x => g x ^ t.card) := by
  letI : Nontrivial S := NormOneClass.nontrivial
  induction t using Multiset.induction_on with
  | empty =>
      simpa using
        (isBigO_const_const (1 : R) (one_ne_zero : (1 : S) ≠ 0) l)
  | @cons i t ih =>
      simpa only [Multiset.map_cons, Multiset.prod_cons,
        Multiset.card_cons, pow_succ'] using (h i).mul ih

/-- A finite complete homogeneous evaluation preserves coordinatewise
Big-O bounds, with the scale raised to the homogeneous degree.

The comparison target needs a multiplicative norm so that products of
coordinate bounds compare directly with `g ^ n`.  No nonvanishing assumption
on `g` is required, and the result also covers `n = 0`. -/
theorem completeHomogeneousEvalOn_isBigO_pow
    {α ι R S : Type*} [SeminormedCommRing R]
    [NormedRing S] [NormMulClass S] [NormOneClass S]
    (l : Filter α) (s : Finset ι) (a : ι → α → R)
    (g : α → S) (n : ℕ)
    (h : ∀ i ∈ s, a i =O[l] g) :
    (fun x => completeHomogeneousEvalOn s (fun i => a i x) n) =O[l]
      (fun x => g x ^ n) := by
  classical
  have hcoord : ∀ i : s, (fun x => a (i : ι) x) =O[l] g := by
    intro i
    exact h i i.property
  have hsum :
      (fun x => ∑ m : Sym s n,
        (m.1.map fun i : s => a (i : ι) x).prod) =O[l]
        (fun x => g x ^ n) := by
    apply IsBigO.sum
    intro m _hm
    simpa only [m.2] using
      (multiset_prod_apply_isBigO_pow l
        (fun i : s => a (i : ι)) g m.1 hcoord)
  unfold completeHomogeneousEvalOn
  apply hsum.congr_left
  intro x
  rw [completeHomogeneousEval_eq_sum_sym]
  apply Finset.sum_congr
  · ext m
    simp
  · intro m hm
    rfl

end

end Fabius
