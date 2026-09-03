import FabiusFunction.FiniteQBinomialCore
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Dissection of finite q-Pochhammer products into residue classes

The factors `1 - a q^j` of `(a;q)_N` are indexed by `j < N`.  Sorting them
by the residue of `j` modulo `r` groups them into `r` products, each of which
is itself a `q^r`-shifted factorial with a shifted parameter:

`(a;q)_{rn} = ∏_{s<r} (a q^s ; q^r)_n`.

When the length `N = rn + u` is not a multiple of `r`, the first `u` residue
classes receive one extra factor:

`(a;q)_{rn+u} = ∏_{s<u} (a q^s ; q^r)_{n+1} · ∏_{u≤s<r} (a q^s ; q^r)_n`.

Both identities are proved over an arbitrary commutative ring, without any
hypothesis on `q`, and the remainder `u` is allowed to equal `r` (in which
case the second product is empty and the identity is the exact dissection
at length `n + 1`).  The infinite-product analogue, valid for every
contracting nome in a complete normed ring, is
`Fabius.qPochhammerInfIn_dissection` in `QPochhammerInfinite`.

## Main results

* `finiteQPochhammerIn_dissection`: the exact dissection `(a;q)_{rn}`.
* `finiteQPochhammerIn_dissection_remainder`: the dissection with a
  remainder `u ≤ r`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

variable {R : Type*} [CommRing R]

/-- **Dissection into residue classes.**  For every `r` and `n`,
`(a;q)_{rn} = ∏_{s<r} (a q^s ; q^r)_n`: the factor of index `j = s + r t`
belongs to the residue class `s` and is the `t`-th factor of the
`q^r`-shifted factorial with parameter `a q^s`.  The proof is an induction on
`n` that peels one full period `(a q^{rn}; q)_r` at a time and distributes
its `r` factors to the `r` classes. -/
theorem finiteQPochhammerIn_dissection (a q : R) (r n : ℕ) :
    finiteQPochhammerIn a q (r * n) =
      ∏ s ∈ range r, finiteQPochhammerIn (a * q ^ s) (q ^ r) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc finiteQPochhammerIn a q (r * (n + 1))
          = finiteQPochhammerIn a q (r * n) *
              finiteQPochhammerIn (a * q ^ (r * n)) q r := by
            rw [mul_add_one, finiteQPochhammerIn_add]
        _ = (∏ s ∈ range r, finiteQPochhammerIn (a * q ^ s) (q ^ r) n) *
              ∏ s ∈ range r, (1 - a * q ^ s * (q ^ r) ^ n) := by
            rw [ih]
            congr 1
            unfold finiteQPochhammerIn
            refine prod_congr rfl fun s _ => ?_
            rw [← pow_mul]
            ring
        _ = ∏ s ∈ range r, finiteQPochhammerIn (a * q ^ s) (q ^ r) (n + 1) := by
            rw [← prod_mul_distrib]
            exact prod_congr rfl fun s _ => (finiteQPochhammerIn_succ _ _ _).symm

/-- **Dissection with a remainder.**  For `u ≤ r`,
`(a;q)_{rn+u} = ∏_{s<u} (a q^s ; q^r)_{n+1} · ∏_{u≤s<r} (a q^s ; q^r)_n`.
The residues `s < u` receive the extra factor `1 - a q^{s}(q^r)^n` of the
trailing partial period `(a q^{rn}; q)_u`; the remaining residues do not.
At `u = 0` this is `finiteQPochhammerIn_dissection`, and at `u = r` it is
the same dissection at length `n + 1`. -/
theorem finiteQPochhammerIn_dissection_remainder (a q : R) (r n : ℕ)
    {u : ℕ} (hu : u ≤ r) :
    finiteQPochhammerIn a q (r * n + u) =
      (∏ s ∈ range u, finiteQPochhammerIn (a * q ^ s) (q ^ r) (n + 1)) *
        ∏ s ∈ Ico u r, finiteQPochhammerIn (a * q ^ s) (q ^ r) n := by
  have hsplit :
      (∏ s ∈ range u, finiteQPochhammerIn (a * q ^ s) (q ^ r) n) *
          ∏ s ∈ Ico u r, finiteQPochhammerIn (a * q ^ s) (q ^ r) n =
        ∏ s ∈ range r, finiteQPochhammerIn (a * q ^ s) (q ^ r) n :=
    prod_range_mul_prod_Ico _ hu
  have htail :
      finiteQPochhammerIn (a * q ^ (r * n)) q u =
        ∏ s ∈ range u, (1 - a * q ^ s * (q ^ r) ^ n) := by
    unfold finiteQPochhammerIn
    refine prod_congr rfl fun s _ => ?_
    rw [← pow_mul]
    ring
  calc finiteQPochhammerIn a q (r * n + u)
      = finiteQPochhammerIn a q (r * n) *
          finiteQPochhammerIn (a * q ^ (r * n)) q u :=
        finiteQPochhammerIn_add a q (r * n) u
    _ = ((∏ s ∈ range u, finiteQPochhammerIn (a * q ^ s) (q ^ r) n) *
            ∏ s ∈ Ico u r, finiteQPochhammerIn (a * q ^ s) (q ^ r) n) *
          ∏ s ∈ range u, (1 - a * q ^ s * (q ^ r) ^ n) := by
        rw [finiteQPochhammerIn_dissection, ← hsplit, htail]
    _ = (∏ s ∈ range u,
            finiteQPochhammerIn (a * q ^ s) (q ^ r) n *
              (1 - a * q ^ s * (q ^ r) ^ n)) *
          ∏ s ∈ Ico u r, finiteQPochhammerIn (a * q ^ s) (q ^ r) n := by
        rw [prod_mul_distrib]
        ring
    _ = _ := by
        congr 1
        exact prod_congr rfl fun s _ => (finiteQPochhammerIn_succ _ _ _).symm

end Fabius
