import FabiusFunction.NewtonBasisGeneratingFunction
import FabiusFunction.NewtonMultiplicityAssembly
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Newton coefficients are forced

`NewtonMultiplicityAssembly` proves the Gregory–Newton reading of a
weight sequence,

`a m = ∑_{r ≤ m} C(m,r) • (Δ^r a) 0`

(`weight_eq_sum_choose_fwdDiff`), and `NewtonBasisGeneratingFunction`
builds `newtonPoly c d` out of prescribed coefficients.  Neither says
that the coefficients are *determined*: as the exponents volume puts
it of `p1:thm:newton`, the corpus "exhibits `Δ^r P(0)` as a valid
choice rather than as the unique one", and it records the missing
half as "that `Δ^s` applied to a Newton sum returns `c_s` --- is not
formalized".

That is what this module proves, and in the generality the statement
actually has rather than the one the volume needs.  The Newton basis
is *triangular* under `Δ`: `Δ C(·,r) = C(·,r-1)`, so `Δ^k C(·,r)` is
`C(·,r-k)`, whose value at `0` is `1` exactly when `k = r`.  Applying
`Δ^k` at `0` to a Newton combination therefore reads off the `k`-th
coefficient and annihilates every other basis vector, with no
hypothesis on the coefficients whatsoever.

Stated over an arbitrary `Finset` of Newton indices and an arbitrary
`AddCommGroup` of coefficients, the inversion is

`Δ^k (∑_{r ∈ s} C(·,r) • c r) 0 = if k ∈ s then c k else 0`.

Two things are gained over the volume's formulation.  The index set is
an arbitrary finite set rather than `range (d+1)`, so no
"degree" is presupposed; and the `k ∉ s` branch is part of the
statement, which is what makes it an inversion rather than an
evaluation --- it says the basis is not merely spanning but free.

* `Fabius.fwdDiff_iter_smul_const` — the iterated form of Mathlib's
  `fwdDiff_smul_const`, missing there;
* `Fabius.fwdDiff_iter_newtonCombination_zero` — **the inversion**;
* `Fabius.newtonCombination_injOn` — hence the coefficients supported
  on `s` are unique;
* `Fabius.fwdDiff_iter_newtonPoly_zero`,
  `Fabius.newtonPoly_coeff_unique` — the two specialized to the
  volume's `newtonPoly` over `ℝ`;
* `Fabius.fwdDiff_iter_weight_zero` — the round trip: run the
  Gregory–Newton expansion of `weight_eq_sum_choose_fwdDiff` back
  through the inversion and the iterated differences come back.

Mathlib supplies the arithmetic kernel, `fwdDiff_iter_choose_zero`;
everything here is the linear algebra around it.
-/

set_option autoImplicit false

open Finset fwdDiff

namespace Fabius

/-- **Iterated `Δ` of a scalar function times a fixed vector.**
Mathlib has the one-step `fwdDiff_smul_const` but not its iterate;
the induction is immediate. -/
theorem fwdDiff_iter_smul_const {M G R : Type*} [AddCommMonoid M]
    [AddCommGroup G] [Ring R] [Module R G] (h : M) (f : M → R)
    (g : G) (n : ℕ) :
    Δ_[h]^[n] (fun y => f y • g) = fun y => (Δ_[h]^[n] f y) • g := by
  induction n generalizing f with
  | zero => simp
  | succ n IH =>
    rw [Function.iterate_succ_apply, fwdDiff_smul_const]
    show Δ_[h]^[n] (fun y => (Δ_[h] f y) • g) = _
    rw [IH (Δ_[h] f)]
    funext y
    rw [Function.iterate_succ_apply]

/-- **The Newton basis is free, and `Δ^k` at `0` is the `k`-th
coordinate functional.**  For any finite index set `s`, any
coefficients `c` in an additive commutative group, and any `k`,

`Δ^k (fun m => ∑_{r ∈ s} C(m,r) • c r) 0 = if k ∈ s then c k else 0`.

No hypothesis relates `k` to `s`: the `k ∉ s` branch says the
functional kills the whole span, which is the half that turns the
Gregory–Newton expansion from *a* representation into *the*
representation. -/
theorem fwdDiff_iter_newtonCombination_zero {G : Type*}
    [AddCommGroup G] (s : Finset ℕ) (c : ℕ → G) (k : ℕ) :
    Δ_[1]^[k] (fun m : ℕ => ∑ r ∈ s, ((m.choose r : ℤ)) • c r) 0
      = if k ∈ s then c k else 0 := by
  have hsplit : (fun m : ℕ => ∑ r ∈ s, ((m.choose r : ℤ)) • c r)
      = ∑ r ∈ s, (fun m : ℕ => ((m.choose r : ℤ)) • c r) := by
    funext m
    simp
  rw [hsplit, fwdDiff_iter_finsetSum]
  have hterm : ∀ r ∈ s,
      (Δ_[1]^[k] (fun m : ℕ => ((m.choose r : ℤ)) • c r)) 0
        = if k = r then c r else 0 := by
    intro r _
    rw [fwdDiff_iter_smul_const (1 : ℕ)
      (fun m : ℕ => ((m.choose r : ℤ))) (c r) k]
    rw [fwdDiff_iter_choose_zero]
    by_cases hkr : k = r
    · simp [hkr]
    · simp [hkr]
  rw [Finset.sum_apply]
  rw [Finset.sum_congr rfl hterm]
  exact Finset.sum_ite_eq s k c

/-- **Uniqueness of Newton coefficients.**  Two coefficient families
that agree as Newton combinations over `s` agree on `s`.  This is the
statement the exponents volume needs: the Gregory–Newton coefficients
are not merely *a* valid choice. -/
theorem newtonCombination_injOn {G : Type*} [AddCommGroup G]
    (s : Finset ℕ) (c c' : ℕ → G)
    (hEq : (fun m : ℕ => ∑ r ∈ s, ((m.choose r : ℤ)) • c r)
      = fun m : ℕ => ∑ r ∈ s, ((m.choose r : ℤ)) • c' r)
    {k : ℕ} (hk : k ∈ s) : c k = c' k := by
  have h := congrArg (fun f : ℕ → G => Δ_[1]^[k] f 0) hEq
  simp only at h
  rw [fwdDiff_iter_newtonCombination_zero s c k,
    fwdDiff_iter_newtonCombination_zero s c' k] at h
  simpa [hk] using h

/-- **The inversion at the volume's `newtonPoly`.**  For `k ≤ d`,

`Δ^k (newtonPoly c d) 0 = c k`,

which is the display the volume marks as unformalized.  The passage
from the `ℤ`-scalar-action form above is `zsmul_eq_mul` together with
the commutation `c r * C(m,r) = C(m,r) * c r`. -/
theorem fwdDiff_iter_newtonPoly_zero (c : ℕ → ℝ) (d k : ℕ)
    (hk : k ≤ d) :
    Δ_[1]^[k] (newtonPoly c d) 0 = c k := by
  have hfun : newtonPoly c d
      = fun m : ℕ => ∑ r ∈ range (d + 1), ((m.choose r : ℤ)) • c r := by
    funext m
    rw [newtonPoly]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [hfun, fwdDiff_iter_newtonCombination_zero]
  simp [Finset.mem_range, Nat.lt_succ_of_le hk]

/-- **Uniqueness for `newtonPoly`.**  Equal Newton polynomials of
degree bound `d` have equal coefficients up to `d`. -/
theorem newtonPoly_coeff_unique {c c' : ℕ → ℝ} {d : ℕ}
    (hEq : newtonPoly c d = newtonPoly c' d) {k : ℕ} (hk : k ≤ d) :
    c k = c' k := by
  have h := congrArg (fun f : ℕ → ℝ => Δ_[1]^[k] f 0) hEq
  simp only at h
  rwa [fwdDiff_iter_newtonPoly_zero c d k hk,
    fwdDiff_iter_newtonPoly_zero c' d k hk] at h

/-- **The round trip.**  `weight_eq_sum_choose_fwdDiff` expands a
weight sequence in the Newton basis with coefficients `(Δ^r a) 0`;
running the inversion back over that expansion returns them.  So for
every weight sequence and every `k ≤ m` the Gregory–Newton
coefficients are *exactly* the iterated forward differences at `0`,
and no other family represents `a` on `range (m+1)`. -/
theorem fwdDiff_iter_weight_zero {G : Type*} [AddCommGroup G]
    (a : ℕ → G) (m k : ℕ) (hk : k ≤ m) :
    Δ_[1]^[k]
        (fun n : ℕ => ∑ r ∈ range (m + 1),
          ((n.choose r : ℤ)) • Δ_[1]^[r] a 0) 0
      = Δ_[1]^[k] a 0 := by
  rw [fwdDiff_iter_newtonCombination_zero]
  simp [Finset.mem_range, Nat.lt_succ_of_le hk]

end Fabius
