import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.MaxPowDiv
import Lean.Elab.Tactic.Omega

/-!
# Weighted multiplicities of geometric scales

Many product expansions in the Fabius--Rvachev theory contain one factor
for every geometric scale dividing an index.  This module isolates the
finite additive calculus behind those multiplicities.

For weights `w : ℕ → M`, `inclusivePrefixSum w n` is the sum of the
first `n + 1` weights.  The generic layer-cake theorem
`sum_inclusivePrefixSum_eq_sum_filter_card_nsmul` exchanges a finite sum of
such prefixes with a sum over their levels.  It works in every additive
commutative monoid and is independent of divisibility.

Specializing the height to `padicValNat b n` gives
`weightedScaleMultiplicity b w n`.  The main consequences are:

* constant weights collapse to one scalar multiple, with unit natural weight
  giving the exact layer count `padicValNat b n + 1`;
* multiplication by `b ^ k` exposes the first `k` layers and shifts the
  remaining weights;
* a bounded multiplicity is exactly a sum over the powers `b ^ h` dividing
  the index;
* summing over the positive integers through `N` replaces every layer by
  the elementary count `N / b ^ h`;
* Pascal weights `h.choose r` turn a multiplicity into the binomial
  coefficient `(padicValNat b n + 1).choose (r + 1)`.

The base need not be prime.  The shift laws require `1 < b`, while the
divisibility and cumulative formulas need only `b ≠ 1`; in particular,
their statements include the harmless degenerate base `0`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- The inclusive prefix of an additive weight sequence:
`inclusivePrefixSum w n = w 0 + ⋯ + w n`. -/
def inclusivePrefixSum {M : Type*} [AddCommMonoid M] (w : ℕ → M) (n : ℕ) : M :=
  ∑ h ∈ range (n + 1), w h

/-- The zeroth inclusive prefix consists only of the zeroth weight. -/
@[simp]
theorem inclusivePrefixSum_zero {M : Type*} [AddCommMonoid M] (w : ℕ → M) :
    inclusivePrefixSum w 0 = w 0 := by
  simp [inclusivePrefixSum]

/-- Extending an inclusive prefix by one appends the next weight. -/
theorem inclusivePrefixSum_succ {M : Type*} [AddCommMonoid M]
    (w : ℕ → M) (n : ℕ) :
    inclusivePrefixSum w (n + 1) = inclusivePrefixSum w n + w (n + 1) := by
  simp [inclusivePrefixSum, Finset.sum_range_succ]

/-- Split an inclusive prefix after its first `m` terms.  The second
summand remains an inclusive prefix, now of the shifted weight sequence. -/
theorem inclusivePrefixSum_add {M : Type*} [AddCommMonoid M]
    (w : ℕ → M) (m n : ℕ) :
    inclusivePrefixSum w (m + n) =
      (∑ h ∈ range m, w h) + inclusivePrefixSum (fun h ↦ w (m + h)) n := by
  rw [inclusivePrefixSum, inclusivePrefixSum,
    show m + n + 1 = m + (n + 1) by omega, Finset.sum_range_add]

/-- **Finite layer-cake identity.**  Suppose every height occurring in `s`
is strictly below `H`.  Summing the inclusive weight prefixes attached to
the points of `s` is the same as summing, at each level `h < H`, the weight
`w h` once for every point whose height reaches that level.

This is a finite Fubini theorem in an arbitrary additive commutative
monoid; neither subtraction nor an order on the codomain is needed. -/
theorem sum_inclusivePrefixSum_eq_sum_filter_card_nsmul
    {ι M : Type*} [AddCommMonoid M]
    (s : Finset ι) (height : ι → ℕ) (w : ℕ → M) (H : ℕ)
    (hheight : ∀ x ∈ s, height x < H) :
    ∑ x ∈ s, inclusivePrefixSum w (height x) =
      ∑ h ∈ range H, ((s.filter fun x ↦ h ≤ height x).card) • w h := by
  classical
  calc
    ∑ x ∈ s, inclusivePrefixSum w (height x) =
        ∑ x ∈ s, ∑ h ∈ range H, if h ≤ height x then w h else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [inclusivePrefixSum, ← Finset.sum_filter]
      apply Finset.sum_congr
      · ext h
        simp only [Finset.mem_range, Finset.mem_filter]
        have hxH := hheight x hx
        omega
      · intro h hh
        rfl
    _ = ∑ h ∈ range H, ∑ x ∈ s, if h ≤ height x then w h else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ h ∈ range H, ((s.filter fun x ↦ h ≤ height x).card) • w h := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [← Finset.sum_filter, Finset.sum_const]

/-- The total weight of all geometric layers of `n` in base `b`.

The layers are numbered `0, …, padicValNat b n`; hence a constant unit
weight records one more than the usual multiplicity. -/
def weightedScaleMultiplicity {M : Type*} [AddCommMonoid M]
    (b : ℕ) (w : ℕ → M) (n : ℕ) : M :=
  inclusivePrefixSum w (padicValNat b n)

/-- A constant weight is repeated once for every layer
`0, …, padicValNat b n`. -/
@[simp]
theorem weightedScaleMultiplicity_const
    {M : Type*} [AddCommMonoid M] (b n : ℕ) (a : M) :
    weightedScaleMultiplicity b (fun _ ↦ a) n =
      (padicValNat b n + 1) • a := by
  simp [weightedScaleMultiplicity, inclusivePrefixSum]

/-- Unit `ℕ`-valued weights count those layers. -/
@[simp]
theorem weightedScaleMultiplicity_one_nat (b n : ℕ) :
    weightedScaleMultiplicity b (fun _ ↦ (1 : ℕ)) n =
      padicValNat b n + 1 := by
  simp

/-- Multiplication by `b ^ k` exposes the first `k` weight layers and shifts
the weights of all layers already present in `n`.

This holds for every (not necessarily prime) base greater than one. -/
theorem weightedScaleMultiplicity_base_pow_mul
    {M : Type*} [AddCommMonoid M] (b : ℕ) (w : ℕ → M) (n k : ℕ)
    (hb : 1 < b) (hn : n ≠ 0) :
    weightedScaleMultiplicity b w (b ^ k * n) =
      (∑ h ∈ range k, w h) +
        weightedScaleMultiplicity b (fun h ↦ w (k + h)) n := by
  unfold weightedScaleMultiplicity
  rw [padicValNat_base_pow_mul hb hn,
    add_comm (padicValNat b n) k, inclusivePrefixSum_add]

/-- One multiplication by the base separates the new bottom layer from
the shifted layers of the original index. -/
theorem weightedScaleMultiplicity_base_mul
    {M : Type*} [AddCommMonoid M] (b : ℕ) (w : ℕ → M) (n : ℕ)
    (hb : 1 < b) (hn : n ≠ 0) :
    weightedScaleMultiplicity b w (b * n) =
      w 0 + weightedScaleMultiplicity b (fun h ↦ w (h + 1)) n := by
  simpa [add_comm] using
    weightedScaleMultiplicity_base_pow_mul b w n 1 hb hn

/-- A bounded weighted multiplicity is the sum of the weights attached to
exactly those powers of the base that divide the index.

The strict bound `padicValNat b n < H` is optimal: it says precisely that
the finite filter `range H` contains every contributing layer. -/
theorem weightedScaleMultiplicity_eq_sum_filter_pow_dvd_of_lt
    {M : Type*} [AddCommMonoid M] (b : ℕ) (w : ℕ → M) (n H : ℕ)
    (hb : b ≠ 1) (hn : n ≠ 0) (hH : padicValNat b n < H) :
    weightedScaleMultiplicity b w n =
      ∑ h ∈ (range H).filter (fun h ↦ b ^ h ∣ n), w h := by
  rw [weightedScaleMultiplicity, inclusivePrefixSum]
  apply Finset.sum_congr
  · ext h
    simp only [Finset.mem_range, Finset.mem_filter]
    rw [Nat.pow_dvd_iff_le_padicValNat hb hn]
    omega
  · intro h hh
    rfl

/-- For a nonzero index, the index itself is a canonical strict upper
bound for all of its scale layers. -/
theorem weightedScaleMultiplicity_eq_sum_filter_pow_dvd
    {M : Type*} [AddCommMonoid M] (b : ℕ) (w : ℕ → M) (n : ℕ)
    (hb : b ≠ 1) (hn : n ≠ 0) :
    weightedScaleMultiplicity b w n =
      ∑ h ∈ (range n).filter (fun h ↦ b ^ h ∣ n), w h :=
  weightedScaleMultiplicity_eq_sum_filter_pow_dvd_of_lt
    b w n n hb hn (Nat.padicValNat_lt_self hn)

/-- **Cumulative weighted scale identity.**  Over the positive integers
`1, …, N`, the layer of height `h` occurs exactly `N / b ^ h` times.

The identity holds in every additive commutative monoid and for every base
other than `1`; no primality or lower bound `1 < b` is required. -/
theorem sum_range_weightedScaleMultiplicity
    {M : Type*} [AddCommMonoid M] (b N : ℕ) (w : ℕ → M) (hb : b ≠ 1) :
    ∑ m ∈ range N, weightedScaleMultiplicity b w (m + 1) =
      ∑ h ∈ range N, (N / b ^ h) • w h := by
  have hheight : ∀ m ∈ range N, padicValNat b (m + 1) < N := by
    intro m hm
    simp only [Finset.mem_range] at hm
    exact (Nat.padicValNat_lt_self (by omega : m + 1 ≠ 0)).trans_le (by omega)
  have hlayer := sum_inclusivePrefixSum_eq_sum_filter_card_nsmul
    (range N) (fun m ↦ padicValNat b (m + 1)) w N hheight
  simp only [weightedScaleMultiplicity] at hlayer ⊢
  rw [hlayer]
  apply Finset.sum_congr rfl
  intro h hh
  have hfilter :
      (range N).filter (fun m ↦ h ≤ padicValNat b (m + 1)) =
        (range N).filter (fun m ↦ b ^ h ∣ m + 1) := by
    apply Finset.filter_congr
    intro m hm
    exact (Nat.pow_dvd_iff_le_padicValNat hb (by omega : m + 1 ≠ 0)).symm
  rw [hfilter, Nat.card_multiples]

/-- Shifted hockey-stick identity for inclusive prefixes.  It is the
universal Pascal-column prefix after translating the row index by the
column index. -/
theorem inclusivePrefixSum_add_choose (n r : ℕ) :
    inclusivePrefixSum (fun h ↦ (h + r).choose r) n =
      (n + r + 1).choose (r + 1) := by
  exact Nat.sum_range_add_choose n r

/-- Direct hockey-stick identity for an unshifted Pascal column. -/
theorem inclusivePrefixSum_choose (n r : ℕ) :
    inclusivePrefixSum (fun h ↦ h.choose r) n = (n + 1).choose (r + 1) := by
  induction n with
  | zero =>
      cases r with
      | zero => simp
      | succ r =>
          rw [inclusivePrefixSum_zero, Nat.choose_zero_succ,
            Nat.choose_eq_zero_of_lt (by omega)]
  | succ n ih =>
      rw [inclusivePrefixSum_succ, ih, Nat.choose_succ_succ]
      exact Nat.add_comm _ _

/-- Pascal weights evaluate a scale multiplicity as one binomial
coefficient of the underlying valuation. -/
theorem weightedScaleMultiplicity_choose (b n r : ℕ) :
    weightedScaleMultiplicity b (fun h ↦ h.choose r) n =
      (padicValNat b n + 1).choose (r + 1) := by
  exact inclusivePrefixSum_choose (padicValNat b n) r

/-- **Cumulative Pascal floor identity.**  The sum of the binomial
valuation statistic over `1, …, N` is the floor sum obtained by weighting
the `h`-th divisibility layer by `h.choose r`. -/
theorem sum_range_padicValNat_choose
    (b N r : ℕ) (hb : b ≠ 1) :
    ∑ m ∈ range N, (padicValNat b (m + 1) + 1).choose (r + 1) =
      ∑ h ∈ range N, (N / b ^ h) * h.choose r := by
  calc
    ∑ m ∈ range N, (padicValNat b (m + 1) + 1).choose (r + 1) =
        ∑ m ∈ range N,
          weightedScaleMultiplicity b (fun h ↦ h.choose r) (m + 1) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact (weightedScaleMultiplicity_choose b (m + 1) r).symm
    _ = ∑ h ∈ range N, (N / b ^ h) • h.choose r :=
      sum_range_weightedScaleMultiplicity b N (fun h ↦ h.choose r) hb
    _ = ∑ h ∈ range N, (N / b ^ h) * h.choose r := by
      simp only [Nat.nsmul_eq_mul]

end Fabius
