import FabiusFunction.ParityCharacter
import Mathlib.Data.Set.Finite.Basic

/-!
# The `2`-kernel of a weighted parity character

`ParityCharacter` defines the weighted binary character
`ε_a(N) = (-1)^{∑_{h ∈ bitSupport N} a h}` and records that only the
*parity word* `h ↦ a h % 2` enters it.  The exponent-sequence volume's
generalized lobe-sign theorem asserts that `ε_a` is `2`-automatic
exactly when that parity word is eventually periodic, and the corpus
files that criterion as not addressed, on the ground that the library
has no automatic-sequence theory.

That assessment is too pessimistic.  Take the *finite `2`-kernel*
property as the working definition of `2`-automaticity — the standard
finite-`2`-kernel characterization of automatic sequences
(Allouche–Shallit, *Automatic Sequences*) — and the criterion becomes
purely combinatorial.  No automaton, no transducer, no free monoid is
needed.  This module proves it.

The mechanism is a single splitting.  For `r < 2 ^ k`, Lean core's
`Nat.testBit_two_pow_mul_add` says the bits of `2 ^ k * n + r` below
`k` are those of `r`, and the bits from `k` upwards are those of `n`
shifted up by `k`.  So `bitSupport (2 ^ k * n + r)` is the disjoint
union of `bitSupport r` with the image of `bitSupport n` under
`(· + k)`, the weight sum splits, and

`ε_a(2 ^ k * n + r) = ε_a(r) · ε_{σ^k a}(n)`,  `(σ^k a) j = a (j + k)`,

which is the volume's kernel-shift identity.  Read at `r = 0` it puts
every shifted character inside the kernel; read in general it makes
every kernel element `± (a shifted character)`.  So the kernel is
finite exactly when the parity word is eventually periodic.
Backwards, the shift-orbit lemma bounds the kernel by twice the
orbit; forwards, a pigeonhole among the shifted *characters*
produces two equal characters, and separation turns that into two
equal shifts of the parity word, which is already an eventual
period.

## What is, and is not, proved here

* The equivalence proved is exactly
  `(twoKernel (parityCharacter a)).Finite ↔
  EventuallyPeriodic (parityWord a)`,
  a statement about the finite-`2`-kernel property alone.
* Mathlib has no automatic-sequence theory.  The equivalence between
  a finite `2`-kernel and any automaton-based definition of
  `2`-automaticity is therefore **not** formalized here; it is taken
  from the literature as the meaning of the word "`2`-automatic".
* Nothing here proves the lobe-sign law `sgn Φ_a(x) = ε_a(⌊x⌋)`.  That
  needs the canonical product at general weights, which the corpus does
  not have.
* The criterion constrains the *weight parity word*, not the character.
  The character itself need not be eventually periodic: the corpus's
  `thueMorseSign_not_eventually_periodic` says the Thue–Morse sign is
  not, while `finite_twoKernel_thueMorseSign` below says its `2`-kernel
  is finite.  `EventuallyPeriodic` is the same predicate the corpus
  uses unbundled, `∃ p N, 0 < p ∧ ∀ n, N ≤ n → f (n + p) = f n`, with
  the two existentials in the other order and for `ℕ`-valued words.

## Main declarations

* `shiftSeq`, `shiftSeq_apply` — the shift `(σ^k w) j = w (j + k)`.
* `parityWord`, `parityWord_apply` — the word `h ↦ a h % 2`.
* `parityWord_shiftSeq` — shifting commutes with taking the
  parity word.
* `EventuallyPeriodic`, `eventuallyPeriodic_iff` — eventual
  periodicity of a word, and its unfolding.
* `shiftOrbit`, `mem_shiftOrbit_iff`, `shiftSeq_mem_shiftOrbit` — the
  set of all shifts of a word.
* `twoKernel`, `mem_twoKernel_iff`, `self_mem_twoKernel` — the
  `2`-kernel `{n ↦ f (2 ^ k * n + r) : r < 2 ^ k}`, which contains `f`.
* `mem_bitSupport_two_pow_mul_add_iff`,
  `bitSupport_two_pow_mul_add`, `sum_bitSupport_two_pow_mul_add` —
  **the bit-support split** in membership, `Finset` and summed form.
* `parityCharacter_two_pow_mul_add` — **the kernel-shift identity.**
* `parityCharacter_two_pow`, `parityCharacter_shiftSeq_two_pow` —
  **the probe** `ε_a(2 ^ m) = (-1)^{a m}` and its shifted form.
* `parityCharacter_eq_one_or_neg_one` — the character is a sign.
* `parityWord_eq_of_parityCharacter_eq` — **separation**: equal
  characters force equal parity words.
* `eventuallyPeriodic_of_shiftSeq_eq`, `exists_lt_shiftSeq_eq` — the
  two halves of the shift-orbit argument.
* `finite_shiftOrbit_iff` — **the shift-orbit lemma**: a word has a
  finite shift orbit iff it is eventually periodic.
* `parityCharacter_shiftSeq_parityWord`,
  `parityCharacter_shiftSeq_mem_twoKernel` — the two bridges into the
  kernel.
* `finite_twoKernel_parityCharacter_iff` — **the criterion.**
* `eventuallyPeriodic_parityWord_const`,
  `parityCharacter_const_one_eq_thueMorseSign`,
  `finite_twoKernel_thueMorseSign` — the constant-weight instance:
  the Thue–Morse sign has a finite `2`-kernel.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Shifts, parity words, orbits, and the `2`-kernel -/

/-- The shift of a weight sequence: `shiftSeq w k` reads `w` from
position `k` onwards.  The offset is written on the right, `w (j + k)`,
because that is the form in which the bit-support split produces it. -/
def shiftSeq (w : ℕ → ℕ) (k : ℕ) : ℕ → ℕ := fun j => w (j + k)

/-- Evaluating a shift reads the original word further along. -/
@[simp] theorem shiftSeq_apply (w : ℕ → ℕ) (k j : ℕ) :
    shiftSeq w k j = w (j + k) := rfl

/-- The parity word of a weight sequence.  By
`parityCharacter_mod_two` this is all of `a` that the character sees. -/
def parityWord (a : ℕ → ℕ) : ℕ → ℕ := fun h => a h % 2

/-- The letters of the parity word are the weight residues.

Deliberately *not* `@[simp]`: the criterion below is stated about
`parityWord a`, and a global unfolding lemma would dissolve that
object on sight in every downstream `simp` call. -/
theorem parityWord_apply (a : ℕ → ℕ) (h : ℕ) :
    parityWord a h = a h % 2 := rfl

/-- Shifting commutes with taking the parity word.  Both sides are
`fun j ↦ a (j + k) % 2`; naming the equality once keeps the two uses
below from resting on an unchecked defeq. -/
theorem parityWord_shiftSeq (a : ℕ → ℕ) (k : ℕ) :
    parityWord (shiftSeq a k) = shiftSeq (parityWord a) k := rfl

/-- Eventual periodicity of a word: some positive period `p` holds
from some threshold `n₀` onwards. -/
def EventuallyPeriodic (w : ℕ → ℕ) : Prop :=
  ∃ n₀ p, 0 < p ∧ ∀ m, n₀ ≤ m → w (m + p) = w m

/-- The definition of `EventuallyPeriodic`, unfolded, so that it can
be built and taken apart without relying on delta reduction. -/
theorem eventuallyPeriodic_iff (w : ℕ → ℕ) :
    EventuallyPeriodic w ↔
      ∃ n₀ p, 0 < p ∧ ∀ m, n₀ ≤ m → w (m + p) = w m := Iff.rfl

/-- The shift orbit of a word: the set of all of its shifts. -/
def shiftOrbit (w : ℕ → ℕ) : Set (ℕ → ℕ) := Set.range (shiftSeq w)

/-- Membership in the shift orbit is being some shift. -/
theorem mem_shiftOrbit_iff {w g : ℕ → ℕ} :
    g ∈ shiftOrbit w ↔ ∃ k, shiftSeq w k = g := Iff.rfl

/-- Every shift lies in the shift orbit. -/
theorem shiftSeq_mem_shiftOrbit (w : ℕ → ℕ) (k : ℕ) :
    shiftSeq w k ∈ shiftOrbit w :=
  mem_shiftOrbit_iff.mpr ⟨k, rfl⟩

/-- **The `2`-kernel** of an integer sequence: all subsequences
`n ↦ f (2 ^ k * n + r)` along arithmetic progressions of dyadic
modulus.  Finiteness of this set is the standard combinatorial
characterization of `2`-automaticity; see the module docstring for
what is and is not claimed about that. -/
def twoKernel (f : ℕ → ℤ) : Set (ℕ → ℤ) :=
  {g | ∃ k r, r < 2 ^ k ∧ g = fun n => f (2 ^ k * n + r)}

/-- Membership in the `2`-kernel, unfolded. -/
theorem mem_twoKernel_iff {f g : ℕ → ℤ} :
    g ∈ twoKernel f ↔
      ∃ k r, r < 2 ^ k ∧ g = fun n => f (2 ^ k * n + r) := Iff.rfl

/-- The sequence itself lies in its `2`-kernel, at `k = r = 0`. -/
theorem self_mem_twoKernel (f : ℕ → ℤ) : f ∈ twoKernel f := by
  have h : f = fun n => f (2 ^ 0 * n + 0) := by
    funext n
    show f n = f (2 ^ 0 * n + 0)
    simp
  exact mem_twoKernel_iff.mpr ⟨0, 0, by norm_num, h⟩

/-! ## The bit-support split -/

/-- **The bit-support split, in membership form.**  For `r < 2 ^ k` a
position lies in the bit support of `2 ^ k * n + r` either because it
is below `k` and lies in the bit support of `r`, or because it is at
least `k` and its drop by `k` lies in the bit support of `n`.  This is
`Nat.testBit_two_pow_mul_add` read through `mem_bitSupport`. -/
theorem mem_bitSupport_two_pow_mul_add_iff {k r : ℕ} (hr : r < 2 ^ k)
    (n j : ℕ) :
    j ∈ bitSupport (2 ^ k * n + r) ↔
      (j < k ∧ j ∈ bitSupport r) ∨ (k ≤ j ∧ j - k ∈ bitSupport n) := by
  rw [mem_bitSupport (n := 2 ^ k * n + r) (j := j),
    Nat.testBit_two_pow_mul_add n hr j]
  rcases Nat.lt_or_ge j k with hj | hj
  · rw [if_pos hj]
    constructor
    · intro h
      exact Or.inl ⟨hj, mem_bitSupport.mpr h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact mem_bitSupport.mp h
      · exfalso; omega
  · rw [if_neg (by omega : ¬ j < k)]
    constructor
    · intro h
      exact Or.inr ⟨hj, mem_bitSupport.mpr h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exfalso; omega
      · exact mem_bitSupport.mp h

/-- **The bit-support split, as a `Finset` identity.**  For
`r < 2 ^ k`,
`bitSupport (2 ^ k * n + r)
  = bitSupport r ∪ (bitSupport n).image (· + k)`,
the low part carrying `r` and the high part carrying `n` shifted up by
`k`.  The union is disjoint, since `bitSupport r ⊆ range k`; that is
recorded inside `sum_bitSupport_two_pow_mul_add`. -/
theorem bitSupport_two_pow_mul_add {k r : ℕ} (hr : r < 2 ^ k) (n : ℕ) :
    bitSupport (2 ^ k * n + r) =
      bitSupport r ∪ (bitSupport n).image (fun i => i + k) := by
  have hsub : bitSupport r ⊆ range k :=
    (bitSupport_subset_range_iff_lt_two_pow r k).mpr hr
  ext j
  rw [Finset.mem_union, Finset.mem_image,
    mem_bitSupport_two_pow_mul_add_iff hr n j]
  constructor
  · rintro (⟨-, h⟩ | ⟨hk, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨j - k, h, ?_⟩
      show j - k + k = j
      omega
  · rintro (h | ⟨i, hi, hij⟩)
    · have hjk : j < k := Finset.mem_range.mp (hsub h)
      exact Or.inl ⟨hjk, h⟩
    · have hij' : i + k = j := hij
      refine Or.inr ⟨by omega, ?_⟩
      have hji : j - k = i := by omega
      rw [hji]
      exact hi

/-- **The bit-support split, summed.**  For `r < 2 ^ k` the weight sum
over `bitSupport (2 ^ k * n + r)` is the weight sum over
`bitSupport r` plus the shifted weight sum over `bitSupport n`. -/
theorem sum_bitSupport_two_pow_mul_add (a : ℕ → ℕ) {k r : ℕ}
    (hr : r < 2 ^ k) (n : ℕ) :
    ∑ h ∈ bitSupport (2 ^ k * n + r), a h =
      (∑ h ∈ bitSupport r, a h) + ∑ i ∈ bitSupport n, a (i + k) := by
  have hsub : bitSupport r ⊆ range k :=
    (bitSupport_subset_range_iff_lt_two_pow r k).mpr hr
  have hdisj : Disjoint (bitSupport r)
      ((bitSupport n).image (fun i => i + k)) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    have hjk : j < k := Finset.mem_range.mp (hsub hj)
    obtain ⟨i, -, hij⟩ := Finset.mem_image.mp hj'
    have hij' : i + k = j := hij
    omega
  have hinj : Set.InjOn (fun i => i + k) (bitSupport n : Set ℕ) := by
    intro x _ y _ hxy
    have hxy' : x + k = y + k := hxy
    omega
  have himg : ∑ x ∈ (bitSupport n).image (fun i => i + k), a x
      = ∑ i ∈ bitSupport n, a (i + k) := Finset.sum_image hinj
  rw [bitSupport_two_pow_mul_add hr n, Finset.sum_union hdisj,
    himg]

/-! ## The kernel-shift identity and the probe -/

/-- **The kernel-shift identity.**  For `r < 2 ^ k`,

`ε_a(2 ^ k * n + r) = ε_a(r) · ε_{σ^k a}(n)`,

where `σ^k a = shiftSeq a k` is the weight sequence read from position
`k` onwards.  This is the volume's `(p1:eq:kernel-shift)`. -/
theorem parityCharacter_two_pow_mul_add (a : ℕ → ℕ) {k r : ℕ}
    (hr : r < 2 ^ k) (n : ℕ) :
    parityCharacter a (2 ^ k * n + r) =
      parityCharacter a r * parityCharacter (shiftSeq a k) n := by
  have hsum : ∑ h ∈ bitSupport (2 ^ k * n + r), a h
      = (∑ h ∈ bitSupport r, a h)
        + ∑ h ∈ bitSupport n, shiftSeq a k h :=
    sum_bitSupport_two_pow_mul_add a hr n
  show (-1 : ℤ) ^ (∑ h ∈ bitSupport (2 ^ k * n + r), a h)
      = (-1) ^ (∑ h ∈ bitSupport r, a h)
        * (-1) ^ (∑ h ∈ bitSupport n, shiftSeq a k h)
  rw [hsum, pow_add]

/-- **The probe.**  At a power of two the character reads off a single
weight: `ε_a(2 ^ m) = (-1)^{a m}`. -/
theorem parityCharacter_two_pow (a : ℕ → ℕ) (m : ℕ) :
    parityCharacter a (2 ^ m) = (-1) ^ a m := by
  have h := parityCharacter_sum_two_pow a {m}
  rw [Finset.sum_singleton, Finset.sum_singleton] at h
  exact h

/-- The probe applied to a shifted weight sequence.  This is the
volume's `ε_{S^k a}(2^j) = (-1)^{ā_{k+j}}`, recorded here for
reference; the separation lemma below uses the unshifted probe. -/
theorem parityCharacter_shiftSeq_two_pow (a : ℕ → ℕ) (k m : ℕ) :
    parityCharacter (shiftSeq a k) (2 ^ m) = (-1) ^ a (m + k) :=
  parityCharacter_two_pow (shiftSeq a k) m

/-- The character takes only the two values `1` and `-1`. -/
theorem parityCharacter_eq_one_or_neg_one (a : ℕ → ℕ) (n : ℕ) :
    parityCharacter a n = 1 ∨ parityCharacter a n = -1 := by
  rcases Nat.even_or_odd (∑ h ∈ bitSupport n, a h) with he | ho
  · refine Or.inl ?_
    show (-1 : ℤ) ^ (∑ h ∈ bitSupport n, a h) = 1
    exact he.neg_one_pow
  · refine Or.inr ?_
    show (-1 : ℤ) ^ (∑ h ∈ bitSupport n, a h) = -1
    exact ho.neg_one_pow

/-! ## Separation: a character determines its parity word -/

/-- A sign depends only on the residue of its exponent. -/
private theorem neg_one_pow_mod (m : ℕ) :
    (-1 : ℤ) ^ m = (-1) ^ (m % 2) := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

/-- Equal signs force equal exponent residues. -/
private theorem mod_two_eq_of_neg_one_pow_eq {x y : ℕ}
    (h : (-1 : ℤ) ^ x = (-1) ^ y) : x % 2 = y % 2 := by
  rw [neg_one_pow_mod x, neg_one_pow_mod y] at h
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy
  · rw [hx, hy]
  · rw [hx, hy] at h; norm_num at h
  · rw [hx, hy] at h; norm_num at h
  · rw [hx, hy]

/-- **Separation.**  Two weight sequences with the same character
everywhere have the same parity word.  The probe at `n = 2 ^ j`
reduces this to `(-1)^x = (-1)^y → x % 2 = y % 2`. -/
theorem parityWord_eq_of_parityCharacter_eq {b c : ℕ → ℕ}
    (h : ∀ n, parityCharacter b n = parityCharacter c n) :
    parityWord b = parityWord c := by
  funext j
  have hj : (-1 : ℤ) ^ b j = (-1) ^ c j := by
    rw [← parityCharacter_two_pow b j, ← parityCharacter_two_pow c j]
    exact h (2 ^ j)
  exact mod_two_eq_of_neg_one_pow_eq hj

/-! ## The shift-orbit lemma -/

/-- Two distinct shifts that coincide already exhibit an eventual
period: the larger index minus the smaller is a period valid from the
smaller index on. -/
theorem eventuallyPeriodic_of_shiftSeq_eq {w : ℕ → ℕ} {k l : ℕ}
    (hkl : k ≠ l) (hsh : shiftSeq w k = shiftSeq w l) :
    EventuallyPeriodic w := by
  rcases Nat.lt_or_ge k l with hlt | hge
  · refine (eventuallyPeriodic_iff w).mpr ⟨k, l - k, by omega, ?_⟩
    intro m hm
    have hval : shiftSeq w k (m - k) = shiftSeq w l (m - k) :=
      congrFun hsh (m - k)
    have h1 : w (m - k + k) = w (m - k + l) := hval
    have e1 : m - k + k = m := by omega
    have e2 : m - k + l = m + (l - k) := by omega
    rw [e1, e2] at h1
    exact h1.symm
  · have hlt : l < k := by omega
    refine (eventuallyPeriodic_iff w).mpr ⟨l, k - l, by omega, ?_⟩
    intro m hm
    have hval : shiftSeq w k (m - l) = shiftSeq w l (m - l) :=
      congrFun hsh (m - l)
    have h1 : w (m - l + k) = w (m - l + l) := hval
    have e1 : m - l + l = m := by omega
    have e2 : m - l + k = m + (k - l) := by omega
    rw [e1, e2] at h1
    exact h1

/-- Under an eventual period `p` from `n₀` on, every shift equals a
shift at an index below `n₀ + p`: repeatedly drop the index by `p`
while it stays at least `n₀ + p`. -/
theorem exists_lt_shiftSeq_eq {w : ℕ → ℕ} {n₀ p : ℕ} (hp : 0 < p)
    (hper : ∀ m, n₀ ≤ m → w (m + p) = w m) (k : ℕ) :
    ∃ k', k' < n₀ + p ∧ shiftSeq w k' = shiftSeq w k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k (n₀ + p) with hk | hk
    · exact ⟨k, hk, rfl⟩
    · obtain ⟨k', hk', heq⟩ := ih (k - p) (by omega)
      refine ⟨k', hk', ?_⟩
      rw [heq]
      funext j
      have hle : n₀ ≤ j + (k - p) := by omega
      have hstep : w (j + (k - p) + p) = w (j + (k - p)) := hper _ hle
      have e1 : j + k = j + (k - p) + p := by omega
      show w (j + (k - p)) = w (j + k)
      rw [e1, hstep]

/-- Pigeonhole: a map out of `ℕ` with finite range is not injective. -/
private theorem exists_ne_map_eq_of_finite_range {β : Type*}
    (f : ℕ → β) (h : (Set.range f).Finite) :
    ∃ k l : ℕ, k ≠ l ∧ f k = f l := by
  obtain ⟨k, -, l, -, hkl, heq⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo
      (s := (Set.univ : Set ℕ)) (t := Set.range f) (f := f)
      Set.infinite_univ (fun x _ => Set.mem_range_self x) h
  exact ⟨k, l, hkl, heq⟩

/-- **The shift-orbit lemma.**  A word has finitely many distinct
shifts exactly when it is eventually periodic.

Forwards: an infinite index set mapping into a finite orbit repeats,
and a repeat is a period.  Backwards: dropping the index by `p` leaves
the shift unchanged once the index is at least `n₀ + p`, so the orbit
is covered by the shifts at indices below `n₀ + p`. -/
theorem finite_shiftOrbit_iff (w : ℕ → ℕ) :
    (shiftOrbit w).Finite ↔ EventuallyPeriodic w := by
  constructor
  · intro hfin
    obtain ⟨k, l, hkl, heq⟩ :=
      exists_ne_map_eq_of_finite_range (shiftSeq w) hfin
    exact eventuallyPeriodic_of_shiftSeq_eq hkl heq
  · intro hEP
    obtain ⟨n₀, p, hp, hper⟩ := (eventuallyPeriodic_iff w).mp hEP
    have hbase : (shiftSeq w '' {i | i < n₀ + p}).Finite :=
      (Set.finite_lt_nat (n₀ + p)).image (shiftSeq w)
    refine hbase.subset ?_
    intro g hg
    obtain ⟨k, hk⟩ := mem_shiftOrbit_iff.mp hg
    obtain ⟨k', hk', heq⟩ := exists_lt_shiftSeq_eq hp hper k
    have hgk : g = shiftSeq w k' := (heq.trans hk).symm
    have hmem : k' ∈ {i | i < n₀ + p} := hk'
    rw [hgk]
    exact Set.mem_image_of_mem (shiftSeq w) hmem

/-! ## The criterion -/

/-- A shifted weight sequence and the corresponding shift of the
parity word carry the same character. -/
theorem parityCharacter_shiftSeq_parityWord (a : ℕ → ℕ) (k : ℕ) :
    parityCharacter (shiftSeq a k)
      = parityCharacter (shiftSeq (parityWord a) k) := by
  funext n
  exact parityCharacter_mod_two (shiftSeq a k) n

/-- Every shifted character is itself a `2`-kernel element, obtained
at residue `r = 0`. -/
theorem parityCharacter_shiftSeq_mem_twoKernel (a : ℕ → ℕ) (k : ℕ) :
    parityCharacter (shiftSeq a k) ∈ twoKernel (parityCharacter a) := by
  have hr : (0 : ℕ) < 2 ^ k := Nat.two_pow_pos k
  have hfun : parityCharacter (shiftSeq a k)
      = fun n => parityCharacter a (2 ^ k * n + 0) := by
    funext n
    show parityCharacter (shiftSeq a k) n
        = parityCharacter a (2 ^ k * n + 0)
    have hkey := parityCharacter_two_pow_mul_add a hr n
    rw [parityCharacter_zero, one_mul] at hkey
    exact hkey.symm
  exact mem_twoKernel_iff.mpr ⟨k, 0, hr, hfun⟩

/-- **The criterion.**  The weighted parity character `ε_a` has a
finite `2`-kernel exactly when the parity word `h ↦ a h % 2` is
eventually periodic.

Forwards: the shifted characters all lie in the kernel, so finitely
many of them are distinct; separation turns a repeat among the
characters into a repeat among the shifts of the parity word, and the
shift-orbit lemma turns that into eventual periodicity.  Backwards:
the kernel-shift identity makes every kernel element `±` a character
of a shift of the parity word, so the kernel sits inside the union of
the finite set of such characters with its negation.

This is the finite-`2`-kernel property, which the literature takes as
equivalent to `2`-automaticity; that equivalence is not formalized
here. -/
theorem finite_twoKernel_parityCharacter_iff (a : ℕ → ℕ) :
    (twoKernel (parityCharacter a)).Finite ↔
      EventuallyPeriodic (parityWord a) := by
  constructor
  · intro hfin
    have hsub : Set.range (fun k => parityCharacter (shiftSeq a k))
        ⊆ twoKernel (parityCharacter a) := by
      intro g hg
      obtain ⟨k, hk⟩ :
          ∃ k, parityCharacter (shiftSeq a k) = g := hg
      rw [← hk]
      exact parityCharacter_shiftSeq_mem_twoKernel a k
    obtain ⟨k, l, hkl, heq⟩ :=
      exists_ne_map_eq_of_finite_range
        (fun k => parityCharacter (shiftSeq a k)) (hfin.subset hsub)
    have heq' : parityCharacter (shiftSeq a k)
        = parityCharacter (shiftSeq a l) := heq
    have hword : parityWord (shiftSeq a k)
        = parityWord (shiftSeq a l) :=
      parityWord_eq_of_parityCharacter_eq (fun n => congrFun heq' n)
    have hshift : shiftSeq (parityWord a) k
        = shiftSeq (parityWord a) l := by
      rw [← parityWord_shiftSeq, ← parityWord_shiftSeq]
      exact hword
    exact eventuallyPeriodic_of_shiftSeq_eq hkl hshift
  · intro hper
    have horbit : (shiftOrbit (parityWord a)).Finite :=
      (finite_shiftOrbit_iff (parityWord a)).mpr hper
    have hA : (parityCharacter '' shiftOrbit (parityWord a)).Finite :=
      horbit.image parityCharacter
    have hB : ((fun q : ℕ → ℤ => fun n => -q n) ''
        (parityCharacter '' shiftOrbit (parityWord a))).Finite :=
      hA.image (fun q : ℕ → ℤ => fun n => -q n)
    refine (hA.union hB).subset ?_
    intro g hg
    obtain ⟨k, r, hr, hgdef⟩ := mem_twoKernel_iff.mp hg
    have hmem0 : shiftSeq (parityWord a) k
        ∈ shiftOrbit (parityWord a) :=
      shiftSeq_mem_shiftOrbit (parityWord a) k
    have hmemA : parityCharacter (shiftSeq (parityWord a) k)
        ∈ parityCharacter '' shiftOrbit (parityWord a) :=
      Set.mem_image_of_mem parityCharacter hmem0
    have hbase : ∀ n, g n = parityCharacter a r
        * parityCharacter (shiftSeq (parityWord a) k) n := by
      intro n
      have h1 : g n = parityCharacter a (2 ^ k * n + r) :=
        congrFun hgdef n
      rw [h1, parityCharacter_two_pow_mul_add a hr n,
        parityCharacter_shiftSeq_parityWord a k]
    rcases parityCharacter_eq_one_or_neg_one a r with hs | hs
    · have hg1 : g = parityCharacter (shiftSeq (parityWord a) k) := by
        funext n
        rw [hbase n, hs, one_mul]
      rw [hg1]
      exact Set.mem_union_left _ hmemA
    · have hg2 : g = fun n =>
          -parityCharacter (shiftSeq (parityWord a) k) n := by
        funext n
        show g n = -parityCharacter (shiftSeq (parityWord a) k) n
        rw [hbase n, hs, neg_one_mul]
      rw [hg2]
      exact Set.mem_union_right _
        (Set.mem_image_of_mem (fun q : ℕ → ℤ => fun n => -q n) hmemA)

/-! ## The constant-weight instance -/

/-- A constant weight sequence has a constant, hence eventually
periodic, parity word. -/
theorem eventuallyPeriodic_parityWord_const (c : ℕ) :
    EventuallyPeriodic (parityWord (fun _ => c)) :=
  (eventuallyPeriodic_iff _).mpr ⟨0, 1, Nat.one_pos, fun _ _ => rfl⟩

/-- The character at the constant weight `a ≡ 1` is the Thue–Morse
sign, in function form. -/
theorem parityCharacter_const_one_eq_thueMorseSign :
    parityCharacter (fun _ => 1) = thueMorseSign := by
  funext n
  exact parityCharacter_const_one n

/-- **The Thue–Morse sign has a finite `2`-kernel**, recovered as the
constant-weight case of the criterion.  Under the finite-`2`-kernel
reading of `2`-automaticity this is the `2`-automaticity of the
Thue–Morse sequence.

Note what is and is not being said: it is the *weight word* `a ≡ 1`
that is periodic here, not the sign sequence.  The sign sequence is
not eventually periodic — that is the corpus's
`thueMorseSign_not_eventually_periodic` — so this corollary would fail
outright if the criterion had been stated about the character
`ε_a` rather than about the weight parity word `h ↦ a h % 2`. -/
theorem finite_twoKernel_thueMorseSign :
    (twoKernel thueMorseSign).Finite := by
  rw [← parityCharacter_const_one_eq_thueMorseSign]
  exact (finite_twoKernel_parityCharacter_iff (fun _ => 1)).mpr
    (eventuallyPeriodic_parityWord_const 1)

end Fabius
