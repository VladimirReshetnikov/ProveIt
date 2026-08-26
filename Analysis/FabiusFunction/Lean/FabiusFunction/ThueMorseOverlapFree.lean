import FabiusFunction.ThueMorseEnumerators

/-!
# Overlap-freeness of the Thue–Morse sequence

Thue's theorem: the Thue–Morse sequence contains no *overlap* — no factor
of the form `x·x·a` with `a` the first letter of `x`.  Equivalently, no
period `p ≥ 1` persists for `p + 1` consecutive steps:
there are no `i` and `p ≥ 1` with `t(i+j) = t(i+p+j)` for all `j ≤ p`.
Consequently the critical exponent of Thue–Morse is exactly `2`: squares
occur (`t(1)=t(2)`), but no fractional power beyond them.

The proof is the classical two-scale descent, organized around two facts:

* `thueMorseBit_pair_ne` — letters paired across an **even boundary**
  always differ: `t(2k) ≠ t(2k+1)`.
* `thueMorseBit_no_triple` — hence no three consecutive letters agree.

For an overlap of **even** period `2q`, reading only the even-indexed
(respectively odd-indexed, if the overlap starts at an odd position)
letters of the window exhibits an overlap of period `q` — strong descent.
For an **odd** period `p = 2q+1`, each even boundary inside the left half
maps under the overlap to an odd boundary in the right half, forcing
`t(l) = t(l+1)` along a run of consecutive `l`; for `p ≥ 5` the run has
length three, contradicting `thueMorseBit_no_triple`, and the residual
periods `p = 1, 3` die by Boolean analysis over the window.

* `thueMorseBit_not_overlap` / `thueMorseBit_overlap_free` — the theorem
  for the zero–one sequence, in universally quantified and negated
  existential forms.
* `thueMorseSign_overlap_free` — the signed version.
* `thueMorseBit_cube_free` — no nonempty cube `x·x·x` occurs.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- Letters paired across an even boundary always differ:
`t(2k) ≠ t(2k+1)`. -/
theorem thueMorseBit_pair_ne (k : ℕ) :
    thueMorseBit (2 * k) ≠ thueMorseBit (2 * k + 1) := by
  have h1 := thueMorseBit_two_mul k
  have h2 := thueMorseBit_two_mul_add_one k
  have h3 := thueMorseBit_le_one k
  omega

/-- No three consecutive Thue–Morse letters agree. -/
theorem thueMorseBit_no_triple (n : ℕ) :
    ¬ (thueMorseBit n = thueMorseBit (n + 1) ∧
        thueMorseBit (n + 1) = thueMorseBit (n + 2)) := by
  rintro ⟨h1, h2⟩
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · subst hk
    exact thueMorseBit_pair_ne k h1
  · subst hk
    have h := thueMorseBit_pair_ne (k + 1)
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring] at h
    rw [show 2 * k + 1 + 1 + 1 = 2 * k + 1 + 2 by omega] at h
    exact h h2

/-- **Thue's theorem** (universal form): no period `p ≥ 1` persists for
`p+1` consecutive steps of the Thue–Morse sequence. -/
theorem thueMorseBit_not_overlap :
    ∀ p, 0 < p → ∀ i,
      ¬ ∀ j ≤ p, thueMorseBit (i + j) = thueMorseBit (i + p + j) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp i hover
    rcases Nat.even_or_odd' p with ⟨q, hq | hq⟩
    · -- even period 2q: descend to period q
      subst hq
      have hq0 : 0 < q := by omega
      rcases Nat.even_or_odd' i with ⟨k, hk | hk⟩
      · -- i = 2k: read the even-indexed letters
        subst hk
        refine ih q (by omega) hq0 k ?_
        intro j hj
        have h := hover (2 * j) (by omega)
        rw [show 2 * k + 2 * j = 2 * (k + j) by ring,
          show 2 * k + 2 * q + 2 * j = 2 * (k + q + j) by ring,
          thueMorseBit_two_mul, thueMorseBit_two_mul] at h
        exact h
      · -- i = 2k+1: read the odd-indexed letters
        subst hk
        refine ih q (by omega) hq0 k ?_
        intro j hj
        have h := hover (2 * j) (by omega)
        rw [show 2 * k + 1 + 2 * j = 2 * (k + j) + 1 by ring,
          show 2 * k + 1 + 2 * q + 2 * j = 2 * (k + q + j) + 1 by ring,
          thueMorseBit_two_mul_add_one, thueMorseBit_two_mul_add_one] at h
        have b1 := thueMorseBit_le_one (k + j)
        have b2 := thueMorseBit_le_one (k + q + j)
        omega
    · -- odd period 2q+1
      subst hq
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · interval_cases q
        · -- p = 1: three consecutive equal letters
          have h0 : thueMorseBit i = thueMorseBit (i + 1) := by
            have h := hover 0 (by omega)
            rwa [Nat.add_zero, Nat.add_zero,
              show i + (2 * 0 + 1) = i + 1 by omega] at h
          have h1 : thueMorseBit (i + 1) = thueMorseBit (i + 2) := by
            have h := hover 1 (by omega)
            rwa [show i + (2 * 0 + 1) + 1 = i + 2 by omega] at h
          exact thueMorseBit_no_triple i ⟨h0, h1⟩
        · -- p = 3: Boolean analysis over the seven-letter window
          rcases Nat.even_or_odd' i with ⟨k, hk | hk⟩ <;> subst hk
          · have e0 : thueMorseBit (2 * k) = thueMorseBit (2 * k + 3) := by
              have h := hover 0 (by omega)
              rwa [Nat.add_zero, Nat.add_zero,
                show 2 * k + (2 * 1 + 1) = 2 * k + 3 by omega] at h
            have e1 : thueMorseBit (2 * k + 1) = thueMorseBit (2 * k + 4) := by
              have h := hover 1 (by omega)
              rwa [show 2 * k + (2 * 1 + 1) + 1 = 2 * k + 4 by omega] at h
            have e2 : thueMorseBit (2 * k + 2) = thueMorseBit (2 * k + 5) := by
              have h := hover 2 (by omega)
              rwa [show 2 * k + (2 * 1 + 1) + 2 = 2 * k + 5 by omega] at h
            have d0 : thueMorseBit (2 * k) ≠ thueMorseBit (2 * k + 1) :=
              thueMorseBit_pair_ne k
            have d1 : thueMorseBit (2 * k + 2) ≠ thueMorseBit (2 * k + 3) := by
              have h := thueMorseBit_pair_ne (k + 1)
              rwa [show 2 * (k + 1) = 2 * k + 2 by ring,
                show 2 * k + 2 + 1 = 2 * k + 3 by omega] at h
            have d2 : thueMorseBit (2 * k + 4) ≠ thueMorseBit (2 * k + 5) := by
              have h := thueMorseBit_pair_ne (k + 2)
              rwa [show 2 * (k + 2) = 2 * k + 4 by ring,
                show 2 * k + 4 + 1 = 2 * k + 5 by omega] at h
            have hb0 := thueMorseBit_le_one (2 * k)
            have hb1 := thueMorseBit_le_one (2 * k + 1)
            have hb2 := thueMorseBit_le_one (2 * k + 2)
            have hb3 := thueMorseBit_le_one (2 * k + 3)
            have hb4 := thueMorseBit_le_one (2 * k + 4)
            have hb5 := thueMorseBit_le_one (2 * k + 5)
            omega
          · have e0 : thueMorseBit (2 * k + 1) = thueMorseBit (2 * k + 4) := by
              have h := hover 0 (by omega)
              rwa [Nat.add_zero, Nat.add_zero,
                show 2 * k + 1 + (2 * 1 + 1) = 2 * k + 4 by omega] at h
            have e1 : thueMorseBit (2 * k + 2) = thueMorseBit (2 * k + 5) := by
              have h := hover 1 (by omega)
              rwa [show 2 * k + 1 + 1 = 2 * k + 2 by omega,
                show 2 * k + 1 + (2 * 1 + 1) + 1 = 2 * k + 5 by omega] at h
            have e2 : thueMorseBit (2 * k + 3) = thueMorseBit (2 * k + 6) := by
              have h := hover 2 (by omega)
              rwa [show 2 * k + 1 + 2 = 2 * k + 3 by omega,
                show 2 * k + 1 + (2 * 1 + 1) + 2 = 2 * k + 6 by omega] at h
            have e3 : thueMorseBit (2 * k + 4) = thueMorseBit (2 * k + 7) := by
              have h := hover 3 (by omega)
              rwa [show 2 * k + 1 + 3 = 2 * k + 4 by omega,
                show 2 * k + 1 + (2 * 1 + 1) + 3 = 2 * k + 7 by omega] at h
            have d1 : thueMorseBit (2 * k + 2) ≠ thueMorseBit (2 * k + 3) := by
              have h := thueMorseBit_pair_ne (k + 1)
              rwa [show 2 * (k + 1) = 2 * k + 2 by ring,
                show 2 * k + 2 + 1 = 2 * k + 3 by omega] at h
            have d2 : thueMorseBit (2 * k + 4) ≠ thueMorseBit (2 * k + 5) := by
              have h := thueMorseBit_pair_ne (k + 2)
              rwa [show 2 * (k + 2) = 2 * k + 4 by ring,
                show 2 * k + 4 + 1 = 2 * k + 5 by omega] at h
            have d3 : thueMorseBit (2 * k + 6) ≠ thueMorseBit (2 * k + 7) := by
              have h := thueMorseBit_pair_ne (k + 3)
              rwa [show 2 * (k + 3) = 2 * k + 6 by ring,
                show 2 * k + 6 + 1 = 2 * k + 7 by omega] at h
            have hb1 := thueMorseBit_le_one (2 * k + 1)
            have hb2 := thueMorseBit_le_one (2 * k + 2)
            have hb3 := thueMorseBit_le_one (2 * k + 3)
            have hb4 := thueMorseBit_le_one (2 * k + 4)
            have hb5 := thueMorseBit_le_one (2 * k + 5)
            have hb6 := thueMorseBit_le_one (2 * k + 6)
            have hb7 := thueMorseBit_le_one (2 * k + 7)
            omega
      · -- p = 2q+1 ≥ 5: the run argument
        have hrun : ∀ k, i ≤ 2 * k → 2 * k + 1 ≤ i + (2 * q + 1) →
            thueMorseBit (k + q) = thueMorseBit (k + q + 1) := by
          intro k hik hki
          have hd := thueMorseBit_pair_ne k
          have h1 := hover (2 * k - i) (by omega)
          have h2 := hover (2 * k + 1 - i) (by omega)
          rw [show i + (2 * k - i) = 2 * k by omega,
            show i + (2 * q + 1) + (2 * k - i) = 2 * (k + q) + 1 by omega,
            thueMorseBit_two_mul_add_one] at h1
          rw [show i + (2 * k + 1 - i) = 2 * k + 1 by omega,
            show i + (2 * q + 1) + (2 * k + 1 - i) = 2 * (k + q + 1) by omega,
            thueMorseBit_two_mul] at h2
          have hbq := thueMorseBit_le_one (k + q)
          have hbq1 := thueMorseBit_le_one (k + q + 1)
          omega
        have h1 := hrun ((i + 1) / 2) (by omega) (by omega)
        have h2 := hrun ((i + 1) / 2 + 1) (by omega) (by omega)
        refine thueMorseBit_no_triple ((i + 1) / 2 + q) ⟨h1, ?_⟩
        rw [show (i + 1) / 2 + q + 1 = (i + 1) / 2 + 1 + q by omega,
          show (i + 1) / 2 + q + 2 = (i + 1) / 2 + 1 + q + 1 by omega]
        exact h2

/-- **Thue's theorem** (existential form): the Thue–Morse sequence is
overlap-free. -/
theorem thueMorseBit_overlap_free :
    ¬ ∃ i p, 0 < p ∧
      ∀ j ≤ p, thueMorseBit (i + j) = thueMorseBit (i + p + j) := by
  rintro ⟨i, p, hp, hover⟩
  exact thueMorseBit_not_overlap p hp i hover

/-- The signed Thue–Morse sequence is overlap-free. -/
theorem thueMorseSign_overlap_free :
    ¬ ∃ i p, 0 < p ∧
      ∀ j ≤ p, thueMorseSign (i + j) = thueMorseSign (i + p + j) := by
  rintro ⟨i, p, hp, hover⟩
  refine thueMorseBit_not_overlap p hp i fun j hj => ?_
  have h := hover j hj
  have h1 := thueMorseSign_eq_one_sub_two_mul_bit (i + j)
  have h2 := thueMorseSign_eq_one_sub_two_mul_bit (i + p + j)
  have b1 := thueMorseBit_le_one (i + j)
  have b2 := thueMorseBit_le_one (i + p + j)
  omega

/-- The Thue–Morse sequence is cube-free: no nonempty block repeats three
times in a row. -/
theorem thueMorseBit_cube_free :
    ¬ ∃ i p, 0 < p ∧
      ∀ j < 2 * p, thueMorseBit (i + j) = thueMorseBit (i + p + j) := by
  rintro ⟨i, p, hp, hcube⟩
  exact thueMorseBit_not_overlap p hp i fun j hj => hcube j (by omega)

end Fabius
