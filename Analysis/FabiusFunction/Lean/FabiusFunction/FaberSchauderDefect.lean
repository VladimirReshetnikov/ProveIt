import FabiusFunction.Convexity
import FabiusFunction.DyadicSpecializations

/-!
# Faber–Schauder midpoint defects of the Fabius function

Fix a bounded Fabius function `F`, i.e. a solution of `IsFabius`.  At
level `m` and index `k` the dyadic cell is `[l, r]` with

`l = k / 2 ^ m`,  `r = (k + 1) / 2 ^ m`,

`ξ = (2 * k + 1) / 2 ^ (m + 1)`,

and the **Faber–Schauder midpoint defect** is

`c m k = F ξ - (F l + F r) / 2`,

the second difference of `F` across the cell, i.e. the coefficient of
the cell's hat function in the Faber–Schauder expansion of `F` up to
the usual normalization.

Two structural laws are proved here.

* **Reflection.**  `F (1 - x) = 1 - F x` is the point reflection of
  the graph through `(1/2, 1/2)`.  It carries the cell of index `k`
  onto the cell of index `2 ^ m - 1 - k`, exchanging the two
  endpoints, and a point reflection *reverses* the sign of a second
  difference.  Hence the defect is **anti**symmetric:

  `c m (2 ^ m - 1 - k) = - c m k`.

  It is not symmetric.  Two independent checks: the fixed index
  `m = 0`, `k = 0` of the reflection forces `c 0 0 = 0`, which is
  confirmed directly below; and the level-one values `c 1 0 = -13/72`
  and (by the law) `c 1 1 = 13/72` have opposite signs.

* **Sign.**  `F` is strictly convex on `[0, 1/2]`, hence lies strictly
  below each of its chords there, so a midpoint value is strictly
  smaller than the chord average.  A cell of level `m + 1` lies in
  `[0, 1/2]` exactly when `k < 2 ^ m`, and there the defect is
  strictly negative.  Reflection then turns this into strict
  positivity on the second half.

## Main declarations

* `faberLeft`, `faberRight`, `faberMid` — the two endpoints and the
  midpoint of the dyadic cell, with their defining equations.
* `faberSchauderDefect` — the midpoint defect `c m k`.
* `faberMid_eq_midpoint` — the midpoint really is the average of the
  two endpoints.
* `faberLeft_reflect`, `faberRight_reflect`, `faberMid_reflect` — the
  index reflection `k ↦ 2 ^ m - 1 - k` mirrors the cell about `1/2`
  and exchanges its two endpoints.
* `fabiusReal_midpoint_lt_chord` — strict midpoint convexity of `F`
  on `[0, 1/2]`.
* `faberSchauderDefect_reflect` — `c m (2 ^ m - 1 - k) = - c m k`.
* `faberSchauderDefect_neg_succ`, `faberSchauderDefect_neg` — the
  defect is strictly negative on the first half.
* `faberSchauderDefect_pos_succ` — and strictly positive on the
  second half.
* `faberSchauderDefect_zero_zero`, `faberSchauderDefect_one_zero`,
  `faberSchauderDefect_two_zero`, `faberSchauderDefect_two_one` —
  the exact values `0`, `-13/72`, `-1/32`, `-1/32`.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-! ## The dyadic cell and its midpoint defect -/

/-- Left endpoint `k / 2 ^ m` of the `k`-th dyadic cell of level `m`. -/
noncomputable def faberLeft (m k : ℕ) : ℝ := (k : ℝ) / 2 ^ m

/-- Right endpoint `(k + 1) / 2 ^ m` of the `k`-th dyadic cell. -/
noncomputable def faberRight (m k : ℕ) : ℝ :=
  ((k : ℝ) + 1) / 2 ^ m

/-- Midpoint `(2 * k + 1) / 2 ^ (m + 1)` of the `k`-th dyadic cell. -/
noncomputable def faberMid (m k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) / 2 ^ (m + 1)

/-- Defining equation of the left endpoint. -/
theorem faberLeft_def (m k : ℕ) :
    faberLeft m k = (k : ℝ) / 2 ^ m := rfl

/-- Defining equation of the right endpoint. -/
theorem faberRight_def (m k : ℕ) :
    faberRight m k = ((k : ℝ) + 1) / 2 ^ m := rfl

/-- Defining equation of the midpoint. -/
theorem faberMid_def (m k : ℕ) :
    faberMid m k = (2 * (k : ℝ) + 1) / 2 ^ (m + 1) := rfl

/--
The **Faber–Schauder midpoint defect** of a bounded Fabius function on
the `k`-th dyadic cell of level `m`: the midpoint value minus the
average of the two endpoint values.
-/
noncomputable def faberSchauderDefect
    (F : BoundedFabius) (m k : ℕ) : ℝ :=
  fabiusReal F (faberMid m k) -
    (fabiusReal F (faberLeft m k) + fabiusReal F (faberRight m k)) / 2

/-- Defining equation of the midpoint defect. -/
theorem faberSchauderDefect_def (F : BoundedFabius) (m k : ℕ) :
    faberSchauderDefect F m k =
      fabiusReal F (faberMid m k) -
        (fabiusReal F (faberLeft m k) +
          fabiusReal F (faberRight m k)) / 2 := rfl

/-- The midpoint of the cell is the average of its two endpoints.
This is pure arithmetic; no property of `F` is involved. -/
theorem faberMid_eq_midpoint (m k : ℕ) :
    faberMid m k = (faberLeft m k + faberRight m k) / 2 := by
  rw [faberMid_def, faberLeft_def, faberRight_def, ← add_div, div_div,
    pow_succ,
    show 2 * (k : ℝ) + 1 = (k : ℝ) + ((k : ℝ) + 1) by ring]

/-! ## Reflection of the index -/

/-- The real value of the reflected index `2 ^ m - 1 - k`, computed in
`ℕ` and then cast, is the reflected real number.  The hypothesis
`k < 2 ^ m` is what makes the truncated subtraction faithful. -/
private theorem cast_reflectIndex {m k : ℕ} (hk : k < 2 ^ m) :
    ((2 ^ m - 1 - k : ℕ) : ℝ) = 2 ^ m - 1 - (k : ℝ) := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 2 ^ m = k + 1 + j :=
    ⟨2 ^ m - (k + 1), by omega⟩
  have hidx : 2 ^ m - 1 - k = j := by omega
  have hj' : ((2 ^ m : ℕ) : ℝ) = ((k + 1 + j : ℕ) : ℝ) := by
    exact_mod_cast hj
  push_cast at hj'
  rw [hidx]
  linarith

/-- Reflecting the index sends the left endpoint of the cell to the
reflection of the right endpoint. -/
theorem faberLeft_reflect {m k : ℕ} (hk : k < 2 ^ m) :
    faberLeft m (2 ^ m - 1 - k) = 1 - faberRight m k := by
  have hne : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  rw [faberLeft_def, faberRight_def, cast_reflectIndex hk,
    eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hne]
  ring

/-- Reflecting the index sends the right endpoint of the cell to the
reflection of the left endpoint. -/
theorem faberRight_reflect {m k : ℕ} (hk : k < 2 ^ m) :
    faberRight m (2 ^ m - 1 - k) = 1 - faberLeft m k := by
  have hne : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  rw [faberRight_def, faberLeft_def, cast_reflectIndex hk,
    eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hne]
  ring

/-- Reflecting the index reflects the midpoint of the cell. -/
theorem faberMid_reflect {m k : ℕ} (hk : k < 2 ^ m) :
    faberMid m (2 ^ m - 1 - k) = 1 - faberMid m k := by
  have hne : ((2 : ℝ) ^ (m + 1)) ≠ 0 := by positivity
  rw [faberMid_def, faberMid_def, cast_reflectIndex hk,
    eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hne]
  ring

/-! ## The reflection law for the defect -/

/--
**Reflection law.**  For `k < 2 ^ m` the midpoint defects at the two
mirror cells of level `m` are negatives of each other:

`c m (2 ^ m - 1 - k) = - c m k`.

The sign reversal is genuine.  `F (1 - x) = 1 - F x` is a point
reflection of the graph, and a point reflection turns a convex arc
into a concave one, hence reverses the sign of every second
difference.  Taking `m = 0`, `k = 0` (a fixed index of the
reflection) forces `c 0 0 = 0`, which `faberSchauderDefect_zero_zero`
confirms independently.
-/
theorem faberSchauderDefect_reflect
    (F : BoundedFabius) (hF : IsFabius F) {m k : ℕ} (hk : k < 2 ^ m) :
    faberSchauderDefect F m (2 ^ m - 1 - k) =
      -faberSchauderDefect F m k := by
  have hmid : fabiusReal F (faberMid m (2 ^ m - 1 - k)) =
      1 - fabiusReal F (faberMid m k) := by
    rw [faberMid_reflect hk, hF.symmetry_all]
  have hleft : fabiusReal F (faberLeft m (2 ^ m - 1 - k)) =
      1 - fabiusReal F (faberRight m k) := by
    rw [faberLeft_reflect hk, hF.symmetry_all]
  have hright : fabiusReal F (faberRight m (2 ^ m - 1 - k)) =
      1 - fabiusReal F (faberLeft m k) := by
    rw [faberRight_reflect hk, hF.symmetry_all]
  rw [faberSchauderDefect_def, faberSchauderDefect_def, hmid, hleft,
    hright]
  ring

/-! ## Strict midpoint convexity on the first half -/

/--
**Strict midpoint convexity.**  On `[0, 1/2]` the bounded Fabius
function is strictly convex, so at the midpoint of any nondegenerate
subinterval it stays strictly below the chord.
-/
theorem fabiusReal_midpoint_lt_chord
    (F : BoundedFabius) (hF : IsFabius F) {l r : ℝ}
    (hl : l ∈ Icc (0 : ℝ) (1 / 2))
    (hr : r ∈ Icc (0 : ℝ) (1 / 2)) (hlr : l < r) :
    fabiusReal F ((l + r) / 2) <
      (fabiusReal F l + fabiusReal F r) / 2 := by
  have hstrict := strictConvexOn_fabiusReal_firstHalf F hF
  unfold StrictConvexOn at hstrict
  rcases hstrict with ⟨_, hstrict⟩
  have h := hstrict
    (x := l) (y := r) (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    hl hr (ne_of_lt hlr)
    (by norm_num) (by norm_num) (by norm_num)
  have harg :
      (1 / 2 : ℝ) • l + (1 / 2 : ℝ) • r = (l + r) / 2 := by
    simp only [smul_eq_mul]
    ring
  have hval :
      (1 / 2 : ℝ) • fabiusReal F l +
          (1 / 2 : ℝ) • fabiusReal F r =
        (fabiusReal F l + fabiusReal F r) / 2 := by
    simp only [smul_eq_mul]
    ring
  rw [harg, hval] at h
  exact h

/-! ## The sign law -/

/--
**Sign law, first half.**  A cell of level `m + 1` with index
`k < 2 ^ m` lies inside `[0, 1/2]`, where the Fabius function is
strictly convex.  Its midpoint defect is therefore strictly negative.
-/
theorem faberSchauderDefect_neg_succ
    (F : BoundedFabius) (hF : IsFabius F) {m k : ℕ} (hk : k < 2 ^ m) :
    faberSchauderDefect F (m + 1) k < 0 := by
  have hkN : k + 1 ≤ 2 ^ m := by omega
  have hkR : (k : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast hkN
  have hpos : (0 : ℝ) < 2 ^ (m + 1) := by positivity
  have hpow : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have hl0 : (0 : ℝ) ≤ faberLeft (m + 1) k := by
    rw [faberLeft_def]
    positivity
  have hl1 : faberLeft (m + 1) k ≤ 1 / 2 := by
    rw [faberLeft_def, div_le_iff₀ hpos]
    linarith
  have hr0 : (0 : ℝ) ≤ faberRight (m + 1) k := by
    rw [faberRight_def]
    positivity
  have hr1 : faberRight (m + 1) k ≤ 1 / 2 := by
    rw [faberRight_def, div_le_iff₀ hpos]
    linarith
  have hstep : ((k : ℝ) + 1) / 2 ^ (m + 1) =
      (k : ℝ) / 2 ^ (m + 1) + 1 / 2 ^ (m + 1) := by
    rw [add_div]
  have hgap : (0 : ℝ) < 1 / 2 ^ (m + 1) := by positivity
  have hlt : faberLeft (m + 1) k < faberRight (m + 1) k := by
    rw [faberLeft_def, faberRight_def, hstep]
    linarith
  have hl : faberLeft (m + 1) k ∈ Icc (0 : ℝ) (1 / 2) :=
    ⟨hl0, hl1⟩
  have hr : faberRight (m + 1) k ∈ Icc (0 : ℝ) (1 / 2) :=
    ⟨hr0, hr1⟩
  have hconv := fabiusReal_midpoint_lt_chord F hF hl hr hlt
  rw [faberSchauderDefect_def, faberMid_eq_midpoint (m + 1) k]
  linarith

/--
**Sign law.**  For `m ≥ 1` and `k < 2 ^ (m - 1)` the whole cell lies
in `[0, 1/2]` and the midpoint defect is strictly negative.  This is
`faberSchauderDefect_neg_succ` with the level written as `m` rather
than `m + 1`.
-/
theorem faberSchauderDefect_neg
    (F : BoundedFabius) (hF : IsFabius F) {m k : ℕ} (hm : 1 ≤ m)
    (hk : k < 2 ^ (m - 1)) :
    faberSchauderDefect F m k < 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  have hk' : k < 2 ^ n := by simpa using hk
  exact faberSchauderDefect_neg_succ F hF hk'

/--
**Sign law, second half.**  A cell of level `m + 1` with index
`2 ^ m ≤ k < 2 ^ (m + 1)` lies inside `[1/2, 1]`, where the Fabius
function is strictly concave.  Its midpoint defect is therefore
strictly positive.  This is the reflection of
`faberSchauderDefect_neg_succ`.
-/
theorem faberSchauderDefect_pos_succ
    (F : BoundedFabius) (hF : IsFabius F) {m k : ℕ}
    (hk1 : 2 ^ m ≤ k) (hk2 : k < 2 ^ (m + 1)) :
    0 < faberSchauderDefect F (m + 1) k := by
  have hp : 0 < 2 ^ m := by positivity
  have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
  have hk' : 2 ^ (m + 1) - 1 - k < 2 ^ m := by omega
  have href := faberSchauderDefect_reflect F hF hk2
  have hneg := faberSchauderDefect_neg_succ F hF hk'
  linarith

/-! ## Exact low-level values -/

/-- The level-zero defect vanishes: the single cell is `[0, 1]`, and
`F (1/2) = 1/2` is exactly the average of `F 0 = 0` and `F 1 = 1`.
This is forced by `faberSchauderDefect_reflect`, whose index map fixes
`m = 0`, `k = 0`. -/
theorem faberSchauderDefect_zero_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    faberSchauderDefect F 0 0 = 0 := by
  have hmid : faberMid 0 0 = (1 / 2 : ℝ) := by
    rw [faberMid_def]; norm_num
  have hleft : faberLeft 0 0 = (0 : ℝ) := by
    rw [faberLeft_def]; norm_num
  have hright : faberRight 0 0 = (1 : ℝ) := by
    rw [faberRight_def]; norm_num
  rw [faberSchauderDefect_def, hmid, hleft, hright, fabius_half F hF,
    hF.zero_of_nonpos 0 le_rfl, hF.one_of_one_le 1 le_rfl]
  norm_num

/-- `c 1 0 = F (1/4) - (F 0 + F (1/2)) / 2 = 5/72 - 1/4 = -13/72`. -/
theorem faberSchauderDefect_one_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    faberSchauderDefect F 1 0 = -13 / 72 := by
  have hmid : faberMid 1 0 = (1 / 4 : ℝ) := by
    rw [faberMid_def]; norm_num
  have hleft : faberLeft 1 0 = (0 : ℝ) := by
    rw [faberLeft_def]; norm_num
  have hright : faberRight 1 0 = (1 / 2 : ℝ) := by
    rw [faberRight_def]; norm_num
  rw [faberSchauderDefect_def, hmid, hleft, hright,
    fabiusReal_one_quarter F hF, fabius_half F hF,
    hF.zero_of_nonpos 0 le_rfl]
  norm_num

/-- `c 2 0 = F (1/8) - (F 0 + F (1/4)) / 2 = 1/288 - 5/144 = -1/32`. -/
theorem faberSchauderDefect_two_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    faberSchauderDefect F 2 0 = -1 / 32 := by
  have hmid : faberMid 2 0 = (1 / 8 : ℝ) := by
    rw [faberMid_def]; norm_num
  have hleft : faberLeft 2 0 = (0 : ℝ) := by
    rw [faberLeft_def]; norm_num
  have hright : faberRight 2 0 = (1 / 4 : ℝ) := by
    rw [faberRight_def]; norm_num
  rw [faberSchauderDefect_def, hmid, hleft, hright,
    fabiusReal_one_eighth F hF, fabiusReal_one_quarter F hF,
    hF.zero_of_nonpos 0 le_rfl]
  norm_num

/-- `c 2 1 = F (3/8) - (F (1/4) + F (1/2)) / 2 = -1/32`, the same
value as `c 2 0`. -/
theorem faberSchauderDefect_two_one
    (F : BoundedFabius) (hF : IsFabius F) :
    faberSchauderDefect F 2 1 = -1 / 32 := by
  have hmid : faberMid 2 1 = (3 / 8 : ℝ) := by
    rw [faberMid_def]; norm_num
  have hleft : faberLeft 2 1 = (1 / 4 : ℝ) := by
    rw [faberLeft_def]; norm_num
  have hright : faberRight 2 1 = (1 / 2 : ℝ) := by
    rw [faberRight_def]; norm_num
  rw [faberSchauderDefect_def, hmid, hleft, hright,
    fabiusReal_three_eighths F hF, fabiusReal_one_quarter F hF,
    fabius_half F hF]
  norm_num

end Fabius
