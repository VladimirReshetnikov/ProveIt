import Lib.Weil.Periods.PointLattice

/-!
# The string of a graded space as the powers `𝔢 ^ i`

The orthogonal complement of `X` in a graded space with a string of `s` vectors behaves like
`E[𝔢] / (𝔢 ^ s)`: the vector called `𝔢 ^ i` is `New.Grading.stringPower`, a multiple of the string
vector with number `i`. That vector has grade `s - 1 - 2 * i`.

* `New.Grading.shift_mulVec_stringPower`: `New.Grading.shift` is the multiplication by `𝔢`.
* `New.Grading.form_stringPower`: `𝔢 ^ i` and `𝔢 ^ l` pair to `-N` if `i + l = s - 1`, else to `0`.
* `New.Grading.middlePower`, `New.Grading.form_middlePower`: for odd `s` the power of `𝔢` of
  grade `0` is the vector `z_N`, of norm `-N`.
* `New.Grading.stringMap_mulVec_stringPower`: the map `New.Grading.stringMap` between neighbouring
  spaces is the projection `E[𝔢] / (𝔢 ^ s) → E[𝔢] / (𝔢 ^ (s - 1))`.
* `New.Grading.exists_stringSum_eq`, `New.Grading.stringMapFin_stringSum`: over the finite adeles
  the `𝔢 ^ i` span the complement of `X` (the vectors fixed by the projection
  `New.Grading.stringProj` to the span of the string vectors), and `New.Grading.stringMapFin`
  keeps the coordinates in `𝔢 ^ i` for `i < s - 1`.

Notions from other files:
* `New.Space E ι ε`: a hermitian matrix `V.J` over `E`, indexed by `ι`, with an adelic point;
* `New.Grading V N X s`: an identification `X ⊕ Fin s ≃ ι` under which string vector `i` pairs only
  with string vector `s - 1 - i`, to `1` (to `-N` in the middle), a constant `c = star c ≠ 0`, and
  the fact `N = star N ≠ 0`;
* `New.Grading.shift`: the matrix, with entries in `E` seen as adeles by the diagonal embedding
  `toAdele`, that kills `X` and the last string vector and raises the number of any other string
  vector by one, up to a factor;
* `New.Grading.stringMap`, `New.Grading.stringMapFin`: the map that kills `X` and the string vector
  `s - 1` and keeps the number of any other string vector, up to a factor, and its part at the
  finite adeles;
-/

open Matrix

noncomputable section

namespace New.Grading

variable {E X X' ι ι' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [DecidableEq X] [DecidableEq X']
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}
  (Y : Grading V N X s)

/-- The coefficient of `𝔢 ^ i` at the string vector `i`: a power of the constant `c` of the grading,
times `-N` if that vector has negative grade, that is if `s ≤ 2 * i`. -/
def powerCoeff (i : ℕ) : E :=
  if 2 * i < s then Y.genericConst.val ^ (i - s / 2 : ℤ) else -N * Y.genericConst.val ^
    (i - (s - 1) / 2 : ℤ)

/-- The vector `𝔢 ^ i` of the complement `E[𝔢] / (𝔢 ^ s)` of `X`: the multiple `Y.powerCoeff i` of
the string vector `i`, and `0` for `s ≤ i`. -/
def stringPower (i : ℕ) (k : ι) : E :=
  (Y.indexEquiv.symm k).elim 0 fun b : Fin s ↦ if b.val = i then Y.powerCoeff i else 0

/-- For a grading `Y` whose string has length `s`, the vector `𝔢 ^ i` is `Y.powerCoeff i` times the
`i`-th string vector. If that vector has nonnegative grade `s − 1 − 2i` (`2 * i < s`), this
coefficient is `c ^ n` for `n = i - s / 2`, where `c` is the constant `Y.genericConst`. -/
lemma powerCoeff_of_lt {i : ℕ} {n : ℤ} (hi : 2 * i < s) (hn : n = i - s / 2) :
    Y.powerCoeff i = Y.genericConst.val ^ n := by
  rw [powerCoeff, ite_eq_left hi, hn]

/-- In negative grade (`s ≤ 2 * i`) the coefficient of `𝔢 ^ i` is `-N * c ^ n` for
`n = i - (s - 1) / 2`. -/
lemma powerCoeff_of_le {i : ℕ} {n : ℤ} (hi : s ≤ 2 * i) (hn : n = i - (s - 1) / 2) :
    Y.powerCoeff i = -N * Y.genericConst.val ^ n := by
  rw [powerCoeff, ite_eq_right hi.not_gt, hn]

/-- The coefficient `Y.powerCoeff i` of `𝔢 ^ i` is nonzero, as `c` and `N` are. -/
lemma powerCoeff_ne_zero (i : ℕ) : Y.powerCoeff i ≠ 0 := by
  simp [powerCoeff, ite_eq_iff, zpow_ne_zero _ Y.genericConst.property.left,
    Y.N_ne_zero_and_star_eq.left]

/-- For `i < s` the vector `𝔢 ^ i` is supported at the string index `i`. -/
lemma stringPower_eq_single (i : Fin s) :
    Y.stringPower i = Pi.single (Y.indexEquiv (.inr i)) (Y.powerCoeff i) := by
  funext k
  obtain ⟨a | b, rfl⟩ := Y.indexEquiv.surjective k <;>
    simp [stringPower, Pi.single_apply, Fin.ext_iff]

lemma stringPower_eq_zero {i : ℕ} (hi : s ≤ i) : Y.stringPower i = 0 := by
  funext k
  obtain ⟨a | b, rfl⟩ := Y.indexEquiv.surjective k
  · simp [stringPower]
  · simp [stringPower, show b.val ≠ i by omega]

/-- The factor by which `Y.shift` takes the string vector `i` to the next one (the `if` below,
times `c`), times the coefficient `Y.powerCoeff i` of `𝔢 ^ i`, is the coefficient of
`𝔢 ^ (i + 1)`. -/
lemma shift_factor_mul_powerCoeff (i : ℕ) :
    Y.genericConst * (if 2 * i + 1 = s then -N else if 2 * (i + 1) = s then -N * Y.genericConst else
      1) *
      Y.powerCoeff i = Y.powerCoeff (i + 1) := by
  have hc : Y.genericConst.val ≠ 0 := Y.genericConst.property.left
  have h_nonneg (hi : 2 * i < s) : Y.powerCoeff i = Y.genericConst.val ^ (i - s / 2 : ℤ) :=
    Y.powerCoeff_of_lt hi rfl
  -- The grade `s - 1 - 2 * i` of `𝔢 ^ i` is `0`, `1`, at least `2`, or negative.
  obtain h | h | h | h :
      2 * i + 1 = s ∨ 2 * (i + 1) = s ∨ 2 * (i + 1) < s ∨ s ≤ 2 * i := by omega
  · have h_next : Y.powerCoeff (i + 1) = -N * Y.genericConst.val ^ (i - s / 2 + 1 : ℤ) :=
      Y.powerCoeff_of_le (by omega) (by omega)
    grind [zpow_add_one₀]
  · have h_next : Y.powerCoeff (i + 1) = -N * Y.genericConst.val ^ (i - s / 2 + 2 : ℤ) :=
      Y.powerCoeff_of_le (by omega) (by omega)
    rw [ite_eq_right (by omega), ite_eq_left h, h_nonneg (by omega), h_next, zpow_add₀ hc, zpow_two]
    ring
  · have h_next : Y.powerCoeff (i + 1) = Y.genericConst.val ^ (i - s / 2 + 1 : ℤ) :=
      Y.powerCoeff_of_lt h (by omega)
    grind [zpow_add_one₀]
  · have h_cur : Y.powerCoeff i = -N * Y.genericConst.val ^ (i - (s - 1) / 2 : ℤ) :=
      Y.powerCoeff_of_le h rfl
    have h_next : Y.powerCoeff (i + 1) = -N * Y.genericConst.val ^ (i - (s - 1) / 2 + 1 : ℤ) :=
      Y.powerCoeff_of_le (by omega) (by omega)
    grind [zpow_add_one₀]

/-- For a grading `Y` of `V` as `X` plus a string of length `s`, write `𝔢 ^ i` for
`Y.stringPower i`: the vector of the complement `E[𝔢] / (𝔢 ^ s)` of `X` that is a fixed multiple of
the `i`-th string vector, and `0` for `s ≤ i`. The matrix `Y.shift`, which kills `X` and acts on
this complement as multiplication by `𝔢`, sends `𝔢 ^ i` (seen over the adeles by the diagonal
embedding `toAdele`) to `𝔢 ^ (i + 1)`, for every `i < s`. For `i + 1 = s` the image is `0`. -/
lemma shift_mulVec_stringPower (i : Fin s) :
    Y.shift *ᵥ toAdele ∘ Y.stringPower i = toAdele ∘ Y.stringPower (i + 1) := by
  funext k
  rw [shift, ← RingHom.map_mulVec, stringPower_eq_single, mulVec_single]
  obtain ⟨a | b, rfl⟩ := Y.indexEquiv.surjective k
  · simp [stringPower]
  · -- At the string index `b` both sides are `Y.powerCoeff (i + 1)` if `b = i + 1`, else `0`.
    by_cases hb : b.val = i + 1 <;> simp [stringPower, hb, ← Y.shift_factor_mul_powerCoeff i]

/-- The vectors `𝔢 ^ i` and `𝔢 ^ l`, that is `Y.stringPower i` and `Y.stringPower l`, pair under
the hermitian form `V.J` to `-N` if `i + l = s - 1`, and to `0` otherwise. -/
lemma form_stringPower (i l : Fin s) :
    star (Y.stringPower i) ⬝ᵥ V.J *ᵥ Y.stringPower l = if i.val + l + 1 = s then -N else 0 := by
  obtain ⟨hc, hc_star⟩ : Y.genericConst.val ≠ 0 ∧ star Y.genericConst.val = Y.genericConst.val :=
    Y.genericConst.property
  -- Only the entry of `V.J` at the string indices `i` and `l` enters.
  have h_entry : star (Y.stringPower i) ⬝ᵥ V.J *ᵥ Y.stringPower l = star (Y.powerCoeff i) *
      (if i = l.rev then if i = l then -N else 1 else 0) * Y.powerCoeff l := by
    simp [stringPower_eq_single, Y.gram_eq, gradedGram, Pi.star_single, mul_comm]
  rw [h_entry]
  by_cases h_sum : i.val + l + 1 = s
  · rw [ite_eq_left h_sum, ite_eq_left (show i = l.rev by grind)]
    -- The exponents of `c` are opposite, and exactly one factor `-N` occurs.
    obtain h | h | h := lt_trichotomy i l
    · have h_i : Y.powerCoeff i = Y.genericConst.val ^ (i - s / 2 : ℤ) :=
        Y.powerCoeff_of_lt (by omega) rfl
      have h_l : Y.powerCoeff l = -N * Y.genericConst.val ^ (-(i - s / 2) : ℤ) :=
        Y.powerCoeff_of_le (by omega) (by omega)
      rw [ite_eq_right h.ne, h_i, h_l, star_zpow₀, hc_star, _root_.zpow_neg]
      field_simp
    · have h_i : Y.powerCoeff i = Y.genericConst.val ^ (0 : ℤ) :=
        Y.powerCoeff_of_lt (by omega) (by omega)
      simp [← h, h_i]
    · have h_i : Y.powerCoeff i = -N * Y.genericConst.val ^ (i - (s - 1) / 2 : ℤ) :=
        Y.powerCoeff_of_le (by omega) rfl
      have h_l : Y.powerCoeff l = Y.genericConst.val ^ (-(i - (s - 1) / 2) : ℤ) :=
        Y.powerCoeff_of_lt (by omega) (by omega)
      rw [ite_eq_right h.ne', h_i, h_l, star_mul, star_neg, Y.N_ne_zero_and_star_eq.right,
        star_zpow₀, hc_star, _root_.zpow_neg]
      field_simp
  · simp [h_sum, show i ≠ l.rev by grind]

/-- The vector `z_N`: for a string of odd length `s = 2 * n + 1` it is the power `𝔢 ^ n`, the one
of grade `0`. -/
def middlePower : ι → E := Y.stringPower (s / 2)

/-- For a string of odd length `s = 2 * n + 1`, the vector `z_N` is the string vector with number
`n`. -/
lemma middlePower_eq_single (n : Fin s) (hn : 2 * n.val + 1 = s) :
    Y.middlePower = Pi.single (Y.indexEquiv (.inr n)) 1 := by
  have h_coeff : Y.powerCoeff n = Y.genericConst.val ^ (0 : ℤ) :=
    Y.powerCoeff_of_lt (by omega) (by omega)
  rw [middlePower, show s / 2 = n by omega, stringPower_eq_single, h_coeff, zpow_zero]

/-- For a grading `Y` of `V` as `X ⊕ J_s` whose string has odd length `s = 2 * n + 1`, consider the
vector `z_N = 𝔢 ^ n` (`Y.middlePower`, a multiple of the middle string vector). It has grade `0`:
its entry vanishes at every basis index `k` of nonzero grade `Y.gradeOf k`. The grade is `0` on `X`
and `s − 1 − 2i` on the `i`-th string vector. -/
lemma middlePower_apply_eq_zero (hs : Odd s) {k : ι} (hk : Y.gradeOf k ≠ 0) :
    Y.middlePower k = 0 := by
  obtain ⟨n, hn⟩ := hs
  -- The only nonzero entry is at the string index `n`, of grade `s - 1 - 2 * n = 0`.
  have h_grade : Y.gradeOf (Y.indexEquiv (.inr ⟨n, by omega⟩)) = 0 := by simp [gradeOf, hn]
  rw [Y.middlePower_eq_single ⟨n, by omega⟩ hn.symm, Pi.single_eq_of_ne]
  rintro rfl
  exact hk h_grade

/-- For a grading `Y` of `V` as `X ⊕ J_s` whose string has odd length `s = 2 * n + 1`, the vector
`z_N = 𝔢 ^ n` (`Y.middlePower`, the multiple of the middle string vector of grade `0`) has norm `-N`
under the hermitian form `V.J`. -/
lemma form_middlePower (hs : Odd s) : star Y.middlePower ⬝ᵥ V.J *ᵥ Y.middlePower = -N := by
  obtain ⟨n, hn⟩ := hs
  have h_form : star (Y.stringPower n) ⬝ᵥ V.J *ᵥ Y.stringPower n =
      if n + n + 1 = s then -N else 0 :=
    Y.form_stringPower ⟨n, by omega⟩ ⟨n, by omega⟩
  rw [middlePower, show s / 2 = n by omega, h_form, ite_eq_left (by omega)]

/-- For gradings `Y` and `Y'` of string lengths `s` and `s - 1` with the same constant `c`, the
factor of `Y.stringMap Y'` at the string vector `i` (the two `if`s below) times the coefficient of
`𝔢 ^ i` in `Y` is its coefficient in `Y'`. -/
lemma stringMap_factor_mul_powerCoeff (Y' : Grading V' N X' (s - 1))
    (hc : Y'.genericConst = Y.genericConst) (i : ℕ) :
    (if Odd s ↔ 2 * i + 1 < s then 1 else Y.genericConst.val) * (if 2 * i + 1 = s then -N else 1) *
      Y.powerCoeff i = Y'.powerCoeff i := by
  have hc_ne : Y.genericConst.val ≠ 0 := Y.genericConst.property.left
  -- The exponent of `c` in the factor.
  set e : ℤ := if s % 2 = 1 ↔ 2 * i + 1 < s then 0 else 1
  have h_factor : (if Odd s ↔ 2 * i + 1 < s then 1 else Y.genericConst.val) = Y.genericConst.val ^
    e := by
    simp [e, Nat.odd_iff]
  rw [h_factor]
  have h_nonneg (hi : 2 * i < s) : Y.powerCoeff i = Y.genericConst.val ^ (i - s / 2 : ℤ) :=
    Y.powerCoeff_of_lt hi rfl
  -- The grade of `𝔢 ^ i` is positive, `0` or negative.
  obtain h | h | h := lt_trichotomy (2 * i + 1) s
  · have h_right : Y'.powerCoeff i = Y'.genericConst.val ^ (e + (i - s / 2) : ℤ) :=
      Y'.powerCoeff_of_lt (by omega) (by omega)
    rw [ite_eq_right h.ne, mul_one, h_nonneg (by omega), h_right, hc, zpow_add₀ hc_ne]
  · have h_right : Y'.powerCoeff i = -N * Y'.genericConst.val ^ (e + (i - s / 2) : ℤ) :=
      Y'.powerCoeff_of_le (by omega) (by omega)
    rw [ite_eq_left h, h_nonneg (by omega), h_right, hc, zpow_add₀ hc_ne]
    ring
  · have h_left : Y.powerCoeff i = -N * Y.genericConst.val ^ (i - (s - 1) / 2 : ℤ) :=
      Y.powerCoeff_of_le (by omega) rfl
    have h_right : Y'.powerCoeff i = -N * Y'.genericConst.val ^ (e + (i - (s - 1) / 2) : ℤ) :=
      Y'.powerCoeff_of_le (by omega) (by omega)
    rw [ite_eq_right h.ne', h_left, h_right, hc, zpow_add₀ hc_ne]
    ring

/-- Let `Y'` be a grading of a second space `V'` with the same `N` and string length `s - 1`. Assume
`Y'` carries the same constant `c` as `Y`, where `c = c̄ ≠ 0` is the element of `E` that each
grading carries for the generic character. Then for `i < s` the matrix `Y.stringMap Y'` sends
`Y.stringPower i` (the vector `𝔢 ^ i` of `V`, seen over the adeles by the diagonal embedding
`toAdele`) to `Y'.stringPower i` (the vector `𝔢 ^ i` of `V'`), which is `0` for `i = s - 1`. -/
lemma stringMap_mulVec_stringPower (Y' : Grading V' N X' (s - 1))
    (hc : Y'.genericConst = Y.genericConst) (i : Fin s) :
    Y.stringMap Y' *ᵥ toAdele ∘ Y.stringPower i = toAdele ∘ Y'.stringPower i := by
  funext k
  rw [stringMap, ← RingHom.map_mulVec, stringPower_eq_single, mulVec_single]
  obtain ⟨a | b, rfl⟩ := Y'.indexEquiv.surjective k
  · simp [stringPower]
  · -- At the string index `b` both sides are `Y'.powerCoeff i` if `b = i`, else `0`.
    by_cases hb : b.val = i <;>
      simp [stringPower, hb, ← Y.stringMap_factor_mul_powerCoeff Y' hc i]

/-- The vector `∑ i < s, t i • 𝔢 ^ i` over the finite adeles, with coefficients `t`. -/
def stringSum (t : ℕ → 𝔸f E) : ι → 𝔸f E :=
  ∑ i ∈ Finset.range s, t i • algebraMap E (𝔸f E) ∘ Y.stringPower i

variable {Y}

lemma stringProj_stringSum [Fintype X] (t : ℕ → 𝔸f E) :
    Y.stringProj (Y.stringSum t) = Y.stringSum t :=
  stringProj_eq_self_iff.2 (by simp [stringSum, stringPower])

/-- At the string index `b` the sum `∑ t i • 𝔢 ^ i` has the entry `Y.powerCoeff b * t b`. -/
lemma stringSum_apply_inr (t : ℕ → 𝔸f E) (b : Fin s) :
    Y.stringSum t (Y.indexEquiv (.inr b)) = algebraMap E (𝔸f E) (Y.powerCoeff b) * t b := by
  simp [stringSum, stringPower, apply_ite (algebraMap E (𝔸f E)), mul_comm]

/-- The vectors `𝔢 ^ i` span the complement of `X` over the finite adeles: a vector `y` fixed by
the projection `Y.stringProj` to the span of the string is a sum `∑ t i • 𝔢 ^ i`. -/
lemma exists_stringSum_eq [Fintype X] {y : ι → 𝔸f E} (hy : Y.stringProj y = y) :
    ∃ t : ℕ → 𝔸f E, Y.stringSum t = y := by
  -- The coefficient of `𝔢 ^ i` is the entry of `y` at the string index `i` over `Y.powerCoeff i`.
  let t (i : ℕ) : 𝔸f E := if hi : i < s then
    algebraMap E (𝔸f E) (Y.powerCoeff i)⁻¹ * y (Y.indexEquiv (.inr ⟨i, hi⟩)) else 0
  refine ⟨t, funext fun k ↦ ?_⟩
  obtain ⟨a | b, rfl⟩ := Y.indexEquiv.surjective k
  · -- Both vectors are fixed by the projection, so both vanish at the indices in `X`.
    rw [stringProj_eq_self_iff.1 (stringProj_stringSum t) a, stringProj_eq_self_iff.1 hy a]
  · simp [stringSum_apply_inr, t, ← mul_assoc, ← map_mul, Y.powerCoeff_ne_zero b]

/-- For gradings with the same constant `c`, the map `Y.stringMapFin Y'`, the finite part of
`Y.stringMap Y'`, sends `𝔢 ^ i` to `𝔢 ^ i`. -/
lemma stringMapFin_stringPower {Y' : Grading V' N X' (s - 1)}
    (hc : Y'.genericConst = Y.genericConst) (i : Fin s) :
    Y.stringMapFin Y' (algebraMap E (𝔸f E) ∘ Y.stringPower i) =
      algebraMap E (𝔸f E) ∘ Y'.stringPower i := by
  funext k
  have h_adele : (Y.stringMap Y' *ᵥ toAdele ∘ Y.stringPower i) k = toAdele (Y'.stringPower i k) :=
    congrFun (Y.stringMap_mulVec_stringPower Y' hc i) k
  -- Take the finite component.
  simpa [stringMapFin, mulVec, dotProduct, Prod.snd_sum, toAdele] using congrArg Prod.snd h_adele

/-- For gradings `Y` and `Y'` of string lengths `s` and `s - 1` with the same constant `c`, the map
`Y.stringMapFin Y'`, the finite part of `Y.stringMap Y'`, acts on the sums `∑ t i • 𝔢 ^ i` as the
projection `E[𝔢] / (𝔢 ^ s) → E[𝔢] / (𝔢 ^ (s - 1))`: it keeps `t i` for `i < s - 1`. -/
lemma stringMapFin_stringSum {Y' : Grading V' N X' (s - 1)} (hc : Y'.genericConst = Y.genericConst)
    (t : ℕ → 𝔸f E) :
    Y.stringMapFin Y' (Y.stringSum t) = Y'.stringSum t := by
  calc Y.stringMapFin Y' (Y.stringSum t)
    _ = ∑ i ∈ Finset.range s, t i • algebraMap E (𝔸f E) ∘ Y'.stringPower i := by
      rw [stringSum, map_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [map_smul, stringMapFin_stringPower hc ⟨i, Finset.mem_range.1 hi⟩]
    _ = Y'.stringSum t := by
      -- The term for `i = s - 1` vanishes in `Y'`.
      refine (Finset.sum_subset (by simp) fun i _ hi ↦ ?_).symm
      simp [Y'.stringPower_eq_zero (show s - 1 ≤ i by simpa using hi)]

end New.Grading

end
