import Lib.Weil.Periods.StringPowers
import New.UpperBound.Seesaw.AdmissibleCombinations

/-!
# The standard lattice of a graded space, line by line

Let `Y` grade the hermitian space `V` by an index set `X ⊕ Unit` of grade `0` and a string of `s`
basis vectors, and let the finite frame of `V` span the same lattice `Λ` as the standard basis
`New.gradedLatticeBasis`. The intersection `Λ⁻` of `Λ` with the span of the string and its
projection `Λ⁺` to this span are sums of lines.

* `New.Grading.SpansLattice.isGraded`: `Λ` is graded.
* `New.Grading.SpansLattice.mem_latticeMinus_iff`, `New.Grading.SpansLattice.mem_latticePlus_iff`:
  the generators of the lines; they differ only by `N⁻¹` at the middle vector of the string.
* `New.Grading.SpansLattice.mem_lattice_and_stringProj_eq_zero_iff`: for odd `s`, the
  intersection of `Λ` with the span of `X ⊕ Unit`.
* `New.Grading.SpansLattice.stringSum_mem_latticeMinus_iff`,
  `New.Grading.SpansLattice.stringSum_mem_latticePlus_iff`: the generators on the lines of the
  vectors `𝔢 ^ i`, for the scale `u = (a / ā) ^ ⌊(s + 2) / 2⌋` and when the constant `c` of `Y`
  has the valuations of `a ā`.
* `New.Grading.SpansLattice.map_stringMapFin_latticePlus`: under the same conditions, the shift to
  a space with a string of `s - 1` vectors and the same constant `c` takes `Λ⁺` onto `a Λ'⁻`.
* `New.Grading.SpansLattice.odd_of_notMem_latticeMinus`: a vector of `Λ⁺` outside `Λ⁻` exists
  only for odd `s`.
* `New.Grading.SpansLattice.exists_place_generates_of_notMem_latticeMinus`: such a vector
  generates `Λ⁺` over `Λ⁻` at some place above `N`.

The results on `Λ⁺` and on the span of `X ⊕ Unit` assume that `N` is split and squarefree
(`IsSplitSquarefree P N π`).

Notions from other files:
* `Y.SpansLattice a π u`: the lattice `Λ = V.lattice 1` has the standard basis
  `New.gradedLatticeBasis Y.indexEquiv a π u` over the integral finite adeles `Ô E`. This basis
  consists of the vectors of `X`, the multiples of the string vectors `b` by `lineIdele a u b`, and
  the last vector `e₀` of `X ⊕ Unit`, replaced for odd `s` by `e₀ / π̄ + u z / (π π̄)`, where `z`
  is the middle vector of the string.
* `IsSplitSquarefree P N π`: `N = π π̄`, where `π` is a uniformiser at the places of `P`, a unit
  elsewhere, and no place of `P` has its conjugate in `P`.
* `Y.stringSum t`: the vector `∑ t i • 𝔢 ^ i`, where `𝔢 ^ i = Y.stringPower i` is a multiple of
  the string vector `i` by an element of `E`.
* `Y.genericConst`: the constant `c` of the grading, a nonzero element of `E` fixed by conjugation.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

open Matrix Pointwise Valued

noncomputable section

namespace New

open Seesaw

variable {E X X' ι ι' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}
  {Y : Grading V N (X ⊕ Unit) s} {Y' : Grading V' N (X' ⊕ Unit) (s - 1)} {a π : (𝔸f E)ˣ}
  {u : unitary (𝔸f E)} {P : Finset (FinPlace E)}

/-- The diagonal entry of `New.gradedLatticeBasis` at the string vector `b`, as an idele: `u` for
odd `s`; for even `s` it is `u a⁻¹` on the first half of the string and `u ā` on the second half.
It generates the part of `Λ⁻` on the line of this vector. -/
def lineIdele (a : (𝔸f E)ˣ) (u : unitary (𝔸f E)) (b : Fin s) : (𝔸f E)ˣ :=
  Unitary.toUnits u * if Odd s then 1 else if 2 * b.val < s then a⁻¹ else star a

/-- The idele `a ^ (s - i) ā ^ (-1 - i)`. The docstrings of the membership criteria below write
`𝔩_i` for the fractional ideal that it generates. -/
def powerIdele (a : (𝔸f E)ˣ) (s i : ℕ) : (𝔸f E)ˣ := a ^ (s - i : ℤ) * star a ^ (-1 - i : ℤ)

lemma powerIdele_eq_mul (hs : 0 < s) (i : ℕ) : powerIdele a s i = a * powerIdele a (s - 1) i := by
  rw [powerIdele, powerIdele, show (s - i : ℤ) = 1 + ((s - 1 : ℕ) - i : ℤ) by omega,
    _root_.zpow_one_add, mul_assoc]

/-- Multiplying `powerIdele a s i = a ^ (s - i) ā ^ (-1 - i)` by `(a ā) ^ n` adds `n` to both
exponents. -/
lemma powerIdele_mul_zpow (i : ℕ) (n : ℤ) : powerIdele a s i * (a * star a) ^ n =
    a ^ (s - i + n : ℤ) * star a ^ (-1 - i + n : ℤ) := by
  rw [powerIdele, mul_zpow, mul_mul_mul_comm, ← _root_.zpow_add, ← _root_.zpow_add]

lemma toUnits_divStar_pow (k : ℕ) :
    Unitary.toUnits (divStar a ^ k) = a ^ (k : ℤ) * star a ^ (-k : ℤ) := by
  rw [map_pow, show Unitary.toUnits (divStar a) = a * (star a)⁻¹ from Units.ext (coe_divStar a),
    ← zpow_natCast, mul_zpow, _root_.inv_zpow']

/-- Let `s` be the number of vectors in a string, indexed by `b : Fin s`, and `a` a finite idele.
For the scale `u = (a / ā) ^ ⌊(s + 2) / 2⌋`, where `divStar a = a / ā`, the idele `lineIdele a u b`
(which is `u` for odd `s`, and `u a⁻¹` or `u ā` on the two halves of the string for even `s`) is
`powerIdele a s b = a ^ (s - b) ā ^ (-1 - b)` times a power of `a ā`. -/
lemma lineIdele_divStar_pow (b : Fin s) :
    lineIdele a (divStar a ^ ((s + 2) / 2)) b = powerIdele a s b *
      (a * star a) ^ (b - (if 2 * b.val < s then s else s - 1 : ℤ) / 2 : ℤ) := by
  set k : ℕ := (s + 2) / 2 with hk
  set n : ℤ := b - (if 2 * b.val < s then s else s - 1 : ℤ) / 2 with hn
  -- Both sides are a power of `a` times a power of `ā`; compare the exponents in each case.
  rw [lineIdele, toUnits_divStar_pow, powerIdele_mul_zpow]
  by_cases hs : Odd s
  · have hs_mod : s % 2 = 1 := Nat.odd_iff.1 hs
    obtain ⟨h_left, h_right⟩ : (s - b + n : ℤ) = k ∧ (-1 - b + n : ℤ) = -k := by omega
    rw [ite_eq_left hs, h_left, h_right, mul_one]
  have hs_mod : s % 2 = 0 := Nat.not_odd_iff.1 hs
  by_cases hb : 2 * b.val < s
  · obtain ⟨h_left, h_right⟩ : (s - b + n : ℤ) = k - 1 ∧ (-1 - b + n : ℤ) = -k := by omega
    simp [hs, hb, h_left, h_right, _root_.zpow_sub_one, mul_right_comm]
  · obtain ⟨h_left, h_right⟩ : (s - b + n : ℤ) = k ∧ (-1 - b + n : ℤ) = -k + 1 := by omega
    simp [hs, hb, h_left, h_right, _root_.zpow_add_one, mul_assoc]

lemma eq_rev_iff (b : Fin s) : b = b.rev ↔ 2 * b.val + 1 = s := by
  rw [Fin.ext_iff, Fin.val_rev]
  omega

lemma odd_of_eq_rev {b : Fin s} (hb : b = b.rev) : Odd s :=
  ⟨b.val, ((eq_rev_iff b).1 hb).symm⟩

lemma eq_of_eq_rev {b b' : Fin s} (hb : b = b.rev) (hb' : b' = b'.rev) : b = b' := by
  rw [eq_rev_iff] at hb hb'
  exact Fin.ext (by omega)

open scoped Classical in
/-- Let `N = π π̄`, with `π` a uniformiser at the places of `P` and a unit elsewhere, and no place
of `P` conjugate to a place of `P`. Then `N` is a uniformiser at the places of `P` and their
conjugates, and a unit elsewhere. -/
lemma Seesaw.IsSplitSquarefree.v_algebraMap (hπ : IsSplitSquarefree P N π) (w : FinPlace E) :
    v (algebraMap E (𝔸f E) N w) = if w ∈ P ∨ star w ∈ P then WithZero.exp (-1) else 1 := by
  rw [hπ.algebraMap_eq_mul_star, finAdele_mul_apply, map_mul, v_star_apply, hπ.v_apply,
    hπ.v_apply]
  by_cases hw : w ∈ P <;> simp +contextual [hw, hπ.star_notMem w]

/-- Under `IsSplitSquarefree P N π` the element `N = π π̄` is integral, being a uniformiser or a
unit at every place. -/
lemma Seesaw.IsSplitSquarefree.algebraMap_mem_Ô (hπ : IsSplitSquarefree P N π) :
    algebraMap E (𝔸f E) N ∈ Ô E := by
  refine mem_Ô.2 fun w ↦ ?_
  rw [hπ.v_algebraMap]
  split_ifs <;> simp [← WithZero.exp_zero]

omit [Fintype X] in
/-- The grading `Y` indexes a basis of a hermitian space through `Y.indexEquiv`, with a string of
`s` vectors `b : Fin s` of grade `s - 1 - 2 b`; `N` is the element of `E` in its Gram matrix, and
its constant `c = Y.genericConst` is assumed to have the valuation `v` of `a ā` at every finite
place `w` of `E`. The vector `𝔢 ^ i` is a multiple of the string vector `i` by an element of `E`,
and `Y.stringSum t = ∑ t i • 𝔢 ^ i`. The claim: a coordinate of this vector at the string vector
`b` lies in the fractional ideal of `lineIdele a u b`, where `u = (a / ā) ^ ⌊(s + 2) / 2⌋` and
`divStar a = a / ā`, if and only if `t b` lies in that of `powerIdele a s b`, times `N⁻¹` in
negative grade (`s ≤ 2 b`). The same holds with both sides multiplied by any adele `r`. -/
lemma Grading.lineIdele_inv_mul_stringSum_mem_iff
    (hc : ∀ w : FinPlace E, v (algebraMap E (𝔸f E) Y.genericConst.val w) = v
      ((a.val * star a.val) w))
    (r : 𝔸f E) (t : ℕ → 𝔸f E) (b : Fin s) :
    r * ((lineIdele a (divStar a ^ ((s + 2) / 2)) b)⁻¹.val *
        Y.stringSum t (Y.indexEquiv (.inr b))) ∈ Ô E ↔
      r * (if 2 * b.val < s then 1 else algebraMap E (𝔸f E) N) *
        ((powerIdele a s b)⁻¹.val * t b) ∈ Ô E := by
  rw [stringSum_apply_inr, lineIdele_divStar_pow]
  set n : ℤ := b - (if 2 * b.val < s then s else s - 1 : ℤ) / 2 with hn
  have h_val (w : FinPlace E) : v (algebraMap E (𝔸f E) (Y.powerCoeff b) w) =
      v (((if 2 * b.val < s then 1 else algebraMap E (𝔸f E) N) * ((a * star a) ^ n).val) w) := by
    have h_unit : ((a * star a) ^ n).val w = (a.val * star a.val) w ^ n :=
      map_zpow ((evalAt w).toMonoidHom.comp (Units.coeHom (𝔸f E))) (a * star a) n
    rw [finAdele_mul_apply, h_unit, map_mul, map_zpow₀, ← hc]
    split_ifs with hb <;> simp [powerCoeff, hn, hb]
  -- At each place the valuation of `(a ā) ^ n` cancels.
  have h_cancel (w : FinPlace E) :
      v ((r * ((powerIdele a s b * (a * star a) ^ n)⁻¹.val *
          (algebraMap E (𝔸f E) (Y.powerCoeff b) * t b))) w) =
        v ((r * (if 2 * b.val < s then 1 else algebraMap E (𝔸f E) N) *
          ((powerIdele a s b)⁻¹.val * t b)) w) := by
    simp only [finAdele_mul_apply, map_mul, h_val, idele_inv_apply_and_ne_zero, Units.val_mul,
      map_inv₀]
    have h_ne : v (((a * star a) ^ n).val w) ≠ 0 := by simp [idele_inv_apply_and_ne_zero]
    field_simp
  simp only [mem_Ô, h_cancel]

omit [DecidableEq ι] in
/-- The coordinates with index in `X ⊕ Unit` of a combination of the vectors of
`New.gradedLatticeBasis`: only the last one is rescaled, by `π̄⁻¹`, and only for odd `s`. -/
lemma gradedLatticeBasis_mulVec_apply_inl (e : (X ⊕ Unit) ⊕ Fin s ≃ ι) (c : ι → 𝔸f E)
    (i : X ⊕ Unit) :
    (gradedLatticeBasis e a π u *ᵥ c) (e (.inl i)) =
      (if Odd s ∧ i = .inr () then (star π)⁻¹.val else 1) * c (e (.inl i)) := by
  rw [gradedLatticeBasis]
  by_cases hs : Odd s <;> cases i <;>
    simp [hs, submatrix_mulVec_equiv, fromBlocks_mulVec, mulVec_diagonal]

omit [DecidableEq ι] in
/-- The string coordinates of a combination of the vectors of `New.gradedLatticeBasis`: the
coordinate of `gradedLatticeBasis e a π u *ᵥ c` at the string vector `b` is `lineIdele a u b` times
the coefficient `c` at `b`. For the middle vector, with `b = b.rev`, there is an added term:
`u (π̄ π)⁻¹` times the coefficient `c` at the last index `.inr ()` of `X ⊕ Unit`. -/
lemma gradedLatticeBasis_mulVec_apply_inr (e : (X ⊕ Unit) ⊕ Fin s ≃ ι) (c : ι → 𝔸f E) (b : Fin s) :
    (gradedLatticeBasis e a π u *ᵥ c) (e (.inr b)) =
      (if b = b.rev then u.val * (star π * π)⁻¹.val else 0) * c (e (.inl (.inr ()))) +
        (lineIdele a u b).val * c (e (.inr b)) := by
  simp [gradedLatticeBasis, lineIdele, mulVec, dotProduct, ← e.sum_comp, diagonal_apply,
    apply_ite Units.val]

namespace Grading.SpansLattice

omit [Fintype X] in
/-- Suppose `hL : Y.SpansLattice a π u`, that is, the lattice `V.lattice 1` is spanned over `Ô E` by
the columns of `gradedLatticeBasis Y.indexEquiv a π u`. Then every vector `y : ι → 𝔸f E` has
coordinates `c` in this basis. Moreover, `y` lies in `V.lattice 1` if and only if every `c i` lies
in `Ô E`. -/
lemma exists_gradedLatticeBasis_mulVec_eq (hL : Y.SpansLattice a π u) (y : ι → 𝔸f E) :
    ∃ c : ι → 𝔸f E, gradedLatticeBasis Y.indexEquiv a π u *ᵥ c = y ∧
      (y ∈ V.lattice 1 ↔ ∀ i : ι, c i ∈ Ô E) := by
  obtain ⟨k, hk, h_frame⟩ : ∃ k ∈ intGL ι (Ô E),
      V.xFin.val = gradedLatticeBasis Y.indexEquiv a π u * k.val := hL
  obtain ⟨hk_int, hk_inv⟩ : IsIntMatrix (Ô E) k.val ∧ IsIntMatrix (Ô E) k⁻¹.val := mem_intGL.1 hk
  refine ⟨k.val *ᵥ V.xFin⁻¹.val *ᵥ y, ?_, ?_⟩
  · rw [mulVec_mulVec, ← h_frame, mulVec_mulVec, Units.mul_inv, one_mulVec]
  · rw [Space.mem_lattice, OneMemClass.coe_one, mul_one]
    refine ⟨hk_int.mulVec, fun hc i ↦ ?_⟩
    simpa only [mulVec_mulVec, Units.inv_mul_cancel_left] using hk_inv.mulVec hc i

/-- The hypothesis `hL` says that `Λ` has, over the integral finite adeles `Ô E`, the standard basis
attached to the ideles `a`, `π` and the unitary scale `u`: the vectors of `X`, the string vectors
`b` times `lineIdele a u b`, and the last vector `e₀` of `X ⊕ Unit`, replaced for odd `s` by
`e₀ / π̄ + u z / (π π̄)`, with `z` the middle vector of the string. So `y` lies in `Λ` if and only
if three conditions hold, on its coordinates at `X`, at the last index, and on the string. The only
condition that links two coordinates glues the last index to the middle, the `b` with
`b = b.rev`. -/
lemma mem_lattice_iff {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u) :
    y ∈ V.lattice 1 ↔
      (∀ i : X, y (Y.indexEquiv (.inl (.inl i))) ∈ Ô E) ∧
      (if Odd s then star π.val else 1) * y (Y.indexEquiv (.inl (.inr ()))) ∈ Ô E ∧
      ∀ b : Fin s, (lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b)) -
        (if b = b.rev then π⁻¹.val * y (Y.indexEquiv (.inl (.inr ()))) else 0) ∈ Ô E := by
  -- The three expressions are the coordinates `c` of `y` in the basis.
  obtain ⟨c, hc, h_mem⟩ : ∃ c : ι → 𝔸f E, gradedLatticeBasis Y.indexEquiv a π u *ᵥ c = y ∧
      (y ∈ V.lattice 1 ↔ ∀ i : ι, c i ∈ Ô E) := hL.exists_gradedLatticeBasis_mulVec_eq y
  set y₀ : 𝔸f E := y (Y.indexEquiv (.inl (.inr ()))) with hy₀
  set c₀ : 𝔸f E := c (Y.indexEquiv (.inl (.inr ())))
  have h_first (i : X) : y (Y.indexEquiv (.inl (.inl i))) = c (Y.indexEquiv (.inl (.inl i))) := by
    simp [← hc, gradedLatticeBasis_mulVec_apply_inl]
  have h_last : (if Odd s then star π.val else 1) * y₀ = c₀ := by
    rw [hy₀, ← hc, gradedLatticeBasis_mulVec_apply_inl]
    by_cases hs : Odd s <;> simp [c₀, hs, ← mul_assoc, ← star_mul]
  have h_line (b : Fin s) : (lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b)) -
      (if b = b.rev then π⁻¹.val * y₀ else 0) = c (Y.indexEquiv (.inr b)) := by
    have hy_inr : y (Y.indexEquiv (.inr b)) = (if b = b.rev then u.val * (star π * π)⁻¹.val
        else 0) * c₀ + (lineIdele a u b).val * c (Y.indexEquiv (.inr b)) := by
      rw [← hc, gradedLatticeBasis_mulVec_apply_inr]
    rw [hy_inr, mul_add, Units.inv_mul_cancel_left]
    by_cases hb : b = b.rev
    · have hu : (lineIdele a u b).val = u.val := by simp [lineIdele, odd_of_eq_rev hb]
      have h_inv : (star π * π)⁻¹.val * star π.val = π⁻¹.val := by simp [mul_assoc, ← star_mul]
      have h_glue : (lineIdele a u b)⁻¹.val * (u.val * (star π * π)⁻¹.val * c₀) = π⁻¹.val * y₀ :=
        calc _ = (star π * π)⁻¹.val * c₀ := by rw [← hu, mul_assoc, Units.inv_mul_cancel_left]
          _ = (star π * π)⁻¹.val * (star π.val * y₀) := by
              rw [← h_last, ite_eq_left (odd_of_eq_rev hb)]
          _ = π⁻¹.val * y₀ := by rw [← mul_assoc, h_inv]
      rw [ite_eq_left hb, ite_eq_left hb, h_glue, add_sub_cancel_left]
    · simp [hb]
  simp only [h_mem, h_first, h_last, h_line, Y.indexEquiv.surjective.forall, Sum.forall,
    Unique.forall_iff, and_assoc, c₀]

/-- The grading `Y` of the hermitian space `V` gives each basis vector an integer grade: `0` on
`X ⊕ Unit` and `s - 1 - 2 b` at the vector `b` of the string of length `s`. If the lattice
`V.lattice 1` has the standard basis for `a`, `π`, `u` (the basis vectors rescaled, except that for
odd `s` the last vector of `X ⊕ Unit` is combined with the middle string vector), then it contains
the part in each grade of each of its vectors, since both combined vectors have grade `0`. -/
lemma isGraded (hL : Y.SpansLattice a π u) : Y.IsGraded (V.lattice 1) := by
  intro d y hy
  have h_proj (i : ι) : Y.gradeProj d y i = if Y.gradeOf i = d then y i else 0 := by
    simp [gradeProj, mulVec_diagonal]
  rw [hL.mem_lattice_iff] at hy ⊢
  obtain ⟨h_first, h_last, h_line⟩ := hy
  simp only [h_proj, gradeOf_inl, gradeOf_inr]
  refine ⟨fun i ↦ ?_, ?_, fun b ↦ ?_⟩
  · simp [ite_mem, h_first i]
  · rw [mul_ite, mul_zero]
    exact ite_mem.2 ⟨fun _ ↦ h_last, fun _ ↦ zero_mem _⟩
  · specialize h_line b
    by_cases hb : b = b.rev
    · have hb_val : 2 * b.val + 1 = s := (eq_rev_iff b).1 hb
      have h_grade : (s - 1 - 2 * b.val : ℤ) = 0 := by omega
      rw [ite_eq_left hb] at h_line ⊢
      by_cases hd : 0 = d <;> simp [h_grade, hd, h_line]
    · rw [ite_eq_right hb, sub_zero] at h_line ⊢
      simp [mul_ite, ite_mem, h_line]

/-- Let the lattice be spanned by `New.gradedLatticeBasis`. Its intersection
`Λ⁻ = Y.latticeMinus 1` with the span of the string, onto which `Y.stringProj` projects, is the sum
of its lines: the multiples of the string vector `b` by the fractional ideal of
`lineIdele a u b`. -/
lemma mem_latticeMinus_iff {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u) :
    y ∈ Y.latticeMinus 1 ↔ Y.stringProj y = y ∧
      ∀ b : Fin s, (lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b)) ∈ Ô E := by
  rw [mem_latticeMinus, and_comm, hL.mem_lattice_iff]
  refine and_congr_right fun hy ↦ ?_
  simp [stringProj_eq_self_iff.1 hy]

/-- Let `Λ = V.lattice 1` have the standard basis for the ideles `a`, `π` and the unitary scale `u`,
in which the string vector `b` is multiplied by `lineIdele a u b` and, for odd `s`, the last vector
of `X ⊕ Unit` is combined with the middle one. Let `N = π π̄` be split and squarefree, `P` being the
places of `π`. Then the projection `Λ⁺ = Y.latticePlus 1` of `Λ` by `Y.stringProj` to the span of
the string is the sum of its lines: the multiples of the string vector `b` by the fractional ideal
of `lineIdele a u b`, times `N⁻¹` at the middle vector, the `b` with `b = b.rev`. -/
lemma mem_latticePlus_iff {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) :
    y ∈ Y.latticePlus 1 ↔ Y.stringProj y = y ∧ ∀ b : Fin s,
      (if b = b.rev then algebraMap E (𝔸f E) N else 1) *
        ((lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b))) ∈ Ô E := by
  constructor
  · intro hy
    refine ⟨stringProj_eq_of_mem_latticePlus hy, fun b ↦ ?_⟩
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ V.lattice 1, Y.stringProj z = y := mem_latticePlus.1 hy
    obtain ⟨-, h_last, h_line⟩ := hL.mem_lattice_iff.1 hz
    specialize h_line b
    rw [stringProj_apply_inr]
    by_cases hb : b = b.rev
    · rw [ite_eq_left hb] at h_line ⊢
      rw [ite_eq_left (odd_of_eq_rev hb)] at h_last
      have h_star_eq : star π.val = algebraMap E (𝔸f E) N * π⁻¹.val := by
        rw [hπ.algebraMap_eq_mul_star, mul_comm, Units.inv_mul_cancel_left]
      rw [h_star_eq, mul_assoc] at h_last
      simpa only [mul_sub, sub_add_cancel] using
        add_mem (mul_mem hπ.algebraMap_mem_Ô h_line) h_last
    · simpa [hb] using h_line
  · rintro ⟨hy, h_line⟩
    have hy_zero := stringProj_eq_self_iff.1 hy
    -- Let `η` be the middle coordinate divided by its generator, or `0` for even `s`. The
    -- coordinate `π η` at the last index of `X ⊕ Unit` glues `y` to a vector `z` of the lattice.
    let η : 𝔸f E := ∑ b : Fin s with b = b.rev,
      (lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b))
    have hη (b : Fin s) (hb : b = b.rev) :
        η = (lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b)) :=
      Finset.sum_eq_single_of_mem b (by simpa using hb) fun b' hb' h_ne ↦
        (h_ne (eq_of_eq_rev (by simpa using hb') hb)).elim
    have hη_mem : (if Odd s then star π.val else 1) * (π.val * η) ∈ Ô E := by
      rw [← mul_assoc, Finset.mul_sum]
      refine sum_mem fun b hb_mem ↦ ?_
      have hb : b = b.rev := by simpa using hb_mem
      rw [ite_eq_left (odd_of_eq_rev hb), mul_comm (star π.val), ← hπ.algebraMap_eq_mul_star]
      simpa only [ite_eq_left hb] using h_line b
    let z : ι → 𝔸f E := Function.update y (Y.indexEquiv (.inl (.inr ()))) (π.val * η)
    have hz : z ∈ V.lattice 1 := by
      refine hL.mem_lattice_iff.2 ⟨fun i ↦ by simp [z, hy_zero],
        by simpa only [z, Function.update_self] using hη_mem, fun b ↦ ?_⟩
      by_cases hb : b = b.rev
      · simp [z, ite_eq_left hb, hη b hb]
      · simpa [z, hb] using h_line b
    refine mem_latticePlus.2 ⟨z, hz, funext fun i ↦ ?_⟩
    obtain ⟨i | b, rfl⟩ := Y.indexEquiv.surjective i <;>
      simp [z, stringProj_apply_inl, stringProj_apply_inr, hy_zero]

/-- The grading `Y` indexes the basis of the hermitian space `V`, through `Y.indexEquiv`, by
`X ⊕ Unit` and a string of `s` vectors, here with `s` odd. Let `Λ = V.lattice 1` have the standard
basis for the ideles `a`, `π` and any unitary scale `u`, in which the last vector `e₀` of
`X ⊕ Unit` is replaced by `e₀ / π̄ + u z / (π π̄)`, with `z` the middle vector of the string, and
let `N = π π̄` be split and squarefree. The intersection of `Λ` with the span of `X ⊕ Unit`, the
kernel of the projection `Y.stringProj` to the span of the string, consists of the vectors whose
coordinates on `X` are integral and whose last coordinate lies in `π Ô E`. -/
lemma mem_lattice_and_stringProj_eq_zero_iff {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) (hs : Odd s) :
    y ∈ V.lattice 1 ∧ Y.stringProj y = 0 ↔ Y.stringProj y = 0 ∧
      (∀ i : X, y (Y.indexEquiv (.inl (.inl i))) ∈ Ô E) ∧
      π⁻¹.val * y (Y.indexEquiv (.inl (.inr ()))) ∈ Ô E := by
  rw [and_comm, hL.mem_lattice_iff, ite_eq_left hs]
  refine and_congr_right fun hy ↦ and_congr_right fun _ ↦ ?_
  have hy_string (b : Fin s) : y (Y.indexEquiv (.inr b)) = 0 := by
    simp [← stringProj_apply_inr y b, hy]
  simp only [hy_string, mul_zero, zero_sub, neg_mem_iff]
  set y₀ : 𝔸f E := y (Y.indexEquiv (.inl (.inr ())))
  refine ⟨?_, fun h_glue ↦ ⟨?_, fun b ↦ ite_mem.2 ⟨fun _ ↦ h_glue, fun _ ↦ zero_mem _⟩⟩⟩
  · -- The glue condition at the middle vector of the string says that `π⁻¹ y₀` is integral.
    rintro ⟨-, h_line⟩
    obtain ⟨k, hk⟩ := hs
    let m : Fin s := ⟨k, by omega⟩
    have hm : m = m.rev := (eq_rev_iff m).2 hk.symm
    simpa only [ite_eq_left hm] using h_line m
  · -- The last condition is `N` times the glue condition, as `N = π π̄`.
    simpa [hπ.algebraMap_eq_mul_star, mul_assoc, mul_left_comm π.val] using
      mul_mem hπ.algebraMap_mem_Ô h_glue

/-- The grading `Y` of the hermitian space `V` has a string of `s` basis vectors; `𝔢 ^ i` is a
multiple of the string vector `i` by an element of `E` and has grade `s - 1 - 2 i`, and `N` is the
element of `E` in the Gram matrix. Let the lattice `Λ = V.lattice 1` have the standard basis of
`gradedLatticeBasis` for the ideles `a`, `π` and the scale `(a / ā) ^ ⌊(s + 2) / 2⌋`, and let the
constant `c` of `Y` have the valuations of `a ā`. Then `Y.stringSum t = ∑ t i • 𝔢 ^ i` lies in
`Λ⁻ = Y.latticeMinus 1`, the intersection of `Λ` with the span of the string, if and only if each
`t i` lies in the fractional ideal `𝔩_i` of `powerIdele a s i` in grade at least `0`, and in
`N⁻¹ 𝔩_i` in negative grade. -/
lemma stringSum_mem_latticeMinus_iff (hL : Y.SpansLattice a π (divStar a ^ ((s + 2) / 2)))
    (hc : ∀ w : FinPlace E, v (algebraMap E (𝔸f E) Y.genericConst.val w) = v
      ((a.val * star a.val) w))
    (t : ℕ → 𝔸f E) :
    Y.stringSum t ∈ Y.latticeMinus 1 ↔ ∀ i : ℕ, i < s →
      (if 2 * i < s then 1 else algebraMap E (𝔸f E) N) *
        ((powerIdele a s i)⁻¹.val * t i) ∈ Ô E := by
  rw [hL.mem_latticeMinus_iff, and_iff_right (stringProj_stringSum t), Nat.forall_lt_iff_fin]
  refine forall_congr' fun b ↦ ?_
  simpa only [one_mul] using lineIdele_inv_mul_stringSum_mem_iff hc 1 t b

/-- The grading `Y` of the hermitian space `V` has a string of `s` basis vectors; `𝔢 ^ i` is a
multiple of the string vector `i` by an element of `E` and has grade `s - 1 - 2 i`. Let the lattice
`Λ = V.lattice 1` have the standard basis of `gradedLatticeBasis` for the ideles `a`, `π` and the
scale `(a / ā) ^ ⌊(s + 2) / 2⌋`, let the constant `c` of `Y` have the valuations of `a ā`, and let
`N = π π̄`, with `π` a uniformiser at the places of `P`, a unit elsewhere, and no place of `P`
conjugate to another or to itself. Then `Y.stringSum t = ∑ t i • 𝔢 ^ i` lies in
`Λ⁺ = Y.latticePlus 1`, the projection of `Λ` to the span of the string, if and only if each `t i`
lies in the fractional ideal `𝔩_i` of `powerIdele a s i` in positive grade, and in `N⁻¹ 𝔩_i` in
grade at most `0`. -/
lemma stringSum_mem_latticePlus_iff (hL : Y.SpansLattice a π (divStar a ^ ((s + 2) / 2)))
    (hπ : IsSplitSquarefree P N π)
    (hc : ∀ w : FinPlace E, v (algebraMap E (𝔸f E) Y.genericConst.val w) = v
      ((a.val * star a.val) w))
    (t : ℕ → 𝔸f E) :
    Y.stringSum t ∈ Y.latticePlus 1 ↔ ∀ i : ℕ, i < s →
      (if 2 * i + 1 < s then 1 else algebraMap E (𝔸f E) N) *
        ((powerIdele a s i)⁻¹.val * t i) ∈ Ô E := by
  rw [hL.mem_latticePlus_iff hπ, and_iff_right (stringProj_stringSum t), Nat.forall_lt_iff_fin]
  refine forall_congr' fun b ↦ ?_
  have h_factor : ((if b = b.rev then algebraMap E (𝔸f E) N else 1) *
      if 2 * b.val < s then 1 else algebraMap E (𝔸f E) N) =
        if 2 * b.val + 1 < s then 1 else algebraMap E (𝔸f E) N := by
    grind [eq_rev_iff]
  rw [lineIdele_inv_mul_stringSum_mem_iff hc, h_factor]

/-- `sh Λ⁺ = a Λ'⁻`: let `Y`, `Y'` be gradings of the hermitian spaces `V`, `V'` with strings of
`s`, `s - 1` basis vectors and the same constant `genericConst`, which has the valuations of `a ā`.
Let `N = π π̄` be split and squarefree, with `P` the places where `π` is a uniformiser. Suppose
`Y.SpansLattice` and `Y'.SpansLattice` hold: the lattices `Λ`, `Λ'` of `1` have, up to `GL(Ô)`, the
bases `gradedLatticeBasis` at the scales `(a / ā) ^ ⌊(s + 2) / 2⌋` and
`(a / ā) ^ ⌊(s - 1 + 2) / 2⌋`. The shift `sh = Y.stringMapFin Y'` kills `X ⊕ Unit` and sends each
string vector of `V` to a multiple of the string vector of `V'` with the same number, if there is
one. It takes the projection `Λ⁺` of `Λ` to the span of the string onto `a` times the intersection
`Λ'⁻` of `Λ'` with the span of the string. -/
lemma map_stringMapFin_latticePlus (hL : Y.SpansLattice a π (divStar a ^ ((s + 2) / 2)))
    (hL' : Y'.SpansLattice a π (divStar a ^ ((s - 1 + 2) / 2))) (hπ : IsSplitSquarefree P N π)
    (hconst_eq : Y'.genericConst = Y.genericConst)
    (hc : ∀ w : FinPlace E, v (algebraMap E (𝔸f E) Y.genericConst.val w) = v
      ((a.val * star a.val) w)) :
    (Y.latticePlus 1).map ((Y.stringMapFin Y').restrictScalars (Ô E)) =
      a.val • Y'.latticeMinus 1 := by
  -- On the line of `𝔢 ^ i` with `i < s - 1` the conditions for `Λ⁺` and for `a Λ'⁻` are the same.
  have h_line (i : ℕ) (hi : i < s - 1) (x : 𝔸f E) :
      (if 2 * i + 1 < s then 1 else algebraMap E (𝔸f E) N) *
          ((powerIdele a s i)⁻¹.val * (a.val * x)) =
        (if 2 * i < s - 1 then 1 else algebraMap E (𝔸f E) N) *
          ((powerIdele a (s - 1) i)⁻¹.val * x) := by
    simp [powerIdele_eq_mul (show 0 < s by omega), Nat.lt_sub_iff_add_lt, mul_assoc]
  have hc' : ∀ w : FinPlace E, v (algebraMap E (𝔸f E) Y'.genericConst.val w) = v
    ((a.val * star a.val) w) := by
    rwa [hconst_eq]
  have h_smul (t : ℕ → 𝔸f E) : a.val • Y'.stringSum t = Y'.stringSum fun i ↦ a.val * t i := by
    simp only [stringSum, Finset.smul_sum, smul_smul]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := exists_stringSum_eq (stringProj_eq_of_mem_latticePlus hy)
    refine ⟨Y'.stringSum fun i ↦ a⁻¹.val * t i, ?_,
      by simp [h_smul, stringMapFin_stringSum hconst_eq]⟩
    refine (hL'.stringSum_mem_latticeMinus_iff hc' _).2 fun i hi ↦ ?_
    rw [← h_line i hi, Units.mul_inv_cancel_left]
    exact (hL.stringSum_mem_latticePlus_iff hπ hc t).1 hy i (by omega)
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨t, rfl⟩ := exists_stringSum_eq (mem_latticeMinus.1 hz).right
    let t' (i : ℕ) : 𝔸f E := if i < s - 1 then a.val * t i else 0
    have h_mem : Y.stringSum t' ∈ Y.latticePlus 1 := by
      refine (hL.stringSum_mem_latticePlus_iff hπ hc t').2 fun i _ ↦ ?_
      by_cases hi : i < s - 1
      · simpa [t', hi, h_line i hi] using (hL'.stringSum_mem_latticeMinus_iff hc' t).1 hz i hi
      · simp [t', hi]
    have h_shift : Y.stringMapFin Y' (Y.stringSum t') = a.val • Y'.stringSum t := by
      rw [stringMapFin_stringSum hconst_eq, h_smul, stringSum, stringSum]
      exact Finset.sum_congr rfl fun i hi ↦ by simp only [t', ite_eq_left (Finset.mem_range.1 hi)]
    exact ⟨Y.stringSum t', h_mem, h_shift⟩

/-- Let `Λ⁻ = Y.latticeMinus 1` and `Λ⁺ = Y.latticePlus 1` be the intersection with and the
projection to the span of the string of the lattice with standard basis `gradedLatticeBasis` for
`a`, `π` and any unitary scale `u`, in which the string vector `b` is multiplied by
`lineIdele a u b`. Let `N = π π̄` be split and squarefree. For `y` in `Λ⁺` outside `Λ⁻`, the string
has a middle index `m = m.rev`, and the coordinate of `y` there, divided by `lineIdele a u m`, which
generates `Λ⁻` on this line, has a pole at a place `w` above `N`: a place of `P` or a conjugate of
one. -/
lemma exists_pole_of_notMem_latticeMinus {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) (hy : y ∈ Y.latticePlus 1) (hy_notMem : y ∉ Y.latticeMinus 1) :
    ∃ (m : Fin s) (w : FinPlace E), m = m.rev ∧ (w ∈ P ∨ star w ∈ P) ∧
      1 < v (((lineIdele a u m)⁻¹.val * y (Y.indexEquiv (.inr m))) w) := by
  obtain ⟨hy_string, hy_line⟩ := (hL.mem_latticePlus_iff hπ).1 hy
  obtain ⟨m, w, h_pole⟩ : ∃ (m : Fin s) (w : FinPlace E),
      1 < v (((lineIdele a u m)⁻¹.val * y (Y.indexEquiv (.inr m))) w) := by
    simpa only [hL.mem_latticeMinus_iff, hy_string, true_and, mem_Ô, not_forall, not_le]
      using hy_notMem
  -- The factor that clears this pole is not a unit at `w`.
  have hm : m = m.rev := by
    by_contra hm
    exact h_pole.not_ge (by simpa [hm] using mem_Ô.1 (hy_line m) w)
  have hw : w ∈ P ∨ star w ∈ P := by
    by_contra hw
    exact h_pole.not_ge
      (by simpa only [ite_eq_left hm, finAdele_mul_apply (algebraMap E (𝔸f E) N), map_mul,
        hπ.v_algebraMap, ite_eq_right hw, one_mul] using mem_Ô.1 (hy_line m) w)
  exact ⟨m, w, hm, hw, h_pole⟩

/-- Let `Λ⁻ = Y.latticeMinus 1` and `Λ⁺ = Y.latticePlus 1` be the intersection with and the
projection to the span of the string of the lattice with basis `New.gradedLatticeBasis`, and let
`N = π π̄` be split and squarefree. If some vector of `Λ⁺` lies outside `Λ⁻`, then the length `s`
of the string is odd. -/
lemma odd_of_notMem_latticeMinus {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) (hy : y ∈ Y.latticePlus 1) (hy_notMem : y ∉ Y.latticeMinus 1) :
    Odd s := by
  obtain ⟨m, -, hm, -⟩ := hL.exists_pole_of_notMem_latticeMinus hπ hy hy_notMem
  exact odd_of_eq_rev hm

/-- Suppose `Y.SpansLattice a π u`: the lattice of `1` has, up to `GL(Ô)`, the basis
`gradedLatticeBasis` built from `a`, `π` and the unitary scale `u`. Let `Λ⁻ = Y.latticeMinus 1` and
`Λ⁺ = Y.latticePlus 1` be its intersection with and its projection to the span of the string. Let
`N = π π̄` be split and squarefree. A vector `y` of `Λ⁺` outside `Λ⁻` generates `Λ⁺` over `Λ⁻` at
some place `w` above `N`: every `z` in `Λ⁺` differs from a multiple `c • y` with `c ∈ Ô E` by a
vector whose component at `w` lies in `Λ⁻`. -/
lemma exists_place_generates_of_notMem_latticeMinus {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) (hy : y ∈ Y.latticePlus 1) (hy_notMem : y ∉ Y.latticeMinus 1) :
    ∃ w : FinPlace E, (w ∈ P ∨ star w ∈ P) ∧ ∀ z ∈ Y.latticePlus 1,
      ∃ c ∈ Ô E, (idem {w} : 𝔸f E) • (z - c • y) ∈ Y.latticeMinus 1 := by
  -- At a place `w` where the middle coordinate of `y` has a pole, it divides that of `z`.
  let coord (x : ι → 𝔸f E) (b : Fin s) : 𝔸f E :=
    (lineIdele a u b)⁻¹.val * x (Y.indexEquiv (.inr b))
  have h_plus (x : ι → 𝔸f E) : x ∈ Y.latticePlus 1 ↔ Y.stringProj x = x ∧
      ∀ b : Fin s, (if b = b.rev then algebraMap E (𝔸f E) N else 1) * coord x b ∈ Ô E :=
    hL.mem_latticePlus_iff hπ
  obtain ⟨hy_string, hy_line⟩ := (h_plus y).1 hy
  obtain ⟨m, w, hm, hw, (h_pole : 1 < v (coord y m w))⟩ :=
    hL.exists_pole_of_notMem_latticeMinus hπ hy hy_notMem
  refine ⟨w, hw, fun z hz ↦ ?_⟩
  obtain ⟨hz_string, hz_line⟩ := (h_plus z).1 hz
  -- The pole of the middle coordinate of `z` at `w` is at most simple.
  have hz_bound : WithZero.exp (-1) * v (coord z m w) ≤ 1 := by
    simpa only [ite_eq_left hm, finAdele_mul_apply (algebraMap E (𝔸f E) N), map_mul,
      hπ.v_algebraMap, ite_eq_left hw] using mem_Ô.1 (hz_line m) w
  have h_le_pole : v (coord z m w) ≤ v (coord y m w) :=
    calc v (coord z m w)
      _ ≤ WithZero.exp 1 := by rwa [WithZero.exp_neg, inv_mul_le_one₀ WithZero.exp_pos] at hz_bound
      _ ≤ v (coord y m w) := by
        simpa [← WithZero.lt_mul_exp_iff_le (zero_lt_one.trans h_pole).ne'] using h_pole
  obtain ⟨c, hc, h_quot⟩ : ∃ c ∈ Ô E, idem {w} * coord z m = coord y m * c := by
    refine exists_eq_mul_iff_v_le.2 fun w' ↦ ?_
    obtain rfl | hw' := eq_or_ne w' w
    · simpa [finAdele_mul_apply] using h_le_pole
    · simp [finAdele_mul_apply, hw']
  refine ⟨c, hc, hL.mem_latticeMinus_iff.2 ⟨by simp [hy_string, hz_string], fun b ↦ ?_⟩⟩
  suffices idem {w} * (coord z b - c * coord y b) ∈ Ô E by
    simpa [coord, mul_sub, mul_left_comm] using this
  by_cases hb : b = b.rev
  · -- The middle index is unique.
    obtain rfl : b = m := eq_of_eq_rev hb hm
    simp [mul_comm c, ← h_quot, mul_sub, ← mul_assoc, idem_mul_self]
  · exact mul_mem (idem_mem_Ô _) (sub_mem (by simpa [hb] using hz_line b)
      (mul_mem hc (by simpa [hb] using hy_line b)))

/-- Let `Λ⁻ = Y.latticeMinus 1` and `Λ⁺ = Y.latticePlus 1` be the intersection with and the
projection to the span of the string of the lattice with basis `New.gradedLatticeBasis`. If `y` is
a vector of `Λ⁺` outside `Λ⁻`, then `s` is odd and `y` generates `Λ⁺` over `Λ⁻` at some place `w`
above `N = π π̄`, that is, a place of `P` or a conjugate of one. -/
lemma odd_and_exists_place_of_notMem_latticeMinus {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) (hy : y ∈ Y.latticePlus 1) (hy_notMem : y ∉ Y.latticeMinus 1) :
    Odd s ∧
      ∃ w : FinPlace E, (w ∈ P ∨ star w ∈ P) ∧ ∀ z ∈ Y.latticePlus 1,
        ∃ c ∈ Ô E, (idem {w} : 𝔸f E) • (z - c • y) ∈ Y.latticeMinus 1 :=
  ⟨hL.odd_of_notMem_latticeMinus hπ hy hy_notMem,
    hL.exists_place_generates_of_notMem_latticeMinus hπ hy hy_notMem⟩

end Grading.SpansLattice

end New

end
