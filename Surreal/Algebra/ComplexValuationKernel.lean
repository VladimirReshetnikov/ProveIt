import Mathlib.Algebra.Ring.Aut
import Mathlib.Tactic.LinearCombination
import Surreal.Algebra.Modulus
import Surreal.Algebra.ExponentialProfile

/-!
# The extended valuation `w_K` and the surcomplex valuation kernel

This file proves `lem:wK` (with `eq:wK` and `eq:min`) and `thm:complex-kernel` of
`docs/surreal/exponential-automorphism-rigidity/article.tex`, in the generic form over an ordered
field `F` carrying an ordered exponential and a convex valuation.

## Setting

* `F` is an ordered field in which nonnegative elements are squares (`HasNonnegSquareRoots F`).
  The source asks for `F` real closed; every real closed field qualifies
  (`Surreal.hasNonnegSquareRoots_of_isRealClosed`), and nothing more is used.
* `K = F(i)` is `Surreal.Complexify F`, with conjugation `star` (bundled as `starRingAut`) and the
  `F`-valued modulus `Complexify.modulus`.
* `w : AddValuation F (WithTop Γ)` is a convex valuation (`IsConvexValuation w`, which is
  `eq:convex-monotone`). Nontriviality is `∃ x, x ≠ 0 ∧ w x ≠ 0`. The source's valuations are onto
  `Γ` by convention; that surjectivity is the explicit hypothesis `hsurj`, used exactly where it is
  needed.
* `E : OrderedExp F` is an ordered exponential in the sense of
  `Surreal/Algebra/ExponentialProfile.lean`, with the hypothesis `hinj : Function.Injective E`.
  The source's `E` is an increasing group isomorphism `(F, +) → (F_{>0}, ·)`, so injectivity is
  one of its hypotheses; the structure `OrderedExp` itself omits it. `log E` is the inverse of `E`
  on `F_{>0}` (`exp_log`, `log_exp`).
* `L E z = log |z|` (`eq:L`) is regarded as an element of `K`. `IsLAut E Φ` (`Aut_L(K)`) says that
  the field automorphism `Φ` of `K` satisfies `Φ (L z) = L (Φ z)` for `z ≠ 0`. Preservation of `F`
  and of conjugation is not assumed.
* The stabilizer of `𝒪_{w_K}` is expressed by `∀ z, 0 ≤ w_K (Φ z) ↔ 0 ≤ w_K z`. The induced action
  on `Γ` is any `τ : Γ → Γ` with `w_K (Φ z) = τ (w_K z)`. When `w` is onto `Γ`, such a `τ`
  exists for `Φ` in the stabilizer (`exists_valueMap_wK`) and is unique for every automorphism
  (`valueMap_wK_unique`, from `Surreal.ExponentialProfile.valueMap_unique` and
  `wK_surjective`). The action on `Γ/Δ` is encoded
  relationally: `Φ` acts trivially on `Γ/Δ` when `τ g - g ∈ Δ` for all `g`
  (`eq:relational-quotient`), as in `Surreal.ExponentialProfile.eq_id_of_coarsening`. The ordered
  quotient `Γ/Δ` itself is not constructed.

## Main results

* `wK` (`eq:wK`, `lem:wK`): the map `z ↦ w |z|` as a valuation on `K`. `wK_apply` is `eq:wK`,
  `wK_eq_min` is `eq:min` (`w_K (a + i b) = min (w a) (w b)`), `wK_algebraMap` says that `w_K`
  extends `w`, and `range_wK` says that `w_K` and `w` have the same values, hence the same value
  group. `lem_wK` bundles these.
* The structure of `L`-automorphisms needed for the kernel, reproved here from `eq:L` alone, as in
  the proof of `thm:L-classification`. `image_L` is `lem:range` (`L (K^×) = F`). `IsLAut.restrict`
  is the restriction `σ = Φ|_F`, an automorphism of `F` (`IsLAut.restrictEquiv`) commuting with
  `E` (`IsLAut.restrict_commute`). Moreover `Φ (a + i b) = σ a + σ b · Φ i` (`IsLAut.apply_eq`),
  with `Φ i = ± i` (`map_I_eq`). These three facts together give the form `eq:Sigma-form`; they
  are not bundled into one statement, and `thm:L-classification` itself is not claimed here. The
  identity and conjugation are `L`-automorphisms (`isLAut_refl`, `isLAut_conj`).
* `thm:complex-kernel`:
  - `eq_refl_or_eq_conj` gives the kernel on `Γ` in value-fixing form. An `L`-automorphism with
    `w_K (Φ z) = w_K z` for all `z ≠ 0` is the identity or conjugation. This needs neither
    surjectivity of `w` nor stabilization of `𝒪_{w_K}`.
  - `valueMap_eq_id_iff` states that the kernel is exactly `{id, conjugation}`: for an
    `L`-automorphism with action `τ`, `τ = id` iff `Φ` is the identity or conjugation.
    `conj_mem_kernel` records that conjugation is an `L`-automorphism fixing every value, so it
    lies in the stabilizer.
  - `eq_refl_or_eq_conj_of_coarsening` and `coarsening_iff` give the kernel on `Γ/Δ` for a proper
    convex subgroup `Δ`. Invariance of `Δ` under `τ` is not needed.
  - `eq_refl_of_map_I`, `eq_refl_of_map_I_of_coarsening`, `eq_of_valuation_eq_of_map_I` and
    `eq_of_coarsening_of_map_I` give faithfulness within the subgroup fixing `i`: both actions
    have trivial kernel there. They are also injective in the strong form. Two
    `L`-automorphisms with the same value on `i` and the same action on `Γ` (or on `Γ/Δ`, for
    the subgroup stabilizing `Δ`) are equal.
  - `complex_kernel` bundles the theorem for an `L`-automorphism in the stabilizer of
    `𝒪_{w_K}`.

## Pending

`cor:surcomplex`, the instantiation at `K = No[i]`, needs the actual surreal exponential as an
`OrderedExp` on the surreal field, which the project does not yet construct. The results above
apply verbatim once it is available. The action is not bundled as a group homomorphism from the
stabilizer subgroup of `RingAut K`. The definitions `log`, `L` and `IsLAut` duplicate those of the
classification module `Surreal/Algebra/LogModulusClassification.lean`, developed independently;
no bridge between the two `Aut_L(K)` predicates is stated yet.
-/

namespace Surreal.ComplexKernel

open Surreal.Complexify Surreal.ExponentialProfile

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [HasNonnegSquareRoots F]

/-! ### Coordinates of `F(i)` -/

omit [LinearOrder F] [IsStrictOrderedRing F] [HasNonnegSquareRoots F] in
/-- The embedding `F → F(i)` is injective. -/
theorem injective_algebraMap : Function.Injective (algebraMap F (Complexify F)) :=
  QuadraticAlgebra.algebraMap_injective

omit [LinearOrder F] [IsStrictOrderedRing F] [HasNonnegSquareRoots F] in
/-- The embedding `F → F(i)` does not vanish on nonzero elements. -/
theorem algebraMap_ne_zero {x : F} (hx : x ≠ 0) : algebraMap F (Complexify F) x ≠ 0 := by
  intro h
  apply hx
  apply injective_algebraMap
  rw [h, map_zero]

omit [LinearOrder F] [IsStrictOrderedRing F] [HasNonnegSquareRoots F] in
/-- The decomposition `z = a + b i` of an element of `F(i)`. -/
theorem re_add_im_mul_I (z : Complexify F) :
    algebraMap F (Complexify F) z.re + algebraMap F (Complexify F) z.im * I = z := by
  ext <;> simp

omit [HasNonnegSquareRoots F] in
/-- The two roots of `X² + 1` in `F(i)` are `i` and `-i`. -/
theorem eq_I_or_eq_neg_I {z : Complexify F} (h : z ^ 2 = -1) : z = I ∨ z = -I := by
  have h' : (z - I) * (z + I) = 0 := by
    linear_combination h - (I_sq : (I : Complexify F) ^ 2 = -1)
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact Or.inl (sub_eq_zero.1 h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h1)

omit [HasNonnegSquareRoots F] in
/-- Conjugation does not fix `i`. -/
theorem star_I_ne_I : star (I : Complexify F) ≠ I := by
  intro h
  have h' : -(1 : F) = 1 := by simpa using congrArg QuadraticAlgebra.im h
  linarith

omit [LinearOrder F] [IsStrictOrderedRing F] [HasNonnegSquareRoots F] in
/-- Conjugation fixes the elements of `F`. -/
theorem star_algebraMap (x : F) :
    star (algebraMap F (Complexify F) x) = algebraMap F (Complexify F) x := by
  ext <;> simp

/-! ### The extended valuation `w_K` (`lem:wK`) -/

section Valuation

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  (w : AddValuation F (WithTop Γ))

omit [HasNonnegSquareRoots F] in
/-- A convex valuation vanishes at `2` (the proof of `lem:wK`). -/
theorem valuation_two {w : AddValuation F (WithTop Γ)} (hw : IsConvexValuation w) : w 2 = 0 := by
  apply le_antisymm
  · have h := hw one_pos one_le_two
    rwa [w.map_one] at h
  · have h := w.map_add 1 1
    rwa [w.map_one, min_self, one_add_one_eq_two] at h

omit [HasNonnegSquareRoots F] in
/-- Positive elements comparable up to a factor `2` have the same convex valuation. -/
theorem valuation_eq_of_le_two_mul {w : AddValuation F (WithTop Γ)} (hw : IsConvexValuation w)
    {x y : F} (hx : 0 < x) (h1 : x ≤ y) (h2 : y ≤ 2 * x) : w y = w x := by
  apply le_antisymm (hw hx h1)
  have h := hw (hx.trans_le h1) h2
  rwa [w.map_mul, valuation_two hw, zero_add] at h

omit [HasNonnegSquareRoots F] in
/-- For a convex valuation, `|a| ≤ |b|` implies `w b ≤ w a`. -/
theorem valuation_le_of_abs_le {w : AddValuation F (WithTop Γ)} (hw : IsConvexValuation w)
    {a b : F} (hab : |a| ≤ |b|) : w b ≤ w a := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [w.map_zero]
    exact le_top
  · have h := hw (abs_pos.2 ha) hab
    rwa [valuation_abs, valuation_abs] at h

/-- The modulus is at most `|a| + |b|`. -/
theorem modulus_le_abs_add_abs (z : Complexify F) : modulus z ≤ |z.re| + |z.im| := by
  apply (sq_le_sq₀ (modulus_nonneg z) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
  rw [modulus_sq, normSq]
  nlinarith [sq_abs z.re, sq_abs z.im, mul_nonneg (abs_nonneg z.re) (abs_nonneg z.im)]

/-- `eq:min` for the modulus: `w |a + i b| = min (w a) (w b)`, from
`max (|a|, |b|) ≤ |a + i b| ≤ 2 max (|a|, |b|)` and `w 2 = 0`. -/
theorem valuation_modulus {w : AddValuation F (WithTop Γ)} (hw : IsConvexValuation w)
    (z : Complexify F) : w (modulus z) = min (w z.re) (w z.im) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hsum := modulus_le_abs_add_abs z
  have hpos : ∀ {a b : F}, |a| ≤ |b| → z.re = a ∨ z.re = b → z.im = a ∨ z.im = b → 0 < |b| := by
    intro a b hab hre him
    by_contra hb
    have hb0 : b = 0 := abs_nonpos_iff.1 (not_lt.1 hb)
    have ha0 : a = 0 := abs_nonpos_iff.1 (hab.trans (not_lt.1 hb))
    subst hb0 ha0
    apply hz
    ext
    · rcases hre with h | h <;> simpa using h
    · rcases him with h | h <;> simpa using h
  rcases le_total |z.re| |z.im| with h | h
  · have hb := hpos h (Or.inl rfl) (Or.inr rfl)
    rw [valuation_eq_of_le_two_mul hw hb (abs_im_le_modulus z) (by linarith), valuation_abs,
      min_eq_right (valuation_le_of_abs_le hw h)]
  · have hb := hpos h (Or.inr rfl) (Or.inl rfl)
    rw [valuation_eq_of_le_two_mul hw hb (abs_re_le_modulus z) (by linarith), valuation_abs,
      min_eq_left (valuation_le_of_abs_le hw h)]

/-- `eq:wK`, `lem:wK`: for a convex valuation `w` on `F`, `w_K z = w |z|` is a valuation on
`K = F(i)`. -/
noncomputable def wK (hw : IsConvexValuation w) : AddValuation (Complexify F) (WithTop Γ) :=
  AddValuation.of (fun z => w (modulus z)) (by simp) (by simp)
    (fun z z' => by
      simp only [valuation_modulus hw, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
      exact le_min ((min_le_min (min_le_left _ _) (min_le_left _ _)).trans (w.map_add _ _))
        ((min_le_min (min_le_right _ _) (min_le_right _ _)).trans (w.map_add _ _)))
    (fun z z' => by simp only [modulus_mul, w.map_mul])

variable {w}

/-- `eq:wK`: `w_K z = w |z|`. -/
theorem wK_apply (hw : IsConvexValuation w) (z : Complexify F) : wK w hw z = w (modulus z) :=
  rfl

/-- `eq:min`: `w_K (a + i b) = min (w a) (w b)`, with `w 0 = ∞`. -/
theorem wK_eq_min (hw : IsConvexValuation w) (z : Complexify F) :
    wK w hw z = min (w z.re) (w z.im) :=
  valuation_modulus hw z

/-- `lem:wK`: `w_K` extends `w`. -/
theorem wK_algebraMap (hw : IsConvexValuation w) (x : F) :
    wK w hw (algebraMap F (Complexify F) x) = w x := by
  rw [wK_apply, modulus_algebraMap, valuation_abs]

/-- `lem:wK`: `w_K` and `w` take the same values, so they have the same value group. -/
theorem range_wK (hw : IsConvexValuation w) : Set.range (wK w hw) = Set.range w := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨modulus z, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨algebraMap F (Complexify F) x, wK_algebraMap hw x⟩

/-- `w_K` is onto `Γ` when `w` is. -/
theorem wK_surjective (hw : IsConvexValuation w) (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) :
    ∀ γ : Γ, ∃ z : Complexify F, wK w hw z = γ := fun γ => by
  obtain ⟨y, hy⟩ := hsurj γ
  exact ⟨algebraMap F (Complexify F) y, by rw [wK_algebraMap, hy]⟩

/-- Conjugation fixes every value of `w_K`. -/
theorem wK_star (hw : IsConvexValuation w) (z : Complexify F) : wK w hw (star z) = wK w hw z := by
  rw [wK_apply, wK_apply, modulus_conj]

/-- `lem:wK`, bundled: for a convex valuation `w` on `F`, `w_K z = w |z|` (`eq:wK`) defines a
valuation on `K = F(i)` extending `w`, with the same values (so the same value group), and
`w_K (a + i b) = min (w a) (w b)` (`eq:min`). -/
theorem lem_wK (hw : IsConvexValuation w) :
    (∀ z, wK w hw z = w (modulus z)) ∧ (∀ x, wK w hw (algebraMap F (Complexify F) x) = w x) ∧
      Set.range (wK w hw) = Set.range w ∧ ∀ z, wK w hw z = min (w z.re) (w z.im) :=
  ⟨wK_apply hw, wK_algebraMap hw, range_wK hw, wK_eq_min hw⟩

end Valuation

/-! ### The logarithmic modulus `L` (`eq:L`) -/

section LogModulus

variable (E : OrderedExp F)

/-- The logarithm `log : F_{>0} → F`, the inverse of `E` on positive elements (junk value `0`
elsewhere). -/
noncomputable def log (y : F) : F :=
  if h : 0 < y then Classical.choose (E.surj y h) else 0

omit [HasNonnegSquareRoots F] in
/-- `E (log y) = y` for `y > 0`. -/
theorem exp_log {y : F} (hy : 0 < y) : E (log E y) = y := by
  rw [log, dif_pos hy]
  exact Classical.choose_spec (E.surj y hy)

omit [HasNonnegSquareRoots F] in
/-- `log (E x) = x` for an injective ordered exponential. -/
theorem log_exp (hinj : Function.Injective E) (x : F) : log E (E x) = x :=
  hinj (exp_log E (E.pos x))

/-- `eq:L`: the logarithmic modulus `L z = log |z|`, regarded as an element of `K`. -/
noncomputable def L (z : Complexify F) : Complexify F :=
  algebraMap F (Complexify F) (log E (modulus z))

/-- `Aut_L(K)`: the field automorphism `Φ` of `K` commutes with `L` on `K^×`. -/
def IsLAut (Φ : Complexify F ≃+* Complexify F) : Prop :=
  ∀ z, z ≠ 0 → Φ (L E z) = L E (Φ z)

/-- `L` on `F`: `L x = log |x|`. -/
theorem L_algebraMap (x : F) :
    L E (algebraMap F (Complexify F) x) = algebraMap F (Complexify F) (log E |x|) := by
  rw [L, modulus_algebraMap]

/-- `L (E x) = x` (the proof of `lem:range`). -/
theorem L_algebraMap_exp (hinj : Function.Injective E) (x : F) :
    L E (algebraMap F (Complexify F) (E x)) = algebraMap F (Complexify F) x := by
  rw [L_algebraMap, abs_of_pos (E.pos x), log_exp E hinj]

/-- `lem:range`: the image of `L` on `K^×` is exactly `F`. -/
theorem image_L (hinj : Function.Injective E) :
    L E '' {z | z ≠ 0} = Set.range (algebraMap F (Complexify F)) := by
  ext y
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, algebraMap_ne_zero (E.ne_zero x), L_algebraMap_exp E hinj x⟩

/-- The identity is an `L`-automorphism. -/
theorem isLAut_refl : IsLAut E (RingEquiv.refl (Complexify F)) := fun _ _ => rfl

/-- Conjugation is an `L`-automorphism. -/
theorem isLAut_conj : IsLAut E starRingAut := fun z _ => by
  simp only [starRingAut_apply, L, modulus_conj, star_algebraMap]

variable {E}

/-! ### The restriction of an `L`-automorphism to `F` -/

section Restrict

variable {Φ : Complexify F ≃+* Complexify F}

/-- An `L`-automorphism is `L`-compatible in the inverse direction as well. -/
theorem IsLAut.symm (hΦ : IsLAut E Φ) : IsLAut E Φ.symm := fun z hz => by
  have hz' : Φ.symm z ≠ 0 := (map_ne_zero Φ.symm).2 hz
  apply Φ.injective
  rw [RingEquiv.apply_symm_apply, hΦ _ hz', RingEquiv.apply_symm_apply]

/-- The proof of `thm:L-classification`: an `L`-automorphism maps `F = L(K^×)` into `F`. -/
theorem IsLAut.exists_algebraMap (hinj : Function.Injective E) (hΦ : IsLAut E Φ) (x : F) :
    ∃ y, Φ (algebraMap F (Complexify F) x) = algebraMap F (Complexify F) y :=
  ⟨log E (modulus (Φ (algebraMap F (Complexify F) (E x)))), by
    rw [← L_algebraMap_exp E hinj x, hΦ _ (algebraMap_ne_zero (E.ne_zero x))]
    rfl⟩

/-- An `L`-automorphism maps `F` to elements with zero imaginary part. -/
theorem IsLAut.im_map_algebraMap (hinj : Function.Injective E) (hΦ : IsLAut E Φ) (x : F) :
    (Φ (algebraMap F (Complexify F) x)).im = 0 := by
  obtain ⟨y, hy⟩ := hΦ.exists_algebraMap hinj x
  rw [hy, QuadraticAlgebra.algebraMap_im]

/-- The restriction `σ = Φ|_F` of an `L`-automorphism, a ring endomorphism of `F`. -/
def IsLAut.restrict (hinj : Function.Injective E) (hΦ : IsLAut E Φ) : F →+* F where
  toFun x := (Φ (algebraMap F (Complexify F) x)).re
  map_one' := by simp only [map_one, QuadraticAlgebra.re_one]
  map_mul' x y := by
    simp only [map_mul, mul_re, hΦ.im_map_algebraMap hinj, mul_zero, sub_zero]
  map_zero' := by simp
  map_add' x y := by simp only [map_add, QuadraticAlgebra.re_add]

/-- `σ x` is the real part of `Φ x`. -/
theorem IsLAut.restrict_apply (hinj : Function.Injective E) (hΦ : IsLAut E Φ) (x : F) :
    hΦ.restrict hinj x = (Φ (algebraMap F (Complexify F) x)).re :=
  rfl

/-- `Φ x = σ x` for `x ∈ F`. -/
theorem IsLAut.algebraMap_restrict (hinj : Function.Injective E) (hΦ : IsLAut E Φ) (x : F) :
    algebraMap F (Complexify F) (hΦ.restrict hinj x) = Φ (algebraMap F (Complexify F) x) := by
  obtain ⟨y, hy⟩ := hΦ.exists_algebraMap hinj x
  rw [IsLAut.restrict_apply, hy, QuadraticAlgebra.algebraMap_re]

/-- The restriction is onto: `Φ⁻¹` also maps `F` into `F`, so `Φ (F) = F`. -/
theorem IsLAut.restrict_surjective (hinj : Function.Injective E) (hΦ : IsLAut E Φ) :
    Function.Surjective (hΦ.restrict hinj) := by
  intro y
  obtain ⟨x, hx⟩ := hΦ.symm.exists_algebraMap hinj y
  refine ⟨x, injective_algebraMap ?_⟩
  rw [hΦ.algebraMap_restrict hinj, ← hx, RingEquiv.apply_symm_apply]

/-- The restriction `σ = Φ|_F` as a field automorphism of `F`. -/
noncomputable def IsLAut.restrictEquiv (hinj : Function.Injective E) (hΦ : IsLAut E Φ) :
    F ≃+* F :=
  RingEquiv.ofBijective (hΦ.restrict hinj)
    ⟨(hΦ.restrict hinj).injective, hΦ.restrict_surjective hinj⟩

/-- The bundled automorphism `IsLAut.restrictEquiv` agrees with `IsLAut.restrict`. -/
theorem IsLAut.restrictEquiv_apply (hinj : Function.Injective E) (hΦ : IsLAut E Φ) (x : F) :
    hΦ.restrictEquiv hinj x = hΦ.restrict hinj x :=
  rfl

/-- The restriction maps `E x` to a positive element, since `E x = E (x/2)²`. -/
theorem IsLAut.restrict_exp_pos (hinj : Function.Injective E) (hΦ : IsLAut E Φ) (x : F) :
    0 < hΦ.restrict hinj (E x) := by
  have hsq : E x = E (x / 2) * E (x / 2) := by rw [← E.map_add, add_halves]
  have hne : hΦ.restrict hinj (E x) ≠ 0 := (map_ne_zero _).2 (E.ne_zero x)
  rw [hsq, map_mul] at hne ⊢
  exact lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm hne)

/-- `σ (log |y|) = log |σ y|` for `y ≠ 0` (commutation with `L` on `F`). -/
theorem IsLAut.restrict_log (hinj : Function.Injective E) (hΦ : IsLAut E Φ) {y : F}
    (hy : y ≠ 0) : hΦ.restrict hinj (log E |y|) = log E |hΦ.restrict hinj y| := by
  have h := hΦ _ (algebraMap_ne_zero hy)
  simp only [L_algebraMap, ← hΦ.algebraMap_restrict hinj] at h
  exact injective_algebraMap h

/-- The proof of `thm:L-classification`: the restriction `σ` commutes with `E`. -/
theorem IsLAut.restrict_commute (hinj : Function.Injective E) (hΦ : IsLAut E Φ) (x : F) :
    hΦ.restrict hinj (E x) = E (hΦ.restrict hinj x) := by
  have h := hΦ.restrict_log hinj (E.ne_zero x)
  rw [abs_of_pos (E.pos x), log_exp E hinj, abs_of_pos (hΦ.restrict_exp_pos hinj x)] at h
  rw [h, exp_log E (hΦ.restrict_exp_pos hinj x)]

/-- The form of `eq:Sigma-form` before `Φ i = ± i` is identified (see `map_I_eq`) and before
`σ` is shown to commute with `E` (see `IsLAut.restrict_commute`):
`Φ (a + i b) = σ a + σ b · Φ i`. -/
theorem IsLAut.apply_eq (hinj : Function.Injective E) (hΦ : IsLAut E Φ) (z : Complexify F) :
    Φ z = algebraMap F (Complexify F) (hΦ.restrict hinj z.re) +
      algebraMap F (Complexify F) (hΦ.restrict hinj z.im) * Φ I := by
  conv_lhs => rw [← re_add_im_mul_I z]
  rw [map_add, map_mul, hΦ.algebraMap_restrict hinj, hΦ.algebraMap_restrict hinj]

omit [HasNonnegSquareRoots F] in
/-- A field automorphism of `K` maps `i` to `i` or `-i`. -/
theorem map_I_eq (Φ : Complexify F ≃+* Complexify F) : Φ I = I ∨ Φ I = -I :=
  eq_I_or_eq_neg_I (by rw [← map_pow, I_sq, map_neg, map_one])

/-- An `L`-automorphism restricting to the identity on `F` is the identity or conjugation. -/
theorem IsLAut.eq_refl_or_eq_conj (hinj : Function.Injective E) (hΦ : IsLAut E Φ)
    (hσ : ∀ x, hΦ.restrict hinj x = x) : Φ = RingEquiv.refl _ ∨ Φ = starRingAut := by
  rcases map_I_eq Φ with h | h
  · left
    refine RingEquiv.ext fun z => ?_
    rw [hΦ.apply_eq hinj, hσ, hσ, h, re_add_im_mul_I]
    rfl
  · right
    refine RingEquiv.ext fun z => ?_
    rw [hΦ.apply_eq hinj, hσ, hσ, h, starRingAut_apply]
    ext <;> simp

/-- Two `L`-automorphisms with the same restriction to `F` and the same value on `i` are
equal. -/
theorem IsLAut.eq_of_restrict_eq (hinj : Function.Injective E)
    {Φ₁ Φ₂ : Complexify F ≃+* Complexify F} (h₁ : IsLAut E Φ₁) (h₂ : IsLAut E Φ₂) (hI : Φ₁ I = Φ₂ I)
    (hσ : ∀ x, h₁.restrict hinj x = h₂.restrict hinj x) : Φ₁ = Φ₂ := by
  refine RingEquiv.ext fun z => ?_
  rw [h₁.apply_eq hinj, h₂.apply_eq hinj, hI, hσ, hσ]

end Restrict

/-! ### The surcomplex valuation kernel (`thm:complex-kernel`) -/

section Kernel

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {w : AddValuation F (WithTop Γ)} {Φ : Complexify F ≃+* Complexify F}

/-- The values of `σ = Φ|_F` are read off from those of `Φ`: if `Φ` acts on `Γ` by `τ` through
`w_K`, then `σ` acts on `Γ` by `τ` through `w`. -/
theorem IsLAut.restrict_valueMap (hw : IsConvexValuation w) (hinj : Function.Injective E)
    (hΦ : IsLAut E Φ) {τ : Γ → Γ}
    (hτ : ∀ (z : Complexify F) (g : Γ), wK w hw z = g → wK w hw (Φ z) = τ g) :
    ∀ (y : F) (g : Γ), w y = g → w (hΦ.restrict hinj y) = τ g := fun y g hy => by
  rw [← wK_algebraMap hw, hΦ.algebraMap_restrict hinj]
  exact hτ _ g (by rw [wK_algebraMap, hy])

/-- Stabilizing `𝒪_{w_K}` implies stabilizing `𝒪_w = F ∩ 𝒪_{w_K}`. -/
theorem IsLAut.restrict_stab (hw : IsConvexValuation w) (hinj : Function.Injective E)
    (hΦ : IsLAut E Φ) (hstab : ∀ z, 0 ≤ wK w hw (Φ z) ↔ 0 ≤ wK w hw z) (y : F) :
    0 ≤ w (hΦ.restrict hinj y) ↔ 0 ≤ w y := by
  rw [← wK_algebraMap hw, hΦ.algebraMap_restrict hinj, hstab, wK_algebraMap]

/-- The induced action on `Γ` of an automorphism of `K` stabilizing `𝒪_{w_K}`, for `w` onto `Γ`:
some `τ : Γ → Γ` has `w_K (Φ z) = τ (w_K z)` for `z ≠ 0`. -/
theorem exists_valueMap_wK (hw : IsConvexValuation w) (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ)
    (hstab : ∀ z, 0 ≤ wK w hw (Φ z) ↔ 0 ≤ wK w hw z) :
    ∃ τ : Γ → Γ, ∀ (z : Complexify F) (g : Γ), wK w hw z = g → wK w hw (Φ z) = τ g :=
  exists_valueMap (wK w hw) (wK_surjective hw hsurj) (σ := (Φ : Complexify F →+* Complexify F))
    hstab

/-- The induced action on `Γ` is unique when `w` is onto `Γ`: two maps `τ`, `τ'` with
`w_K (Φ z) = τ (w_K z)` and `w_K (Φ z) = τ' (w_K z)` coincide. -/
theorem valueMap_wK_unique (hw : IsConvexValuation w) (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ)
    {τ τ' : Γ → Γ} (hτ : ∀ (z : Complexify F) (g : Γ), wK w hw z = g → wK w hw (Φ z) = τ g)
    (hτ' : ∀ (z : Complexify F) (g : Γ), wK w hw z = g → wK w hw (Φ z) = τ' g) : τ = τ' :=
  valueMap_unique (wK w hw) (wK_surjective hw hsurj) (σ := (Φ : Complexify F →+* Complexify F))
    hτ hτ'

/-- `thm:complex-kernel`, the kernel on `Γ` in value-fixing form: let `w` be a nontrivial convex
valuation and `E` an injective ordered exponential. An `L`-automorphism `Φ` of `K = F(i)` with
`w_K (Φ z) = w_K z` for every `z ≠ 0` is the identity or conjugation. -/
theorem eq_refl_or_eq_conj (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hinj : Function.Injective E) (hΦ : IsLAut E Φ)
    (hval : ∀ z, z ≠ 0 → wK w hw (Φ z) = wK w hw z) :
    Φ = RingEquiv.refl _ ∨ Φ = starRingAut := by
  have hval' : ∀ y : F, y ≠ 0 → w (hΦ.restrict hinj y) = w y := fun y hy => by
    rw [← wK_algebraMap hw, hΦ.algebraMap_restrict hinj, hval _ (algebraMap_ne_zero hy),
      wK_algebraMap]
  have hσ := eq_id_of_commute E hw hnt hval' (hΦ.restrict_commute hinj)
  exact hΦ.eq_refl_or_eq_conj hinj fun x => RingHom.congr_fun hσ x

omit [LinearOrder F] [IsStrictOrderedRing F] [HasNonnegSquareRoots F] in
/-- The identity and conjugation fix every element of `F`. -/
theorem map_algebraMap_of_eq_refl_or_eq_conj (h : Φ = RingEquiv.refl _ ∨ Φ = starRingAut)
    (y : F) : Φ (algebraMap F (Complexify F) y) = algebraMap F (Complexify F) y := by
  rcases h with rfl | rfl
  · rfl
  · rw [starRingAut_apply, star_algebraMap]

/-- `thm:complex-kernel`: the kernel of the action on `Γ` is exactly `{id, conjugation}`. For an
`L`-automorphism `Φ` acting on `Γ` by `τ` (`w_K (Φ z) = τ (w_K z)`), with `w` a nontrivial convex
valuation onto `Γ` and `E` an injective ordered exponential, `τ = id` if and only if `Φ` is the
identity or conjugation. -/
theorem valueMap_eq_id_iff (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) (hinj : Function.Injective E) (hΦ : IsLAut E Φ)
    {τ : Γ → Γ} (hτ : ∀ (z : Complexify F) (g : Γ), wK w hw z = g → wK w hw (Φ z) = τ g) :
    τ = id ↔ Φ = RingEquiv.refl _ ∨ Φ = starRingAut := by
  constructor
  · rintro rfl
    refine eq_refl_or_eq_conj hw hnt hinj hΦ fun z hz => ?_
    obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.1 ((wK w hw).ne_top_iff.2 hz)
    rw [hτ z g hg.symm, ← hg]
    rfl
  · intro h
    funext g
    obtain ⟨y, hy⟩ := hsurj g
    have h' := hτ (algebraMap F (Complexify F) y) g (by rw [wK_algebraMap, hy])
    rw [map_algebraMap_of_eq_refl_or_eq_conj h, wK_algebraMap, hy] at h'
    exact (WithTop.coe_injective h').symm

/-- `thm:complex-kernel`, membership: conjugation is an `L`-automorphism fixing every value of
`w_K`; in particular it stabilizes `𝒪_{w_K}`. -/
theorem conj_mem_kernel (hw : IsConvexValuation w) :
    IsLAut E starRingAut ∧ (∀ z, 0 ≤ wK w hw (starRingAut z) ↔ 0 ≤ wK w hw z) ∧
      ∀ z, wK w hw (starRingAut z) = wK w hw z := by
  refine ⟨isLAut_conj E, fun z => ?_, fun z => ?_⟩
  · rw [starRingAut_apply, wK_star]
  · rw [starRingAut_apply, wK_star]

/-- `thm:complex-kernel`, coarsening: let `w` be a nontrivial convex valuation onto `Γ`, `E` an
injective ordered exponential, and `Δ` a proper convex subgroup of `Γ`. An `L`-automorphism acting
on `Γ` by `τ` and trivially on `Γ/Δ` (`τ g - g ∈ Δ` for all `g`) is the identity or conjugation.
Invariance of `Δ` under `τ` is not needed. -/
theorem eq_refl_or_eq_conj_of_coarsening (hw : IsConvexValuation w)
    (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ)
    (hinj : Function.Injective E) (hΦ : IsLAut E Φ) {τ : Γ → Γ}
    (hτ : ∀ (z : Complexify F) (g : Γ), wK w hw z = g → wK w hw (Φ z) = τ g)
    {Δ : AddSubgroup Γ} (hΔc : (Δ : Set Γ).OrdConnected) (hΔ : Δ ≠ ⊤)
    (hid : ∀ g, τ g - g ∈ Δ) : Φ = RingEquiv.refl _ ∨ Φ = starRingAut :=
  hΦ.eq_refl_or_eq_conj hinj fun x => RingHom.congr_fun
    (eq_id_of_coarsening E hw hnt hsurj (hΦ.restrict_commute hinj)
      (hΦ.restrict_valueMap hw hinj hτ) hΔc hΔ hid) x

/-- `thm:complex-kernel`, coarsening: for `w`, `E` as above and a proper convex subgroup `Δ`, the
kernel of the action on `Γ/Δ` is again `{id, conjugation}`: `Φ` acts trivially on `Γ/Δ` if and
only if it is the identity or conjugation. -/
theorem coarsening_iff (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) (hinj : Function.Injective E) (hΦ : IsLAut E Φ)
    {τ : Γ → Γ} (hτ : ∀ (z : Complexify F) (g : Γ), wK w hw z = g → wK w hw (Φ z) = τ g)
    {Δ : AddSubgroup Γ} (hΔc : (Δ : Set Γ).OrdConnected) (hΔ : Δ ≠ ⊤) :
    (∀ g, τ g - g ∈ Δ) ↔ Φ = RingEquiv.refl _ ∨ Φ = starRingAut := by
  refine ⟨eq_refl_or_eq_conj_of_coarsening hw hnt hsurj hinj hΦ hτ hΔc hΔ, fun h g => ?_⟩
  rw [(valueMap_eq_id_iff hw hnt hsurj hinj hΦ hτ).2 h, id, sub_self]
  exact Δ.zero_mem

omit [HasNonnegSquareRoots F] in
/-- Among the identity and conjugation, only the identity fixes `i`. -/
theorem eq_refl_of_map_I_of_or (hI : Φ I = I) (h : Φ = RingEquiv.refl _ ∨ Φ = starRingAut) :
    Φ = RingEquiv.refl _ := by
  rcases h with h | h
  · exact h
  · rw [h, starRingAut_apply] at hI
    exact absurd hI star_I_ne_I

/-- `thm:complex-kernel`, faithfulness on `Γ` within the subgroup fixing `i`: an `L`-automorphism
fixing `i` and every value of `w_K` is the identity. -/
theorem eq_refl_of_map_I (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hinj : Function.Injective E) (hΦ : IsLAut E Φ) (hI : Φ I = I)
    (hval : ∀ z, z ≠ 0 → wK w hw (Φ z) = wK w hw z) : Φ = RingEquiv.refl _ :=
  eq_refl_of_map_I_of_or hI (eq_refl_or_eq_conj hw hnt hinj hΦ hval)

/-- `thm:complex-kernel`, faithfulness on `Γ/Δ` within the subgroup fixing `i`: an
`L`-automorphism fixing `i` and acting trivially on `Γ/Δ`, for a proper convex subgroup `Δ`, is the
identity. -/
theorem eq_refl_of_map_I_of_coarsening (hw : IsConvexValuation w)
    (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ)
    (hinj : Function.Injective E) (hΦ : IsLAut E Φ) (hI : Φ I = I) {τ : Γ → Γ}
    (hτ : ∀ (z : Complexify F) (g : Γ), wK w hw z = g → wK w hw (Φ z) = τ g)
    {Δ : AddSubgroup Γ} (hΔc : (Δ : Set Γ).OrdConnected) (hΔ : Δ ≠ ⊤)
    (hid : ∀ g, τ g - g ∈ Δ) : Φ = RingEquiv.refl _ :=
  eq_refl_of_map_I_of_or hI (eq_refl_or_eq_conj_of_coarsening hw hnt hsurj hinj hΦ hτ hΔc hΔ hid)

/-- `thm:complex-kernel`, faithfulness on `Γ` in injective form: two `L`-automorphisms with the
same value on `i` (for instance, both fixing `i`) acting in the same way on the values of `w_K`
are equal. -/
theorem eq_of_valuation_eq_of_map_I (hw : IsConvexValuation w)
    (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) (hinj : Function.Injective E)
    {Φ₁ Φ₂ : Complexify F ≃+* Complexify F} (h₁ : IsLAut E Φ₁) (h₂ : IsLAut E Φ₂)
    (hI : Φ₁ I = Φ₂ I) (hval : ∀ z, z ≠ 0 → wK w hw (Φ₁ z) = wK w hw (Φ₂ z)) : Φ₁ = Φ₂ := by
  have hval' : ∀ y : F, y ≠ 0 → w (h₁.restrict hinj y) = w (h₂.restrictEquiv hinj y) :=
    fun y hy => by
      rw [IsLAut.restrictEquiv_apply, ← wK_algebraMap hw,
        ← wK_algebraMap hw (h₂.restrict hinj y), h₁.algebraMap_restrict hinj,
        h₂.algebraMap_restrict hinj, hval _ (algebraMap_ne_zero hy)]
  have hσ := eq_of_valuation_eq E hw hnt (h₁.restrict hinj) (h₂.restrictEquiv hinj)
    (h₁.restrict_commute hinj) (h₂.restrict_commute hinj) hval'
  exact h₁.eq_of_restrict_eq hinj h₂ hI fun x => RingHom.congr_fun hσ x

/-- `thm:complex-kernel`, faithfulness on `Γ/Δ` in injective form: let `Φ₁`, `Φ₂` be
`L`-automorphisms with the same value on `i`, acting on `Γ` by `τ₁`, `τ₂`, where `Φ₂` stabilizes
`𝒪_{w_K}` and `τ₂` stabilizes the proper convex subgroup `Δ`. If they induce the same map on
`Γ/Δ` (`τ₁ g - τ₂ g ∈ Δ` for all `g`), then `Φ₁ = Φ₂`. -/
theorem eq_of_coarsening_of_map_I (hw : IsConvexValuation w)
    (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ)
    (hinj : Function.Injective E) {Φ₁ Φ₂ : Complexify F ≃+* Complexify F} (h₁ : IsLAut E Φ₁)
    (h₂ : IsLAut E Φ₂) (hI : Φ₁ I = Φ₂ I) (hstab₂ : ∀ z, 0 ≤ wK w hw (Φ₂ z) ↔ 0 ≤ wK w hw z)
    {τ₁ τ₂ : Γ → Γ} (hτ₁ : ∀ (z : Complexify F) (g : Γ), wK w hw z = g → wK w hw (Φ₁ z) = τ₁ g)
    (hτ₂ : ∀ (z : Complexify F) (g : Γ), wK w hw z = g → wK w hw (Φ₂ z) = τ₂ g)
    {Δ : AddSubgroup Γ} (hΔc : (Δ : Set Γ).OrdConnected) (hΔ : Δ ≠ ⊤)
    (hΔ₂ : ∀ g, τ₂ g ∈ Δ ↔ g ∈ Δ) (hq : ∀ g, τ₁ g - τ₂ g ∈ Δ) : Φ₁ = Φ₂ := by
  have hσ := eq_of_coarsening E hw hnt hsurj (h₁.restrictEquiv hinj) (h₂.restrictEquiv hinj)
    (h₁.restrict_commute hinj) (h₂.restrict_commute hinj) (h₂.restrict_stab hw hinj hstab₂)
    (h₁.restrict_valueMap hw hinj hτ₁) (h₂.restrict_valueMap hw hinj hτ₂) hΔc hΔ hΔ₂ hq
  exact h₁.eq_of_restrict_eq hinj h₂ hI fun x => DFunLike.congr_fun hσ x

/-- `thm:complex-kernel`, bundled: let `w` be a nontrivial convex valuation onto `Γ`, `E` an
injective ordered exponential, and `Φ` an `L`-automorphism of `K = F(i)` stabilizing `𝒪_{w_K}`.
Then `Φ` acts on `Γ` by some `τ` (`w_K (Φ z) = τ (w_K z)`). This action is trivial exactly when
`Φ` is the identity or conjugation. For every proper convex subgroup `Δ`, the action on `Γ/Δ` is
trivial exactly when `Φ` is the identity or conjugation. If `Φ` fixes `i`, either action is
trivial exactly when `Φ` is the identity. -/
theorem complex_kernel (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) (hinj : Function.Injective E) (hΦ : IsLAut E Φ)
    (hstab : ∀ z, 0 ≤ wK w hw (Φ z) ↔ 0 ≤ wK w hw z) :
    ∃ τ : Γ → Γ, (∀ (z : Complexify F) (g : Γ), wK w hw z = g → wK w hw (Φ z) = τ g) ∧
      (τ = id ↔ Φ = RingEquiv.refl _ ∨ Φ = starRingAut) ∧
      (∀ Δ : AddSubgroup Γ, (Δ : Set Γ).OrdConnected → Δ ≠ ⊤ →
        ((∀ g, τ g - g ∈ Δ) ↔ Φ = RingEquiv.refl _ ∨ Φ = starRingAut)) ∧
      (Φ I = I → (τ = id ↔ Φ = RingEquiv.refl _)) ∧
      (Φ I = I → ∀ Δ : AddSubgroup Γ, (Δ : Set Γ).OrdConnected → Δ ≠ ⊤ →
        ((∀ g, τ g - g ∈ Δ) ↔ Φ = RingEquiv.refl _)) := by
  obtain ⟨τ, hτ⟩ := exists_valueMap_wK hw hsurj hstab
  have hker := valueMap_eq_id_iff hw hnt hsurj hinj hΦ hτ
  have hcoar := fun Δ hΔc hΔ => coarsening_iff (Δ := Δ) hw hnt hsurj hinj hΦ hτ hΔc hΔ
  refine ⟨τ, hτ, hker, hcoar, fun hI => ⟨fun h => eq_refl_of_map_I_of_or hI (hker.1 h),
    fun h => hker.2 (Or.inl h)⟩, fun hI Δ hΔc hΔ => ⟨fun h => eq_refl_of_map_I_of_or hI
      ((hcoar Δ hΔc hΔ).1 h), fun h => (hcoar Δ hΔc hΔ).2 (Or.inl h)⟩⟩

end Kernel

end LogModulus

end Surreal.ComplexKernel
