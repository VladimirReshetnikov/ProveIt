import Mathlib.Algebra.Ring.Aut
import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic.LinearCombination
import Surreal.Algebra.Modulus
import Surreal.Algebra.ExponentialProfile

/-!
# Logarithmic-modulus classification of automorphisms of `F(i)`

This file proves `lem:range` and `thm:L-classification` (with `eq:L` and `eq:Sigma-form`) of
`docs/surreal/exponential-automorphism-rigidity/article.tex`, in the generic form over an ordered
field `F` carrying an ordered exponential. It is the generic content of `eq:main-complex`.

## Setting

* `F` is an ordered field in which nonnegative elements are squares (`HasNonnegSquareRoots F`).
  The source asks for `F` real closed; every real closed field qualifies
  (`Surreal.hasNonnegSquareRoots_of_isRealClosed`), and nothing more is used.
* `E : OrderedExp F` is an ordered exponential in the sense of
  `Surreal/Algebra/ExponentialProfile.lean` (monotone, positive, additive-to-multiplicative, onto
  `F_{>0}`), together with the hypothesis `hinj : Function.Injective E`. The source's `E` is an
  increasing group isomorphism `(F, +) → (F_{>0}, ·)`, so injectivity is part of its hypotheses;
  `OrderedExp` itself omits it. `log E` is the inverse of `E` on `F_{>0}` (`exp_log`, `log_exp`),
  extended by `0` elsewhere.
* `K = F(i)` is `Surreal.Complexify F`, with its `F`-valued modulus `Complexify.modulus`.
  `L E z = log |z|` (`eq:L`) is regarded as an element of `K`; its value at `z = 0` is a junk
  value that is never used.
* `IsLAut E Φ` (`Aut_L(K)`) says that the field automorphism `Φ` of `K` satisfies
  `Φ (L z) = L (Φ z)` for `z ≠ 0`; preservation of `F` or of conjugation is not assumed.
  `IsExpAut E σ` (`Aut_exp(F)`) says that the field automorphism `σ` of `F` commutes with `E`.
* `extend σ ε` is the map `a + i b ↦ σ a + ε i σ b` of `eq:Sigma-form` (`extend_add_mul_I`), with
  the sign `ε ∈ C₂ = {1, -1}` represented by `ℤˣ`.

## Main results

* `image_L` (`lem:range`): `L (K^×) = F`.
* `IsLAut.image_algebraMap`: an `L`-automorphism maps `F` onto `F`; `IsLAut.restrict` is its
  restriction `σ = Φ|_F`, which is order preserving (`ringHom_monotone`) and exponential
  (`IsLAut.isExpAut_restrict`), and `IsLAut.eq_extend` gives `Φ = extend σ ε` with `Φ i = ε i`
  (`map_I_eq`, via `sq_eq_neg_one_iff`).
* `existsUnique_extend` (`thm:L-classification`, forward direction with uniqueness):
  every `Φ ∈ Aut_L(K)` is `extend σ ε` for a unique pair with `σ ∈ Aut_exp(F)`.
* `isLAut_extend` (`thm:L-classification`, converse): every `extend σ ε` with `σ ∈ Aut_exp(F)`
  lies in `Aut_L(K)`, through `modulus_extend` (`|Φ z| = σ |z|`) and `IsExpAut.map_log`.
  `isLAut_iff` combines both directions.
* `autLEquiv` (`thm:L-classification`, the consequence): the subgroup `autL E` of `RingAut K`
  is isomorphic, as a group, to the direct product `autExp E × ℤˣ`. The direct-product structure
  rests on `extend_mul`; `extend_refl_neg_one` identifies `extend id (-1)` with conjugation,
  `extend_mul_conj` records that every extension commutes with it, and
  `extend_eq_conj_or_one_iff` that the extensions `extend σ 1` meet `{id, conjugation}` only in
  the identity (the source's own argument for directness, not used by `autLEquiv`).

`extend` and `restrict` are defined over any commutative ring, and `ringHom_monotone`
(`ringHom_nonneg`, `ringHom_pos`) holds for every ring endomorphism of `F`.

## Pending

The surreal instantiation `eq:main-complex`, `Aut_L(No[i]) ≃ Aut_exp(No) × C₂`, needs the actual
surreal exponential `exp : No → No_{>0}` as an `OrderedExp`, which the project does not yet
construct. The results above apply verbatim once it is available.
-/

namespace Surreal.LogModulus

open Surreal.Complexify Surreal.ExponentialProfile

/-! ### Coordinates of `F(i)` -/

section Ring

variable {F : Type*} [CommRing F]

/-- The decomposition `z = a + b i` of an element of `F(i)`. -/
theorem algebraMap_re_add_im_mul_I (z : Complexify F) :
    algebraMap F (Complexify F) z.re + algebraMap F (Complexify F) z.im * I = z := by
  ext <;> simp

/-- An element with zero imaginary part is the image of its real part. -/
theorem algebraMap_re_of_im_eq_zero {z : Complexify F} (h : z.im = 0) :
    algebraMap F (Complexify F) z.re = z := by
  ext <;> simp [h]

/-! ### The coefficientwise extensions `eq:Sigma-form` -/

/-- A sign `ε ∈ ℤˣ` squares to `1` in `F`. -/
theorem units_cast_mul_self (ε : ℤˣ) : ((ε : ℤ) : F) * ((ε : ℤ) : F) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-- The underlying map `a + i b ↦ σ a + ε i σ b` of `eq:Sigma-form`. -/
def extendFun (σ : F → F) (ε : ℤˣ) (z : Complexify F) : Complexify F :=
  ⟨σ z.re, ((ε : ℤ) : F) * σ z.im⟩

@[simp] theorem re_extendFun (σ : F → F) (ε : ℤˣ) (z : Complexify F) :
    (extendFun σ ε z).re = σ z.re := rfl

@[simp] theorem im_extendFun (σ : F → F) (ε : ℤˣ) (z : Complexify F) :
    (extendFun σ ε z).im = ((ε : ℤ) : F) * σ z.im := rfl

/-- `eq:Sigma-form`: the automorphism `a + i b ↦ σ a + ε i σ b` of `F(i)` determined by an
automorphism `σ` of `F` and a sign `ε ∈ ℤˣ = {1, -1}` (for any commutative ring `F`). -/
def extend (σ : F ≃+* F) (ε : ℤˣ) : Complexify F ≃+* Complexify F where
  toFun := extendFun σ ε
  invFun := extendFun σ.symm ε
  left_inv z := by
    ext
    · simp
    · simp [← mul_assoc, units_cast_mul_self]
  right_inv z := by
    ext
    · simp
    · simp [← mul_assoc, units_cast_mul_self]
  map_mul' z w := by
    have he := units_cast_mul_self (F := F) ε
    ext
    · simp only [re_extendFun, im_extendFun, mul_re, map_sub, map_mul]
      linear_combination (σ z.im * σ w.im) * he
    · simp only [re_extendFun, im_extendFun, mul_im, map_add, map_mul]
      ring
  map_add' z w := by
    ext
    · simp
    · simp [mul_add]

variable (σ : F ≃+* F) (ε : ℤˣ)

@[simp] theorem re_extend (z : Complexify F) : (extend σ ε z).re = σ z.re := rfl

@[simp] theorem im_extend (z : Complexify F) :
    (extend σ ε z).im = ((ε : ℤ) : F) * σ z.im := rfl

theorem extend_algebraMap (x : F) :
    extend σ ε (algebraMap F (Complexify F) x) = algebraMap F (Complexify F) (σ x) := by
  ext <;> simp

theorem extend_I : extend σ ε I = ((ε : ℤ) : Complexify F) * I := by
  ext <;> simp

/-- The explicit formula of `eq:Sigma-form`: `σ a + ε i σ b` is the image of `a + i b`. -/
theorem extend_add_mul_I (a b : F) :
    extend σ ε (algebraMap F (Complexify F) a + I * algebraMap F (Complexify F) b) =
      algebraMap F (Complexify F) (σ a) +
        ((ε : ℤ) : Complexify F) * I * algebraMap F (Complexify F) (σ b) := by
  rw [map_add, map_mul, extend_algebraMap, extend_algebraMap, extend_I]

/-- The extensions compose coordinatewise: `(σ₁, ε₁) (σ₂, ε₂) ↦ (σ₁ σ₂, ε₁ ε₂)`. -/
theorem extend_mul (σ₁ σ₂ : F ≃+* F) (ε₁ ε₂ : ℤˣ) :
    extend σ₁ ε₁ * extend σ₂ ε₂ = extend (σ₁ * σ₂) (ε₁ * ε₂) := by
  refine RingEquiv.ext fun z => ?_
  ext
  · simp [RingAut.mul_apply]
  · simp [RingAut.mul_apply, mul_assoc]

@[simp] theorem extend_one : extend (1 : F ≃+* F) 1 = 1 := by
  refine RingEquiv.ext fun z => ?_
  ext <;> simp [RingAut.one_apply]

/-- `extend id (-1)` is conjugation `a + i b ↦ a - i b`. -/
theorem extend_refl_neg_one :
    extend (RingEquiv.refl F) (-1) = (starRingAut : Complexify F ≃+* Complexify F) := by
  refine RingEquiv.ext fun z => ?_
  ext <;> simp

/-- The coefficientwise extensions commute with conjugation. -/
theorem extend_mul_conj :
    extend σ ε * (starRingAut : Complexify F ≃+* Complexify F) = starRingAut * extend σ ε := by
  rw [← extend_refl_neg_one, extend_mul, extend_mul, mul_comm ε]
  congr 1

/-- An extension recovers `σ` on `F`. -/
theorem re_extend_algebraMap (x : F) :
    (extend σ ε (algebraMap F (Complexify F) x)).re = σ x := by
  simp

/-! ### Restriction to `F` -/

/-- The restriction to `F` of a ring automorphism of `F(i)` that maps `F` into `F` in both
directions. -/
def restrict (Φ : Complexify F ≃+* Complexify F)
    (h₁ : ∀ x, (Φ (algebraMap F (Complexify F) x)).im = 0)
    (h₂ : ∀ x, (Φ.symm (algebraMap F (Complexify F) x)).im = 0) : F ≃+* F where
  toFun x := (Φ (algebraMap F (Complexify F) x)).re
  invFun x := (Φ.symm (algebraMap F (Complexify F) x)).re
  left_inv x := by
    simp only
    rw [algebraMap_re_of_im_eq_zero (h₁ x), RingEquiv.symm_apply_apply,
      QuadraticAlgebra.algebraMap_re]
  right_inv x := by
    simp only
    rw [algebraMap_re_of_im_eq_zero (h₂ x), RingEquiv.apply_symm_apply,
      QuadraticAlgebra.algebraMap_re]
  map_mul' x y := by
    simp only [map_mul, mul_re, h₁ x, h₁ y, mul_zero, sub_zero]
  map_add' x y := by
    simp only [map_add, QuadraticAlgebra.re_add]

theorem restrict_apply (Φ : Complexify F ≃+* Complexify F) (h₁ h₂) (x : F) :
    restrict Φ h₁ h₂ x = (Φ (algebraMap F (Complexify F) x)).re := rfl

theorem algebraMap_restrict (Φ : Complexify F ≃+* Complexify F) (h₁ h₂) (x : F) :
    algebraMap F (Complexify F) (restrict Φ h₁ h₂ x) = Φ (algebraMap F (Complexify F) x) :=
  algebraMap_re_of_im_eq_zero (h₁ x)

end Ring

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-! ### The logarithm of an ordered exponential -/

section Log

variable (E : OrderedExp F)

/-- The logarithm of an ordered exponential: an inverse of `E` on `F_{>0}`, extended by `0` to
nonpositive arguments. -/
noncomputable def log (y : F) : F :=
  if h : 0 < y then Classical.choose (E.surj y h) else 0

theorem exp_log {y : F} (hy : 0 < y) : E (log E y) = y := by
  rw [log, dif_pos hy]
  exact Classical.choose_spec (E.surj y hy)

/-- For an injective ordered exponential, `log` is a left inverse of `E`. -/
theorem log_exp (hinj : Function.Injective E) (x : F) : log E (E x) = x :=
  hinj (exp_log E (E.pos x))

/-- `Aut_exp(F)`: the field automorphism `σ` of `F` commutes with `E`. -/
def IsExpAut (σ : F ≃+* F) : Prop :=
  ∀ x, σ (E x) = E (σ x)

variable {E}

/-- An exponential automorphism commutes with `log` on `F_{>0}`. -/
theorem IsExpAut.map_log (hinj : Function.Injective E) {σ : F ≃+* F} (hσ : IsExpAut E σ)
    {y : F} (hy : 0 < y) : σ (log E y) = log E (σ y) := by
  have h := hσ (log E y)
  rw [exp_log E hy] at h
  rw [h, log_exp E hinj]

theorem IsExpAut.trans {σ τ : F ≃+* F} (hσ : IsExpAut E σ) (hτ : IsExpAut E τ) :
    IsExpAut E (σ.trans τ) := by
  intro x
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, hσ, hτ]

theorem IsExpAut.symm {σ : F ≃+* F} (hσ : IsExpAut E σ) : IsExpAut E σ.symm := by
  intro x
  apply σ.injective
  rw [hσ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end Log

/-! ### Ring endomorphisms of `F` preserve order -/

section Order

variable [HasNonnegSquareRoots F] {G : Type*} [FunLike G F F] [RingHomClass G F F]

/-- Nonnegative elements are squares, so a ring endomorphism of `F` preserves nonnegativity. -/
theorem ringHom_nonneg (σ : G) {x : F} (hx : 0 ≤ x) : 0 ≤ σ x := by
  obtain ⟨y, -, rfl⟩ := HasNonnegSquareRoots.exists_nonneg_sq hx
  rw [map_pow]
  exact sq_nonneg _

/-- A ring endomorphism of `F` is order preserving. -/
theorem ringHom_monotone (σ : G) : Monotone σ := fun x y h => by
  have h' := ringHom_nonneg σ (sub_nonneg.2 h)
  rwa [map_sub, sub_nonneg] at h'

theorem ringHom_pos (σ : G) {x : F} (hx : 0 < x) : 0 < σ x :=
  lt_of_le_of_ne (ringHom_nonneg σ hx.le) ((map_ne_zero σ).2 hx.ne').symm

end Order

/-! ### Square roots of `-1` and the sign of an automorphism -/

section Sign

theorem I_ne_zero : (I : Complexify F) ≠ 0 := fun h => by
  simpa using congrArg QuadraticAlgebra.im h

/-- The only square roots of `-1` in `F(i)` are `i` and `-i`. -/
theorem sq_eq_neg_one_iff (z : Complexify F) : z ^ 2 = -1 ↔ z = I ∨ z = -I := by
  constructor
  · intro h
    have hI := I_sq (F := F)
    have hprod : (z - I) * (z + I) = 0 := by linear_combination h - hI
    rcases mul_eq_zero.1 hprod with h1 | h1
    · exact Or.inl (sub_eq_zero.1 h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
  · rintro (rfl | rfl)
    · exact I_sq
    · rw [neg_sq, I_sq]

open scoped Classical in
/-- The sign `ε ∈ ℤˣ` with `Φ i = ε i`. -/
noncomputable def unitSign (Φ : Complexify F ≃+* Complexify F) : ℤˣ :=
  if Φ I = I then 1 else -1

/-- Every field automorphism of `F(i)` sends `i` to `ε i` with `ε = ±1`. -/
theorem map_I_eq (Φ : Complexify F ≃+* Complexify F) :
    Φ I = ((unitSign Φ : ℤ) : Complexify F) * I := by
  have h : Φ I ^ 2 = -1 := by rw [← map_pow, I_sq, map_neg, map_one]
  unfold unitSign
  split_ifs with hI
  · simp [hI]
  · rcases (sq_eq_neg_one_iff _).1 h with h' | h'
    · exact absurd h' hI
    · simp [h']

@[simp] theorem unitSign_extend (σ : F ≃+* F) (ε : ℤˣ) : unitSign (extend σ ε) = ε := by
  have h := map_I_eq (extend σ ε)
  rw [extend_I] at h
  exact (Units.ext (Int.cast_injective (mul_right_cancel₀ I_ne_zero h))).symm

/-- Uniqueness in `eq:Sigma-form`: an extension determines `σ` and `ε`. -/
theorem extend_inj {σ σ' : F ≃+* F} {ε ε' : ℤˣ} :
    extend σ ε = extend σ' ε' ↔ σ = σ' ∧ ε = ε' := by
  constructor
  · intro h
    refine ⟨RingEquiv.ext fun x => ?_, ?_⟩
    · rw [← re_extend_algebraMap σ ε x, h, re_extend_algebraMap]
    · rw [← unitSign_extend σ ε, h, unitSign_extend]
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The coefficientwise extensions `extend σ 1` meet `{id, conjugation}` only in the identity.
This is the source's argument for the directness of the product in `thm:L-classification`; the
Lean isomorphism `autLEquiv` gets its direct-product structure from `extend_mul` instead. -/
theorem extend_eq_conj_or_one_iff (σ : F ≃+* F) :
    (extend σ 1 = starRingAut ∨ extend σ 1 = 1) ↔ σ = 1 := by
  rw [← extend_refl_neg_one, ← extend_one, extend_inj, extend_inj]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (by decide)
    · exact h
  · intro h
    exact Or.inr ⟨h, rfl⟩

/-- A ring automorphism of `F(i)` preserving `F` is `extend σ ε`, with `σ` its restriction and
`Φ i = ε i`. -/
theorem eq_extend_restrict (Φ : Complexify F ≃+* Complexify F) (h₁ h₂) :
    Φ = extend (restrict Φ h₁ h₂) (unitSign Φ) := by
  refine RingEquiv.ext fun z => ?_
  conv_lhs => rw [← algebraMap_re_add_im_mul_I z]
  rw [map_add, map_mul, ← algebraMap_restrict Φ h₁ h₂, ← algebraMap_restrict Φ h₁ h₂, map_I_eq]
  ext
  · simp
  · simp [mul_comm]

end Sign

/-! ### The logarithmic modulus and `Aut_L(K)` -/

section LogModulus

variable [HasNonnegSquareRoots F] (E : OrderedExp F)

/-- `eq:L`: the logarithmic modulus `L z = log |z|`, regarded as an element of `K = F(i)`.
Its value at `z = 0` is the junk value `log 0 = 0`; only `z ≠ 0` is ever used. -/
noncomputable def L (z : Complexify F) : Complexify F :=
  algebraMap F (Complexify F) (log E (modulus z))

@[simp] theorem im_L (z : Complexify F) : (L E z).im = 0 := rfl

theorem L_mem_range (z : Complexify F) : L E z ∈ Set.range (algebraMap F (Complexify F)) :=
  ⟨_, rfl⟩

theorem L_algebraMap {y : F} (hy : 0 < y) :
    L E (algebraMap F (Complexify F) y) = algebraMap F (Complexify F) (log E y) := by
  rw [L, modulus_algebraMap, abs_of_pos hy]

theorem L_algebraMap_exp (hinj : Function.Injective E) (x : F) :
    L E (algebraMap F (Complexify F) (E x)) = algebraMap F (Complexify F) x := by
  rw [L_algebraMap E (E.pos x), log_exp E hinj]

/-- `lem:range`: the image of `L` on `K^×` is exactly `F`. -/
theorem image_L (hinj : Function.Injective E) :
    L E '' {z | z ≠ 0} = Set.range (algebraMap F (Complexify F)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨z, -, rfl⟩
    exact L_mem_range E z
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, (map_ne_zero (algebraMap F (Complexify F))).2 (E.ne_zero x),
      L_algebraMap_exp E hinj x⟩

/-- `Aut_L(K)`: the field automorphism `Φ` of `K = F(i)` satisfies `Φ (L z) = L (Φ z)` for every
`z ≠ 0`. Preservation of `F` or of conjugation is not required. -/
def IsLAut (Φ : Complexify F ≃+* Complexify F) : Prop :=
  ∀ z, z ≠ 0 → Φ (L E z) = L E (Φ z)

variable {E}

theorem IsLAut.trans {Φ Ψ : Complexify F ≃+* Complexify F} (hΦ : IsLAut E Φ)
    (hΨ : IsLAut E Ψ) : IsLAut E (Φ.trans Ψ) := by
  intro z hz
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, hΦ z hz, hΨ _ ((map_ne_zero Φ).2 hz)]

theorem IsLAut.symm {Φ : Complexify F ≃+* Complexify F} (hΦ : IsLAut E Φ) :
    IsLAut E Φ.symm := by
  intro z hz
  apply Φ.injective
  rw [hΦ _ ((map_ne_zero Φ.symm).2 hz), RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-- An `L`-automorphism maps `F` into `F`. -/
theorem IsLAut.im_map_algebraMap (hinj : Function.Injective E)
    {Φ : Complexify F ≃+* Complexify F} (hΦ : IsLAut E Φ) (x : F) :
    (Φ (algebraMap F (Complexify F) x)).im = 0 := by
  rw [← L_algebraMap_exp E hinj x,
    hΦ _ ((map_ne_zero (algebraMap F (Complexify F))).2 (E.ne_zero x)), im_L]

/-- The first step of the proof of `thm:L-classification`: `Φ(F) = F`, from `lem:range`. -/
theorem IsLAut.image_algebraMap (hinj : Function.Injective E)
    {Φ : Complexify F ≃+* Complexify F} (hΦ : IsLAut E Φ) :
    Φ '' Set.range (algebraMap F (Complexify F)) = Set.range (algebraMap F (Complexify F)) := by
  refine Set.Subset.antisymm ?_ fun w hw => ?_
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, algebraMap_re_of_im_eq_zero (hΦ.im_map_algebraMap hinj x)⟩
  · obtain ⟨x, rfl⟩ := hw
    exact ⟨Φ.symm (algebraMap F (Complexify F) x),
      ⟨_, algebraMap_re_of_im_eq_zero (hΦ.symm.im_map_algebraMap hinj x)⟩,
      RingEquiv.apply_symm_apply _ _⟩

/-- The restriction `σ = Φ|_F` of an `L`-automorphism. -/
def IsLAut.restrict (hinj : Function.Injective E) {Φ : Complexify F ≃+* Complexify F}
    (hΦ : IsLAut E Φ) : F ≃+* F :=
  LogModulus.restrict Φ (hΦ.im_map_algebraMap hinj) (hΦ.symm.im_map_algebraMap hinj)

theorem IsLAut.algebraMap_restrict (hinj : Function.Injective E)
    {Φ : Complexify F ≃+* Complexify F} (hΦ : IsLAut E Φ) (x : F) :
    algebraMap F (Complexify F) (hΦ.restrict hinj x) = Φ (algebraMap F (Complexify F) x) :=
  LogModulus.algebraMap_restrict Φ _ _ x

/-- The restriction `σ = Φ|_F` of an `L`-automorphism commutes with `E`. -/
theorem IsLAut.isExpAut_restrict (hinj : Function.Injective E)
    {Φ : Complexify F ≃+* Complexify F} (hΦ : IsLAut E Φ) : IsExpAut E (hΦ.restrict hinj) := by
  have hlog : ∀ y : F, 0 < y → hΦ.restrict hinj (log E y) = log E (hΦ.restrict hinj y) := by
    intro y hy
    have h := hΦ _ ((map_ne_zero (algebraMap F (Complexify F))).2 hy.ne')
    rw [L_algebraMap E hy, ← hΦ.algebraMap_restrict hinj, ← hΦ.algebraMap_restrict hinj,
      L_algebraMap E (ringHom_pos (hΦ.restrict hinj) hy)] at h
    exact QuadraticAlgebra.algebraMap_injective h
  intro x
  have h := hlog (E x) (E.pos x)
  rw [log_exp E hinj] at h
  rw [h, exp_log E (ringHom_pos (hΦ.restrict hinj) (E.pos x))]

/-- `eq:Sigma-form` for an `L`-automorphism: `Φ = extend (Φ|_F) ε` with `ε = unitSign Φ`, so that
`Φ i = ε i` (`map_I_eq`). -/
theorem IsLAut.eq_extend (hinj : Function.Injective E) {Φ : Complexify F ≃+* Complexify F}
    (hΦ : IsLAut E Φ) : Φ = extend (hΦ.restrict hinj) (unitSign Φ) :=
  eq_extend_restrict Φ _ _

/-- The modulus of an extension: `|extend σ ε z| = σ |z|`. -/
theorem modulus_extend (σ : F ≃+* F) (ε : ℤˣ) (z : Complexify F) :
    modulus (extend σ ε z) = σ (modulus z) := by
  refine modulus_eq_of_nonneg_sq (ringHom_nonneg σ (modulus_nonneg z)) ?_
  rw [← map_pow, modulus_sq]
  simp only [normSq, re_extend, im_extend, map_add, map_pow]
  linear_combination (-(σ z.im) ^ 2) * units_cast_mul_self (F := F) ε

/-- `thm:L-classification`, converse: every map `a + i b ↦ σ a + ε i σ b` with
`σ ∈ Aut_exp(F)` belongs to `Aut_L(K)`. -/
theorem isLAut_extend (hinj : Function.Injective E) {σ : F ≃+* F} (hσ : IsExpAut E σ)
    (ε : ℤˣ) : IsLAut E (extend σ ε) := by
  intro z hz
  unfold L
  rw [extend_algebraMap, modulus_extend, hσ.map_log hinj (modulus_pos hz)]

/-- `thm:L-classification`: every `Φ ∈ Aut_L(K)` has the unique form
`Φ (a + i b) = σ a + ε i σ b` (`extend σ ε`, see `extend_add_mul_I`) with `ε ∈ {1, -1}` and
`σ ∈ Aut_exp(F)`. -/
theorem existsUnique_extend (hinj : Function.Injective E) {Φ : Complexify F ≃+* Complexify F}
    (hΦ : IsLAut E Φ) : ∃! p : (F ≃+* F) × ℤˣ, IsExpAut E p.1 ∧ Φ = extend p.1 p.2 := by
  refine ⟨(hΦ.restrict hinj, unitSign Φ), ⟨hΦ.isExpAut_restrict hinj, hΦ.eq_extend hinj⟩, ?_⟩
  rintro ⟨σ, ε⟩ ⟨-, h⟩
  obtain ⟨h1, h2⟩ := extend_inj.1 (h.symm.trans (hΦ.eq_extend hinj))
  exact Prod.ext h1 h2

/-- `thm:L-classification`, both directions: `Φ ∈ Aut_L(K)` if and only if `Φ = extend σ ε` for
some `σ ∈ Aut_exp(F)` and `ε ∈ {1, -1}`. -/
theorem isLAut_iff (hinj : Function.Injective E) (Φ : Complexify F ≃+* Complexify F) :
    IsLAut E Φ ↔ ∃ σ : F ≃+* F, ∃ ε : ℤˣ, IsExpAut E σ ∧ Φ = extend σ ε := by
  constructor
  · intro hΦ
    exact ⟨_, _, hΦ.isExpAut_restrict hinj, hΦ.eq_extend hinj⟩
  · rintro ⟨σ, ε, hσ, rfl⟩
    exact isLAut_extend hinj hσ ε

end LogModulus

/-! ### The groups `Aut_L(K)` and `Aut_exp(F)` -/

section Groups

variable (E : OrderedExp F)

/-- `Aut_exp(F)` as a subgroup of `RingAut F`. -/
def autExp : Subgroup (RingAut F) where
  carrier := {σ | IsExpAut E σ}
  mul_mem' ha hb := IsExpAut.trans hb ha
  one_mem' _ := rfl
  inv_mem' ha := IsExpAut.symm ha

theorem mem_autExp (σ : RingAut F) : σ ∈ autExp E ↔ IsExpAut E σ := Iff.rfl

variable [HasNonnegSquareRoots F]

/-- `Aut_L(K)` as a subgroup of `RingAut (F(i))`. -/
def autL : Subgroup (RingAut (Complexify F)) where
  carrier := {Φ | IsLAut E Φ}
  mul_mem' ha hb := IsLAut.trans hb ha
  one_mem' _ _ := rfl
  inv_mem' ha := IsLAut.symm ha

theorem mem_autL (Φ : RingAut (Complexify F)) : Φ ∈ autL E ↔ IsLAut E Φ := Iff.rfl

/-- The extension map `Aut_exp(F) × C₂ → Aut_L(K)`, `(σ, ε) ↦ extend σ ε`, is a group
isomorphism. -/
noncomputable def extendMulEquiv (hinj : Function.Injective E) : autExp E × ℤˣ ≃* autL E where
  toFun p := ⟨extend p.1.1 p.2, isLAut_extend hinj ((mem_autExp E _).1 p.1.2) p.2⟩
  invFun Φ :=
    (⟨((mem_autL E _).1 Φ.2).restrict hinj,
      ((mem_autL E _).1 Φ.2).isExpAut_restrict hinj⟩, unitSign Φ.1)
  left_inv p := by
    refine Prod.ext (Subtype.ext (RingEquiv.ext fun x => ?_)) ?_
    · exact re_extend_algebraMap p.1.1 p.2 x
    · exact unitSign_extend p.1.1 p.2
  right_inv Φ := Subtype.ext (((mem_autL E _).1 Φ.2).eq_extend hinj).symm
  map_mul' p q := Subtype.ext (extend_mul _ _ _ _).symm

/-- `thm:L-classification`, the consequence: `Aut_L(K) ≃ Aut_exp(F) × C₂` as groups, a direct
product, with `C₂ = ℤˣ`. -/
noncomputable def autLEquiv (hinj : Function.Injective E) : autL E ≃* autExp E × ℤˣ :=
  (extendMulEquiv E hinj).symm

theorem autLEquiv_symm_apply (hinj : Function.Injective E) (p : autExp E × ℤˣ) :
    ((autLEquiv E hinj).symm p : RingAut (Complexify F)) = extend p.1 p.2 := by
  rw [autLEquiv, MulEquiv.symm_symm]
  rfl

/-- The first component of `autLEquiv` is the restriction `Φ|_F`. -/
theorem autLEquiv_apply_fst (hinj : Function.Injective E) (Φ : autL E) (x : F) :
    ((autLEquiv E hinj Φ).1 : RingAut F) x = ((Φ : RingAut (Complexify F))
      (algebraMap F (Complexify F) x)).re := rfl

/-- The second component of `autLEquiv` is the sign `ε` with `Φ i = ε i`. -/
theorem autLEquiv_apply_snd (hinj : Function.Injective E) (Φ : autL E) :
    (autLEquiv E hinj Φ).2 = unitSign (Φ : RingAut (Complexify F)) := rfl

end Groups

end Surreal.LogModulus
