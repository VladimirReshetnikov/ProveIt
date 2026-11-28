import Lib.ClassField.HeckeCharacter.SplitTameCharacters

/-!
# Splitting characters

Here a pair of spaces is indexed by two characters `ν_S`, `ν_T` of `[U(1)]`; one can also use
splitting characters `χ_S`, `χ_T`. The two descriptions agree: `ν ↦ ν.spaceChar k`, the Hecke
character `y ↦ ν(y / ȳ) υ(y)⁻ᵏ` (with `υ` the splitting character from `WeilData`), is a bijection
onto the splitting characters of rank `k` (`HeckeChar.isSplitting_iff`). Here `divStar` is the map
`y ↦ y / ȳ` from the ideles onto the norm-one ideles `unitary (𝔸 E)`. The file also gives the rules
for products, inverses and hyperbolic planes, the character of `[U(1)]` that gives the power of `υ`
by minus the signature of a space, and the splitting characters of a pair with one character.

## Relation to the literature

Known result: splitting characters of a CM extension, described through Hilbert's Theorem 90.
Source: Harris–Kudla–Sweet (1996), §1.
-/

noncomputable section

namespace New

open WeilData Fintype

variable {E : Type} [Field E] [CMType E]

lemma divStar_eq_iff {y : (𝔸 E)ˣ} {u : unitary (𝔸 E)} :
    divStar y = u ↔ (y : 𝔸 E) = u * star (y : 𝔸 E) := by
  rw [Subtype.ext_iff, coe_divStar]
  exact Units.mul_inv_eq_iff_eq_mul (star y)

lemma divStar_eq_one_iff {x : (𝔸 E)ˣ} : divStar x = 1 ↔ star x = x := by
  rw [divStar_eq_iff, OneMemClass.coe_one, one_mul, Units.ext_iff, eq_comm, Units.coe_star]

variable [WeilData E]

/-- A Hecke character `ξ` that is trivial on the ideles of the totally real subfield, that is, on
the ideles fixed by conjugation, is a base change from `[U(1)]`: `ξ(y) = ν(y / ȳ)` for a character
`ν` of `[U(1)]`. -/
theorem HeckeChar.exists_baseChange_eq {ξ : HeckeChar E}
    (h_fixed : ∀ x : (𝔸 E)ˣ, star x = x → ξ.val x = 1) : ∃ ν : AutChar E, ν.baseChange = ξ := by
  -- The character descends along `f : y ↦ y / ȳ`, which is a quotient map by the open mapping
  -- theorem; the descended character is trivial on the points of `E` by Hilbert's Theorem 90.
  let f : (𝔸 E)ˣ →* unitary (𝔸 E) := (divStar : (𝔸 E)ˣ →ₜ* unitary (𝔸 E)).toMonoidHom
  have f_cont : Continuous f := (divStar : (𝔸 E)ˣ →ₜ* unitary (𝔸 E)).continuous_toFun
  have : SecondCountableTopology (𝔸 E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (𝔸 E)ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have : LocallyCompactSpace (unitary (𝔸 E)) :=
    isClosed_unitary.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have f_quot : Topology.IsQuotientMap f :=
    (f.isOpenMap_of_sigmaCompact divStar_surjective f_cont).isQuotientMap f_cont divStar_surjective
  have h_ker : f.ker ≤ ξ.val.toMonoidHom.ker := fun x hx ↦ h_fixed x (divStar_eq_one_iff.mp hx)
  let ν : unitary (𝔸 E) →* Circle :=
    f.liftOfSurjective divStar_surjective ⟨ξ.val.toMonoidHom, h_ker⟩
  have ν_f (x : (𝔸 E)ˣ) : ν (f x) = ξ.val x :=
    f.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv divStar_surjective) _ x
  have ν_cont : Continuous ν :=
    f_quot.continuous_iff.mpr (ξ.val.continuous_toFun.congr fun x ↦ (ν_f x).symm)
  -- A point `a` of `E` of norm one is `b / b̄` with `b ∈ Eˣ`, so its image `u` has
  -- `ν u = ξ(b) = 1`.
  have ν_eq_one (u : unitary (𝔸 E)) (a : E) (ha : toAdele a = (u : 𝔸 E)) : ν u = 1 := by
    have norm_a : a * star a = 1 := (toAdele (E := E)).injective <| by
      rw [map_mul, ← star_toAdele, ha, map_one]
      exact Unitary.coe_mul_star_self u
    obtain ⟨b, hb_ne, hb_eq⟩ := exists_eq_mul_star j_ne_zero star_j norm_a
    let y : (𝔸 E)ˣ := (Units.mk0 b hb_ne).map (toAdele (E := E)).toMonoidHom
    have f_y : f y = u := by
      refine divStar_eq_iff.mpr ?_
      show toAdele b = u * star (toAdele b)
      rw [← ha, star_toAdele, ← map_mul, ← hb_eq]
    rw [← f_y, ν_f, ξ.prop y ⟨b, rfl⟩]
  refine ⟨⟨⟨ν, ν_cont⟩, fun u ⟨a, ha⟩ ↦ ν_eq_one u a ha⟩, Subtype.ext ?_⟩
  ext x : 1
  exact ν_f x

/-- A Hecke character is a base change from `[U(1)]` if and only if it is trivial on the ideles
fixed by conjugation. -/
theorem HeckeChar.exists_baseChange_iff {ξ : HeckeChar E} :
    (∃ ν : AutChar E, ν.baseChange = ξ) ↔ ∀ x : (𝔸 E)ˣ, star x = x → ξ.val x = 1 := by
  refine ⟨?_, exists_baseChange_eq⟩
  rintro ⟨ν, rfl⟩ x hx
  show ν.val (divStar x) = 1
  rw [divStar_eq_one_iff.mpr hx, map_one]

/-- A splitting character for a space of rank `k`: a Hecke character whose restriction to the ideles
of the totally real subfield (the ideles fixed by conjugation) is that of `υ ^ k`. Classically this
restriction is `η ^ k`, with `η` the quadratic character of the CM extension; here we use only that
the restriction of `υ` has order at most two. -/
def HeckeChar.IsSplitting (χ : HeckeChar E) (k : ℕ) : Prop :=
  ∀ x : (𝔸 E)ˣ, star x = x → χ.val x = υ.val x ^ k

namespace AutChar

variable {ν ν' : AutChar E} {χ : HeckeChar E} {k l : ℕ}

lemma spaceChar_eq_iff : ν.spaceChar k = χ ↔ ν.baseChange = χ * υ ^ k := by
  rw [spaceChar, inv_pow, mul_inv_eq_iff_eq_mul]

/-- A Hecke character `χ` is a splitting character for rank `k` if and only if
`ν(y / ȳ) = χ(y) υ(y) ^ k` for exactly one character `ν` of `[U(1)]`. -/
theorem _root_.New.HeckeChar.isSplitting_iff :
    χ.IsSplitting k ↔ ∃! ν : AutChar E, ν.spaceChar k = χ := by
  -- Both sides say that `χ * υ ^ k` is trivial on the ideles fixed by conjugation, since `υ`
  -- takes values of order at most two there.
  have h_υ_inv (x : (𝔸 E)ˣ) (hx : star x = x) : (υ.val x)⁻¹ = υ.val x := by rw [← υ_star x, hx]
  have h_existsUnique_iff : (∃! ν : AutChar E, ν.spaceChar k = χ) ↔
      ∀ x : (𝔸 E)ˣ, star x = x → (χ * υ ^ k).val x = 1 := by
    simp only [spaceChar_eq_iff]
    rw [← baseChange_injective.mem_range_iff_existsUnique, Set.mem_range,
      HeckeChar.exists_baseChange_iff]
  rw [HeckeChar.IsSplitting, h_existsUnique_iff]
  refine forall₂_congr fun x hx ↦ ?_
  show χ.val x = υ.val x ^ k ↔ χ.val x * (υ.val ^ k) x = 1
  rw [ContinuousMonoidHom.pow_apply, mul_eq_one_iff_eq_inv, ← inv_pow, h_υ_inv x hx]

/-- The character `ν` of `[U(1)]` with `ν(y / ȳ) = χ(y) υ(y) ^ k`, for a splitting character `χ` of
rank `k`. The Weil representation `ω_{χ_S, χ_T}` is `pairWeil` at these characters for `χ_S` and
`χ_T`. -/
def _root_.New.HeckeChar.IsSplitting.autChar (h : χ.IsSplitting k) : AutChar E :=
  (HeckeChar.isSplitting_iff.mp h).choose

lemma spaceChar_autChar (h_split : χ.IsSplitting k) : h_split.autChar.spaceChar k = χ :=
  (HeckeChar.isSplitting_iff.mp h_split).choose_spec.left

/-- The splitting character of `ν * ν'` at rank `k + l` is the product of those of `ν` at rank `k`
and of `ν'` at rank `l`, as for an orthogonal sum of spaces. -/
lemma spaceChar_mul : (ν * ν').spaceChar (k + l) = ν.spaceChar k * ν'.spaceChar l := by
  rw [spaceChar, map_mul, pow_add, mul_mul_mul_comm, spaceChar, spaceChar]

/-- For a character `ν` of `[U(1)]` and `k : ℕ`, `ν.spaceChar k` is the Hecke character
x ↦ `ν (x / x̄) * υ x ^ (-k)` of `E`, where `υ` is the splitting character from `WeilData`.
Replacing `ν` by `ν⁻¹ * upsilonU1 ^ k`, where `upsilonU1` is the restriction of `υ` to the norm-one
ideles, inverts this rank-`k` Hecke character. -/
lemma spaceChar_inv_mul_upsilonU1_pow : (ν⁻¹ * upsilonU1 ^ k).spaceChar k = (ν.spaceChar k)⁻¹ := by
  simp only [spaceChar, map_mul, map_inv, map_pow, baseChange_upsilonU1, mul_inv]
  group

/-- Adding `l` hyperbolic planes, that is, raising the rank by `2 * l`, keeps the splitting
character if `ν` is multiplied by `upsilonU1 ^ l`. Here `ν.spaceChar k` is the Hecke character
`x ↦ ν (x / x̄) * υ x ^ (-k)` of `E`, where `υ` is the splitting character of the Weil data.
`upsilonU1` is the restriction of `υ` to the norm-one ideles. -/
lemma spaceChar_add_two_mul : (ν * upsilonU1 ^ l).spaceChar (k + 2 * l) = ν.spaceChar k := by
  simp only [spaceChar, map_mul, map_pow, baseChange_upsilonU1]
  group

/-- For signs `s : n → ℤˣ` of a space of rank `card n`, with `n₊ = negCount (-s)` signs `1` and
`n₋ = negCount s` signs `-1`, consider the standard character `stdChar s = upsilonU1 ^ n₋`, where
`upsilonU1` is the restriction to `U(1)` of the splitting character `υ` from `WeilData`. Its
rank-`card n` Hecke character `spaceChar` (x ↦ `stdChar s (x / x̄) * υ x ^ (-card n)`) is
`υ ^ (-(n₊ - n₋))`, the power of `υ` by minus the signature. -/
theorem spaceChar_stdChar {n : Type*} [Fintype n] (s : n → ℤˣ) :
    (stdChar s : AutChar E).spaceChar (card n) =
      υ ^ (-((Exchange.negCount (-s) : ℤ) - Exchange.negCount s)) := by
  -- `(υ ^ 2) ^ n₋ * υ⁻¹ ^ (n₊ + n₋) = υ ^ (n₋ - n₊)`
  rw [spaceChar, stdChar, map_pow, baseChange_upsilonU1, ← Exchange.negCount_neg_add s]
  group

/-- Let `E` be a CM field with Weil data, whose splitting character is `υ`. For a character `ν` of
`[U(1)]` and a finite type `n`, let `rankTwist ν n = ν · υ^⌊card n / 2⌋` (with `υ` restricted to
norm-one ideles). Its space character at rank `card n`, the Hecke character
`x ↦ (rankTwist ν n)(x / x̄) · υ(x)^(-card n)`, equals `ν.baseChange` if `card n` is even and
`ν.baseChange * υ⁻¹` if `card n` is odd. -/
theorem spaceChar_rankTwist_eq_ite (ν : AutChar E) (n : Type*) [Fintype n] :
    (rankTwist ν n).spaceChar (card n) =
      if Even (card n) then ν.baseChange else ν.baseChange * υ⁻¹ := by
  -- `rankTwist` adds `card n / 2` hyperbolic planes to a space of rank `card n % 2`.
  have h_mod_two : (rankTwist ν n).spaceChar (card n) = ν.spaceChar (card n % 2) := by
    rw [rankTwist, ← spaceChar_add_two_mul (ν := ν), Nat.mod_add_div]
  split_ifs with hn
  · rw [h_mod_two, Nat.even_iff.mp hn, spaceChar, pow_zero, mul_one]
  · rw [h_mod_two, Nat.not_even_iff.mp hn, spaceChar, pow_one]

/-- Let `E` be a CM field with Weil data, whose splitting character is `υ`. For a character `ν` of
`[U(1)]` and a finite type `n`, let `rankTwist ν⁻¹ n = ν⁻¹ · υ^⌊card n / 2⌋` (with `υ` restricted to
norm-one ideles). Its space character at rank `card n` is the Hecke character
`x ↦ (rankTwist ν⁻¹ n)(x / x̄) · υ(x)^(-card n)`. The inverse of that character equals
`ν.baseChange` if `card n` is even and `ν.baseChange * υ` if `card n` is odd. -/
theorem inv_spaceChar_rankTwist_inv (ν : AutChar E) (n : Type*) [Fintype n] :
    ((rankTwist ν⁻¹ n).spaceChar (card n))⁻¹ =
      if Even (card n) then ν.baseChange else ν.baseChange * υ := by
  rw [spaceChar_rankTwist_eq_ite, map_inv]
  split_ifs <;> simp [mul_comm]

end AutChar

end New

end
