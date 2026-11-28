import New.OneLift.HeckeValues.CharacterLiftNorm
import New.OneLift.TestedForms
import New.Reduction.Lattices.Heights

/-!
# The ratio of twisted to untwisted Hecke L-values, main pairs and regular families of twists

Consider a pair `(ν, z)`, a tame character `ϑ` with set of places `Q` and a sign `s = ±1` (by
default `1`). For these, `New.Data.CriticalPair.ratio` is the quotient
`|L(z, (ν ϑ^s)⁻¹)| / |L(z, ν⁻¹)|`, as a complex number. The remaining definitions record what the
congruence arguments need to know about a family of twists `θ ι`. The family has one twist for each
prime `ℓ` and isomorphism `ι : ℂ ≃ ℚ̄_ℓ` (`New.PrimePadicIso`).

## Main definitions

* `New.Data.goodLift`: the lift `New.Data.singleLift` restricted to good forms, whose range is the
  space of lifts.
* `New.Data.CriticalPair.IsRamified`, `New.Data.CriticalPair.IsMainPair`: ramified pairs and main
  pairs.
* `New.Data.denominatorBudget`: the bound for the sums over primes of the logarithmic denominator
  bounds.
* `New.Data.IsNegligible`: numbers `e ℓ ≥ 0` with `∑ e ℓ log ℓ ≤ x ^ C` over every finite set of
  primes.
* `New.Data.HasSmallRatios`: families of twists `θ ι` with modulus prime to `ℓ` whose powers have
  ratios of L-values of small height.
* `New.Data.IsRegularFamily`: regular families, that is, families with small ratios for whose powers
  the projections to the lifts have small denominators.

Notions from other files:
* `New.AutChar.L`: The partial Hecke L-function of the character x ↦ ν(x/x̄) of E.
* `New.Data.CriticalPair`: An integer 1 ≤ z ≤ `D.t` and a character ν of U(1)(𝔸) of weight −c, with
  z ≤ c(v) ≤ 4 `D.b` at every infinite place v and tame part ψ supported on the chosen places.
* `New.Data.Twist`, `New.Data.MFoldTwist`: A tame character whose tame part ψ_w (for an m-fold
  twist: each ψ_wⁿ, 1 ≤ n ≤ m) is non-trivial at every place w of its finite set Q.
* `New.HeightLe`: A bound for the height of a family of complex numbers indexed by the ι.

## Relation to the literature

See `New.Congruences.FitTwistsExist` for related work.
-/

namespace New.Data

/-!
## The ratio of twisted to untwisted Hecke L-values of a pair

`New.AutChar.L S` omits the Euler factors at `S` and its conjugate. The inverse in the denominator
does not change the L-value (`New.Data.CriticalPair.L_inv`).
-/

section LValueRatio

variable {P : Parameters} {D : Data P}

/-- The trivial twist has the trivial character of `U(1)(𝔸)`. -/
lemma Twist.toAutChar_one : (1 : D.Twist).toAutChar = 1 :=
  rfl

/-- The modulus `Q` of the trivial twist, its finite set of finite places, is empty. -/
lemma Twist.Q_one : (1 : D.Twist).Q = ∅ :=
  rfl

/-- The twist underlying the trivial `m`-fold twist is the trivial twist. -/
lemma MFoldTwist.toTwist_one : (1 : D.MFoldTwist).toTwist = 1 :=
  rfl

/-- Let `D` be admissible data, with CM field `E = D.E` and number of lifts `m = D.m`. The trivial
twist has the trivial character, underlies the trivial `m`-fold twist, and has empty modulus. -/
lemma toAutChar_one_and_toTwist_one_and_Q_one :
    ((1 : D.Twist).toAutChar = 1 ∧ (1 : D.MFoldTwist).toTwist = 1) ∧
      (1 : D.Twist).Q = ∅ :=
  ⟨⟨Twist.toAutChar_one, MFoldTwist.toTwist_one⟩, Twist.Q_one⟩

/-- For a pair `p = (ν, z)`, a tame character `ϑ` and a sign `s` (by default `1`), the ratio
`|L(z, (ν ϑ^s)⁻¹)| / |L(z, ν⁻¹)|`, as a complex number. Both L-functions omit the Euler factors at
the chosen places and their conjugates. The numerator also omits those at the places `Q` of `ϑ` and
their conjugates. -/
noncomputable def CriticalPair.ratio (p : D.CriticalPair) (ϑ : D.TameChar) (s : ℤˣ := 1) : ℂ :=
  (‖(p.character * ϑ.toAutChar ^ (s : ℤ))⁻¹.L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) p.z‖ /
    ‖p.character⁻¹.L {w : FinPlace D.E | D.IsChosen w} p.z‖ : ℂ)

end LValueRatio

/-!
## Lifts, ramified pairs, main pairs and regular families

Valuations at `ι : ℂ ≃ ℚ̄_ℓ` are written as norms: `v_ι (y) ≥ -β_ℓ` reads `‖ι y‖ ≤ exp β` with
`β = β_ℓ log ℓ`.
-/

section FitTwists

open Set Selmer

variable {P : Parameters} (D : Data P)

/-- An index type with `20 + (2 z - 20)` elements, so `2 z` for `z ≥ 10`: the basis of the
definite space `E ^ (2 z)` to which the character of a main pair is lifted, split into four blocks
of ranks `12`, `4`, `4` and `2 z - 20`. -/
abbrev RankOneIndex (z : ℕ) : Type := (Fin 12 ⊕ Fin 4 ⊕ Fin 4) ⊕ Fin (2 * z - 20)

/-- The theta lift `New.Data.singleLift` for the tame character `ϑ` and index `j`, restricted to the
good forms. It takes forms on the hermitian space `W_j = D.spaceW j` of rank `D.r` to forms on the
definite space `V` of rank `D.r + D.t`; `D.descentPair ϑ j` is the datum of this lift. The good
forms are the forms fixed by the principal congruence subgroup at the chosen places that lie in the
image of `D.e₀`, an idempotent of the group algebra of the product of the groups `GL_r (k_w)` over
the residue fields `k_w` of the chosen places. -/
noncomputable abbrev goodLift (ϑ : D.TameChar) (j : ℕ) :
    D.goodForms (D.spaceW j) →ₗ[ℂ] (D.descentPair ϑ j).FormV :=
  D.singleLift ϑ j ∘ₗ (D.goodForms (D.spaceW j)).subtype

/-- A pair `p = (ν, z)` is ramified if the tame part `ψ` of `ν`, a character `ψ_w` of the residue
field at each finite place `w` of `E`, is nontrivial exactly at the chosen places, those dividing
the integer `D.piM` of norm `p₀ p₁` of the imaginary quadratic field `K`. -/
def CriticalPair.IsRamified {D : Data P} (p : D.CriticalPair) : Prop :=
  ∀ w : FinPlace D.E, p.tamePart w ≠ 1 ↔ D.IsChosen w

/-- The pair `p = (ν, z)`, with `ν` of weight `-c`, is a main pair for `j`: the type
`RankOneIndex z` has `2 z` elements and `2 ≤ z` (`HasLiftRank`), `m < z ≤ r`, `1 ≤ j ≤ m`, the tame
part of `ν` is `D.chiMLocal ^ j`, and `w_j + r - t ≤ c ≤ w_j` at every infinite place. Here
`m = D.m` is the number of lifts, `r = D.r` the rank of the spaces `W_j` and `t = D.t = 5 r`;
`D.chiMLocal` is the fixed family of residue characters that is trivial off the chosen places, and
`w_j = D.liftWeight j` is minus the weight of the character of the `j`-th lift. -/
structure CriticalPair.IsMainPair {D : Data P} (p : D.CriticalPair) (j : ℕ) : Prop where
  /-- The type `RankOneIndex z` has `2 z` elements, and `2 ≤ z`. -/
  hasLiftRank : p.HasLiftRank (RankOneIndex p.z)
  /-- The point satisfies `m < z ≤ r`. -/
  z_mem : p.z ∈ Ioc D.m D.r
  /-- The index satisfies `1 ≤ j ≤ m`. -/
  j_mem : j ∈ D.LiftIndex
  /-- The tame part of `ν` is `ω ^ j`, with `ω = D.chiMLocal`. -/
  tamePart_eq : p.tamePart = D.chiMLocal ^ (j : ℤ)
  /-- The upper bound `c ≤ w_j` at each infinite place. -/
  negWeight_le (v : D.Φ) : p.negWeight v ≤ D.liftWeight j v
  /-- The lower bound `w_j + r - t ≤ c` at each infinite place, written without subtraction. -/
  le_negWeight (v : D.Φ) : D.liftWeight j v + D.r ≤ p.negWeight v + D.t

/-- Let `D` be admissible data, with CM field `E = D.E` and number of lifts `m = D.m`. If `p` is a
main pair for `j`, so in particular `1 ≤ j ≤ m` and the tame part is `ω ^ j` for the fixed family
`ω = D.chiMLocal` of residue characters, trivial off the chosen places and of order above `8 m` at
them, then `p` is ramified: its tame part is nontrivial exactly at the chosen places. -/
lemma CriticalPair.IsMainPair.isRamified {D : Data P} {p : D.CriticalPair} {j : ℕ}
    (hp : p.IsMainPair j) :
    p.IsRamified := by
  obtain ⟨hj_pos, hj_le⟩ : 1 ≤ j ∧ j ≤ D.m := hp.j_mem
  rw [CriticalPair.IsRamified, hp.tamePart_eq]
  exact D.chiMLocal_zpow_ne_one_iff_isChosen j (by omega) (by omega)

/-- The bound `denominatorBudget = f a log³ b / (m k)` for the sum over all primes of the
logarithmic denominator bounds. The numerator is `D.errorUnit`, with `f` the number of infinite
places of `E`, `b` the weight scale of the data and `a = x b` for `x` the length of the prime sum;
`m` is the number of lifts and `k = r + 1 - m`. -/
noncomputable abbrev denominatorBudget : ℝ := D.errorUnit / (D.m * D.k)

open scoped Classical in
/-- Let `Z` be the space of lifts from `W_j` for the twist `ϑ`, the range of `D.goodLift ϑ j` in the
forms on the space `V` of the lift datum `D.descentPair ϑ j`, and let `pr` be the orthogonal
projection to `Z`. Some operator `Λ` on `Z`, with `log |ι (det Λ)| ≥ -(dim Z) r β` for `r = D.r`,
makes `Λ (pr y)` integral at `ι` for every form `y` that is integral at `ι` and orthogonal to the
false lifts. A form is integral (`integralForms`) if all its values lie in the unit ball of the
`ℓ`-adic gauge at `ι`. The false lifts (`IsOrthogonalToFalseLifts`) are the forms orthogonal to `Z`,
in the image of the idempotent `D.e₀`, that are killed by the Hecke polynomial at its test value at
some split place off the level. -/
def ClearsProjection {ℓ : ℕ} [Fact ℓ.Prime] (ι : ℂ ≃+* PadicAlgCl ℓ) (ϑ : D.Twist) (j : ℕ)
    (β : ℝ) : Prop :=
  ∃ Λ : Module.End ℂ (D.goodLift ϑ j).range,
    Real.exp (-(Module.finrank ℂ (D.goodLift ϑ j).range * (D.r * β))) ≤ ‖ι Λ.det‖ ∧
    ∀ y ∈ LevelPlaces.LevelForm.integralForms ⟨(algebraMap (PadicAlgCl ℓ) ℂ_[ℓ]).comp ι.toRingHom⟩,
      (D.descentPair ϑ j).IsOrthogonalToFalseLifts D.e₀ (D.goodLift ϑ j).rangeᗮ y →
        (Λ ((D.goodLift ϑ j).range.orthogonalProjectionOnto y) : (D.descentPair ϑ j).FormV) ∈
          LevelPlaces.LevelForm.integralForms ⟨(algebraMap (PadicAlgCl ℓ) ℂ_[ℓ]).comp ι.toRingHom⟩

/-- At `ι` and for the twist `ϑ`, two bounds hold. An operator on the space `Z` of lifts from `W_j`,
with determinant of norm at least `exp (-(dim Z) r β)` at `ι`, clears the denominators of the
projection to `Z` (`ClearsProjection`). For each main pair `p = (ν, z)` for `j`, the inner product
of the projections of two test forms (`IsTestForm`) to the line of the lift of `ν ϑ` has norm at
most `exp β`. Here `p.lValueData _ ϑ` is the datum of the theta lift of the character `ν ϑ` from
`U(1)` to the definite space of rank `2 z`, its `descentPair.FormV` is the space of forms on that
space, and its `trivialLift` is the lifted form. -/
structure HasDenominatorsLe {ℓ : ℕ} [Fact ℓ.Prime] (ι : ℂ ≃+* PadicAlgCl ℓ) (ϑ : D.Twist) (j : ℕ)
    (β : ℝ) : Prop where
  /-- An operator of controlled determinant clears the denominator of the projection. -/
  clearsProjection : D.ClearsProjection ι ϑ j β
  /-- For a main pair for `j` and two test forms (`IsTestForm`: integral above `ℓ` and orthogonal to
  the false lifts in the kernel of the adjoint of the lift), the inner product of the projections to
  the line of the lift of the constant function has norm at most `exp β` at `ι`. -/
  mainPair (p : D.CriticalPair) (hp : p.IsMainPair j)
    {Ξ Ξ' : (p.lValueData hp.hasLiftRank ϑ).descentPair.FormV}
    (hΞ : (p.lValueData hp.hasLiftRank ϑ).descentPair.IsTestForm ℓ Ξ)
    (hΞ' : (p.lValueData hp.hasLiftRank ϑ).descentPair.IsTestForm ℓ Ξ') :
    ‖ι (inner ℂ ((ℂ ∙ (p.lValueData hp.hasLiftRank ϑ).trivialLift).starProjection Ξ)
      ((ℂ ∙ (p.lValueData hp.hasLiftRank ϑ).trivialLift).starProjection Ξ'))‖ ≤ Real.exp β

/-- The reals `γ ℓ`, one for each prime `ℓ`, bound the logarithms of the denominators
(`HasDenominatorsLe`) for the `j`-th powers of the twists `θ ι`, and their sum stays within the
budget `denominatorBudget`. -/
structure IsDenominatorBound (θ : PrimePadicIso → D.MFoldTwist) (j : D.LiftIndex) (γ : ℕ → ℝ) :
    Prop where
  /-- The sum of `γ ℓ` over a finite set of primes is at most `denominatorBudget`. -/
  sum_le (T : Finset ℕ) (hT : ∀ ℓ ∈ T, ℓ.Prime) : ∑ ℓ ∈ T, γ ℓ ≤ D.denominatorBudget
  /-- At `ι`, with prime `ℓ = ι.1`, both bounds of `HasDenominatorsLe` hold for the `j`-th power of
  `θ ι` with `β = γ ℓ`. -/
  hasDenominatorsLe (ι : PrimePadicIso) : D.HasDenominatorsLe ι.2 ((θ ι).powTwist j) j (γ ι.1)

/-- Reals `e ℓ ≥ 0`, one for each `ℓ`, are negligible, with the exponent `C`, if
`∑ e ℓ log ℓ ≤ x ^ C`, the sum taken over any finite set of primes. Here `x = D.x` is the length of
the prime sum, the smallest scale of the data. -/
structure IsNegligible (C : ℕ) (e : ℕ → ℝ) : Prop where
  /-- The numbers `e ℓ` are nonnegative. -/
  nonneg (ℓ : ℕ) : 0 ≤ e ℓ
  /-- The sum of `e ℓ log ℓ` over a finite set of primes is at most `x ^ C`. -/
  sum_mul_log_le (T : Finset ℕ) (hT : ∀ ℓ ∈ T, ℓ.Prime) : ∑ ℓ ∈ T, e ℓ * Real.log ℓ ≤ D.x ^ C

/-- A family of `m`-fold twists `θ ι`, one for each prime `ℓ` and `ι : ℂ ≃ ℚ̄_ℓ`, has small ratios
if the modulus of `θ ι` is prime to `ℓ` and, for `1 ≤ j ≤ m`, the `j`-th powers `(θ ι).powTwist j`
and their inverses have, for every ramified pair, inverse ratios of L-values of height at most
`D.x₁`, the second cut-off of the data. -/
structure HasSmallRatios (θ : PrimePadicIso → D.MFoldTwist) : Prop where
  /-- The norm of the modulus of `θ ι` is prime to the prime `ℓ = ι.1` of `ι`. -/
  coprime (ι : PrimePadicIso) : Nat.Coprime ι.1 (θ ι).normQ
  /-- For a ramified pair, the inverse ratios of L-values at the `j`-th powers of the twists
  (`s = 1`) or at their inverses (`s = -1`) form a family of height at most `D.x₁`. -/
  height_le (j : D.LiftIndex) (p : D.CriticalPair) (s : ℤˣ) (hp : p.IsRamified) :
    HeightLe (D.x₁) fun ι : PrimePadicIso ↦ (p.ratio ((θ ι).powTwist j) s)⁻¹

/-- A family of `m`-fold twists `θ ι`, one for each prime `ℓ` and `ι : ℂ ≃ ℚ̄_ℓ`, is regular if it
has small ratios (`HasSmallRatios`) and, for `1 ≤ j ≤ m`, the `j`-th powers `(θ ι).powTwist j`
have denominators within the budget `denominatorBudget` (`IsDenominatorBound`). -/
structure IsRegularFamily (θ : PrimePadicIso → D.MFoldTwist) : Prop extends D.HasSmallRatios θ where
  /-- Some reals `γ ℓ` bound the denominators of the `j`-th powers within `denominatorBudget`. -/
  exists_denominator_bound (j : D.LiftIndex) : ∃ γ : ℕ → ℝ, D.IsDenominatorBound θ j γ

end FitTwists

end New.Data
