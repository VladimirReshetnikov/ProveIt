import Lib.ClassField.GaloisCohomology.KummerCyclicClasses
import Lib.ClassField.Places.Ideles
import Lib.GaloisRep.Hilbert90.UnitaryGroups

/-!
# Characters of U(1) of a CM field: existence, weights and conjugates

This file studies characters of the idele group and of the unitary group `U(1)` of a CM field `E`.
Here `U(1)(𝔸)` is `unitary (𝔸 E)`, the group of adeles `u` with `u ū = 1`, and `(u : 𝔸 E).fst` and
`(u : 𝔸 E).snd` are the archimedean and finite components of `u`. `New.integralU1 S` denotes the
points with integral finite part that are 1 modulo the places of a finite set `S`. `μ.HasWeight e ψ`
says that `μ(u) = ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w)` for integral `u` and that `ψ_w = 1` for almost
all `w`.

## Main definitions and results

* `New.AutChar`: continuous unitary characters of `U(1)(𝔸) = {u | u ū = 1}` trivial on the elements
  that come from `E`.
* `New.AdelicU1ClassGroup`, `New.finite_u1_classGroup`: the class group of level `S`, the quotient
  of `U(1)(𝔸)` by the join of the rational points `New.rationalU1` and `New.integralU1 S`, is
  finite.
* `New.AutChar.exists_hasWeight_of_prod_eq_one`: a character of weight `e` and tame part `ψ` exists
  if the formula defining `μ.HasWeight e ψ` is trivial on the integers of `E` of norm one (these
  integers are roots of unity, by `New.pow_torsionOrder_eq_one`).
* `New.AutChar.tameChars`, `New.AutChar.exists_mem_tameChars`,
  `New.AutChar.exists_classGroup_char_eq_of_hasWeight_zero`, `New.AutChar.finite_tameChars`: the
  characters of weight 0 and level `S` are those of the class group, and they are finitely many.
* `New.AutChar.finite_setOf_hasWeight`: there are finitely many characters of a given weight and
  tame part.
* `New.AutChar.HasWeight.exists_conj`: for an automorphism σ of ℂ that permutes the embeddings of
  the CM type, σ ∘ μ on points with archimedean component 1 extends to a character with permuted
  weight and tame part σ ∘ ψ.

Notions from other files:
* `New.𝔸`: The ring ℂ^f × 𝔸_f, one copy of ℂ for each infinite place of E times the ring `𝔸f E` of
  finite adeles (whose units are the finite ideles): the adele ring of E when E is totally complex.
* `New.Ô`: The ring of finite adeles of E that are integral at every finite place.

## Relation to the literature

Known; see `Lib.ClassField.Global.CMSplittingCharacters` for sources.
-/

noncomputable section

/-!
## Hecke characters and characters of U(1), with base change

* `New.HeckeChar`: unitary Hecke characters, trivial on principal ideles.
-/

namespace New

variable (E : Type*) [Field E] [CMType E]
  (G : Type*) [Monoid G] [TopologicalSpace G]

@[simp]
lemma circleChar_inv_apply (χ : G →ₜ* Circle) (x : G) : χ⁻¹ x = (χ x)⁻¹ := rfl

/-- The group of continuous circle-valued characters of a topological monoid `G` that are trivial at
every `x` whose image under `f` lies in the diagonal copy of `E` in its adeles. -/
def charsTrivialOnPrincipal (f : G → 𝔸 E) : Subgroup (G →ₜ* Circle) where
  carrier := {χ : G →ₜ* Circle | ∀ x : G, f x ∈ toAdele.range → χ x = 1}
  mul_mem' hχ hχ' x hx := by simp [hχ x hx, hχ' x hx]
  one_mem' := by simp
  inv_mem' hχ x hx := by simp [hχ x hx]

/-- The group of unitary Hecke characters of E: continuous circle-valued characters of the idele
group trivial on principal ideles. -/
abbrev HeckeChar : Type _ := ↥(charsTrivialOnPrincipal E (𝔸 E)ˣ Units.val)

/-- The group of continuous circle-valued characters of U(1)(𝔸), the norm-one adeles of the CM
field E, trivial on elements coming from E. -/
abbrev AutChar : Type _ := ↥(charsTrivialOnPrincipal E (unitary (𝔸 E)) Subtype.val)

variable {E}
  {R : Type*} [CommMonoid R] [StarMul R] [TopologicalSpace R] [ContinuousMul R] [ContinuousStar R]

/-- The homomorphism sending a unitary Hecke character of E to its restriction to the finite
ideles, with values in ℂ^×. -/
def HeckeChar.finPart : HeckeChar E →* (𝔸f E)ˣ →* ℂˣ :=
  MonoidHom.mk' (fun χ ↦ Circle.toUnits.comp (χ.1.toMonoidHom.comp finIdeleIncl)) (by aesop)

/-- The value of the Hecke character χ at the local idele given by the chosen uniformiser at the
finite place w. -/
def HeckeChar.atUniformizer (χ : HeckeChar E) (w : FinPlace E) : ℂ :=
  (χ.finPart (locIdele w (uniformizer w))).val

/-- The continuous homomorphism x ↦ x/x̄ from the units of a commutative topological monoid R
with involution to the elements u with uū = 1. -/
def divStar : Rˣ →ₜ* unitary R where
  toMonoidHom :=
    MonoidHom.mk' (fun x ↦
        ⟨x * star ↑x⁻¹, (x.mul_inv_mem_unitary (star x)).2 (by simp [mul_comm])⟩) <| by
      simp
      grind
  continuous_toFun := by fun_prop

lemma coe_divStar (x : Rˣ) : (divStar x).val = x * star ↑x⁻¹ := rfl

/-- If `μ` is trivial on the rational points of `U(1)`, then `x ↦ μ(x / x̄)` is trivial on the
rational ideles. -/
lemma comp_divStar_mem_charsTrivialOnPrincipal (μ : AutChar E) :
    μ.val.comp divStar ∈ charsTrivialOnPrincipal E (𝔸 E)ˣ Units.val := by
  rintro x ⟨y, hy⟩
  -- `x / x̄` is the image of `y / ȳ`
  refine μ.prop _ ⟨y / star y, (star x).eq_mul_inv_iff_mul_eq.mpr ?_⟩
  simp [← hy, ← map_mul, div_mul_cancel_of_imp]

/-- Base change: the homomorphism sending a character μ of U(1)(𝔸), trivial on rational points,
to the Hecke character x ↦ μ(x/x̄) of E. -/
@[simps! -isSimp]
def AutChar.baseChange : AutChar E →* HeckeChar E :=
  MonoidHom.mk' (fun μ ↦ ⟨μ.1.comp divStar, comp_divStar_mem_charsTrivialOnPrincipal μ⟩) fun _ _ ↦
    rfl

/-- On a unitary adele `w`, where `w / w̄ = w * w`, the base change of `ν` is `ν (w * w)`. -/
lemma AutChar.baseChange_toUnits (ν : AutChar E) (w : unitary (𝔸 E)) :
    ν.baseChange.val (Unitary.toUnits w) = ν.val (w * w) := by
  have h_div : divStar (Unitary.toUnits w) = w * w :=
    Subtype.ext (congrArg (w.val * ·) (star_star w.val))
  exact congrArg ν.val h_div

/-- μ has weight e and tame part ψ: almost all residue characters ψ_w are trivial, and μ(u) = ∏_v
u_v^{e(v)} · ∏_w ψ_w(u mod w) whenever u has integral finite part. -/
class AutChar.HasWeight (μ : AutChar E) (e : outParam (NumberField.InfinitePlace E → ℤ))
    (ψ : outParam (∀ w : FinPlace E, MulChar (ResField w) ℂ)) where
  /-- Only finitely many of the residue characters `ψ w` are nontrivial. -/
  finite_ramification : {w : FinPlace E | ψ w ≠ 1}.Finite
  /-- If `u` has integral finite part, then `μ u` is the product of the powers `u_v ^ e v` over the
  infinite places and of the values of `ψ w` at the reductions `reduceAt w` of the finite part of
  `u` modulo the finite places `w` (in the residue field `ResField w`). -/
  apply_eq (u : unitary (𝔸 E)) (h : (u : 𝔸 E).snd ∈ Ô E) :
      μ.val u = (∏ v : NumberField.InfinitePlace E, (u : 𝔸 E).fst v ^ e v) *
          ∏ᶠ w : FinPlace E, ψ w (reduceAt w ⟨(u : 𝔸 E).snd, h⟩)

end New

/-!
## Rational and integral points of U(1) and its class group

* `New.integralU1`: the points with integral finite part that are 1 modulo each place of a finite
  set S; an open subgroup (`New.isOpen_integralU1`).
* `New.exists_snd_div_divStar_finIdeleIncl_eq_one`: by Hilbert 90, the finite part of every point is
  y / ȳ for a finite idele y.
* `New.exists_eq_mul_star`, `New.divStar_surjective`: Hilbert 90 for a field with an involution,
  and for the ideles.
-/

section CharacterLevels

open NumberField IsCMField Subgroup QuotientGroup

namespace New

variable {E : Type*} [Field E] [CMType E]
  (S : Finset (FinPlace E)) (u : unitary (𝔸 E))

/-- The subgroup of rational points of U(1)(𝔸): the adeles u with uū = 1 that come from E. -/
def rationalU1 : Subgroup (unitary (𝔸 E)) where
  toSubmonoid := Submonoid.comap (unitary (𝔸 E)).subtype toAdele.range.toSubsemiring.toSubmonoid
  -- The inverse of a unitary element is its conjugate.
  inv_mem' := fun ⟨x, hx⟩ ↦ ⟨star x, (star_toAdele x).symm.trans (congrArg star hx)⟩

open Prod

/-- For a finite set S of finite places, the subgroup of U(1)(𝔸) of elements whose finite part is
integral and congruent to 1 modulo every place of S. -/
def integralU1 {E : Type*} [Field E] [NumberField E] [IsCMField E] (S : Finset (FinPlace E)) :
    Subgroup (unitary (𝔸 E)) :=
  ofDiv {u : unitary (𝔸 E) | ∃ h : (u : 𝔸 E).2 ∈ Ô E, ∀ w ∈ S, reduceAt w ⟨(u : 𝔸 E).2, h⟩ = 1}
    ⟨1, one_mem (Ô E), fun w _ ↦ map_one (reduceAt w)⟩ (by
      -- The finite part of `u / v` is that of `u v̄`; reduce `u v̄ * v = u` modulo `w`.
      rintro u ⟨hu, hu_red⟩ v ⟨hv, hv_red⟩
      have h_int : (u : 𝔸 E).2 * star (v : 𝔸 E).2 ∈ Ô E := mul_mem hu (star_mem_Ô hv)
      refine ⟨h_int, fun w hw ↦ ?_⟩
      simpa [Unitary.star_mul_self_of_mem, hu_red, hv_red, hw, mul_assoc, ← snd_mul,
        ← snd_star] using! (map_mul (reduceAt w) ⟨_, h_int⟩ ⟨_, hv⟩).symm)

/-- Membership in `integralU1 S`: the finite part of `u` is integral and reduces to `1` modulo every
place of `S`. -/
private lemma mem_integralU1_iff {S : Finset (FinPlace E)} {u : unitary (𝔸 E)} :
    u ∈ integralU1 S ↔
      ∃ h : (u : 𝔸 E).snd ∈ Ô E, ∀ w : FinPlace E, w ∈ S → reduceAt w ⟨(u : 𝔸 E).snd, h⟩ = 1 :=
  Iff.rfl

variable {E : Type*} [Field E] [NumberField E] in
private lemma reduceAt_eq_one_iff {w : FinPlace E} {x : Ô E} :
    reduceAt w x = 1 ↔ Valued.v (x.val w - 1) < 1 := by
  rw [← sub_eq_zero, ← map_one (reduceAt w), ← map_sub, reduceAt_eq_zero]
  simp

/-- The subgroup `integralU1 S` of U(1)(𝔸) is open. -/
lemma isOpen_integralU1 : (integralU1 S).IsOpen := by
  -- An integral `x` reduces to `1` modulo `w` exactly if `v (x_w - 1) < 1`, an open condition.
  have h_eq : SetLike.coe (integralU1 S) = (fun u : unitary (𝔸 E) ↦ (u : 𝔸 E).snd) ⁻¹'
      (Ô E ∩ ⋂ w ∈ S, {x : 𝔸f E | Valued.v (x w - 1) < 1}) := by
    ext u
    simp [mem_integralU1_iff, reduceAt_eq_one_iff]
  rw [Subgroup.IsOpen, h_eq]
  exact (isOpen_Ô.inter (isOpen_biInter_finset fun w _ ↦
    (isOpen_v_lt w 1).preimage ((continuous_evalAt w).sub continuous_one))).preimage (by fun_prop)

/-- A point of U(1)(𝔸) with finite part `1` lies in `integralU1 S`. -/
lemma mem_integralU1_of_snd_eq_one {S : Finset (FinPlace E)} (hu : (u : 𝔸 E).snd = 1) :
    u ∈ integralU1 S := by
  simp [mem_integralU1_iff, reduceAt_eq_one_iff, hu]

/-- Every `u` in U(1)(𝔸) has a finite idele `y` such that `u / divStar (finIdeleIncl y)` has finite
part `1`. In other words, the finite part of `u` equals y / ȳ; here `finIdeleIncl y` is the idele
with archimedean part 1 and finite part `y`.

A consequence of Hilbert's Theorem 90. Only finite parts are matched, for norm-one adeles of a CM
field over its real subfield. -/
lemma exists_snd_div_divStar_finIdeleIncl_eq_one :
    ∃ y : (𝔸f E)ˣ, ((u / divStar (finIdeleIncl y) : unitary (𝔸 E)) : 𝔸 E).snd = 1 := by
  -- Hilbert 90 for the finite part of `u`, whose norm `u ū` is `1`, gives an idele `c` with
  -- `u c̄ = c`.
  have h_norm : adeleMap (complexConj E) (u : 𝔸 E).snd * (u : 𝔸 E).snd = 1 :=
    congrArg Prod.snd (Unitary.star_mul_self_of_mem u.property)
  obtain ⟨c, hc_unit, hc⟩ : ∃ c : 𝔸f E,
      IsUnit c ∧ (u : 𝔸 E).snd * adeleMap (complexConj E : E →+* E) c = c :=
    hilbert90_finite_idele
      (by simpa [orderOf_complexConj, Finset.range, AlgEquiv.aut_one] using h_norm)
  refine ⟨hc_unit.unit, ?_⟩
  -- The finite part of `u / (c / c̄)` is `u c̄ c⁻¹ = c c⁻¹`.
  have h_fin : ((divStar (finIdeleIncl hc_unit.unit) : unitary (𝔸 E)) : 𝔸 E).snd =
      c * star (↑(hc_unit.unit⁻¹) : 𝔸f E) := rfl
  change (u : 𝔸 E).snd * star ((divStar (finIdeleIncl hc_unit.unit)).val : 𝔸 E).snd = 1
  have h_star_c : star c = adeleMap (complexConj E : E →+* E) c := rfl
  rw [h_fin, star_mul', star_star, ← mul_assoc, h_star_c, hc]
  exact hc_unit.mul_val_inv

/-- If an idele `y` satisfies `y = u * ȳ` for some `u` in `U(1)(𝔸)`, then `y / ȳ = u`. -/
lemma divStar_eq_of_eq_mul_star {y : (𝔸 E)ˣ} {u : unitary (𝔸 E)}
    (h_eq : (y : 𝔸 E) = (u : 𝔸 E) * star (y : 𝔸 E)) :
    divStar y = u := by
  apply Subtype.ext
  rw [coe_divStar]
  nth_rw 1 [h_eq]
  rw [mul_assoc, ← star_mul', Units.mul_inv, star_one, mul_one]

/-- Hilbert's Theorem 90 for a field with an involution that negates some nonzero element `j`: an
element `a` with `a * star a = 1` satisfies `b = a * star b`, that is `a = b / star b`, for some
nonzero `b`. -/
theorem exists_eq_mul_star {K : Type*} [Field K] [StarRing K] {j : K} (hj_ne : j ≠ 0)
    (hj_star : star j = -j) {a : K} (ha_norm : a * star a = 1) :
    ∃ b : K, b ≠ 0 ∧ b = a * star b := by
  by_cases h_one_add : 1 + a = 0
  · exact ⟨j, hj_ne, by linear_combination (-a) * hj_star + j * h_one_add⟩
  · exact ⟨1 + a, h_one_add, by simp [mul_add, ha_norm, add_comm]⟩

/-- Hilbert's Theorem 90 for the ideles: every `u` with `u ū = 1` is `y / ȳ` for an idele `y`. -/
lemma divStar_surjective : Function.Surjective (divStar : (𝔸 E)ˣ →ₜ* unitary (𝔸 E)) := by
  intro u
  -- `exists_snd_div_divStar_finIdeleIncl_eq_one` settles the finite part; at each infinite place
  -- use the theorem for `ℂ`.
  obtain ⟨y, hy⟩ := exists_snd_div_divStar_finIdeleIncl_eq_one u
  set w : unitary (𝔸 E) := u / divStar (finIdeleIncl y) with hw
  have h_circle (τ : InfinitePlace E) : ∃ b : ℂ, b ≠ 0 ∧ b = (w : 𝔸 E).fst τ * star b := by
    have h_norm : (w : 𝔸 E).fst τ * star ((w : 𝔸 E).fst τ) = 1 :=
      congrFun (congrArg Prod.fst (Unitary.mul_star_self_of_mem w.property)) τ
    exact exists_eq_mul_star Complex.I_ne_zero Complex.conj_I h_norm
  choose b hb_ne hb using h_circle
  let z : (𝔸 E)ˣ := .mkOfMulEqOne (b, 1) (fun τ ↦ (b τ)⁻¹, 1)
    (Prod.ext (funext fun τ ↦ mul_inv_cancel₀ (hb_ne τ)) (one_mul 1))
  have h_finite : (1 : 𝔸f E) = (w : 𝔸 E).snd * star 1 := by rw [hy, star_one, one_mul]
  have h_z_eq : (z : 𝔸 E) = (w : 𝔸 E) * star (z : 𝔸 E) := Prod.ext (funext hb) h_finite
  refine ⟨z * finIdeleIncl y, ?_⟩
  rw [map_mul, divStar_eq_of_eq_mul_star h_z_eq, hw, div_mul_cancel]

/-- Base change is injective: a character `μ` of `U(1)(𝔸)` is determined by `x ↦ μ(x / x̄)`, since
every point of `U(1)(𝔸)` is of the form `y / ȳ` (`divStar_surjective`). -/
lemma AutChar.baseChange_injective :
    Function.Injective (AutChar.baseChange : AutChar E →* HeckeChar E) := by
  intro α β h_eq
  ext u
  obtain ⟨y, rfl⟩ := divStar_surjective u
  exact congrArg (fun χ : HeckeChar E ↦ (χ.val y : ℂ)) h_eq

/-- Reduction modulo w: the homomorphism from the elements of U(1)(𝔸) with integral finite part
to the multiplicative group of the residue field at w. -/
def reduceU1 {E : Type*} [Field E] [NumberField E] [IsCMField E]
    (w : FinPlace E) : integralU1 (∅ : Finset (FinPlace E)) →* (ResField w)ˣ :=
  ((reduceAt w).toMonoidHom.comp
    { toFun (u : integralU1 ∅) := ⟨u.val.val.snd, u.property.fst⟩
      map_one' := rfl
      map_mul' := by simp }).toHomUnits

/-- For `x` in `Eˣ` with finite idele `y`, the point `y / ȳ` of U(1)(𝔸) is a rational point times a
point that has integral finite part and is 1 modulo the places of `S`. -/
lemma divStar_principalIdele_mem_sup (x : Eˣ) :
    divStar (finIdeleIncl (principalIdele x)) ∈ rationalU1 ⊔ integralU1 S := by
  -- It is the rational point `x / x̄` times a point with finite part `1`.
  have h_rat : divStar (x.map toAdele.toMonoidHom) ∈ rationalU1 :=
    (toAdele (E := E)).range.mul_mem ⟨x, rfl⟩ (by simp)
  have h_snd : ((divStar (finIdeleIncl (principalIdele x)) /
      divStar (x.map toAdele.toMonoidHom) : unitary (𝔸 E)) : 𝔸 E).2 = 1 := by
    rw [← map_div, coe_divStar]
    simp [toAdele, div_eq_mul_inv, ← map_mul]
  exact mem_sup.2 ⟨_, h_rat, _, mem_integralU1_of_snd_eq_one _ h_snd, mul_div_cancel _ _⟩

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] in
/-- If a finite idele `y` is a unit at every place, then `y / ȳ` has integral finite part. -/
lemma divStar_mem_integralU1_empty {y : (𝔸f E)ˣ} (hy : y ∈ idelesUnitOff ∅) :
    divStar (finIdeleIncl y) ∈ integralU1 (∅ : Finset (FinPlace E)) := by
  obtain ⟨hy_int, hy_inv_int⟩ : (y : 𝔸f E) ∈ Ô E ∧ ((y⁻¹ : (𝔸f E)ˣ) : 𝔸f E) ∈ Ô E :=
    (Submonoid.mem_units_iff _ y).1 (idelesUnitOff_empty.le hy)
  have h_snd : ((divStar (finIdeleIncl y) : unitary (𝔸 E)) : 𝔸 E).2 =
      (y : 𝔸f E) * star ((y⁻¹ : (𝔸f E)ˣ) : 𝔸f E) := rfl
  refine ⟨?_, nofun⟩
  rw [h_snd]
  exact mul_mem hy_int (star_mem_Ô hy_inv_int)

/-- The class group of `U(1)` of tame level `S`: the quotient of U(1)(𝔸) by the subgroup generated
by the rational points and the points with integral finite part that are 1 modulo every place of
the finite set `S`. -/
abbrev AdelicU1ClassGroup {E : Type*} [Field E] [CMType E] (S : Finset (FinPlace E)) :
    Type _ :=
  unitary (𝔸 E) ⧸ rationalU1 ⊔ integralU1 S

/-- Every class in the class group of `U(1)` of tame level `S`, the quotient of U(1)(𝔸) by the join
of `New.rationalU1` and `New.integralU1 S`, is the class of `y / ȳ` for a finite idele `y`. -/
lemma exists_mk_divStar_eq (q : unitary (𝔸 E) ⧸ rationalU1 ⊔ integralU1 S) :
    ∃ y : (𝔸f E)ˣ, (divStar (finIdeleIncl y) : unitary (𝔸 E) ⧸ rationalU1 ⊔ integralU1 S) = q := by
  -- By Hilbert 90, every `u` has the finite part of some `y / ȳ`.
  obtain ⟨u, rfl⟩ := mk_surjective q
  obtain ⟨y, hy⟩ := exists_snd_div_divStar_finIdeleIncl_eq_one u
  exact ⟨y, (eq_iff_div_mem.2 (mem_sup_right (mem_integralU1_of_snd_eq_one _ hy))).symm⟩

/-- The class group of `U(1)` of tame level `S` is finite.

This is the analogue for `U(1)` of a CM field of the finiteness of ray class groups of a number
field, for a tame level given by a finite set of finite places. -/
instance finite_u1_classGroup : Finite (unitary (𝔸 E) ⧸ rationalU1 ⊔ integralU1 S) := by
  -- `f x = x / x̄` maps the finite ideles onto the class group, through a finite quotient.
  let f : (𝔸f E)ˣ →* unitary (𝔸 E) := divStar.1.comp finIdeleIncl
  have h_cont : Continuous f := divStar.2.comp (.units_map _ (.prodMk_right 1))
  have h_open : IsOpen (SetLike.coe ((rationalU1 ⊔ integralU1 S).comap f)) :=
    (isOpen_mono le_sup_right (isOpen_integralU1 S)).preimage h_cont
  -- An open subgroup of the finite ideles that contains `Eˣ` has finite index.
  have h_index : ((rationalU1 ⊔ integralU1 S).comap f).FiniteIndex :=
    finiteIndex_idele_subgroup_of_isOpen _ h_open fun x _ ↦ divStar_principalIdele_mem_sup S x
  refine .of_surjective (map _ _ f le_rfl) fun q ↦ ?_
  obtain ⟨y, hy⟩ := exists_mk_divStar_eq S q
  exact ⟨y, hy⟩

/-- The class group of `U(1)` of tame level `∅`, the quotient of U(1)(𝔸) by its rational points and
its points with integral finite part, has order dividing the class number of `E`. -/
lemma card_u1_classGroup_dvd_classNumber :
    Nat.card (unitary (𝔸 E) ⧸ rationalU1 ⊔ integralU1 (∅ : Finset (FinPlace E))) ∣
      classNumber E := by
  -- The map `g` induced by `y ↦ y / ȳ` from the finite ideles onto this quotient kills the
  -- principal ideles and the ideles that are units at every place. These generate the kernel of
  -- a map `c` to the ideal class group.
  let N : Subgroup (unitary (𝔸 E)) := rationalU1 ⊔ integralU1 (∅ : Finset (FinPlace E))
  let g : (𝔸f E)ˣ →* unitary (𝔸 E) ⧸ N := (mk' N).comp (divStar.1.comp finIdeleIncl)
  have hg_surj : Function.Surjective g := exists_mk_divStar_eq ∅
  obtain ⟨c, hc⟩ : ∃ c : (𝔸f E)ˣ →* ClassGroup (𝓞 E),
      c.ker = principalIdele.range ⊔ idelesUnitOff ∅ := exists_idele_classGroup_hom
  have h_ker : c.ker ≤ g.ker := by
    rw [hc, sup_le_iff]
    constructor
    · rintro _ ⟨x, rfl⟩
      exact (eq_one_iff _).2 (divStar_principalIdele_mem_sup ∅ x)
    · intro y hy
      exact (eq_one_iff _).2 (mem_sup_right (divStar_mem_integralU1_empty hy))
  calc Nat.card (unitary (𝔸 E) ⧸ N)
      = g.ker.index := (Nat.card_congr (quotientKerEquivOfSurjective g hg_surj).toEquiv).symm
    _ ∣ c.ker.index := index_dvd_of_le h_ker
    _ = Nat.card c.range := index_ker c
    _ ∣ Nat.card (ClassGroup (𝓞 E)) := card_subgroup_dvd_card c.range
    _ = classNumber E := Nat.card_eq_fintype_card

end New

end CharacterLevels

/-!
## Characters of given weight and tame part

* `New.AutChar.HasWeight.exists_pow_eq_prod`: a power of a value at a finite idele is algebraic,
  explicitly.
-/

section CharacterExistence

open NumberField Units QuotientGroup Unitary Subgroup Circle CStarRing Function

namespace New

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {ψ ψ' : ∀ w : FinPlace E, MulChar (ResField w) ℂ} (u : unitary (𝔸 E)) {S : Finset (FinPlace E)}

/-! ### Elements of norm one -/

/-- A point `u` of `U(1)(𝔸)` with integral finite part lies in `New.integralU1 ∅`. -/
lemma mem_integralU1_empty_of_snd_mem_Ô {u : unitary (𝔸 E)} (h : (u : 𝔸 E).snd ∈ Ô E) :
    u ∈ integralU1 (∅ : Finset (FinPlace E)) := ⟨h, nofun⟩

/-- The finite part of a point `u` of `New.integralU1 S` is integral. -/
lemma snd_mem_Ô_of_mem_integralU1 {S : Finset (FinPlace E)} {u : unitary (𝔸 E)}
    (hu : u ∈ integralU1 S) : (u : 𝔸 E).snd ∈ Ô E := hu.1

/-- A point `u` of `New.integralU1 S` reduces to `1` modulo every place `w` of `S`. -/
lemma reduceAt_eq_one_of_mem_integralU1 {S : Finset (FinPlace E)} {u : unitary (𝔸 E)}
    (hu : u ∈ integralU1 S) {w : FinPlace E} (hw : w ∈ S) :
    reduceAt w ⟨(u : 𝔸 E).snd, snd_mem_Ô_of_mem_integralU1 hu⟩ = 1 :=
  hu.2 w hw

/-- The unit `New.reduceU1 w u` of the residue field at `w` is the reduction modulo `w` of the
finite part of `u`. -/
lemma val_reduceU1 (w : FinPlace E) {u : unitary (𝔸 E)}
    (hu : u ∈ integralU1 (∅ : Finset (FinPlace E))) :
    (reduceU1 w ⟨u, hu⟩ : ResField w) =
      reduceAt w ⟨(u : 𝔸 E).snd, snd_mem_Ô_of_mem_integralU1 hu⟩ := rfl

/-- If the finite part of `u` in `U(1)(𝔸)` is integral, its reduction modulo `w` is a unit of the
residue field at `w`. -/
@[simp↓]
lemma isUnit_reduceAt_unitary (u : unitary (𝔸 E)) (h : (u : 𝔸 E).snd ∈ Ô E) (w : FinPlace E) :
    IsUnit (reduceAt w ⟨(u : 𝔸 E).snd, h⟩) := by
  rw [← val_reduceU1 w (mem_integralU1_empty_of_snd_mem_Ô h)]
  exact Units.isUnit _

/-- Every complex embedding `φ` of `E` sends an element `γ` of `E` with `γ γ̄ = 1` to the unit
circle. -/
lemma norm_map_unitary (φ : E →+* ℂ) (γ : unitary E) : ‖φ (γ : E)‖ = 1 := by
  -- `φ` commutes with complex conjugation, so it maps `U(1)(E)` to `U(1)(ℂ)`.
  let φ_star : E →⋆* ℂ := ⟨φ.toMonoidHom, fun x ↦ by simp⟩
  exact norm_coe_unitary (map φ_star γ)

/-- At every infinite place `v`, the component of a point `u` of `U(1)(𝔸)` has absolute value 1. -/
@[simp]
lemma norm_unitary_fst (u : unitary (𝔸 E)) (v : InfinitePlace E) : ‖(u : 𝔸 E).fst v‖ = 1 := by
  have h_mul : star ((u : 𝔸 E).fst v) * (u : 𝔸 E).fst v = 1 :=
    congrFun (congrArg Prod.fst (star_mul_self_of_mem u.property)) v
  exact norm_of_mem_unitary (mem_iff_star_mul_self.mpr h_mul)

/-- Kronecker's theorem in a CM field `E`: an algebraic integer `γ` of `E` with `γ γ̄ = 1` satisfies
`γ ^ n = 1`, where `n = torsionOrder E` is the number of roots of unity in `E`. -/
lemma pow_torsionOrder_eq_one (γ : unitary E) (h : IsIntegral ℤ (γ : E)) :
    (γ : E) ^ torsionOrder E = 1 := by
  -- Read γ as a unit of the ring of integers; it has absolute value 1 at every infinite place,
  -- so it is a torsion unit.
  let γ_int : 𝓞 E := ⟨γ, h⟩
  have h_unitary : γ_int ∈ unitary (𝓞 E) :=
    mem_iff_star_mul_self.mpr (Subtype.ext (star_mul_self_of_mem γ.property))
  let ε : (𝓞 E)ˣ := toUnits ⟨γ_int, h_unitary⟩
  have h_tors : ε ∈ torsion E :=
    (mem_torsion E).mpr fun w ↦ (w.norm_embedding_eq _).symm.trans (norm_map_unitary _ γ)
  have h_pow : (⟨ε, h_tors⟩ : torsion E) ^ torsionOrder E = 1 := pow_card_eq_one'
  exact congrArg (fun x : torsion E ↦ ((x.val : 𝓞 E) : E)) h_pow

/-- If `ψ` is trivial outside `S`, the product of the `ψ_w(u mod w)` over all finite places is the
finite product over `S`, with `u mod w` written as the unit `New.reduceU1 w u`. -/
lemma finprod_tame_eq_prod_reduceU1 {ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ}
    (u : unitary (𝔸 E)) {S : Finset (FinPlace E)} (hS : ∀ w : FinPlace E, w ∉ S → ψ w = 1)
    (h : (u : 𝔸 E).snd ∈ Ô E) :
    ∏ᶠ w : FinPlace E, ψ w (reduceAt w ⟨(u : 𝔸 E).snd, h⟩) =
      ∏ w ∈ S, ψ w (reduceU1 w ⟨u, mem_integralU1_empty_of_snd_mem_Ô h⟩) := by
  have h_support :
      mulSupport (fun w : FinPlace E ↦ ψ w (reduceAt w ⟨(u : 𝔸 E).snd, h⟩)) ⊆ S := by
    intro w hw
    by_contra h_notMem
    simp [hS w h_notMem, MulChar.one_apply (isUnit_reduceAt_unitary u h w)] at hw
  rw [finprod_eq_prod_of_mulSupport_subset _ h_support]
  simp only [val_reduceU1]

end

variable {E : Type*} [Field E] [CMType E] {ψ ψ' : ∀ w : FinPlace E, MulChar (ResField w) ℂ}
  (u : unitary (𝔸 E)) {S : Finset (FinPlace E)} {μ ν : AutChar E} {e e' : InfinitePlace E → ℤ}

/-- A rational point `u` of `U(1)(𝔸)` is the image of an element `y` of `E` with `y ȳ = 1`. -/
lemma exists_unitary_of_mem_rationalU1 {u : unitary (𝔸 E)} (hu : u ∈ rationalU1) :
    ∃ y : unitary E, toAdele (y : E) = (u : 𝔸 E) := by
  obtain ⟨y, hy⟩ : ∃ y : E, toAdele y = (u : 𝔸 E) := hu
  -- `toAdele` is injective and commutes with conjugation, so `y` is unitary with its image.
  have h_image : toAdele (star y * y) = toAdele 1 := by
    rw [map_mul, ← star_toAdele, hy, star_mul_self_of_mem u.property, map_one]
  exact ⟨⟨y, mem_iff_star_mul_self.mpr (toAdele.injective h_image)⟩, hy⟩

namespace AutChar

/-! ### Weight and tame part under the group operations -/

/-- Let `ψ` be a family of residue characters, trivial outside the finite set `S` of places. If
`f u = g u * ∏_w ψ_w(u mod w)` for all `u` with integral finite part, then `f u = g u` for `u` in
`New.integralU1 S`. -/
lemma eq_of_mem_integralU1 {f g : unitary (𝔸 E) → ℂ} (hS : ∀ w : FinPlace E, w ∉ S → ψ w = 1)
    (h_eq : ∀ (u : unitary (𝔸 E)) (hu : (u : 𝔸 E).snd ∈ Ô E),
      f u = g u * ∏ᶠ w : FinPlace E, ψ w (reduceAt w ⟨(u : 𝔸 E).snd, hu⟩))
    (u : unitary (𝔸 E)) (hu : u ∈ integralU1 S) :
    f u = g u := by
  have h_int : (u : 𝔸 E).snd ∈ Ô E := snd_mem_Ô_of_mem_integralU1 hu
  -- Each factor `ψ_w(u mod w)` is 1: outside `S` as `ψ_w = 1`, on `S` as `u ≡ 1` modulo `w`.
  have h_tame : ∏ᶠ w : FinPlace E, ψ w (reduceAt w ⟨(u : 𝔸 E).snd, h_int⟩) = 1 := by
    rw [finprod_tame_eq_prod_reduceU1 u hS h_int]
    refine Finset.prod_eq_one fun w hw ↦ ?_
    rw [val_reduceU1, reduceAt_eq_one_of_mem_integralU1 hu hw, map_one]
  rw [h_eq u h_int, h_tame, mul_one]

/-- The trivial character has weight 0 and trivial tame part. -/
instance HasWeight.one : HasWeight (1 : AutChar E) 0 1 where
  finite_ramification := by simp
  apply_eq := by simp [MulChar.one_apply]

/-- If `μ` has weight `e` and tame part `ψ`, and `ν` has weight `e'` and tame part `ψ'`, then `μ ν`
has weight `e + e'` and tame part `ψ ψ'`. -/
lemma HasWeight.mul (h : μ.HasWeight e ψ) (h' : ν.HasWeight e' ψ') :
    (μ * ν).HasWeight (e + e') (ψ * ψ') := by
  have h_fin : ({w | ψ w ≠ 1} ∪ {w | ψ' w ≠ 1} : Set (FinPlace E)).Finite :=
    h.finite_ramification.union h'.finite_ramification
  refine ⟨h_fin.subset (by grind [Pi.mul_def]), fun u hu ↦ ?_⟩
  -- Write all three tame products over the finite set `T` where `ψ` or `ψ'` is nontrivial.
  set T : Finset (FinPlace E) := h_fin.toFinset
  have hψ : ∀ w : FinPlace E, w ∉ T → ψ w = 1 := by simp +contextual [T]
  have hψ' : ∀ w : FinPlace E, w ∉ T → ψ' w = 1 := by simp +contextual [T]
  have hψψ' : ∀ w : FinPlace E, w ∉ T → (ψ * ψ') w = 1 := by simp +contextual [hψ, hψ']
  have h_ne (v : InfinitePlace E) : (u : 𝔸 E).fst v ≠ 0 := by simp [← norm_ne_zero_iff]
  have h_μν : ((μ * ν).val u : ℂ) = μ.val u * ν.val u := rfl
  -- Both products of the weight `e + e'` and of the tame part `ψ ψ'` split into two.
  have h_arch : ∏ v, (u : 𝔸 E).fst v ^ (e + e') v =
      (∏ v, (u : 𝔸 E).fst v ^ e v) * ∏ v, (u : 𝔸 E).fst v ^ e' v := by
    simp [zpow_add₀ (h_ne _), Finset.prod_mul_distrib]
  have h_tame (r : ∀ w : FinPlace E, ResField w) :
      ∏ w ∈ T, (ψ * ψ') w (r w) = (∏ w ∈ T, ψ w (r w)) * ∏ w ∈ T, ψ' w (r w) := by
    simp only [Pi.mul_apply, MulChar.mul_apply, Finset.prod_mul_distrib]
  rw [h_μν, h.apply_eq u hu, h'.apply_eq u hu, finprod_tame_eq_prod_reduceU1 u hψ hu,
    finprod_tame_eq_prod_reduceU1 u hψ' hu, finprod_tame_eq_prod_reduceU1 u hψψ' hu, h_arch,
    h_tame fun w ↦ reduceU1 w ⟨u, mem_integralU1_empty_of_snd_mem_Ô hu⟩]
  ring

/-- If `μ` has weight `e` and tame part `ψ`, then `μ⁻¹` has weight `-e` and tame part `ψ⁻¹`. -/
instance HasWeight.inv [h : μ.HasWeight e ψ] : μ⁻¹.HasWeight (-e) ψ⁻¹ where
  finite_ramification := by simpa using h.finite_ramification
  apply_eq := by simp +contextual [apply_eq, MulChar.inv_apply_eq_inv', finprod_inv_distrib, field]

/-- The `n`-th power of a character has `n` times the weight and the `n`-th power of the tame
part. -/
lemma HasWeight.zpow (h : μ.HasWeight e ψ) (n : ℤ) : (μ ^ n).HasWeight (n • e) (ψ ^ n) := by
  induction n with
  | zero => simpa using HasWeight.one
  | succ k ih => simpa [zpow_add_one, add_smul] using ih.mul h
  | pred k ih =>
    rw [zpow_sub_one, zpow_sub_one, sub_smul, one_smul, sub_eq_add_neg]
    exact ih.mul (HasWeight.inv (h := h))

/-! ### Existence and finiteness -/

/-- Let ψ be trivial off a finite set S. A homomorphism χ : U(1)(𝔸) → ℂ, trivial on rational
points and equal to ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w) on integral u, is a continuous unitary
character of weight e and tame part ψ. -/
lemma exists_hasWeight (χ : unitary (𝔸 E) →* ℂ) (h_rat : rationalU1 ≤ χ.ker)
    (hS : ∀ w : FinPlace E, w ∉ S → ψ w = 1)
    (hχ : ∀ (u : unitary (𝔸 E)) (hu : (u : 𝔸 E).snd ∈ Ô E),
      χ u = (∏ v : InfinitePlace E, (u : 𝔸 E).fst v ^ e v) *
          ∏ᶠ w : FinPlace E, ψ w (reduceAt w ⟨(u : 𝔸 E).snd, hu⟩)) :
    ∃ μ : AutChar E, HasWeight μ e ψ ∧ ∀ u : unitary (𝔸 E), μ.val u = χ u := by
  -- On the open subgroup `integralU1 S` the tame part is trivial and χ is the archimedean monomial.
  have h_arch : ∀ u ∈ integralU1 S, χ u = ∏ v, (u : 𝔸 E).fst v ^ e v :=
    eq_of_mem_integralU1 hS hχ
  -- So |χ| = 1 on `integralU1 S` as on `rationalU1`: |χ| factors through the finite class group,
  -- and a nonnegative real of finite order is 1.
  have h_ker : rationalU1 ⊔ integralU1 S ≤ (normHom.toMonoidHom.comp χ).ker :=
    sup_le (fun u hu ↦ by simp [MonoidHom.mem_ker.mp (h_rat hu)])
      (fun u hu ↦ by simp [h_arch u hu])
  have h_norm (u : unitary (𝔸 E)) : ‖χ u‖ = 1 := by
    have h_order : IsOfFinOrder ‖χ u‖ :=
      (lift (rationalU1 ⊔ integralU1 S) (normHom.toMonoidHom.comp χ) h_ker).isOfFinOrder
        (isOfFinOrder_of_finite (u : AdelicU1ClassGroup S))
    exact h_order.eq_one (norm_nonneg _)
  -- χ agrees with the monomial near 1, so it is continuous at 1, hence everywhere.
  have h_cont : Continuous χ := by
    have h_near : χ =ᶠ[nhds 1] fun u ↦ ∏ v, (u : 𝔸 E).fst v ^ e v :=
      .mono ((isOpen_integralU1 S).mem_nhds (one_mem _)) h_arch
    have h_monomial : ContinuousAt (fun u : unitary (𝔸 E) ↦ ∏ v, (u : 𝔸 E).fst v ^ e v) 1 := by
      fun_prop (disch := simp)
    exact continuous_of_continuousAt_one χ (h_monomial.congr h_near.symm)
  let χ' : unitary (𝔸 E) →ₜ* Circle :=
    ⟨χ.codRestrict _ fun u ↦ mem_sphere_zero_iff_norm.mpr (h_norm u), h_cont.subtype_mk _⟩
  have h_trivial : χ' ∈ charsTrivialOnPrincipal E (unitary (𝔸 E)) Subtype.val :=
    fun u hu ↦ ext (h_rat hu)
  have h_finite : {w : FinPlace E | ψ w ≠ 1}.Finite :=
    S.finite_toSet.subset fun w hw ↦ by_contra fun h_notMem ↦ hw (hS w h_notMem)
  exact ⟨⟨χ', h_trivial⟩, ⟨h_finite, hχ⟩, fun _ ↦ rfl⟩

/-- Let ψ be trivial off a finite set S. If ∏_v Φ_v(u)^{e(v)} · ∏_{w∈S} ψ_w(u mod w) = 1 for every
integer u of E with uū = 1 (Φ_v the embedding of E chosen at v), then some character of U(1)(𝔸),
trivial on rational points, has weight e and tame part ψ. -/
lemma exists_hasWeight_of_prod_eq_one (hS : ∀ w : FinPlace E, w ∉ S → ψ w = 1)
    (h_one : ∀ (u : unitary E) (hu : algebraMap E (𝔸f E) u ∈ Ô E),
      (∏ v : InfinitePlace E, Φ v (u : E) ^ e v) *
        ∏ w ∈ S, ψ w (reduceAt w ⟨algebraMap E (𝔸f E) u, hu⟩) = 1) :
    ∃ μ : AutChar E, HasWeight μ e ψ := by
  -- The formula defines a character θ of the points with integral finite part.
  let θ : integralU1 (∅ : Finset (FinPlace E)) →* ℂ :=
    { toFun u := (∏ v, ((u : unitary (𝔸 E)) : 𝔸 E).fst v ^ e v) * ∏ w ∈ S, ψ w (reduceU1 w u)
      map_one' := by simp
      map_mul' := by simp [mul_zpow, Finset.prod_mul_distrib, field] }
  -- By `h_one` it kills the rational integral points, so it extends to a character χ of U(1)(𝔸)
  -- that kills all rational points.
  have h_θ_rat : ∀ u : integralU1 (∅ : Finset (FinPlace E)),
      (u : unitary (𝔸 E)) ∈ rationalU1 → θ.toHomUnits u = 1 := by
    rintro ⟨⟨x, hx_unitary⟩, hx_int⟩ hx_rat
    obtain ⟨y, rfl⟩ := exists_unitary_of_mem_rationalU1 hx_rat
    exact ext (h_one y (snd_mem_Ô_of_mem_integralU1 hx_int))
  obtain ⟨χ, h_rat, hχ⟩ : ∃ χ : unitary (𝔸 E) →* ℂˣ, rationalU1 ≤ χ.ker ∧
      ∀ u : integralU1 (∅ : Finset (FinPlace E)), χ u = θ.toHomUnits u :=
    exists_monoidHom_extend (integralU1 ∅).subtype θ.toHomUnits rationalU1 h_θ_rat
  have h_rat_ℂ : rationalU1 ≤ ((coeHom ℂ).comp χ).ker :=
    fun u hu ↦ by simp [MonoidHom.mem_ker.mp (h_rat hu)]
  have h_formula : ∀ (u : unitary (𝔸 E)) (hu : (u : 𝔸 E).snd ∈ Ô E),
      (coeHom ℂ).comp χ u = (∏ v : InfinitePlace E, (u : 𝔸 E).fst v ^ e v) *
        ∏ᶠ w : FinPlace E, ψ w (reduceAt w ⟨(u : 𝔸 E).snd, hu⟩) := fun u hu ↦ by
    rw [finprod_tame_eq_prod_reduceU1 u hS hu]
    -- At `u`, `χ` is `θ`, which is the formula.
    exact congrArg Units.val (hχ ⟨u, mem_integralU1_empty_of_snd_mem_Ô hu⟩)
  obtain ⟨μ, hμ, -⟩ := exists_hasWeight (e := e) ((coeHom ℂ).comp χ) h_rat_ℂ hS h_formula
  exact ⟨μ, hμ⟩

/-- For a finite set S of finite places, the group of pairs (μ, ψ): μ a character of U(1)(𝔸) of
weight 0 with tame part ψ, and ψ trivial outside S. -/
noncomputable def tameChars (S : Finset (FinPlace E)) :
    Subgroup (AutChar E × ∀ w : FinPlace E, MulChar (ResField w) ℂ) :=
  ofDiv {μ : AutChar E × ((w : FinPlace E) → MulChar (ResField w) ℂ) |
    HasWeight μ.1 0 μ.2 ∧ ∀ w ∉ S, μ.2 w = 1} ⟨1, HasWeight.one, by simp⟩
    fun _ ⟨hμ, _⟩ _ ⟨hν, _⟩ ↦ ⟨(hμ.mul hν.inv :), by simp_all⟩

/-- Let `χ` be a complex character of the class group `U(1)(𝔸) / (rationalU1 ⊔ integralU1 S)` of
level `S`. Its pullback to `U(1)(𝔸)` is a continuous unitary character of weight 0 whose tame part
is trivial outside `S`. That is, some pair `(μ, ψ)` in `New.AutChar.tameChars S` has `μ u = χ ↑u`
for all `u`, where `↑u` is the class of `u`. -/
lemma exists_mem_tameChars (χ : unitary (𝔸 E) ⧸ (rationalU1 ⊔ integralU1 S) →* ℂ) :
    -- `μ.val.fst` is the character of the pair `μ`, and `↑u` is the class of `u`
    ∃ μ : tameChars S, ∀ u : unitary (𝔸 E),
      ((μ.val.fst : unitary (𝔸 E) →ₜ* Circle) u : ℂ) = χ ↑u := by
  classical
  -- χ kills the integral points that are 1 modulo `S`, so on integral points it comes from a
  -- character θ of the product of the residue unit groups at `S`, that is, from a family φ.
  obtain ⟨θ, -, hθ⟩ :
      ∃ θ : (∀ w : S, (ResField (w : FinPlace E))ˣ) →* ℂˣ,
        ⊥ ≤ θ.ker ∧
        ∀ u : integralU1 (∅ : Finset (FinPlace E)),
          θ (fun w ↦ reduceU1 (w : FinPlace E) u) = χ.toHomUnits (u : unitary (𝔸 E)) := by
    refine exists_monoidHom_extend (.pi fun w : S ↦ reduceU1 (w : FinPlace E))
      ((χ.toHomUnits.comp (mk' _)).domRestrict _) ⊥ fun u hu ↦ ?_
    -- `u` reduces to 1 at every place of `S`, so it lies in `integralU1 S`, which χ kills.
    have h_mem : (u : unitary (𝔸 E)) ∈ integralU1 S := ⟨snd_mem_Ô_of_mem_integralU1 u.2,
      fun w hw ↦ congrArg Units.val (congrFun (Subgroup.mem_bot.1 hu) ⟨w, hw⟩)⟩
    exact ext (le_comap_mk' _ χ.ker (mem_sup_right h_mem))
  let e_pi := Pi.monoidHomMulEquiv (fun w : S ↦ (ResField (w : FinPlace E))ˣ) ℂˣ
  obtain ⟨φ, rfl⟩ := e_pi.symm.surjective θ
  -- The tame part is φ on `S` and trivial elsewhere.
  let ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ := updateFinset 1 S fun w ↦ .ofUnitHom (φ w)
  have hψ : ∀ w : FinPlace E, w ∉ S → ψ w = 1 := by simp +contextual [ψ, updateFinset]
  have h_rat : rationalU1 ≤ (χ.comp (mk' _)).ker := le_sup_left.trans (le_comap_mk' _ χ.ker)
  have h_formula : ∀ (u : unitary (𝔸 E)) (hu : (u : 𝔸 E).snd ∈ Ô E),
      χ.comp (mk' _) u = (∏ v : InfinitePlace E, (u : 𝔸 E).fst v ^ (0 : InfinitePlace E → ℤ) v) *
        ∏ᶠ w : FinPlace E, ψ w (reduceAt w ⟨(u : 𝔸 E).snd, hu⟩) := by
    intro u hu
    -- At `u`, χ is θ at the reductions of `u`, that is, the product of the `φ_w` over `S`.
    have hu_int : u ∈ integralU1 (∅ : Finset (FinPlace E)) := mem_integralU1_empty_of_snd_mem_Ô hu
    have h_χ_u : χ.comp (mk' _) u =
        (e_pi.symm φ (fun w ↦ reduceU1 (w : FinPlace E) ⟨u, hu_int⟩) : ℂ) :=
      (congrArg Units.val (hθ ⟨u, hu_int⟩)).symm
    rw [finprod_tame_eq_prod_reduceU1 u hψ, h_χ_u]
    simp [e_pi, ψ, updateFinset, ← S.prod_coe_sort, Pi.monoidHomMulEquiv]
  obtain ⟨μ, hμ, hμχ⟩ := exists_hasWeight (e := 0) _ h_rat hψ h_formula
  exact ⟨⟨(μ, ψ), hμ, hψ⟩, hμχ⟩

/-- Let `μ` be a character of `U(1)(𝔸)` of weight 0 whose tame part `ψ` is trivial outside a finite
set `S` of finite places. Then `μ` is the pullback of a character `χ` of the class group
`U(1)(𝔸) / (rationalU1 ⊔ integralU1 S)` of level `S`: `χ ↑u = μ u` for all `u`, where `↑u` is the
class of `u`. This is the converse of `New.AutChar.exists_mem_tameChars`. -/
lemma exists_classGroup_char_eq_of_hasWeight_zero {S : Finset (FinPlace E)}
    {ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ} {μ : AutChar E} (hμ : μ.HasWeight 0 ψ)
    (hS : ∀ w : FinPlace E, w ∉ S → ψ w = 1) :
    ∃ χ : unitary (𝔸 E) ⧸ (rationalU1 ⊔ integralU1 S) →* Circle,
      ∀ u : unitary (𝔸 E), χ ↑u = μ.val u := by
  -- On integral points `μ` is the product of the `ψ_w` at the reductions, which is 1 if the point
  -- is 1 modulo the places of `S`.
  have h_int : integralU1 S ≤ μ.val.toMonoidHom.ker := fun u hu ↦
    Circle.ext (by simpa using eq_of_mem_integralU1 hS hμ.apply_eq u hu)
  have h_ker : rationalU1 ⊔ integralU1 S ≤ μ.val.toMonoidHom.ker := sup_le μ.property h_int
  exact ⟨lift _ μ.val.toMonoidHom h_ker, lift_mk _ h_ker⟩

/-- There are finitely many characters of weight `0` and given tame level. -/
instance finite_tameChars : Finite (tameChars S) := by
  -- Such a character comes from a character of the finite class group of level `S`; its tame part
  -- is determined by its finitely many components at the places of `S`.
  choose θ hθ using fun χ : tameChars S ↦
    exists_classGroup_char_eq_of_hasWeight_zero χ.2.1 χ.2.2
  let data (χ : tameChars S) :
      (AdelicU1ClassGroup S →* ℂˣ) × ∀ w : S, MulChar (ResField w.1) ℂ :=
    (toUnits.comp (θ χ), S.restrict χ.1.2)
  refine .of_injective data fun χ χ' h ↦ ?_
  ext w
  · rw [← hθ χ w, ← hθ χ' w]
    congrm $h.1 w
  · by_cases hw : w ∈ S
    · congrm $h.2 ⟨w, hw⟩ _
    · rw [χ.2.2 w hw, χ'.2.2 w hw]

/-- There are finitely many characters `μ` of `U(1)(𝔸)` of a given weight `e` and tame part `ψ`.
These satisfy `μ u = ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w)` for all `u` with integral finite part. -/
lemma finite_setOf_hasWeight (e : InfinitePlace E → ℤ)
    (ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ) :
    {μ : AutChar E | μ.HasWeight e ψ}.Finite := by
  -- Division by one such character `ν` gives characters of weight `0` and trivial tame part.
  obtain h_empty | ⟨ν, hν⟩ := {μ : AutChar E | μ.HasWeight e ψ}.eq_empty_or_nonempty
  · rw [h_empty]
    exact Set.finite_empty
  have h_quot (μ : {μ : AutChar E | μ.HasWeight e ψ}) :
      (μ.val * ν⁻¹, 1) ∈ tameChars (∅ : Finset (FinPlace E)) :=
    ⟨by simpa using HasWeight.mul μ.prop (HasWeight.inv (h := hν)), fun _ _ ↦ rfl⟩
  let quot (μ : {μ : AutChar E | μ.HasWeight e ψ}) : tameChars (∅ : Finset (FinPlace E)) :=
    ⟨_, h_quot μ⟩
  refine Finite.of_injective quot fun μ μ' h_eq ↦ ?_
  have h_mul : μ.val * ν⁻¹ = μ'.val * ν⁻¹ := congrArg (fun χ ↦ χ.val.fst) h_eq
  exact Subtype.ext (mul_right_cancel h_mul)

/-- The values of a character of `U(1)(𝔸)` of weight 0 are roots of unity. -/
lemma HasWeight.isOfFinOrder_apply (h : μ.HasWeight 0 ψ) (u : unitary (𝔸 E)) :
    IsOfFinOrder (μ.val u : ℂ) := by
  -- `μ` comes from a character of the finite class group of its level.
  let S : Finset (FinPlace E) := h.finite_ramification.toFinset
  obtain ⟨χ, hχ⟩ := exists_classGroup_char_eq_of_hasWeight_zero h (S := S) (by simp [S])
  rw [← hχ u]
  exact coeHom.isOfFinOrder (χ.isOfFinOrder (isOfFinOrder_of_finite _))

/-- Let `μ` have weight `e` and tame part `ψ`, and let `u` in `U(1)(𝔸)` have archimedean part 1.
There are `n > 0` and `γ` in `E` with `γ γ̄ = 1` such that (a) `uⁿ γ` is a unit at every finite
place, and (b) `μ(u)ⁿ = ∏_v Φ_v(γ)^{e v}`, with `Φ` the CM type. -/
lemma HasWeight.exists_pow_eq_prod (h : μ.HasWeight e ψ) (hu : (u : 𝔸 E).fst = 1) :
    ∃ n : ℕ, n > 0 ∧ ∃ γ : unitary E,
      -- (a)
      (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
        Valued.v (((u : 𝔸 E).snd ^ n * ((γ : E) : 𝔸f E)) w) = 1) ∧
      -- (b)
      (μ.val u : ℂ) ^ n = ∏ v : InfinitePlace E, Φ v (γ : E) ^ e v := by
  -- Let n be the order of the class group of the level `T` of ψ; then uⁿ = g z with g rational
  -- and z integral and 1 modulo `T`. Take γ = g⁻¹, so that z = uⁿγ.
  set T : Finset (FinPlace E) := h.finite_ramification.toFinset
  let H : Subgroup (unitary (𝔸 E)) := rationalU1 ⊔ integralU1 T
  obtain ⟨g, hg, z, hz, hgz⟩ : ∃ g ∈ rationalU1, ∃ z ∈ integralU1 T, g * z = u ^ H.index :=
    mem_sup.mp (pow_index_mem H u)
  obtain ⟨γ, hγ⟩ := exists_unitary_of_mem_rationalU1 (inv_mem hg)
  have hz_eq : z = g⁻¹ * u ^ H.index := eq_inv_mul_of_mul_eq hgz
  refine ⟨H.index, Nat.pos_of_ne_zero index_ne_zero_of_finite, γ, fun w ↦ ?_, ?_⟩
  · -- z is integral with nonzero reduction at w.
    have hz_int : (z : 𝔸 E).snd ∈ Ô E := snd_mem_Ô_of_mem_integralU1 hz
    have h_val : Valued.v ((z : 𝔸 E).snd w) = 1 := (mem_Ô.mp hz_int w).eq_of_not_lt fun h_lt ↦
      (isUnit_reduceAt_unitary z hz_int w).ne_zero (reduceAt_eq_zero.mpr h_lt)
    have hz_snd : (z : 𝔸 E).snd = (u : 𝔸 E).snd ^ H.index * ((γ : E) : 𝔸f E) := by
      simp [hz_eq, ← hγ, mul_comm]
    rwa [hz_snd] at h_val
  · -- μ(z) is the archimedean monomial, μ(g) = 1, and z and γ have the same archimedean part.
    have h_arch : (μ.val z : ℂ) = ∏ v, (z : 𝔸 E).fst v ^ e v :=
      eq_of_mem_integralU1 (fun w hw ↦ by simpa [T] using hw) h.apply_eq z hz
    have hμ_g : μ.val g = 1 := μ.property _ hg
    have hμ_z : (μ.val z : ℂ) = (μ.val u : ℂ) ^ H.index := by simp [hz_eq, hμ_g]
    have hz_fst (v : InfinitePlace E) : (z : 𝔸 E).fst v = Φ v (γ : E) := by
      simp [hz_eq, ← hγ, hu]
    simp only [← hμ_z, h_arch, hz_fst]

end AutChar

end New

end CharacterExistence

/-! ## Galois conjugates of characters of U(1) -/

namespace New.AutChar.HasWeight

variable {E : Type*} [Field E] [CMType E]
  {μ : AutChar E} {e : NumberField.InfinitePlace E → ℤ}
  {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}

/-- Let μ have weight e and tame part ψ, and let σ be an automorphism of ℂ that permutes the
embeddings of the CM type through a permutation p of the infinite places: σ ∘ Φ_v = Φ_{p(v)}.
Then some character ν has weight e ∘ p⁻¹ and tame part w ↦ σ ∘ ψ_w, and ν(u) = σ(μ(u)) for every
u with archimedean component 1. -/
lemma exists_conj (h : μ.HasWeight e ψ) {σ : ℂ ≃+* ℂ}
    {p : NumberField.InfinitePlace E ≃ NumberField.InfinitePlace E}
    (hσp : ∀ (v : NumberField.InfinitePlace E) (x : E), σ (Φ v x) = Φ (p v) x) :
    ∃ ν : AutChar E,
      -- (a) the weight is permuted by p and the tame part is composed with σ
      HasWeight ν (e ∘ p.symm) (fun w : FinPlace E ↦ (ψ w).ringHomComp σ) ∧
      -- (b) where the archimedean part is 1, the values are those of μ moved by σ
      ∀ u : unitary (𝔸 E), (u : 𝔸 E).fst = 1 → ν.val u = σ (μ.val u) := by
  -- Permute the archimedean monomial by p and apply σ to the rest of μ.
  let χ : unitary (𝔸 E) →* ℂ :=
    { toFun u := (∏ v, (u : 𝔸 E).fst (p v) ^ e v) * σ (μ.val u / ∏ v, (u : 𝔸 E).fst v ^ e v)
      map_one' := by simp
      map_mul' := by
        simp [mul_zpow, Finset.prod_mul_distrib, mul_div_mul_comm, mul_mul_mul_comm] }
  have hχ (u : unitary (𝔸 E)) :
      χ u = (∏ v, (u : 𝔸 E).fst (p v) ^ e v) * σ (μ.val u / ∏ v, (u : 𝔸 E).fst v ^ e v) :=
    rfl
  -- On a rational point μ is 1 and σ permutes the embeddings, so the two monomials cancel.
  have h_rat : rationalU1 ≤ χ.ker := by
    intro u hu
    obtain ⟨y, hy⟩ := exists_unitary_of_mem_rationalU1 hu
    have hμ_u : μ.val u = 1 := μ.property u hu
    have h_arch (v : NumberField.InfinitePlace E) : (u : 𝔸 E).fst v = Φ v (y : E) := by
      simp [← hy]
    simp [hχ, hμ_u, h_arch, hσp, norm_map_unitary _ y, ← norm_ne_zero_iff]
  have h_level : ∀ w : FinPlace E, w ∉ h.finite_ramification.toFinset →
      (ψ w).ringHomComp (σ : ℂ →+* ℂ) = 1 := by
    simp +contextual
  -- `exists_hasWeight` makes χ a unitary character once it has the right formula on integral
  -- points; there μ divided by its monomial is the tame product.
  have h_formula : ∀ (u : unitary (𝔸 E)) (hu : (u : 𝔸 E).snd ∈ Ô E),
      χ u = (∏ v : NumberField.InfinitePlace E, (u : 𝔸 E).fst v ^ (e ∘ p.symm) v) *
        ∏ᶠ w : FinPlace E, (ψ w).ringHomComp (σ : ℂ →+* ℂ) (reduceAt w ⟨(u : 𝔸 E).snd, hu⟩) := by
    intro u hu
    rw [hχ, ← p.symm.prod_comp]
    simp [h.apply_eq u hu, ← norm_ne_zero_iff, MulEquivClass.map_finprod]
  obtain ⟨ν, hν, hνχ⟩ := exists_hasWeight (e := e ∘ p.symm) χ h_rat h_level h_formula
  exact ⟨ν, hν, fun u hu ↦ by simp [hνχ, hχ, hu]⟩

end New.AutChar.HasWeight

end
