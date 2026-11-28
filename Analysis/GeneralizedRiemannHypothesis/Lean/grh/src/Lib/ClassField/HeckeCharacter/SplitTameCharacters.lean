import Lib.Adelic.Adeles.SemilocalProducts
import Lib.Weil.DualPair.Defs

/-!
# Splitting character on U(1), characters tamely ramified at split places, theta integrals

The subject is continuous characters of U(1)(𝔸), the norm-one adeles of a CM field E, with their
weights and tame parts (`New.AutChar.HasWeight`). Write x̄ for complex conjugation, w̄ for the place
conjugate to w, and υ for the splitting character of the Weil data (`New.WeilData`). The file first
computes the base change x ↦ μ(x / x̄) on local units. It then introduces characters tamely ramified
exactly at a set of split places, and defines the theta integral of a datum for an arbitrary pair
of characters.

## Main definitions and results

* `New.AutChar.HasWeight.baseChange_finPart_locIdele`: if μ has tame part ψ, w̄ ≠ w and ψ is trivial
  at w̄, the base change x ↦ μ(x / x̄) is given on local units at w by ψ_w.
* `New.AutChar.HasWeight.baseChange_finPart_locIdele_eq_one`: if w̄ = w and ψ_w is trivial, the
  base change is trivial on E_w^×.
* `New.WeilData.upsilonU1_hasWeight`, `New.WeilData.baseChange_upsilonU1`: on U(1), υ has weight 1
  and trivial tame part, and its base change is υ².
* `New.Exchange.SplitTameChar`: a character of positive weight, tamely ramified exactly on a
  nonempty set S of split places. `New.Exchange.SplitTameChar.semilocalChar` is its character at S.
* `New.Exchange.SplitTameChar.tameLocalChar`: the character at S is tame in the sense of
  `New.TameLocalChar`.
* `New.Exchange.thetaIntegral`: the integral over [U(T)] of the theta kernel of the dual pair
  (U(S), U(T)), for arbitrary characters a and b of U(1)(𝔸).

Notions from other files:
* `New.AutChar`: The group of continuous circle-valued characters of U(1)(𝔸), the norm-one adeles of
  the CM field E, trivial on elements coming from E.
* `New.divStar`: The map x ↦ x / x̄ from ideles to norm-one adeles.

## Relation to the literature

The results of this file are known; see `Lib.ClassField.Global.CMSplittingCharacters` and
`Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

noncomputable section

/-!
## Base change at local units and the splitting character on U(1)

`New.locIdele` places any element of E_w^× at w in the ideles, with 1 at all other places.
-/

section SplittingCharOnU1

open NumberField Finset Valued Complex OneMemClass

namespace New

variable {E : Type*} [Field E] [CMType E]
  {w : FinPlace E} {μ : AutChar E} {e : InfinitePlace E → ℤ}
  {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}

/-! ### Base change at local units -/

lemma AutChar.HasWeight.of_weight_eq (h : μ.HasWeight e ψ) {e' : InfinitePlace E → ℤ}
    (he : e = e') : μ.HasWeight e' ψ := by
  rwa [← he]

/-- Let `μ` be an automorphic character of `U(1)(𝔸)` for the CM field `E`, of weight `e` with tame
part `ψ` (residue characters `ψ_w` with `μ u = ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w)` for `u` with
integral finite part), and suppose `ψ` is trivial at the conjugate place `w̄` (`star w`). Let
`x ∈ E_w^×` be viewed as an idele at `w`, with `x` a local unit if `w` is split (`w̄ ≠ w`). Then
`x/x̄` has integral finite part, and the finite part of the base change `y ↦ μ(y/ȳ)` evaluated at
the finite idele `x` equals `ψ_w` of the finite part of `x/x̄` reduced mod `w`. -/
lemma AutChar.HasWeight.exists_baseChange_finPart_locIdele (hμ : μ.HasWeight e ψ)
    (hψ : ψ (star w) = 1) (x : (LocField w)ˣ) (hx : w.IsSplit → v x.val = 1) :
    ∃ h_int : (divStar (locFullIdele w x) : 𝔸 E).snd ∈ Ô E,
      μ.baseChange.finPart (locIdele w x) =
        ψ w (reduceAt w ⟨(divStar (locFullIdele w x) : 𝔸 E).snd, h_int⟩) := by
  classical
  -- `x / x̄` has component `1` at infinity and at all finite places other than `w` and `w̄`.
  have h_val (y : (LocField w)ˣ) (u : FinPlace E) :
      v ((locFullIdele w y : 𝔸 E).snd u) = if u = w then v (y : LocField w) else 1 := by
    aesop (add simp locFullIdele)
  -- It is integral: the valuations cancel if `w̄ = w`, and `x` is a unit otherwise.
  have h_int : (divStar (locFullIdele w x) : 𝔸 E).snd ∈ Ô E := by
    suffices h_le : ∀ u : FinPlace E,
        (if star u = w then if u = w then 1 else (v (x : LocField w))⁻¹
          else if u = w then v (x : LocField w) else 1) ≤ 1 by
      simpa [mem_Ô, h_val, ← map_inv, coe_divStar] using h_le
    -- If `w` is split, `v x = 1` and every value is `1`. Otherwise `w̄ = w`, so `star u = w`
    -- exactly when `u = w`, and the two valuations cancel at `w`.
    intro u
    by_cases h_split : w.IsSplit
    · simp [hx h_split]
    · have h_star_w : star w = w := not_not.mp h_split
      have h_star_iff : star u = w ↔ u = w := by rw [← h_star_w, star_inj, h_star_w]
      by_cases hu_eq : u = w <;> simp [hu_eq, h_star_iff, h_star_w]
  -- In the product that gives `μ (x / x̄)`, only the factor at `w` is left.
  have h_inf : ∏ u : InfinitePlace E, (divStar (locFullIdele w x) : 𝔸 E).fst u ^ e u = 1 := by
    simp [locFullIdele, ← map_inv, coe_divStar]
  have h_fin (u : FinPlace E) (hu : u ≠ w) :
      ψ u (reduceAt u ⟨(divStar (locFullIdele w x) : 𝔸 E).snd, h_int⟩) = 1 := by
    obtain rfl | hu_ne_star := eq_or_ne u (star w)
    · -- `ψ` is trivial at `w̄`, and the reduction is a unit (`isUnit_reduceAt_unitary`)
      simp [hψ, MulChar.one_apply]
    · simp [reduceAt, locFullIdele, ← map_inv, ← one_def, hu, hu_ne_star, RingHom.codRestrict,
        coe_divStar, star_singleAdele]
  refine ⟨h_int, (hμ.apply_eq _ h_int).trans ?_⟩
  rw [h_inf, one_mul, finprod_eq_single _ w h_fin]

/-- Let μ have weight e and tame part ψ, and let w be a finite place with w̄ ≠ w and ψ_{w̄}
trivial. Then the base change y ↦ μ(y/ȳ), at a local unit x placed at w, equals ψ_w(x mod
w). -/
lemma AutChar.HasWeight.baseChange_finPart_locIdele (hμ : μ.HasWeight e ψ) (hw : w.IsSplit)
    (hψ : ψ (star w) = 1) {x : (LocField w)ˣ} (hx : v x.val = 1) :
    μ.baseChange.finPart (locIdele w x) = ψ w (IsLocalRing.residue (LocInt w) ⟨x, hx.le⟩) := by
  obtain ⟨h_int, h_eq⟩ := hμ.exists_baseChange_finPart_locIdele hψ x fun _ ↦ hx
  -- As `w̄ ≠ w`, the component of `x / x̄` at `w` is `x`.
  have h_comp : reduceAt w ⟨(divStar (locFullIdele w x) : 𝔸 E).2, h_int⟩ =
      IsLocalRing.residue (LocInt w) ⟨x, hx.le⟩ := by
    simp [reduceAt, locFullIdele, ← map_inv, hw.symm, RingHom.codRestrict, coe_divStar,
      star_singleAdele]
  rw [h_eq, h_comp]

/-- Let μ be a continuous circle-valued character of U(1)(𝔸), the norm-one adeles of the CM field E,
trivial on elements of E. Suppose μ has weight e and tame part ψ, i.e. μ(u) = ∏_v u_v^{e(v)} · ∏_w
ψ_w(u mod w) when u has integral finite part. If w is a finite place with w̄ = w and ψ_w trivial,
then the base change y ↦ μ(y/ȳ) is trivial on E_w^×, viewed as finite ideles supported at w. -/
lemma AutChar.HasWeight.baseChange_finPart_locIdele_eq_one (hμ : μ.HasWeight e ψ)
    (hw : star w = w) (hψ : ψ w = 1) (x : (LocField w)ˣ) :
    μ.baseChange.finPart (locIdele w x) = 1 := by
  have hψ_star : ψ (star w) = 1 := by rwa [hw]
  obtain ⟨h_int, h_eq⟩ :=
    hμ.exists_baseChange_finPart_locIdele hψ_star x fun h_split ↦ absurd hw h_split
  -- The value is that of the trivial character `ψ w` at the reduction of `x / x̄`, a unit.
  exact Units.ext (by simpa [hψ, MulChar.one_apply] using h_eq)

namespace WeilData

variable [WeilData E]

/-! ### The splitting character on U(1) -/

/-- The restriction to U(1)(𝔸) of the splitting character υ of the Weil data has weight 1 at
every infinite place and trivial tame part. -/
instance upsilonU1_hasWeight : upsilonU1.HasWeight (E := E) 1 1 where
  finite_ramification := by simp
  apply_eq _ h := (υ_unit _ ⟨h, star_mem_Ô h⟩).trans (by simp [MulChar.one_apply])

/-- For every integer z, υ^z on U(1)(𝔸) has weight z at every infinite place and trivial tame
part. -/
instance hasWeight_upsilonU1_zpow (z : ℤ) :
    (upsilonU1 ^ z : AutChar E).HasWeight (fun _ : InfinitePlace E ↦ z) 1 := by
  -- `z • 1` is the constant weight `z`, and `1 ^ z = 1`.
  have h_zpow : (upsilonU1 ^ z : AutChar E).HasWeight (z • 1) 1 := by
    simpa only [one_zpow] using upsilonU1_hasWeight.zpow z
  exact h_zpow.of_weight_eq (funext fun _ ↦ by simp)

/-- For every natural number n, υ^n on U(1)(𝔸) has weight n at every infinite place and trivial tame
part. -/
instance hasWeight_upsilonU1_pow (n : ℕ) :
    (upsilonU1 ^ n : AutChar E).HasWeight (fun _ : InfinitePlace E ↦ (n : ℤ)) 1 :=
  hasWeight_upsilonU1_zpow n

/-- If μ has weight e and tame part ψ, then μ·υ^n has weight n + e and tame part ψ. -/
instance _root_.New.AutChar.HasWeight.mul_upsilonU1_pow [h : μ.HasWeight e ψ] (n : ℕ) :
    (μ * upsilonU1 ^ n).HasWeight (fun v : InfinitePlace E ↦ (n : ℤ) + e v) ψ := by
  have h_mul : (μ * upsilonU1 ^ n).HasWeight (e + fun _ ↦ (n : ℤ)) ψ := by
    simpa only [mul_one] using h.mul (hasWeight_upsilonU1_pow n)
  exact h_mul.of_weight_eq (funext fun _ ↦ add_comm _ _)

/-- If μ has weight e and tame part ψ, and n is a finite type with #n elements, then the character
μ·υ^⌊#n/2⌋ (`New.rankTwist μ n`) has weight e + ⌊#n/2⌋ at every infinite place and tame part ψ. -/
instance _root_.New.AutChar.HasWeight.hasWeight_rankTwist [h : μ.HasWeight e ψ] {n : Type*}
    [Fintype n] :
    (rankTwist μ n).HasWeight (fun v : InfinitePlace E ↦ ((Fintype.card n / 2 : ℕ) : ℤ) + e v) ψ :=
  h.mul_upsilonU1_pow (Fintype.card n / 2)

/-- The base change x ↦ υ(x/x̄) of the restriction of the splitting character υ to U(1)(𝔸)
equals the Hecke character υ². -/
@[simp]
lemma baseChange_upsilonU1 : upsilonU1.baseChange = υ (E := E) ^ 2 := by
  -- `υ (x / x̄) = υ x ^ 2`, since `υ x̄ = (υ x)⁻¹`.
  ext x : 2
  have h_div : Unitary.toUnits (divStar x) = x / star x := by aesop
  change upsilonU1.val (divStar x) = υ.val x ^ 2
  rw [upsilonU1_apply, h_div, map_div, υ_star, div_inv_eq_mul, sq]

end WeilData

end New

end SplittingCharOnU1

/-!
## Characters tamely ramified at split places, local data and theta integrals

The theta integral is defined for an arbitrary pair of characters of U(1)(𝔸). For a character
tamely ramified at split places, its character at the ramified places is shown to be tame.
-/

namespace New.Exchange

open NumberField Pi Space SemilocalField IsLocalRing WithZero MulChar

variable (E : Type) [Field E] [CMType E] [WeilData E]
  {F n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {s : n → ℤˣ}
  {s' : n' → ℤˣ} [SemilocalField F]
  (A : Set (FinPlace E)) (π : 𝔸f E →+* F) (S : Space E n s) (T : Space E n' s')
  (P : Finset (FinPlace E))

/-- A character ν (`character`) of [U(1)] of weight e, with e(v) > 0 for every v, and with tame part
ψ (`tamePart`) non-trivial exactly on a non-empty finite set S (`ramifiedPlaces`) of places disjoint
from its conjugate. -/
structure SplitTameChar (e : InfinitePlace E → ℤ) where
  /-- The character of the norm-one adeles. -/
  character : AutChar E
  /-- The tame part of `character`: a character of the residue field at each finite place. -/
  tamePart (w : FinPlace E) : MulChar (ResField w) ℂ
  /-- `character` has weight `e` and tame part `tamePart`. -/
  hasWeight : character.HasWeight e tamePart
  /-- The set of ramified places. -/
  ramifiedPlaces : Finset (FinPlace E)
  /-- At least one place is ramified. -/
  nonempty : ramifiedPlaces.Nonempty
  /-- The conjugate of a place of `ramifiedPlaces` is not in `ramifiedPlaces`; in particular these
  places are split. -/
  star_notMem : ∀ w ∈ ramifiedPlaces, star w ∉ ramifiedPlaces
  /-- The residue character `tamePart w` is non-trivial exactly when `w` is in `ramifiedPlaces`. -/
  ne_one_iff (w : FinPlace E) : tamePart w ≠ 1 ↔ w ∈ ramifiedPlaces
  /-- Every component of the weight `e` is positive. -/
  weight_pos (v : InfinitePlace E) : 0 < e v

attribute [instance] SplitTameChar.hasWeight

variable {E}

/-! ### Reading the components at a set of places -/

/-- π reads the components at A: A is disjoint from its conjugate, π is continuous with a
continuous additive section σ, σ(πx) being the A-part of x, and π(x) ∈ O iff x is integral
at A. -/
structure ReadsAt {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Set (FinPlace E))
    (π : 𝔸f E →+* F) where
  /-- No place of `A` has its conjugate in `A`. -/
  disjoint_star : A.IsConjDisjoint
  /-- `π x` lies in the subring `SemilocalField.O` exactly when `x` is integral at the places of
  `A`. -/
  mem_iff (x : 𝔸f E) : π x ∈ O ↔ idem A * x ∈ Ô E
  /-- `π` is continuous and has a continuous additive section `σ`, with `σ (π x)` the part of `x` at
  the places of `A`. -/
  exists_section :
      Continuous π ∧
      ∃ σ : F →+ 𝔸f E, Continuous σ ∧ (∀ y : F, π (σ y) = y) ∧ ∀ x : 𝔸f E, σ (π x) = idem A * x

/-- The multiplicative character of ∏_{w∈P} E_w that is t ↦ ξ(t)|t|^{k/2} on invertible
elements, t read as an idele, and 0 on the others. -/
def localChar (ξ : HeckeChar E) (k : ℤ) : MulChar (∀ i : P, LocField i.1) ℂ :=
  MulChar.ofUnitHom <|
    ∏ i : P,
      (ξ.finPart.comp (locIdele i) *
          MonoidHom.toHomUnits
            { toFun (t : (LocField i.1)ˣ) := (√‖t.1‖ : ℂ)
              map_one' := by simp
              map_mul' := by simp } ^ k).comp (Units.map (evalMonoidHom _ i))

variable {μ : InfinitePlace E → ℤ} {P A π} (𝔠 : SplitTameChar E μ) (a b : AutChar E)
  (f : 𝒮 (S.hom T)) (v : Heisenberg.IsVacuum.Model
    (Fock.realHeisenberg (realSigns E (homSigns s s'))))
  (Ψ : _ → ℂ) (i : P)

omit [WeilData E] in
/-- If `π` reads the components at `A`, then `π` composed with complex conjugation reads the
components at the conjugate places `star ⁻¹' A`. -/
lemma ReadsAt.star (h_read : ReadsAt A π) : ReadsAt (star ⁻¹' A) (π.comp (starRingEnd (𝔸f E))) := by
  -- the new section is the conjugate of the old one; conjugation moves `idem A` to the
  -- idempotent of the conjugate places (`star_idem`)
  obtain ⟨h_dis, h_mem, hπ, σ, hσ, h_sect⟩ := h_read
  have h_dis_star : (Star.star ⁻¹' A).IsConjDisjoint := by grind
  refine ⟨h_dis_star, ?_, hπ.comp continuous_star, .comp (starRingEnd (𝔸f E)) σ, hσ.star, ?_⟩
  · -- `star x` is integral at `w` exactly when `x` is integral at `star w`
    grind [idem_mul_mem_Ô, v_star_apply, star_star, starRingEnd_apply, π.comp_apply]
  · simp [h_sect, star_idem, starRingEnd_apply]

omit [WeilData E] in
/-- The projection to the ramified places of `𝔠` reads the components there. -/
lemma SplitTameChar.readsAt : ReadsAt 𝔠.ramifiedPlaces (evalPlaces 𝔠.ramifiedPlaces) := by
  -- the section is extension by zero
  have h_dis : (𝔠.ramifiedPlaces : Set (FinPlace E)).IsConjDisjoint := by grind [star_notMem]
  refine ⟨h_dis, ?_, by fun_prop, adeleOfLocal 𝔠.ramifiedPlaces, continuous_adeleOfLocal _,
    evalPlaces_adeleOfLocal _, adeleOfLocal_evalPlaces _⟩
  simp [mem_O_locProd, idem_mul_mem_Ô]

/-- The ring map from the integers of ∏_{w∈P} E_w to the residue field at the place i of P. -/
def residueAt {E : Type} [Field E] [NumberField E] {P : Finset (FinPlace E)} (i : P) :
    O (F := LocProd P) →+* ResField i.1 :=
  (residue (LocInt i.1)).comp
    ((evalRingHom (fun w : P ↦ LocField w.1) i).restrict O (LocInt i.1) (by aesop (add simp
      mem_O_locProd)))

/-- The vector of 𝒮(Hom(S,T)) obtained from the vacuum by applying the operator
`New.Space.schrodingerOp`, for the places A, of the function y ↦ Ψ(π y) on finite adelic matrices,
π acting entrywise. The argument of type `ReadsAt A π` only records that `π` reads the components
at `A`. -/
abbrev namedVector (Ψ : Matrix n' n F → ℂ) (_h_read : ReadsAt A π) : 𝒮 (S.hom T) :=
  (S.hom T).schrodingerOp A (fun y ↦ Ψ ((vecToMatrix y).map π)) (S.hom T).vacElem

/-- The datum in 𝒮(Hom(S,T)) with real part v, the function Ψ of the components at the places A read
through π, and the vacuum elsewhere. -/
abbrev localDatum (Ψ : Matrix n' n F → ℂ) (r : ReadsAt A π) : 𝒮 (S.hom T) :=
  (S.hom T).integrated v (delta% namedVector S T Ψ r)

/-- The function g ↦ ∫ θ^{S,T}_{a,b}(f)(g,h) dh on U(S) = G E s, for f in 𝒮(Hom(S,T)). Here h runs
over U(T) = G E s', and dh is the measure `T.quotMeasure` on [U(T)]. It is the integral of the theta
kernel `New.pairTheta` over [U(T)], for arbitrary characters a and b of U(1)(𝔸). -/
def thetaIntegral (g : G E s) : ℂ := ∫ h : G E s', pairTheta S T a b f (g, h) ∂T.quotMeasure

omit [WeilData E]

lemma evalPlaces_mem_O : ∀ x ∈ Ô E, evalPlaces P x ∈ O :=
  fun _ hx ↦ mem_O_locProd.mpr fun i ↦ mem_Ô.mp hx i

/-! ### Units at the places of P -/

@[simp]
lemma isUnit_iff_residueAt_ne_zero {u : O} : IsUnit u ↔ ∀ i : P, residueAt i u ≠ 0 := by
  simp [residueAt, ResField, Subtype.ext_iff, isUnit_iff_exists_inv, Classical.skolem, funext_iff,
    mem_O_locProd, forall_and]
  rfl

/-- The residue at `i` of an integral `u` is zero exactly when the component `u i` has valuation
below `1`. -/
@[local simp]
lemma residueAt_eq_zero {u : O} : residueAt i u = 0 ↔ Valued.v (u.val i) < 1 :=
  residue_eq_iff_valuation_sub_lt_one.trans (by simp)

/-- An element of ∏_{w∈P} E_w is an integral unit exactly when each component has valuation 1. -/
lemma isIntegralUnit_iff_v_eq_one {t : LocProd P} :
    IsIntegralUnit t ↔ ∀ i : P, Valued.v (t i) = 1 := by
  -- Integral means `v ≤ 1` at each place, a residue that is not zero means `1 ≤ v`.
  have h_unit_iff (ht : t ∈ O) : IsIntegralUnit t ↔ ∀ i : P, 1 ≤ Valued.v (t i) := by
    simpa only [ne_eq, residueAt_eq_zero, not_lt] using
      (isIntegralUnit_iff_isUnit (u := ⟨t, ht⟩)).trans isUnit_iff_residueAt_ne_zero
  constructor
  · rintro ⟨ht_O, ht_inv⟩ i
    exact le_antisymm (mem_O_locProd.mp ht_O i) ((h_unit_iff ht_O).mp ⟨ht_O, ht_inv⟩ i)
  · intro h_val
    exact (h_unit_iff (mem_O_locProd.mpr fun i ↦ (h_val i).le)).mpr fun i ↦ (h_val i).ge

namespace SplitTameChar

/-- The character t ↦ ν(t/t̄) of ∏_{w∈S} E_w, t read as an idele supported on S, extended by 0
to non-invertible elements. -/
abbrev semilocalChar : MulChar ((i : 𝔠.ramifiedPlaces) → LocField (i : FinPlace E)) ℂ :=
  localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange 0

/-! ### The character at the ramified places through its residue characters -/

/-- On a unit u of the ring of integers at S, the character `New.Exchange.localChar` of the base
change of ν is, for every k, the product over S of the residue characters ψ_w at the residues of
u. -/
lemma localChar_apply_of_isUnit (k : ℤ) (u : O (F := LocProd 𝔠.ramifiedPlaces)) (hu : IsUnit u) :
    localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange k u.val = ∏ i : 𝔠.ramifiedPlaces,
      𝔠.tamePart i (residueAt i u) := by
  have h_val : ∀ i : 𝔠.ramifiedPlaces, Valued.v (u.val i) = 1 :=
    isIntegralUnit_iff_v_eq_one.mp (isIntegralUnit_iff_isUnit.mpr hu)
  -- `erw`: `u.val` is the value of the unit `(hu.map O.subtype).unit` only up to unfolding.
  erw [ofUnitHom_coe _ (hu.map O.subtype).unit]
  -- The components of `u` have absolute value one, so the factors `√‖u i‖ ^ k` drop out; it
  -- remains to compare the factors at each `i ∈ S`.
  simp [FinitePlace.norm_def, h_val]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  -- At `i`, `ν (x / x̄)` for the unit `x = u i` is `ψ i` at the residue of `u`
  -- (`baseChange_finPart_locIdele`, which applies since `star i ∉ S`, so `ψ` is trivial there).
  have h_conj : star (i : FinPlace E) ∉ 𝔠.ramifiedPlaces := 𝔠.star_notMem i i.prop
  have hψ_conj : 𝔠.tamePart (star (i : FinPlace E)) = 1 := (𝔠.ne_one_iff _).not_right.mpr h_conj
  have h_split : (i : FinPlace E).IsSplit := fun h_eq ↦ h_conj (by simp [h_eq])
  -- `baseChange_finPart_locIdele` applies with these facts and `h_val`.
  apply_rules [𝔠.hasWeight.baseChange_finPart_locIdele]

/-- On a norm-one adele u with integral finite part, ν(u) is the weight factor ∏_v u_v^{μ(v)} times
the character `New.Exchange.SplitTameChar.semilocalChar` at the components of u at S. -/
lemma character_apply_of_integral (u : unitary (𝔸 E)) (hu : (u : 𝔸 E).2 ∈ Ô E) :
    𝔠.character.val u =
      (∏ v : InfinitePlace E, (u : 𝔸 E).1 v ^ μ v) * 𝔠.semilocalChar
        (evalPlaces 𝔠.ramifiedPlaces (u : 𝔸 E).2) := by
  have h_mem : evalPlaces 𝔠.ramifiedPlaces (u : 𝔸 E).2 ∈ O := evalPlaces_mem_O _ hu
  have h_unit : IsUnit (⟨_, h_mem⟩ : O (F := LocProd 𝔠.ramifiedPlaces)) :=
    isUnit_iff_residueAt_ne_zero.mpr fun i ↦ (isUnit_reduceAt_unitary u hu i).ne_zero
  -- Both sides are the weight factor times the product over `S` of `ψ` at the residues of `u`.
  have hψ_off : ∀ w ∉ 𝔠.ramifiedPlaces, 𝔠.tamePart w = 1 := fun w ↦ (𝔠.ne_one_iff w).not_right.mpr
  -- `erw`: `𝔠.semilocalChar` at `evalPlaces 𝔠.ramifiedPlaces u.2` is `localChar … 0` at the value
  -- of the unit `⟨evalPlaces 𝔠.ramifiedPlaces u.2, h_mem⟩` only up to unfolding.
  erw [𝔠.hasWeight.apply_eq u hu, finprod_tame_eq_prod_reduceU1 _ hψ_off,
    ← 𝔠.ramifiedPlaces.prod_attach,
    localChar_apply_of_isUnit 𝔠 0 ⟨evalPlaces 𝔠.ramifiedPlaces (u : 𝔸 E).2, h_mem⟩ h_unit]
  -- The reductions of `u` at each `i` by `reduceU1` and by `residueAt` agree by definition.
  have h_red : ∀ i : 𝔠.ramifiedPlaces,
      ((reduceU1 (i : FinPlace E) ⟨u, hu, nofun⟩ : (ResField i.1)ˣ) : ResField i.1) =
        residueAt i ⟨evalPlaces 𝔠.ramifiedPlaces (u : 𝔸 E).2, h_mem⟩ :=
    fun i ↦ rfl
  simp only [h_red, Finset.univ_eq_attach]

open scoped Classical in
/-- The tameness data (`New.TameLocalChar`) of t ↦ ν(t/t̄)|t|^{k/2} on ∏_{w∈S} E_w: the product of
the residue fields at S, with the character ∏ψ_w⁻¹ on it. -/
instance tameLocalChar (k := 0) : TameLocalChar
  (localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange k) where
  -- the product over `S` of the residue fields
  ResidueRing := _
  reduction := .pi residueAt
  resChar := ⟨∏ i : 𝔠.ramifiedPlaces, (𝔠.tamePart i)⁻¹.comp (evalMonoidHom _ i), by
    simp [isUnit_iff, Finset.prod_eq_zero_iff, apply_eq_zero_iff]⟩
  reduction_surjective_and_eq_zero_iff := by
    constructor
    · -- Lift each component of `r` from the residue field.
      intro r
      simpa [Classical.skolem, funext_iff, mem_O_locProd] using! fun i ↦ residue_surjective (r i)
    · simp [ϖ, ← lt_mul_exp_iff_le, funext_iff, mem_O_locProd]
  isPrimitive_resChar_and_invOnUnits_eq := by
    constructor
    · -- Primitivity: if `a i ≠ 0`, solve `1 + a y = x` at `i` for a unit `x` with `ψ i x ≠ 1`.
      intro a ha
      obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
      obtain ⟨x, hx⟩ := MulChar.ne_one_iff.1 ((𝔠.ne_one_iff i).2 i.2)
      exact ⟨(mulSingle i x - 1) / a, by
        simp_all [Finset.prod_eq_single i, inv_apply_eq_inv', apply_eq_zero_iff]⟩
    · -- On units this is `localChar_apply_of_isUnit`; a non-unit has residue `0` at some place, so
      -- both sides are `0`.
      simp_all [invOnUnits, ↓isIntegralUnit_iff_isUnit, localChar_apply_of_isUnit, @eq_comm ℂ 0,
        inv_apply_eq_inv', Finset.prod_eq_zero_iff, apply_eq_zero_iff]

end SplitTameChar

end New.Exchange

end
