import Lib.ClassField.Global.CMSplittingCharacters
import Lib.ClassField.Global.Chebotarev
import Lib.ClassField.Global.ExistenceTheorem
import Lib.General.NumberTheory.FrobeniusOrbits

/-!
# Auxiliary primes, anticyclotomic characters, slopes and ties

The setting is a CM field `E` and anticyclotomic characters of `Gal(Ω/E)` with values in `ℤ/q`. The
file defines data at auxiliary primes and sets of auxiliary primes. Chebotarev's theorem yields
auxiliary primes carrying such data.

## Main definitions and results

* `New.IsAuxPrimeDataAt`: a prime `P ≠ P̄` of norm `≡ 1 mod q` outside `T`, with a Frobenius
  element, a generator of tame inertia and a character to `ℤ/q` that comes from an idele class
  character of level `P` (`New.IsFromU1`).
* `New.IsAuxiliary`: finite sets of primes of prime norm, disjoint from their conjugates, with
  neither the primes nor their conjugates in `S`.
* `New.Selmer.exists_anticyclotomicChar_of_frob_fixes_roots`: a Galois character that sends the tame
  generator above a prime `P` to the generator `1 ∈ ℤ/q` and comes from an idele class character of
  level `P`.
* `New.Selmer.exists_isAuxPrimeDataAt`: an auxiliary prime `P` of `E` of prime norm with data
  `New.Selmer.AuxPrimeData`. These include a Frobenius element close to a given element of the
  normal closure of the inertia groups at the places of a finite set `R` outside `S ∪ S̄` and not
  above `ℓ`, and a character of `Gal(Ω/E)` to `ℤ/ℓ^N` that is trivial at this Frobenius element. The
  data satisfy `New.IsAuxPrimeDataAt` for every `T` contained in `S ∪ {v ∣ ℓ}`.
* `New.Selmer.IsTiedPrimes`: a set `J` of auxiliary primes with their data (place, tame generator
  `γ = tameGenerator`, Frobenius `φ = frob`, character, slopes) and a first prime `P₀`.
* `New.Selmer.tieRelations`: the relations `z γ = s • z φ` imposed on cocycles at the primes of `J`
  and their conjugates.

Notions from other files:
* `New.IsFrob`: `σ` stabilises the valuation subring `A` and `σ • x ≡ x ^ q` modulo the maximal
  ideal for all `x ∈ A`.
* `New.IsPlaceOver.tameGenerator`: a chosen generator of tame inertia at a place above `w`, as an
  element of the inertia group.
* `New.idOrConjInv`: `g` if `b` is true, and `g^{-c} = (conjGal g)⁻¹` if `b` is false.

## Relation to the literature

See `New.Congruences.Selmer.TwistingTheorem` and `New.Congruences.Selmer.Descent` for related work.
-/

noncomputable section

/-!
## Auxiliary prime data and auxiliary sets of primes
-/

namespace New

/-- The data at an auxiliary prime of a CM field `E` inside `Ω`, the algebraic closure of `ℚ`: a
place `place` of `Ω`, two elements `tameGenerator` and `frob` of `Gal(Ω/E)`, and a homomorphism
`character` from `Gal(Ω/E)` to `ℤ/q`. -/
structure Selmer.AuxPrimeData (E : Type*) [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E] (q : ℕ) where
  /-- A place of `Ω`, meant to lie over the auxiliary prime. -/
  place : ClosurePlace
  /-- The element meant to be the tame generator of inertia at `place`. -/
  tameGenerator : Gal(Ω/E)
  /-- The element meant to be a Frobenius at `place`. -/
  frob : Gal(Ω/E)
  /-- The character to `ℤ / q` attached to the prime. -/
  character : Gal(Ω/E) →* Multiplicative (ZMod q)

/-- For auxiliary prime data `l`: `P ≠ P̄` has norm `≡ 1 mod q` and lies outside `T`, `l.frob` is a
Frobenius and `l.tameGenerator` the chosen tame generator at the place `l.place` over `P`, and the
character `l.character` to `ℤ/q` comes from an idele class character of level `P` (`New.IsFromU1`
for `T` and `{P}`) and takes the value `1 ∈ ℤ/q` at `l.tameGenerator`. -/
structure IsAuxPrimeDataAt {E : Type} [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E] (T : Set (FinPlace E))
    (P : FinPlace E) {q : ℕ} (l : Selmer.AuxPrimeData E q) :
      Prop extends IsFromU1 T {P} l.character where
  /-- The norm of `P` is congruent to `1` modulo `q`. -/
  norm_modEq : P.q ≡ 1 [MOD q]
  /-- The valuation subring `l.place` of `Ω` lies over `P`. -/
  isPlaceOver : IsPlaceOver l.place P
  /-- `l.frob` is an arithmetic Frobenius at `l.place`: it stabilises `l.place` and acts on residues
  as the power `P.q`. -/
  isFrob : IsFrob l.place P.q l.frob
  /-- The prime `P` does not lie in `T`. -/
  notMem : P ∉ T
  /-- The prime `P` is not its own conjugate. -/
  star_ne : star P ≠ P
  /-- `l.tameGenerator` lies in the inertia group of `l.place`, `l.character` sends it to
  `1 ∈ ℤ/q`, and it is the chosen generator of tame inertia at `l.place`. -/
  tame_gen :
      l.tameGenerator ∈ inertiaGroup Gal(Ω/E) l.place ∧
      l.character l.tameGenerator = Multiplicative.ofAdd 1 ∧
      isPlaceOver.tameGenerator = l.tameGenerator

/-- A finite set `I` of places is auxiliary for `S` if every place of `I` has prime norm, neither it
nor its conjugate lies in `S`, and its conjugate lies outside `I`. -/
@[grind]
def IsAuxiliary {E : Type*} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
    (S I : Finset (FinPlace E)) : Prop :=
  ∀ v ∈ I, v ∉ S ∧ v.q.Prime ∧ star v ∉ I ∧ star v ∉ S

end New

/-!
## An anticyclotomic character ramified at a new prime with prescribed Frobenius

`P` comes from Chebotarev's theorem so that, for a suitable finite set `T` of places, all `T`-units
are `ℓ^N`-th powers modulo `P`. The discrete logarithm at `P` then descends to idele classes.
-/

section AnticyclotomicChar

open NeZero Nat Subgroup QuotientGroup MonoidHom Valued Multiplicative
open scoped Pointwise

/-- A discrete logarithm at `P`: let `P.q = 1 + q * k` be prime and let the residue of the local
unit `u` generate the units of the residue field. Then some character of `E_Pˣ` to `ℤ/q` sends `u`
to the generator `1` and is trivial on every `t` with `t ≡ 1` or `t ^ k ≡ 1` modulo `P`. -/
lemma New.Selmer.exists_discreteLog {E : Type*} [Field E] [NumberField E] {P : FinPlace E}
    {q k : ℕ} (hp : P.q.Prime) (hk : P.q = 1 + q * k) {u : (LocField P)ˣ}
    (hu : u ∈ (LocInt P).unitGroup)
    (h_gen : ∀ z : (IsLocalRing.ResidueField (LocInt P))ˣ,
      z ∈ zpowers ((LocInt P).unitGroupToResidueFieldUnits ⟨u, hu⟩)) :
    ∃ lg : (LocField P)ˣ →* Multiplicative (ZMod q),
      lg u = ofAdd 1 ∧
      (∀ t : (LocField P)ˣ, v (t.val - 1) < 1 → lg t = 1) ∧
      ∀ t : (LocField P)ˣ, v ((t ^ k).val - 1) < 1 → lg t = 1 := by
  set g : (IsLocalRing.ResidueField (LocInt P))ˣ := (LocInt P).unitGroupToResidueFieldUnits ⟨u, hu⟩
  have hu_unit : v u.val = 1 := (v.mem_unitGroup_iff _ u).mp hu
  have h_unit_mem (t : (LocField P)ˣ) :
      t * uniformizer P ^ (v t.val).log ∈ (LocInt P).unitGroup := by
    refine (v.mem_unitGroup_iff ..).mpr ?_
    have h_cancel : v t.val * WithZero.exp (-(v t.val).log) = 1 := by
      rw [WithZero.exp_neg, WithZero.exp_log (by simp), mul_inv_cancel₀ (by simp)]
    simpa [v_uniformizer, ← WithZero.exp_zsmul] using h_cancel
  -- `unitPart` divides out the power of the uniformizer; `residueUnit` is the residue of the result
  let unitPart : (LocField P)ˣ →* (LocInt P).unitGroup :=
    .mk' (fun t ↦ ⟨t * uniformizer P ^ (v t.val).log, h_unit_mem t⟩) <| by
      intro t t'
      have h_log : (v (t * t').val).log = (v t.val).log + (v t'.val).log := by simp
      ext1
      simp only [Subgroup.coe_mul, h_log, zpow_add]
      exact mul_mul_mul_comm ..
  let residueUnit : (LocField P)ˣ →* (IsLocalRing.ResidueField (LocInt P))ˣ :=
    (LocInt P).unitGroupToResidueFieldUnits.comp unitPart
  have h_residue_one (t : (LocField P)ˣ) (ht : v (t.val - 1) < 1) : residueUnit t = 1 := by
    have ht_unit : v t.val = 1 := by simpa using v.map_one_add_of_lt ht
    exact Units.ext (residue_eq_iff_valuation_sub_lt_one.mpr (by simpa [unitPart, ht_unit]))
  have h_order : orderOf g = q * k := by
    rw [orderOf_eq_card_of_forall_mem_zpowers h_gen, card_units, ← tsub_eq_of_eq_add_rev hk,
      ← card_ResField P]
    rfl
  have h_order_dvd : orderOf (ofAdd (1 : ZMod q)) ∣ orderOf g := by simp [h_order]
  -- `lg` is `residueUnit` followed by the character of the residue units that sends `g` to `1`
  let lg : (LocField P)ˣ →* Multiplicative (ZMod q) :=
    (monoidHomOfForallMemZpowers h_gen h_order_dvd).comp residueUnit
  have hlg_u : lg u = ofAdd 1 := by simp [lg, residueUnit, unitPart, hu_unit, g]
  refine ⟨lg, hlg_u, fun t ht ↦ by simp [lg, h_residue_one t ht], fun t ht ↦ ?_⟩
  -- `residueUnit t = g ^ e` has `k`-th power `1`, so the order `q * k` of `g` divides `e * k`
  obtain ⟨e, he⟩ : ∃ e : ℤ, g ^ e = residueUnit t := h_gen (residueUnit t)
  have h_residue_pow : residueUnit t ^ k = 1 := by simpa using h_residue_one _ ht
  have h_dvd : (q * k : ℤ) ∣ e * k := by
    simpa [← he, ← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, h_order]
      using h_residue_pow
  have hk_ne : k ≠ 0 := fun h ↦ hp.one_lt.ne' (by simpa [h] using hk)
  have hq_dvd : (q : ℤ) ∣ e := Int.dvd_of_mul_dvd_mul_right (Int.natCast_ne_zero.2 hk_ne) h_dvd
  simpa [lg, ← he, ← orderOf_dvd_iff_zpow_eq_one] using hq_dvd

/-- Let `σ` be a Frobenius at a place above `P`, with `P.q = 1 + n * k`. If `σ` fixes an `n`-th root
of a `T`-unit `u`, where `P ∉ T`, then `u ^ k ≡ 1` modulo `P`. -/
lemma New.Selmer.valuation_pow_sub_one_lt_one_of_isFrob {E : Type*} [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E]
    {A : ClosurePlace} {P : FinPlace E} (hA : IsPlaceOver A P) {σ : Gal(Ω/E)} (hσ : IsFrob A P.q σ)
    {n k : ℕ} [NeZero n] (hk : P.q = 1 + n * k) {T : Set (FinPlace E)} (hPT : P ∉ T) {u : Eˣ}
    (hu : u ∈ T.unit E) {y : Ω} (hy : y ^ n = algebraMap E Ω u) (hy_fix : σ • y = y) :
    v ((ideleAt P (principalIdele u) ^ k).val - 1) < 1 := by
  have hy_unit : A y = 1 := by
    simpa [ne, ← hy, valuationVia] using hA.valuationVia_eq_one_iff.mpr (hu P hPT)
  -- `y = σ y ≡ y ^ P.q = y * u ^ k`, and `y` is a unit at `A`
  have h_cong : A (algebraMap E Ω (u ^ k - 1)) < 1 := by
    have h_res : A (y - y * algebraMap E Ω (u : E) ^ k) < 1 := by
      simpa [hy_fix, hk, hy, pow_add, pow_mul] using hσ.2 y hy_unit.le
    simpa [hy_unit, ← mul_one_sub, Valuation.map_sub_swap] using h_res
  change v ((algebraMap E (LocField P) u) ^ k - 1) < 1
  simpa using (v_algebraMap_eq_valuation _).trans_lt (hA.isEquiv.lt_one_iff_lt_one.mp h_cong)

/-- Let the principal ideles and the `T`-ideles (those that are units off `T`) generate all finite
ideles. A continuous character `lg` of `E_Pˣ` that kills the `T`-units extends to a continuous
character of the idele classes which on `T`-ideles is `lg` of the component at `P`. -/
lemma New.Selmer.exists_ideleClassChar_of_local {E : Type*} [Field E] [NumberField E]
    {T : Set (FinPlace E)} (h_gen : principalIdele.range ⊔ idelesUnitOff T = ⊤) {P : FinPlace E}
    {C : Type*} [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C] {lg : (LocField P)ˣ →* C}
    (hlg_cont : Continuous lg) (hlg_unit : ∀ x ∈ T.unit E, lg (ideleAt P (principalIdele x)) = 1) :
    ∃ θ : (𝔸f E)ˣ →* C,
      Continuous θ ∧
      (∀ x : Eˣ, θ (principalIdele x) = 1) ∧
      ∀ a ∈ idelesUnitOff T, θ a = lg (ideleAt P a) := by
  -- the `T`-ideles map onto the idele classes with kernel the `T`-units, so `lg` at `P` descends
  let cls : (𝔸f E)ˣ →* (𝔸f E)ˣ ⧸ principalIdele.range := mk' principalIdele.range
  let π : idelesUnitOff T →* (𝔸f E)ˣ ⧸ principalIdele.range := cls.domRestrict (idelesUnitOff T)
  have hπ : Function.Surjective π :=
    range_eq_top.mp (comap_injective (mk'_surjective _) (by simpa [π, cls] using h_gen))
  let lgT : idelesUnitOff T →* C := (lg.comp (ideleAt P)).domRestrict (idelesUnitOff T)
  have h_ker : π.ker ≤ lgT.ker := by
    rintro ⟨a, ha⟩ h1
    obtain ⟨x, rfl⟩ : a ∈ principalIdele.range := (eq_one_iff a).mp h1
    exact hlg_unit x (principalIdele_mem_idelesUnitOff.mp ha)
  let η : (𝔸f E)ˣ ⧸ principalIdele.range →* C := π.liftOfSurjective hπ ⟨lgT, h_ker⟩
  let θ : (𝔸f E)ˣ →* C := η.comp cls
  have hθ_rat (x : Eˣ) : θ (principalIdele x) = 1 := by
    simp [θ, show cls (principalIdele x) = 1 from (eq_one_iff _).mpr ⟨x, rfl⟩]
  have hθ (a : (𝔸f E)ˣ) (ha : a ∈ idelesUnitOff T) : θ a = lg (ideleAt P a) := by
    change η (π ⟨a, ha⟩) = lgT ⟨a, ha⟩
    exact π.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hπ) ⟨lgT, h_ker⟩ ⟨a, ha⟩
  -- `θ` agrees with `lg` at `P` on the open group of `T`-ideles
  have hθ_cont_on : ContinuousOn θ (SetLike.coe (idelesUnitOff T)) :=
    (hlg_cont.comp_continuousOn (by fun_prop)).congr hθ
  exact ⟨θ, continuous_of_continuousAt_one _
    (hθ_cont_on.continuousAt ((isOpen_idelesUnitOff T).mem_nhds (one_mem _))), hθ_rat, hθ⟩

/-- Let `E` be a CM field, `Ω` the algebraic closure of `ℚ` containing it, and `T` a set of finite
places such that the ideles that are units off `T` (the `T`-ideles) and the principal ideles
generate all finite ideles. Let `P ∉ T`, `P ≠ P̄`, have prime norm `1 + q * k`, and let a Frobenius
`σ` at a place `A` over `P` fix a `q`-th root of each element of a finite set `s` that generates the
`T`-units. Then there is a continuous character `χ` of `Gal(Ω/E)` with values in `ℤ/q` that takes
the value `1` at `hA.tameGenerator`, the generator of tame inertia at `A` fixed in
`New.IsPlaceOver.tameGenerator`. It satisfies `χ (Art x) = θ (x / x̄)` for the Artin map `Art` and a
character `θ` of the finite ideles that is trivial on `Eˣ` and on the `T`-ideles congruent to `1` at
`P`. -/
lemma New.Selmer.exists_anticyclotomicChar_of_frob_fixes_roots {E : Type} [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E] {q k : ℕ} [NeZero q] {T : Set (FinPlace E)}
    (h_gen : principalIdele.range ⊔ idelesUnitOff T = ⊤) {s : Finset (Additive (T.unit E))}
    (hs : Submodule.span ℤ (s : Set (Additive (T.unit E))) = ⊤) {P : FinPlace E}
    (hp : P.q.Prime) (hk : P.q = 1 + q * k) (hPT : P ∉ T) (hP_ne_star : star P ≠ P)
    {A : ClosurePlace} (hA : IsPlaceOver A P) {σ : Gal(Ω/E)} (hσ : IsFrob A P.q σ)
    (h_fix : ∀ u ∈ s, ∃ y : Ω, y ^ q = algebraMap E Ω (u.toMul : Eˣ) ∧ σ • y = y) :
    ∃ (χ : Gal(Ω/E) →* Multiplicative (ZMod q)) (θ : (𝔸f E)ˣ →* Multiplicative (ZMod q)),
      Continuous χ ∧
      χ hA.tameGenerator = ofAdd 1 ∧
      (∀ x : Eˣ, θ (principalIdele x) = 1) ∧
      (∀ a ∈ idelesUnitOff T, v ((ideleAt P a).val - 1) < 1 → θ a = 1) ∧
      ∀ (x : (𝔸f E)ˣ) (g : Gal(Ω/E)), artinMap Gal(Ω/E) x = g → χ g = θ (x / star x) := by
  -- The discrete logarithm at `P` kills the `T`-units, so extends to a character `θ` of the idele
  -- classes; the existence theorem turns `θ (x / star x)` into a Galois character.
  obtain ⟨u₀, hu₀_mem, hu₀_art, hu₀_gen, hu₀_unit⟩ := hA.exists_isTameUnit
  obtain ⟨lg, hlg_u₀, hlg_one, hlg_pow⟩ := exists_discreteLog hp hk hu₀_mem hu₀_gen
  have hlg_gen (u : Additive (T.unit E)) (hu : u ∈ s) :
      lg (ideleAt P (principalIdele u.toMul)) = 1 := by
    obtain ⟨y, hy, hy_fix⟩ := h_fix u hu
    exact hlg_pow _ (valuation_pow_sub_one_lt_one_of_isFrob hA hσ hk hPT u.toMul.property hy hy_fix)
  let lgT : T.unit E →* Multiplicative (ZMod q) :=
    (lg.comp (ideleAt P)).comp (principalIdele.domRestrict (T.unit E))
  have h_ker : lgT.ker.toAddSubgroup.toIntSubmodule = ⊤ := by
    rw [eq_top_iff, ← hs]
    exact Submodule.span_le.2 hlg_gen
  have hlg_unit (x : Eˣ) (hx : x ∈ T.unit E) : lg (ideleAt P (principalIdele x)) = 1 :=
    Submodule.eq_top_iff'.1 h_ker (Additive.ofMul ⟨x, hx⟩)
  -- `lg.ker` is open, as it contains all powers with exponent its finite index
  have hlg_cont : Continuous lg :=
    .of_isOpen_ker lg (isOpen_of_forall_pow_mem index_ne_zero_of_finite lg.ker.pow_index_mem)
  obtain ⟨θ, hθ_cont, hθ_rat, hθ⟩ := exists_ideleClassChar_of_local h_gen hlg_cont hlg_unit
  let θ' : (𝔸f E)ˣ →* Multiplicative (ZMod q) := θ.comp (.id _ / starMulAut.toMonoidHom)
  have hθ'_rat (x : Eˣ) : θ' (principalIdele x) = 1 := by
    have h_conj : star (principalIdele x) = principalIdele (star x) := by
      ext1
      simp [principalIdele]
    change θ (principalIdele x / star (principalIdele x)) = 1
    rw [h_conj, ← map_div, hθ_rat]
  obtain ⟨χ, hχ_cont, hχ⟩ := exists_comp_artinMap Gal(Ω/E) θ'
    (hθ_cont.comp (continuous_id.div' continuous_star)) hθ'_rat
  refine ⟨χ, θ, hχ_cont, ?_, hθ_rat, fun a ha ha_one ↦ (hθ a ha).trans (hlg_one _ ha_one), hχ⟩
  -- the tame generator is the Artin symbol of `u₀` at `P`; its conjugate has component `1` at `P`
  have h_art : artinMap Gal(Ω/E) (locIdele P u₀) = hA.tameGenerator.1 := by
    rw [artinMap_locIdele, hA.artinAt_eq_of_localArtin_eq hu₀_art]
  have h_conj_mem : star (locIdele P u₀) ∈ idelesUnitOff T := by
    rw [star_locIdele]
    exact locIdele_mem_idelesUnitOff (by simpa using hu₀_unit)
  have hθ_conj : θ (star (locIdele P u₀)) = 1 := by
    rw [hθ _ h_conj_mem]
    simp [star_locIdele, hP_ne_star.symm]
  rw [hχ _ _ h_art]
  change θ (locIdele P u₀ / star (locIdele P u₀)) = ofAdd 1
  rw [map_div, hθ_conj, div_one, hθ _ (locIdele_mem_idelesUnitOff hu₀_unit)]
  simpa using hlg_u₀

/-- Let `q` be a unit at all places off `T`, let the places of `R` lie off `T`, and let `y x` be a
`q`-th root of `x`. Then an element of the normal closure of the inertia groups above `R` fixes the
`q`-th roots of unity and the roots `y u` of each element `u` of a set `s` of `T`-units. -/
lemma New.Selmer.mem_ker_inf_stabilizer_of_mem_normalClosure {E : Type} [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E]
    {q : ℕ} [NeZero q] {T R : Set (FinPlace E)} (hRT : ∀ w ∈ R, w ∉ T)
    (hq : ∀ (w : FinPlace E) (A : ClosurePlace), w ∉ T → IsPlaceOver A w → A (q : Ω) = 1)
    {y : E → Ω} (hy : ∀ x : E, y x ^ q = algebraMap E Ω x) (s : Finset (Additive (T.unit E)))
    {z : Gal(Ω/E)} (hz_mem : z ∈ normalClosure (inertiaAbove R)) :
    z ∈ (cyclotomicCharMod Ω q).ker ⊓
      ⨅ u : s, MulAction.stabilizer Gal(Ω/E) (y (u.val.toMul : Eˣ)) := by
  let U : Subgroup Gal(Ω/E) :=
    (cyclotomicCharMod Ω q).ker ⊓ ⨅ u : s, MulAction.stabilizer Gal(Ω/E) (y (u.val.toMul : Eˣ))
  -- the inertia groups in question lie in `U` together with all their conjugates
  have h_ine : inertiaAbove R ⊆ U.normalCore := by
    rintro g ⟨w, hw, A, hA, hg⟩ b
    have hA_conj : IsPlaceOver (b • A) w := hA.smul b
    have hq_unit : (b • A) (q : Ω) = 1 := hq w _ (hRT w hw) hA_conj
    refine ⟨cyclotomicCharMod_eq_one_of_mem_inertiaGroup (hg.conj b) hq_unit,
      mem_iInf.2 fun u ↦ ?_⟩
    -- `u` is a unit at `w`, so inertia above `w` fixes its `q`-th roots
    have hu_unit : w.valuation E (u.val.toMul : Eˣ) = 1 := u.val.toMul.property w (hRT w hw)
    exact Cohomology.inertia_fixes_root_of_unit (hg.conj b) hq_unit (hy _)
      (hA_conj.valuationVia_eq_one_iff.2 hu_unit) (by simp)
  exact U.normalCore_le (U.normalCore.normalClosure_le_normal h_ine hz_mem)

/-- Chebotarev gives auxiliary primes with prescribed Frobenius. Let `E` be a CM field in `Ω`, the
algebraic closure of `ℚ`, `ℓ` a prime (`New.ThePrime`), `S` and `R` finite sets of places of `E`,
and `W` a neighbourhood of an element `z` of the normal closure of the inertia groups at the places
of `R` that are outside `S ∪ S̄` and not above `ℓ`. Then there are a prime `P ∉ R ∪ R̄` of prime
norm and data `auxData`, made of a place `place` of `Ω`, elements `tameGenerator` and `frob` of
`Gal(Ω/E)` and a `character` to `ℤ / ℓ ^ N`, such that (a) `frob ∈ W` and `character` is trivial at
`frob`, and (b) `New.IsAuxPrimeDataAt` holds for every `T ⊆ S ∪ {v ∣ ℓ}`. -/
lemma New.Selmer.exists_isAuxPrimeDataAt {E : Type} [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E] {ℓ : ℕ}
    [ThePrime ℓ] (N : ℕ) (S : Finset (FinPlace E)) {R : Set (FinPlace E)} (hR_fin : R.Finite)
    {z : Gal(Ω/E)} {W : Set Gal(Ω/E)}
    (hz_mem : z ∈ normalClosure (inertiaAbove (R \ (Set.conjClosure S ∪ placesDividing E ℓ))))
    (hW : W ∈ nhds z) :
    ∃ P : FinPlace E, P ∉ R.conjClosure ∧
      P.q.Prime ∧
      ∃ auxData : AuxPrimeData E (ℓ ^ N),
        -- (a)
        auxData.frob ∈ W ∧ auxData.character auxData.frob = 1 ∧
        -- (b)
        ∀ T : Set (FinPlace E), T ⊆ ↑S ∪ placesDividing E ℓ → IsAuxPrimeDataAt T P auxData := by
  -- Take a finite `T` containing `S`, its conjugate and the places above `ℓ`, but no other place of
  -- `R`, whose ideles map onto the idele classes. The open group `U` fixing the `ℓ ^ N`-th roots of
  -- the `T`-units contains `z`; Chebotarev gives `P` with its Frobenii in `U` and in `W`. This
  -- gives the character `χ`; correct the Frobenius by tame inertia so that `χ` is trivial at it.
  obtain ⟨T, hT, hST, hRT, h_gen⟩ :=
    exists_sup_idelesUnitOff_eq_top (↑S ∪ placesDividing E ℓ).toFinite.conjClosure R hR_fin
  -- `ℓ` is a unit above the places off `T`
  have hℓ {w : FinPlace E} {A : ClosurePlace} (hw : w ∉ T) (hA : IsPlaceOver A w) :
      A (ℓ ^ N : ℕ) = 1 := by
    have hℓw : ↑ℓ ∉ w.asIdeal := fun h ↦ hw (hST (.inl (.inr h)))
    simp [hA.valuation_natCast_eq_one_iff, hℓw]
  -- the `T`-units are finitely generated, say by `s`
  obtain ⟨h_finite, -⟩ := SUnit.dirichlet_unit_theorem (K := E) hT
  obtain ⟨s, hs⟩ : ∃ s : Finset (Additive (T.unit E)),
      Submodule.span ℤ (s : Set (Additive (T.unit E))) = ⊤ := h_finite.fg_top
  have h_root (x : E) : ∃ y : Ω, y ^ ℓ ^ N = algebraMap E Ω x :=
    Variety.IsAbsIntegrallyClosed.exists_pow_eq (ℓ ^ N) (algebraMap E Ω x)
  choose y hy using h_root
  -- `U` fixes the roots of unity of order `ℓ ^ N` and the roots of the generators of the `T`-units
  let U : Subgroup Gal(Ω/E) :=
    (cyclotomicCharMod Ω (ℓ ^ N)).ker ⊓
      ⨅ u : s, MulAction.stabilizer Gal(Ω/E) (y (u.val.toMul : Eˣ))
  have hU_open : IsOpen (SetLike.coe U) := isOpen_ker_cyclotomicCharMod.1.inter
    (by simp [isOpen_iInter_of_finite, stabilizer_isOpen_of_isIntegral])
  -- the inertia groups in question sit at places off `T`, so `z` lies in `U`
  have hz : z ∈ U := by
    refine mem_ker_inf_stabilizer_of_mem_normalClosure ?_ (fun _ _ ↦ hℓ) hy s hz_mem
    rintro w ⟨hwR, hw⟩ hwT
    have hw_conj : w ∈ (↑S ∪ placesDividing E ℓ).conjClosure := hRT w hwR hwT
    simp_all
  -- Chebotarev: `P ≠ P̄` off `T ∪ R ∪ R̄` of prime norm, `A` over `P` and a Frobenius `σ` at `A`;
  -- every Frobenius at `A` lies in `U` and has `W` as a neighbourhood (`h_frob`)
  obtain ⟨P, hP, hp, A, hA, σ, ⟨⟨hσ_cyc, hσ_root⟩, -⟩, hσ, h_frob⟩ := chebotarev
    (hU_open.inter (isOpen_setOfPred_eventually_nhds (p := (· ∈ W)))) ⟨z, hz, hW⟩
    ((hT.union hR_fin.conjClosure).union (finite_prime_q_star_eq E))
  have hPT : P ∉ T := fun h ↦ hP (.inl (.inl h))
  have hP_ne_star : star P ≠ P := fun h ↦ hP (.inr ⟨hp, h⟩)
  -- `σ` fixes the roots of unity, so the norm of `P` is `1` modulo `ℓ ^ N`
  have h_norm : P.q ≡ 1 [MOD ℓ ^ N] := (hσ.mem_ker_cyclotomicCharMod_iff (hℓ hPT hA)).1 hσ_cyc
  obtain ⟨k, hk⟩ : ∃ k : ℕ, P.q = 1 + ℓ ^ N * k := (modEq_iff_exists_eq_add hp.pos).1 h_norm.symm
  obtain ⟨χ, θ, hχ_cont, hχ_tg, hθ_rat, hθ_one, hχ⟩ :=
    exists_anticyclotomicChar_of_frob_fixes_roots h_gen hs hp hk hPT hP_ne_star hA hσ
      fun u hu ↦ ⟨y (u.toMul : Eˣ), hy _, mem_iInf.1 hσ_root ⟨u, hu⟩⟩
  -- multiply `σ` by a power of the tame generator to get a Frobenius `τ` at which `χ` is trivial
  let τ : Gal(Ω/E) := σ * hA.tameGenerator.1 ^ (χ σ⁻¹).toAdd.val
  have hτ : IsFrob A P.q τ := by simpa using hσ.mul_iff.2 (pow_mem hA.tameGenerator.2 _)
  have hχτ : χ τ = 1 := by simp [τ, hχ_tg, ← ofAdd_nsmul]
  obtain ⟨-, hτW⟩ := h_frob τ hτ
  have hχ_lc : IsLocallyConstant χ := fun V ↦ hχ_cont.isOpen_preimage V (isOpen_discrete V)
  refine ⟨P, fun h ↦ hP (.inl (.inr h)), hp, ⟨A, hA.tameGenerator, τ, χ⟩, hτW.self_of_nhds, hχτ,
    fun T' hT' ↦ ?_⟩
  have hT'T : T'.conjClosure ⊆ T :=
    (Set.union_subset_union hT' (Set.preimage_mono hT')).trans hST
  refine ⟨⟨hχ_lc, θ, hθ_rat, fun a ha ha_one ↦ ?_, hχ⟩, h_norm, hA, hτ,
    fun h ↦ hPT (hT'T (.inl h)), hP_ne_star, hA.tameGenerator.2, hχ_tg, rfl⟩
  -- an idele that is a unit off `T'.conjClosure ⊆ T` and `≡ 1` at `P` is killed by `θ`
  exact hθ_one a (idelesUnitOff_mono hT'T ha) (ha_one P ⟨rfl, fun h ↦ hPT (hT'T h)⟩)

end AnticyclotomicChar

/-!
## Auxiliary primes with slopes, and ties

Statements about a prime and its conjugate are indexed by `b : Bool` through `New.idOrConjInv`.

* `New.Selmer.pointChar`: the character `g ↦ ∏ j, y j ^ h j g` for `q`-th roots of unity `y j`.
-/

namespace New.Selmer

open IsDiscreteValuationRing Module Fintype Matrix.Module

open scoped Classical in
/-- The set `S ∪ J ∪ J̄` of places, for finite sets `S` and `J`. -/
@[grind] def unionWithConj {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
    (S J : Finset (FinPlace E)) :
    Finset (FinPlace E) :=
  S ∪ (J ∪ J.image star)

/-- The character `g ↦ ∏ j, y j ^ h j g` of `G`, for characters `h j` to `ℤ/q` and `q`-th roots of
unity `y j`. -/
@[simps] def pointChar {G O σ : Type} [CommRing O] [Fintype σ] [Monoid G] {q : ℕ} [NeZero q]
    (h : σ → G →* Multiplicative (ZMod q)) (y : σ → O) (hy : ∀ j : σ, y j ^ q = 1) : G →* O where
  toFun g := ∏ j : σ, y j ^ (h j g).toAdd.val
  map_one' := by simp
  map_mul' := by simp [ZMod.val_add, ← pow_eq_pow_mod, hy, pow_add, Finset.prod_mul_distrib]

/-- The reduction of the matrix representation `ρ` modulo `l ^ M`. -/
def reduceModPow {G O n : Type} [CommRing O] [Fintype n] [DecidableEq n] [Monoid G] (l M : ℕ)
    (ρ : G →* Matrix n n O) : G →* Matrix n n (QuotSpan (l ^ M : O)) :=
  (algebraMap O (QuotSpan (l ^ M : O))).mapMatrix.toMonoidHom.comp ρ

open scoped Classical in
/-- A set of tied primes for the finite set `S₀` of places records the auxiliary primes chosen so
far: a set `J` that consists of a first prime `P₀`, whose Frobenius element lies in `W`, and later
primes. Each prime `v ∈ J` carries the data `(x v).1` (place, Frobenius element, tame generator,
character to `ℤ / ℓ ^ N`) and a slope `(x v).2 i` for each datum `i`. One set `J` serves all data:
the primes chosen for datum `i` are those with a nonzero slope, and there the Frobenius elements
satisfy the given condition `U i` (typically: they act trivially on the datum `i`). -/
structure IsTiedPrimes (ℓ : ℕ) {E ι O : Type} [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E] [CommRing O]
    (S₀ : Finset (FinPlace E)) (U : ι → Gal(Ω/E) → Prop) (W : Set Gal(Ω/E)) (N : ℕ)
    (P₀ : FinPlace E) (J : Finset (FinPlace E))
    (x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)) : Prop where
  /-- `J` is a set of auxiliary primes for `S₀`. -/
  auxiliary : IsAuxiliary S₀ J
  /-- The first prime `P₀` lies in `J`. -/
  first_mem : P₀ ∈ J
  /-- At each `v ∈ J` the first component is a place over `v`, a Frobenius, the tame generator
  and the character attached to them. -/
  isAuxPrimeDataAt : ∀ v ∈ J, IsAuxPrimeDataAt (placesDividing E ℓ) v (x v).1
  /-- For `v ≠ P₀` in `J`, the Frobenius at `v` has value `1` in `ℤ / ℓ ^ N` under the character of
  `P₀` and value `0` under the characters of the other primes of `J`. -/
  char_frob_eq_ite : ∀ v ∈ J, v ≠ P₀ → ∀ w ∈ J,
    (x w).1.character (x v).1.frob = if w = P₀ then Multiplicative.ofAdd 1 else 1
  /-- The Frobenius element of the first prime lies in `W`. -/
  first_frob_mem : (x P₀).1.frob ∈ W
  /-- The first prime has slope `0` for every datum. -/
  first_slope : (x P₀).2 = 0
  /-- The primes of `S₀` and the later primes do not divide the norm of the first prime, so that the
  Greenberg–Wiles count can choose its extra primes away from the first prime. -/
  notMem_placesDividing : ∀ v : FinPlace E, v ∈ S₀ ∨ v ∈ J ∧ v ≠ P₀ → v ∉ placesDividing E P₀.q
  /-- Where the slope for datum `i` at `v` is not zero, `U i` holds at `φ_v = (x v).1.frob` and at
  `φ_v^{-c}`. -/
  frob_of_slope_ne_zero : ∀ v ∈ J, ∀ i : ι,
    (x v).2 i ≠ 0 → U i (x v).1.frob ∧ U i (conjGal (x v).1.frob)⁻¹

/-- If a tied prime has a nonzero slope, its Frobenius `φ_v` and the inverse `φ_v^{-c}` of its
conjugate satisfy the chosen condition. -/
lemma IsTiedPrimes.apply_idOrConjInv_of_slope_ne_zero {ℓ : ℕ} {E ι O : Type} [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E]
    [CommRing O] {S₀ : Finset (FinPlace E)} {U : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)} {N : ℕ}
    {P₀ : FinPlace E} {J : Finset (FinPlace E)}
    {x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)} (hJ : IsTiedPrimes ℓ S₀ U W N P₀ J x)
    {v : FinPlace E} (hv : v ∈ J) {i : ι} (h_slope : (x v).2 i ≠ 0) (b : Bool) :
    U i (idOrConjInv b (x v).1.frob) := by
  obtain ⟨h_frob, h_conj⟩ := hJ.frob_of_slope_ne_zero v hv i h_slope
  cases b
  exacts [h_conj, h_frob]

/-- The ties `z(γ_w) = s • z(φ_w)` of datum `i`, for `v ∈ J` with slope `s = (x v).2 i` and
`w = v, v̄`, as formal combinations of group elements with matrix coefficients, where
`γ_v = (x v).1.tameGenerator` and `φ_v = (x v).1.frob`; at `v̄` the elements are `γ_v^{-c}` and
`φ_v^{-c}`. -/
def tieRelations {E ι O n : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
    [CommRing O] [DecidableEq n] {q : ℕ}
    (J : Finset (FinPlace E)) (x : FinPlace E → AuxPrimeData E q × (ι → O)) (i : ι) :
    Set (Gal(Ω/E) →₀ Matrix n n O) :=
  Set.range fun p : J × Bool ↦
    Finsupp.single (idOrConjInv p.2 (x p.1).1.tameGenerator) 1 -
      Finsupp.single (idOrConjInv p.2 (x p.1).1.frob) ((x p.1).2 i • 1)

/-- If `τ` is inertial at a place over `P` and `S` contains `P` and its conjugate, then `τ` and
`τ^{-c}` (the two values of `New.idOrConjInv b τ`) lie in inertia groups above `S`. -/
lemma idOrConjInv_mem_inertiaAbove {E : Type} [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E] {A : ClosurePlace}
    {P : FinPlace E} {S : Set (FinPlace E)} {τ : Gal(Ω/E)} (hA : IsPlaceOver A P)
    (hτ : τ ∈ inertiaGroup Gal(Ω/E) A) (hS : P ∈ S ∧ star P ∈ S) (b : Bool) :
    idOrConjInv b τ ∈ inertiaAbove S := by
  cases b
  · -- The element `τ^c` is inertial at the conjugate place, over `star P`; so is its inverse.
    exact ⟨star P, hS.2, conjPlace A, hA.conjPlace_star, inv_mem hτ.conjPlace_conjGal⟩
  · exact ⟨P, hS.1, A, hA, hτ⟩

end New.Selmer

end
