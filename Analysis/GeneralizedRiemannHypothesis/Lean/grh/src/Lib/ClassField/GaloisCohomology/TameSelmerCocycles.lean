import Lib.ClassField.Global.CMSplittingCharacters

/-!
# Selmer groups unramified outside a set and cocycles of tamely ramified actions

The file concerns locally constant cocycles of `Gal(Ω/E)`, where `Ω` is the fixed algebraic closure
of `ℚ` and the number field `E` is embedded in it (`EmbeddedNumberField E`), with values in `B ^ n`
for a matrix action `ρ`. It describes membership in the Selmer modules `New.selmerModule ρ S L B`
and how they depend on `S` and `L`. It then studies such cocycles at a place where `ρ` is tamely
ramified, for `B` killed by `ℓ ^ M` with `ℓ ^ M` prime to the place.

## Main definitions and results

* `New.Selmer.mem_selmerModule_iff`: membership spelled out as the cocycle identity, vanishing on
  inertia outside `S`, the relations `L` and local constancy.
* `New.Selmer.mem_selmerModule_of_eq_zero_on_inertiaAbove`: a member for `(S, L)` is a member for
  `(T, K)` when `K ⊆ L` and it vanishes on inertia at the places of `S` outside `T`. The case
  `S ⊆ T` is `New.Selmer.mem_selmerModule_of_subset`.
* `New.Selmer.cocycle_eq_zero_on_inertia_of_tameGenerator`: a cocycle that vanishes at the tame
  generator vanishes on inertia.
* `New.Selmer.length_localCocycles_le`: a bound for the length of the local cocycles
  `New.Selmer.localCocycles`.
* `New.Selmer.exists_conj_side_detects`: at a place prime to `ℓ` or at its complex conjugate, where
  `ρ` is unramified, vanishing at two elements detects vanishing on the decomposition group.

Notions from other files:
* `New.IsPlaceOver A P`: the place `A` of `Ω` lies above the place `P` of the number field.
* `New.IsPlaceOver.tameGenerator`: a chosen generator of tame inertia at `A`.
* `New.IsFrob A q φ`: `φ` fixes `A` and acts as `x ↦ x ^ q` on its residue field; `P.q` is the order
  of the residue field of `P`.
* `New.idOrConjInv b g`: `g` if `b` is true, `(conjGal g)⁻¹` otherwise, where `conjGal g` is the
  conjugate of `g` by a chosen complex conjugation.

## Relation to the literature

Known; see `Lib.ClassField.GreenbergWiles.CocycleCounts`,
`Lib.ClassField.GaloisCohomology.KummerCyclicClasses`,
`Lib.ClassField.LocalDuality.CrystallineDuality` and `Lib.ClassField.Places.LocalFields` for
sources.
-/

namespace New.Selmer

/-!
## Membership and monotonicity of Selmer modules

`New.selmerModule ρ S L B` is the module of locally constant cocycles `Gal(Ω/E) → B ^ n` for the
map `ρ` to matrices. They vanish on the inertia groups outside `S` (`New.inertiaAbove`) and obey
the linear relations `L`: the function `c` is in `New.obeying L B` if it annihilates each formal
combination of group elements with matrix coefficients in `L`.
-/

section SelmerMembership

open Matrix.Module

variable {E : Type}
  {Λ n B : Type*} [Field E] [EmbeddedNumberField E] [CommRing Λ] [Fintype n] [DecidableEq n]
  [AddCommGroup B] [Module Λ B]
  {ρ : Gal(Ω/E) → Matrix n n Λ} {S T : Set (FinPlace E)} {L K : Set (Gal(Ω/E) →₀ Matrix n n Λ)}
  {c : Gal(Ω/E) → n → B}

/-- A function `c : Gal(Ω/E) → B ^ n` lies in the Selmer module exactly when four conditions hold.
It satisfies the cocycle identity `c(gh) = c(g) + ρ(g)c(h)`. It vanishes on the inertia groups above
the places outside `S`. It obeys the relations `L` and is locally constant. -/
lemma mem_selmerModule_iff :
    c ∈ selmerModule ρ S L B ↔
      (∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h) ∧
      (∀ g ∈ inertiaAbove Sᶜ, c g = 0) ∧
      c ∈ obeying L B ∧
      IsLocallyConstant c := by
  -- The defining set of relations is a union of three; the relation `single g 1` says `c g = 0`.
  rw [selmerModule, Submodule.mem_inf, ← mem_obeying_cocycleRelations]
  change _ ∧ IsLocallyConstant c ↔ _
  simp [obeying, or_imp, forall_and, and_assoc]

/-- Let `c` lie in the Selmer module for the places `S` and the relations `L`. If `K ⊆ L` and `c`
vanishes on the inertia groups above every place of `S` outside `T`, then `c` lies in the Selmer
module for `T` and `K`. -/
lemma mem_selmerModule_of_eq_zero_on_inertiaAbove (hc : c ∈ selmerModule ρ S L B) (hKL : K ⊆ L)
    (h_unr : ∀ v : FinPlace E, v ∈ S \ T → ∀ g : Gal(Ω/E), g ∈ inertiaAbove {v} → c g = 0) :
    c ∈ selmerModule ρ T K B := by
  obtain ⟨h_cocycle, h_unr_compl, h_obey, h_locConst⟩ := mem_selmerModule_iff.1 hc
  -- A place outside `T` is outside `S` or in `S \ T`; either way `c` vanishes on its inertia.
  have h_unr_target : ∀ g ∈ inertiaAbove Tᶜ, c g = 0 := by
    rintro g ⟨v, hvT, A, hA, hg⟩
    by_cases hvS : v ∈ S
    · exact h_unr v ⟨hvS, hvT⟩ g ⟨v, rfl, A, hA, hg⟩
    · exact h_unr_compl g ⟨v, hvS, A, hA, hg⟩
  exact mem_selmerModule_iff.2 ⟨h_cocycle, h_unr_target,
    mem_obeying.2 fun f hf ↦ mem_obeying.1 h_obey f (hKL hf), h_locConst⟩

/-- The Selmer module grows when more places may ramify and fewer relations are imposed: a member
for the places `S` and the relations `L` is a member for `T ⊇ S` and `K ⊆ L`. -/
lemma mem_selmerModule_of_subset (hc : c ∈ selmerModule ρ S L B) (hKL : K ⊆ L) (hST : S ⊆ T) :
    c ∈ selmerModule ρ T K B :=
  mem_selmerModule_of_eq_zero_on_inertiaAbove hc hKL fun _ ⟨hvS, hvT⟩ ↦ absurd (hST hvS) hvT

end SelmerMembership

/-!
## Cocycles of tamely ramified actions

Locally constant cocycles `c` of `Gal(Ω/E)` for a matrix representation `ρ`, with values in `n → B`,
`B` killed by `ℓ ^ M`, at a place `A` of `Ω` where `ρ` is tamely ramified. The idea is to apply the
structure of tame inertia (`New.IsPlaceOver.tame_inertia`) to the affine action
`New.Selmer.affineAction`, `v ↦ c g + ρ g • v`.
-/

section TameCocycles

open Equiv.Perm Matrix Module MulAction LinearMap

variable {ℓ : ℕ} {E : Type} {O n : Type*} [Field E] [EmbeddedNumberField E] [CommRing O]
  [Fintype n] [DecidableEq n] {ρ : Gal(Ω/E) →* Matrix n n O} {L : Set (Gal(Ω/E) →₀ Matrix n n O)}
  {A : ClosurePlace} {B : Type*} [AddCommGroup B] [Module O B] {M : ℕ} {P : FinPlace E}
  {c : Gal(Ω/E) → n → B} {m : ℕ}

variable (ρ L A B) in
/-- The module of restrictions to the decomposition group at `A` of the locally constant cocycles
for `ρ` with values in `B ^ n` that obey the relations `L`. -/
noncomputable def localCocycles : Submodule O (decompGroup Gal(Ω/E) A → n → B) :=
  (selmerModule ρ .univ L B).map (funLeft O (n → B) (decompGroup Gal(Ω/E) A).subtype)

/-- The affine action `u ↦ c g + ρ g • u` of `Gal(Ω/E)` on `B ^ n` given by a cocycle `c` for the
matrix representation `ρ`. -/
noncomputable def affineAction (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h) :
    Gal(Ω/E) →* Equiv.Perm (n → B) :=
  MonoidHom.mk' (fun g ↦ Equiv.addLeft (c g) * toPerm (ρ.toHomUnits g))
    (by simp [Equiv.ext_iff, Units.smul_def, hc, mul_smul, add_assoc])

/-- The affine action of a cocycle `c` sends `u` to `c g + ρ g • u`. -/
private lemma affineAction_apply_eq (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    (g : Gal(Ω/E)) (u : n → B) : affineAction hc g u = c g + ρ g • u := by
  simp [affineAction, Units.smul_def]

lemma cocycle_apply_inv (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h) (g : Gal(Ω/E)) :
    c g⁻¹ = -(ρ g⁻¹ • c g) := by
  have h_one : c 1 = 0 := by simpa using hc 1 1
  rw [eq_neg_iff_add_eq_zero, ← hc, inv_mul_cancel, h_one]

/-- A cocycle that vanishes at the tame generator vanishes on inertia. In detail: let `A` be a place
of `Ω` over `P` and let `c` be a locally constant cocycle for the representation `ρ` with values in
`B ^ n`, where `ℓ ^ M` kills `B`. Assume that `ρ` is trivial on inertia at `A` near `1` and on the
`m`-th powers of inertia, and that `m * ℓ ^ M` is prime to `A`. If `c` is zero at the tame generator
of `A`, it is zero at every inertia element `γ`. -/
lemma cocycle_eq_zero_on_inertia_of_tameGenerator (hB : ∀ b : B, ℓ ^ M • b = 0)
    (hA : IsPlaceOver A P) (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    (h_exp : ∀ i ∈ inertiaGroup Gal(Ω/E) A, ρ (i ^ m) = 1)
    (h_open : ∀ᶠ g : Gal(Ω/E) in nhds 1, g ∈ inertiaGroup Gal(Ω/E) A → ρ g = 1)
    (γ : inertiaGroup Gal(Ω/E) A) (h_prime : A.valuation (m * ℓ ^ M : ℕ) = 1)
    (hc_lc : IsLocallyConstant c) (h_zero : c hA.tameGenerator = 0) : c γ = 0 := by
  -- The affine action is trivial on inertia near `1` and kills `m * ℓ ^ M`-th powers of inertia,
  -- so it is tame, and `γ` acts as a power of the tame generator.
  have h_one : c 1 = 0 := by simpa using hc 1 1
  have h_near : ∀ᶠ g in nhds 1, g ∈ inertiaGroup Gal(Ω/E) A → affineAction hc g = 1 := by
    filter_upwards [hc_lc.eventually_eq 1, h_open] with g hg_const hg_triv hg_inertia
    simp [Equiv.ext_iff, affineAction_apply_eq, hg_const, h_one, hg_triv hg_inertia]
  -- `g ^ m` acts as a translation, and translations are killed by `ℓ ^ M`.
  have h_pow (g : Gal(Ω/E)) (hg : g ∈ inertiaGroup Gal(Ω/E) A) :
      affineAction hc g ^ (m * ℓ ^ M) = 1 := by
    rw [pow_mul, ← map_pow]
    simp [affineAction, Equiv.ext_iff, Units.smul_def, coe_pow, ← map_pow ρ, h_exp g hg, hB,
      Function.comp_def, funext_iff]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, affineAction hc γ = affineAction hc hA.tameGenerator ^ a :=
    (hA.tame_inertia (affineAction hc) h_near h_prime h_pow γ).1
  -- `c g` is the image of `0` under `g`, and the tame generator fixes `0`.
  have h_apply (g : Gal(Ω/E)) : affineAction hc g 0 = c g := by simp [affineAction_apply_eq]
  rw [← h_apply γ, ha, coe_pow, Function.iterate_fixed ((h_apply _).trans h_zero)]

/-- A locally constant cocycle `c` for `ρ` that vanishes on the inertia group of a place `A'` over
`v` and at a Frobenius element there vanishes on the decomposition group of `A'`. -/
lemma eq_zero_on_decompGroup {A' : ClosurePlace} {v : FinPlace E} (hA' : IsPlaceOver A' v)
    (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h) (hc_lc : IsLocallyConstant c)
    (h_zero : ∀ g ∈ inertiaGroup Gal(Ω/E) A', c g = 0) {φ : Gal(Ω/E)} (hφ : IsFrob A' v.q φ)
    (hφ_zero : c φ = 0) (g : decompGroup Gal(Ω/E) A') : c g = 0 :=
  -- The zeros of `c` form an open subgroup containing inertia and `φ`.
  hA'.decompGroup_le hφ (U := cocycleKer ρ hc) (hc_lc {0}) h_zero hφ_zero g.2

/-- An upper bound on length, of the kind given by the local Euler characteristic formula and local
duality. Let `A` be a place of `Ω` over `P`, let `ℓ ^ M` kill `B`, let `ρ` be trivial on inertia at
`A` near `1` and on the `m`-th powers of inertia, and let `m * ℓ ^ M` be prime to `A`. For inertial
`γ`, the module `localCocycles ρ L A B` of restrictions to the decomposition group at `A` of the
cocycles obeying the relations `L` has length at most the length of `B ^ n` plus the length of the
kernel of `ρ γ - 1` on `B ^ n`. -/
lemma length_localCocycles_le (hB : ∀ b : B, ℓ ^ M • b = 0) (hA : IsPlaceOver A P)
    (h_exp : ∀ i ∈ inertiaGroup Gal(Ω/E) A, ρ (i ^ m) = 1)
    (h_open : ∀ᶠ g : Gal(Ω/E) in nhds 1, g ∈ inertiaGroup Gal(Ω/E) A → ρ g = 1)
    (γ : inertiaGroup Gal(Ω/E) A) (h_prime : A.valuation (m * ℓ ^ M : ℕ) = 1) :
    length O (localCocycles ρ L A B) ≤
      length O (n → B) + length O (ker ((ρ γ - 1) • 1 : End O (n → B))) := by
  -- Evaluate at the tame generator; the kernel `Z₀` of that map embeds in `ker (ρ γ - 1)` by
  -- evaluation at a Frobenius `φ`.
  obtain ⟨φ, hφ⟩ := hA.exists_isFrob Gal(Ω/E)
  let evalTame : (decompGroup Gal(Ω/E) A → n → B) →ₗ[O] n → B :=
    proj ⟨hA.tameGenerator, hA.tameGenerator.property.left⟩
  let evalFrob : (decompGroup Gal(Ω/E) A → n → B) →ₗ[O] n → B := proj ⟨φ, hφ.1⟩
  let Z₀ : Submodule O (decompGroup Gal(Ω/E) A → n → B) := localCocycles ρ L A B ⊓ ker evalTame
  have h_unram {y : Gal(Ω/E) → n → B} (hy : y ∈ selmerModule ρ .univ L B)
      (h_tame : y hA.tameGenerator = 0) (g : Gal(Ω/E)) (hg : g ∈ inertiaGroup Gal(Ω/E) A) :
      y g = 0 := by
    obtain ⟨h_cocycle, -, -, h_locConst⟩ := mem_selmerModule_iff.1 hy
    exact cocycle_eq_zero_on_inertia_of_tameGenerator hB hA h_cocycle h_exp h_open ⟨g, hg⟩ h_prime
      h_locConst h_tame
  -- `γ φ = φ (φ⁻¹ γ φ)` with `γ` and `φ⁻¹ γ φ` in inertia, so `ρ γ` fixes `y φ`.
  have h_fixed : ∀ x ∈ Z₀, evalFrob x ∈ ker ((ρ γ - 1) • 1 : End O (n → B)) := by
    rintro _ ⟨⟨y, hy, rfl⟩, h_tame : y hA.tameGenerator = 0⟩
    obtain ⟨h_cocycle, -, -, -⟩ := mem_selmerModule_iff.1 hy
    have h_conj_mem : φ⁻¹ * (γ * φ) ∈ inertiaGroup Gal(Ω/E) A :=
      .inv_mul_mem_inertiaGroup (by simpa) (γ.2.mul_iff.2 hφ : IsFrob A (1 * P.q) (γ * φ))
    have h_fix : ρ γ • y φ = y φ := by
      simpa [h_cocycle γ, h_unram hy h_tame _ h_conj_mem, h_unram hy h_tame γ γ.property]
        using h_cocycle φ (φ⁻¹ * (γ * φ))
    simpa [evalFrob, sub_smul, sub_eq_zero] using h_fix
  have h_inj : ∀ x ∈ Z₀, evalFrob x = 0 → x = 0 := by
    rintro _ ⟨⟨y, hy, rfl⟩, h_tame : y hA.tameGenerator = 0⟩ (hφ_zero : y φ = 0)
    obtain ⟨h_cocycle, -, -, h_lc⟩ := mem_selmerModule_iff.1 hy
    exact funext (eq_zero_on_decompGroup hA h_cocycle h_lc (h_unram hy h_tame) hφ hφ_zero)
  have h_ker : length O Z₀ ≤ length O (ker ((ρ γ - 1) • 1 : End O (n → B))) := by
    simpa using relLength_le_of_mapsTo evalFrob (T := ⊥) (T' := ⊥) h_fixed h_inj
  have h_quot : relLength (localCocycles ρ L A B) (ker evalTame) ≤ length O (n → B) := by
    grw [relLength_ker, length_mono le_top, length_top]
  rw [← relLength_add_length_inf _ (ker evalTame)]
  exact add_le_add h_quot h_ker

/-- Let `A'` be a place of `Ω` over `v`, and let `ρ` be trivial on the inertia groups above `v`.
A cocycle `c` for `ρ` that vanishes on the inertia group of `A'` vanishes on every inertia group
above `v`. -/
lemma eq_zero_on_inertiaAbove {A' : ClosurePlace} {v : FinPlace E} (hA' : IsPlaceOver A' v)
    (hρ : ∀ g : Gal(Ω/E), g ∈ inertiaAbove {v} → ρ g = 1)
    (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    (h_zero : ∀ g ∈ inertiaGroup Gal(Ω/E) A', c g = 0) :
    ∀ g ∈ inertiaAbove {v}, c g = 0 := by
  intro g hg_above
  have h_triv : ρ g = 1 := hρ g hg_above
  obtain ⟨v', rfl : v' = v, A'', hA'', hg⟩ := hg_above
  -- The inertia groups above `v` are conjugate: `A'` is `s • A''` for some `s`.
  obtain ⟨s, rfl⟩ := hA''.exists_smul Gal(Ω/E) hA'
  exact add_eq_right.mp <| calc
    c g + c s⁻¹ = c (g * s⁻¹) := by rw [hc, h_triv, one_smul]
    _ = c (s⁻¹ * (s * g * s⁻¹)) := by simp [mul_assoc]
    _ = c s⁻¹ := by rw [hc, h_zero _ (hg.conj s), smul_zero, add_zero]

/-- Let `A` be a place of `Ω` over `P`, prime to `ℓ`, let `ℓ ^ M` kill `B`, let `θ` be an
endomorphism of `Gal(Ω/E)` and let `ρ ∘ θ` be trivial on inertia at `A`. A locally constant cocycle
for `ρ ∘ θ` that vanishes at the tame generator vanishes on inertia at `A`. -/
lemma eq_zero_on_inertiaGroup_of_tameGenerator (hB : ∀ b : B, ℓ ^ M • b = 0) (hA : IsPlaceOver A P)
    (hP : P ∉ placesDividing E ℓ) (θ : Gal(Ω/E) →* Gal(Ω/E))
    (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ (θ g) • c h)
    (hθ : ∀ g ∈ inertiaGroup Gal(Ω/E) A, ρ (θ g) = 1)
    (hc_lc : IsLocallyConstant c) (h_zero : c hA.tameGenerator = 0) :
    ∀ g ∈ inertiaGroup Gal(Ω/E) A, c g = 0 := fun g hg ↦
  -- The case `m = 1` of `cocycle_eq_zero_on_inertia_of_tameGenerator`, as `ℓ` is a unit at `A`.
  cocycle_eq_zero_on_inertia_of_tameGenerator hB hA (ρ := ρ.comp θ) hc (m := 1) (by simpa)
    (.of_forall hθ) ⟨g, hg⟩ (by simp [hA.valuation_natCast_eq_one_iff.2 hP]) hc_lc h_zero

/-- Let `P` be a place of the CM field `E` prime to `ℓ`, let `A` be a place of `Ω` over `P` and let
`ℓ ^ M` kill `B`. Let `v` be `P` or its complex conjugate, and let `ρ` be unramified at `v`. For a
side `b`, write `idOrConjInv b g` for `g` or `(conjGal g)⁻¹` according to `b`, where `conjGal g` is
the conjugate of `g` by complex conjugation. Then vanishing at two elements detects vanishing at
`v`. Precisely, there are a side `b` and a place `A'` over `v` such that every cocycle `c` in
`selmerModule ρ S L B` that is zero at `idOrConjInv b` of the tame generator at `A` is unramified at
`v`. If it is also zero at `idOrConjInv b φ` for a Frobenius element `φ` at `A`, it is zero on the
decomposition group at `A'`. Here `selmerModule ρ S L B` consists of the locally constant cocycles
for `ρ` in `B ^ n` that are zero on inertia above places outside `S` and obey the relations `L`. -/
lemma exists_conj_side_detects [NumberField.IsCMField E] (hB : ∀ b : B, ℓ ^ M • b = 0)
    (hA : IsPlaceOver A P) (hP : P ∉ placesDividing E ℓ) {v : FinPlace E}
    (hρ : ∀ g : Gal(Ω/E), g ∈ inertiaAbove {v} → ρ g = 1) (hv : v = P ∨ v = star P) :
    ∃ (b : Bool) (A' : ClosurePlace), IsPlaceOver A' v ∧
      ∀ {S : Set (FinPlace E)} {L : Set (Gal(Ω/E) →₀ Matrix n n O)},
      ∀ c : Gal(Ω/E) → n → B, c ∈ selmerModule ρ S L B →
        c (idOrConjInv b hA.tameGenerator) = 0 →
        (∀ g : Gal(Ω/E), g ∈ inertiaAbove {v} → c g = 0) ∧
        ∀ φ : Gal(Ω/E), IsFrob A P.q φ → c (idOrConjInv b φ) = 0 →
          ∀ g : decompGroup Gal(Ω/E) A', c g = 0 := by
  -- The side `v = P` uses `A`, and the side `v = star P` the conjugate place.
  obtain rfl | rfl := hv
  · refine ⟨true, A, hA, fun {S L} c hc h_gen ↦ ?_⟩
    obtain ⟨h_cocycle, -, -, h_locConst⟩ := mem_selmerModule_iff.1 hc
    have h_unram : ∀ g ∈ inertiaGroup Gal(Ω/E) A, c g = 0 :=
      eq_zero_on_inertiaGroup_of_tameGenerator hB hA hP (MonoidHom.id Gal(Ω/E)) h_cocycle
        (fun g hg ↦ hρ g ⟨v, rfl, A, hA, hg⟩) h_locConst h_gen
    exact ⟨eq_zero_on_inertiaAbove hA hρ h_cocycle h_unram,
      fun φ hφ hφ_zero ↦ eq_zero_on_decompGroup hA h_cocycle h_locConst h_unram hφ hφ_zero⟩
  · -- Argue as in the first case with `c ∘ conjGal`, a cocycle for `ρ ∘ conjGal`.
    refine ⟨false, conjPlace A, hA.conjPlace_star, fun {S L} c hc h_gen ↦ ?_⟩
    obtain ⟨h_cocycle, -, -, h_locConst⟩ := mem_selmerModule_iff.1 hc
    have h_of_inv (g : Gal(Ω/E)) (hg : c (conjGal g)⁻¹ = 0) : c (conjGal g) = 0 := by
      simpa [hg] using cocycle_apply_inv h_cocycle (conjGal g)⁻¹
    have h_conj_unram : ∀ g ∈ inertiaGroup Gal(Ω/E) A, c (conjGal g) = 0 :=
      eq_zero_on_inertiaGroup_of_tameGenerator hB hA hP conjGal (c := c ∘ conjGal)
        (by simp [h_cocycle])
        (fun g hg ↦ hρ _ ⟨star P, rfl, conjPlace A, hA.conjPlace_star, hg.conjPlace_conjGal⟩)
        (h_locConst.comp_continuous continuous_conjGal) (h_of_inv hA.tameGenerator h_gen)
    have h_unram (g : Gal(Ω/E)) (hg : g ∈ inertiaGroup Gal(Ω/E) (conjPlace A)) : c g = 0 := by
      simpa using h_conj_unram (conjGal g) (conjGal_mem_inertiaGroup_iff.1 (by simpa using hg))
    exact ⟨eq_zero_on_inertiaAbove hA.conjPlace_star hρ h_cocycle h_unram, fun φ hφ hφ_zero ↦
      eq_zero_on_decompGroup hA.conjPlace_star h_cocycle h_locConst h_unram
        (by simp [hφ.conjPlace_conjGal] : IsFrob (conjPlace A) (star P).q (conjGal φ))
        (h_of_inv φ hφ_zero)⟩

end TameCocycles

end New.Selmer
