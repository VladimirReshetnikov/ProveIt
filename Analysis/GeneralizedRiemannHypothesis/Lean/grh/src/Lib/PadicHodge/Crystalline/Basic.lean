import Lib.ClassField.Places.DecompositionCompletion
import Lib.PadicHodge.PeriodRings.DeRhamPeriods

/-!
# Crystalline and potentially crystalline representations and admissibility

This file concerns a representation `ρ` of a group `Γ` on an `R`-module `T`. The group `Γ` carries a
homomorphism `j` (the field `toGp` of `New.Period.OverGp`) with open image in the Galois group
`New.Gp p` of `ℚ_[p]`. Tensor products are over `ℤ_[p]` and the period ring is `New.Period.Bmax`;
the class `ThePrime p` makes `p` a prime (it supplies the `Fact p.Prime` needed by `OverGp`).

"Near `1`" means along the filter `New.Period.nearOne`, which takes the place of passing to a finite
extension. Let `B` be a `ℤ_[p]`-algebra with an action of `New.Gp p`. The diagonal action
`New.Period.tensorAction` of `g` on `B ⊗ T` is `j(g) ⊗ ρ(g)`. For a filter `F` on `Γ`,
`New.Period.fixedPeriods ρ B F` is the set of elements of `B ⊗ T` fixed by the diagonal action for
`F`-almost all `g`. `New.Period.IsAdmissible ρ F` says that for `B = Bmax` this set spans `B ⊗ T`
over `B`.

## Main definitions and results

* `New.Period.IsCrystalline`, `New.Period.IsPotentiallyCrystalline`: the vectors of `Bmax ⊗ T` fixed
  by `Γ`, or fixed near `1` (`New.Period.Dpcris`), span `Bmax ⊗ T`.
* `New.Period.crysCocycles`: the functions `Γ → T` that become coboundaries in `Bmax ⊗ T`.
* `New.Period.hodgeTateMaps`, `New.Period.HasJumps`: Hodge–Tate maps `T → ℂ_[p]` of weight `u` along
  `γ : R → ℂ_[p]`, and the multiset of weights counted with the dimensions of these spaces.
* `New.Period.IsWeilPair`, `New.Period.linearFrob`, `New.Period.IsKilledBy`: the action of `φ ^ m s`
  on `Dpcris`, extended linearly, and the polynomials over `R` that annihilate it.
* `New.Period.IsAdmissible.tate_twist`, `New.Period.isAdmissible_of_cyclotomicGp_zpow`: twists by
  powers of the cyclotomic character, through the unit of `New.Period.exists_tate_twist_unit`.
* `New.Period.equivFun_tensorAction`: in the coordinates given by a finite basis `e` of `T`, the
  diagonal action is `New.Period.coordAction`.

Notions from other files:
* `New.Period.Bmax`: the period ring B⁺[1/μ] (Colmez's B_max), used here in place of B_cris.
* `New.Period.FrobGal`: the monoid ℕ × `Gp p`; on the period rings with a Frobenius `φ`, the pair
  `(n, g)` acts as `φ ^ n ∘ g`.

## Relation to the literature

Known; see `Lib.PadicHodge.Crystalline.Regularity`, `Lib.PadicHodge.BlochKato` and
`Lib.PadicHodge.Kisin.PeriodMatrixFrame` for sources.
-/

noncomputable section

namespace New.Period

/-! ## Crystalline representations, Hodge–Tate weights and linear Frobenius -/

section Defs

open TensorProduct Module DistribSMul RingHomClass

/-- A group `Γ` together with a homomorphism `j` from `Γ` to `Gp p` = Gal(Q̄_p/Q_p) whose image
is open. -/
class OverGp (Γ : Type*) (p : outParam ℕ) [Fact p.Prime] [Group Γ] where
  /-- The homomorphism from the group to `New.Gp p`. -/
  toGp : Γ →* Gp p
  /-- The image of the homomorphism is open in `New.Gp p`. -/
  isOpen_range : Fact (IsOpen (SetLike.coe toGp.range))

/-- A group `G` bundled with a homomorphism from `G` to `Gp p` = Gal(Q̄_p/Q_p) whose image is
open. -/
class GroupOverGp (p : outParam ℕ) [Fact p.Prime] where
  /-- The group. -/
  G : Type
  /-- The group structure on `G`. -/
  [group : Group G]
  /-- The homomorphism from `G` to `New.Gp p` with open image. -/
  [overGp : OverGp G p]

attribute [instance] OverGp.isOpen_range
attribute [instance_reducible, instance] GroupOverGp.group GroupOverGp.overGp

export OverGp (toGp)

variable {p : ℕ} [ThePrime p]
  {Γ R T : Type*} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R]
  [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [𝒥 : OverGp Γ p]
  (ρ : Representation R Γ T) (B : Type*) [CommRing B] [Algebra ℤ_[p] B] (u : ℤ)

/-- A bundled group over `Gp p` is read as its underlying type. -/
instance : CoeSort (GroupOverGp p) Type := ⟨(·.G)⟩

/-! ### Periods and crystalline cocycles -/

/-- For an element `m` of a monoid `M` acting on the `ℤ_p`-algebra `B` and an endomorphism `f` of
`T`, the `ℤ_p`-linear endomorphism `b ⊗ x ↦ (m • b) ⊗ f x` of `B ⊗ T`, the tensor product taken over
`ℤ_p`. -/
def tensorAction {M : Type*} [Monoid M] [MulSemiringAction M B] [SMulCommClass M ℤ_[p] B] (m : M)
    (f : End R T) : End ℤ_[p] (B ⊗[ℤ_[p]] T) :=
  map (toLinearMap ℤ_[p] B m) f

/-- For a `ℤ_p`-algebra `B` with an action of `Gp p` and a filter `F` on `Γ`, the set of elements of
`B ⊗ T` (over `ℤ_p`) fixed by `j(g) ⊗ ρ(g)` for `F`-almost all `g`, where `j` is `toGp`. -/
def fixedPeriods [MulSemiringAction (Gp p) B] [SMulCommClass (Gp p) ℤ_[p] B] (F : Filter Γ) :
    Set (B ⊗[ℤ_[p]] T) :=
  {x : B ⊗[ℤ_[p]] T | ∀ᶠ g : Γ in F, tensorAction B (toGp g) (ρ g) x = x}

/-- For a representation `ρ` of `Γ` on `T` and a filter `F` on `Γ`: the elements of `Bmax ⊗ T`
fixed by `j(g) ⊗ ρ(g)` for `F`-almost all `g` span `Bmax ⊗ T` over `Bmax`. -/
def IsAdmissible (F : Filter Γ) : Prop := Submodule.span Bmax (fixedPeriods ρ Bmax F) = ⊤

/-- `ρ` is crystalline: the elements of `Bmax ⊗ T` fixed by `j(g) ⊗ ρ(g)` for all `g` in `Γ` span
`Bmax ⊗ T` over `Bmax`. -/
abbrev IsCrystalline : Prop := IsAdmissible ρ ⊤

/-- The `R`-submodule of functions `c : Γ → T` that become coboundaries in `Bmax ⊗ T`: some `y` in
`Bmax ⊗ T` satisfies `1 ⊗ c g = (j(g) ⊗ ρ(g)) y - y` for all `g` in `Γ`. -/
def crysCocycles : Submodule R (Γ → T) where
  carrier := {c : Γ → T |
    ∃ y : Bmax ⊗[ℤ_[p]] T, ∀ g : Γ, 1 ⊗ₜ c g = tensorAction Bmax (toGp g) (ρ g) y - y}
  add_mem' := by
    rintro c d ⟨y, hy⟩ ⟨z, hz⟩
    refine ⟨y + z, fun g ↦ ?_⟩
    rw [Pi.add_apply, tmul_add, hy, hz, map_add, sub_add_sub_comm]
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a c ⟨y, hy⟩
    -- Apply `A = 1 ⊗ a`, which commutes with `tensorAction` because `ρ g` is `R`-linear.
    let A : End ℤ_[p] (Bmax ⊗[ℤ_[p]] T) := map 1 (a • LinearMap.id)
    refine ⟨A y, fun g ↦ ?_⟩
    have h_comm :
        A (tensorAction Bmax (toGp g) (ρ g) y) = tensorAction Bmax (toGp g) (ρ g) (A y) := by
      simp [A, tensorAction, map_map, LinearMap.comp]
    have h_tmul : A (1 ⊗ₜ c g) = 1 ⊗ₜ (a • c) g := by simp [A]
    rw [← h_tmul, hy, map_sub, h_comm]

/-! ### Weil pairs and potentially crystalline representations -/

/-- `(s, m)` is a Weil pair: `s` in `Gp p` acts on the residue field of the valuation ring of Q̄_p
as `x ↦ x ^ (1 / p ^ m)`, that is, `s⁻¹` is a Frobenius element for `p ^ m`; `m = 0` means
inertia. -/
def IsWeilPair (s : Gp p) (m : ℕ) : Prop := IsFrob (intQpBar p) (p ^ m) s⁻¹

/-- For `s` in `Gp p` = Gal(ℚ̄_p/ℚ_p), `(s, 0)` is a Weil pair (that is, `s` acts trivially on the
residue field of the valuation ring of ℚ̄_p) if and only if `s` lies in the inertia group of that
valuation ring. -/
lemma isWeilPair_zero_iff {s : Gp p} : IsWeilPair s 0 ↔ s ∈ inertiaGroup (Gp p) (intQpBar p) := by
  rw [IsWeilPair, pow_zero]
  -- The inertia group is by definition the set of Frobenius elements for `q = 1`.
  exact inv_mem_iff (H := inertiaGroup (Gp p) (intQpBar p))

/-- The p-adic cyclotomic character of `Γ`: the cyclotomic character of `Gp p` composed with `j`. -/
abbrev χ : Γ →* ℤ_[p]ˣ := cyclotomicGp.comp 𝒥.toGp

variable (Γ) in
/-- The filter 'near 1' on `Γ`: the pull-back along `j : Γ → Gp p` of the filter of
neighbourhoods of the identity. -/
def nearOne : Filter Γ := (nhds 1).comap 𝒥.toGp

variable (Γ) in
/-- An element of Q̄_p is fixed by `toGp g` for `g` near `1`, as its stabiliser is open. -/
lemma eventually_nearOne_apply_eq (c : PadicAlgCl p) : ∀ᶠ g : Γ in nearOne Γ, toGp g c = c := by
  -- The stabiliser of `c` in `Gp p` is open, as `σ ↦ σ • c` is locally constant.
  have h_stab_nhds : {σ : Gp p | σ • c = c} ∈ nhds (1 : Gp p) :=
    (isLocallyConstant_smul c {c}).mem_nhds (one_smul (Gp p) c)
  filter_upwards [Filter.preimage_mem_comap h_stab_nhds] with g hg using hg

/-- `Dpcris ρ`: the set of elements of `Bmax ⊗ T` fixed by `j(g) ⊗ ρ(g)` for all `g` with `j(g)` in
some neighbourhood of `1` in `Gp p`. -/
abbrev Dpcris : Set (Bmax ⊗[ℤ_[p]] T) := fixedPeriods ρ Bmax (nearOne Γ)

/-- `ρ` is potentially crystalline: the elements of `Bmax ⊗ T` fixed by `j(g) ⊗ ρ(g)` for all `g`
with `j(g)` near `1` span `Bmax ⊗ T` over `Bmax`. -/
abbrev IsPotentiallyCrystalline : Prop := IsAdmissible ρ (nearOne Γ)

/-- The element `y` of `ℂ_p ⊗ T` (over `ℤ_p`) has Hodge–Tate weight `u`:
`(j(g) ⊗ ρ(g)) y = χ(j(g)) ^ (-u) • y` for all `g` in `Γ`, with `χ` the cyclotomic character. -/
def _root_.New.HasHodgeTateWeight (y : ℂ_[p] ⊗[ℤ_[p]] T) : Prop :=
  ∀ g : Γ,
    tensorAction ℂ_[p] (toGp g) (ρ g) y = ((cyclotomicGp (toGp g) ^ (-u) : ℤ_[p]ˣ) : ℤ_[p]) • y

/-- For a homomorphism `r` from `Γ` to `GL n R`, the representation on `n → R` in which `g` acts
by multiplying column vectors by `r g`. -/
abbrev matrixRep {n : Type _} [Fintype n] [DecidableEq n] (r : Γ →* GL n R) :
    Representation R Γ (n → R) :=
  actionRep R (n → R) ((Units.coeHom (Matrix n n R)).comp r)

end Defs

/-! ### Hodge–Tate jumps and the linear Frobenius -/

section Frobenius

open TensorProduct Module DistribSMul RingHomClass

variable {p : ℕ} [ThePrime p]
  {Γ R T : Type*} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R]
  [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [𝒥 : OverGp Γ p]
  (ρ : Representation R Γ T) (γ : R →ₐ[ℤ_[p]] ℂ_[p]) (u : ℤ)

/-- For `γ : R → ℂ_p` and an integer `u`, the Q̄_p-space of `γ`-semilinear maps `f : T → ℂ_p` with,
for each `x`, `f (ρ g x) = χ(g) ^ (-u) • j(g) • f x` for `g` near `1`, where `χ` is the cyclotomic
character. -/
def hodgeTateMaps : Submodule (PadicAlgCl p) (T →ₛₗ[toRingHom γ] ℂ_[p]) where
  carrier := {f : T →ₛₗ[toRingHom γ] ℂ_[p] |
    ∀ x : T, ∀ᶠ g : Γ in nearOne Γ, f (ρ g x) = ((χ g ^ (-u) : ℤ_[p]ˣ) : ℤ_[p]) • toGp g • f x}
  add_mem' hf hf' x := by
    filter_upwards [hf x, hf' x] with g hg hg'
    simp [hg, hg']
  zero_mem' := by simp
  smul_mem' c f hf x := by
    -- the algebraic scalar `c` is fixed by `toGp g` for `g` near 1
    filter_upwards [hf x, eventually_nearOne_apply_eq Γ c] with g hg h_fix
    simp [hg, h_fix, Algebra.smul_def c, ← PadicComplex.coe_eq, smul_coe_Cp]

/-- The multiplicity of the Hodge–Tate jump `u` at `γ`: the dimension over Q̄_p (zero if infinite)
of the space `New.Period.hodgeTateMaps ρ γ u`. -/
def jump : ℕ := finrank (PadicAlgCl p) (hodgeTateMaps ρ γ u)

/-- The multiset `J` of integers lists the Hodge–Tate jumps of `ρ` at `γ`: for every integer `u`,
the multiplicity `jump ρ γ u` equals the number of times `u` occurs in `J`. -/
def HasJumps (J : Multiset ℤ) : Prop := ∀ u : ℤ, jump ρ γ u = Multiset.count u J

/-- A chosen `Bmax`-linear endomorphism of `Bmax ⊗ T` that agrees on `Dpcris ρ` with the map
`φ ^ m s ⊗ ρ s`, where `φ` is Frobenius, if one exists (`linearFrob_eq_tensorAction_of_exists`);
otherwise the value is unspecified. If `ρ` is potentially crystalline, there is at most one such map
(`IsPotentiallyCrystalline.linearFrob_eq`), and there is one when `toGp s` and `m` form a Weil pair
(`linearFrob_apply`).

This operator plays the role of Fontaine's Weil–Deligne representation: it extends the action of a
Weil pair on `Dpcris ρ` linearly to `Bmax ⊗ T`. -/
def linearFrob (s : Γ) (m : ℕ) : End Bmax (Bmax ⊗[ℤ_[p]] T) :=
  Classical.epsilon fun β : End Bmax (Bmax ⊗[ℤ_[p]] T) ↦ ∀ d ∈ Dpcris ρ,
    β d = tensorAction Bmax (⟨.ofAdd m, toGp s⟩ : FrobGal) (ρ s) d

/-- If some `Bmax`-linear map agrees with `φ ^ m s ⊗ ρ s` on `Dpcris ρ`, then so does
`linearFrob ρ s m`. -/
lemma linearFrob_eq_tensorAction_of_exists (s : Γ) (m : ℕ)
    (h_exists : ∃ β : End Bmax (Bmax ⊗[ℤ_[p]] T), ∀ d ∈ Dpcris ρ,
      β d = tensorAction Bmax (⟨.ofAdd m, toGp s⟩ : FrobGal) (ρ s) d) :
    ∀ d ∈ Dpcris ρ, linearFrob ρ s m d = tensorAction Bmax (⟨.ofAdd m, toGp s⟩ : FrobGal) (ρ s) d :=
  Classical.epsilon_spec h_exists

/-- For potentially crystalline `ρ`, a `Bmax`-linear map that agrees with `φ ^ m s ⊗ ρ s` on
`Dpcris ρ` is `linearFrob ρ s m`. -/
lemma IsPotentiallyCrystalline.linearFrob_eq {ρ : Representation R Γ T}
    (h_potCrys : IsPotentiallyCrystalline ρ) {s : Γ} {m : ℕ} {β : End Bmax (Bmax ⊗[ℤ_[p]] T)}
    (hβ : ∀ d ∈ Dpcris ρ, β d = tensorAction Bmax (⟨.ofAdd m, toGp s⟩ : FrobGal) (ρ s) d) :
    linearFrob ρ s m = β := by
  -- Both maps are linear and agree on `Dpcris ρ`, which spans.
  refine LinearMap.ext_on (s := Dpcris ρ) h_potCrys fun d hd ↦ ?_
  rw [linearFrob_eq_tensorAction_of_exists ρ s m ⟨β, hβ⟩ d hd, hβ d hd]

variable (R T) in
/-- The ring homomorphism from `R` to the `Bmax`-linear endomorphisms of `Bmax ⊗ T` (tensor over
`ℤ_p`) sending `a` to `1 ⊗ (multiplication by a on T)`. -/
def coeffEnd : R →+* End Bmax (Bmax ⊗[ℤ_[p]] T) :=
  toRingHom ((End.baseChangeHom ℤ_[p] Bmax T).comp (Algebra.lsmul (A := R) ℤ_[p] ℤ_[p] T))

/-- The polynomial `P` over `R` kills `(s, m)`: `ρ` is potentially crystalline and `P`, evaluated
at `linearFrob ρ s m` with the coefficients acting on `T` through `coeffEnd`, is zero on
`Bmax ⊗ T`.

This is the analogue, tested on `Bmax ⊗ T`, of the vanishing of a polynomial at an element acting on
Fontaine's Weil–Deligne representation. -/
def IsKilledBy (s : Γ) (m : ℕ) (P : Polynomial R) : Prop :=
  IsPotentiallyCrystalline ρ ∧ Polynomial.eval₂ (coeffEnd R T) (linearFrob ρ s m) P = 0

/-- `P` kills `(s, m)` if and only if `ρ` is potentially crystalline and `P`, evaluated at
`linearFrob ρ s m` through `coeffEnd`, is zero. -/
lemma isKilledBy_iff {ρ : Representation R Γ T} {s : Γ} {m : ℕ} {P : Polynomial R} :
    IsKilledBy ρ s m P ↔
      IsPotentiallyCrystalline ρ ∧ Polynomial.eval₂ (coeffEnd R T) (linearFrob ρ s m) P = 0 :=
  Iff.rfl

/-- If `P` kills `(s, m)`, then `ρ` is potentially crystalline. -/
lemma IsKilledBy.isPotentiallyCrystalline {ρ : Representation R Γ T} {s : Γ} {m : ℕ}
    {P : Polynomial R} (h_killed : IsKilledBy ρ s m P) : IsPotentiallyCrystalline ρ :=
  (isKilledBy_iff.mp h_killed).left

/-- If `P` kills `(s, m)`, then `P` evaluated at `linearFrob ρ s m` through `coeffEnd` is zero. -/
lemma IsKilledBy.eval₂_eq_zero {ρ : Representation R Γ T} {s : Γ} {m : ℕ} {P : Polynomial R}
    (h_killed : IsKilledBy ρ s m P) : Polynomial.eval₂ (coeffEnd R T) (linearFrob ρ s m) P = 0 :=
  (isKilledBy_iff.mp h_killed).right

end Frobenius

/-!
## The filter near 1, fixed fields and embeddings of Q̄_p in ℂ_p

* `New.Period.flat_padicInt_of_algebra_padic`: a `ℚ_p`-algebra is flat over `ℤ_p`.
* `New.Period.nearOne_eq_nhds_one`: if `toGp` is an open embedding, the filter near `1` on `Γ` is
  the filter of neighbourhoods of `1`.
* `New.Period.localFieldOf`: the subfield of Q̄_p fixed by the image of `toGp`.
-/

section NearOne

open Module Filter Topology nonZeroDivisors AlgHom

variable {p : ℕ} [ThePrime p] {Γ : Type*} [Group Γ] [𝒥 : OverGp Γ p]

/-- A `ℚ_p`-algebra is flat over `ℤ_p`. -/
instance flat_padicInt_of_algebra_padic {B : Type*} [CommRing B] [Algebra ℤ_[p] B] [Algebra ℚ_[p] B]
    [IsScalarTower ℤ_[p] ℚ_[p] B] : Flat ℤ_[p] B := Module.Flat.trans ℤ_[p] ℚ_[p] B

/-- If `j : Γ → Gp p` is an open embedding for a topology on `Γ`, the filter near `1` on `Γ` is the
filter of neighbourhoods of `1`. -/
lemma nearOne_eq_nhds_one [TopologicalSpace Γ] (hj : IsOpenEmbedding 𝒥.toGp) :
    nearOne Γ = 𝓝 1 := by simp [nearOne, hj.nhds_eq_comap]

variable (Γ) in
/-- The subfield of ℚ̄_p fixed by the image of `j : Γ → Gp p`. -/
noncomputable abbrev localFieldOf : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  fixedFieldOf 𝒥.toGp.range

/-- An element of ℚ̄_p lies in `localFieldOf Γ` if and only if every `j(g)` fixes it. -/
lemma mem_localFieldOf {x : PadicAlgCl p} : x ∈ localFieldOf Γ ↔ ∀ g : Γ, 𝒥.toGp g x = x := by
  simp

/-- Every `ℤ_p`-algebra map from `Q̄_p` to `ℂ_p` is an element of the Galois group `Gp p` followed
by the inclusion. -/
lemma exists_gp_eq_algHom (γ : PadicAlgCl p →ₐ[ℤ_[p]] ℂ_[p]) :
    ∃ s : Gp p, ∀ x : PadicAlgCl p, γ x = s x := by
  -- `γ` is `ℚ_[p]`-linear, so it restricts to an automorphism of the normal extension
  -- `PadicAlgCl p` of `ℚ_[p]`.
  let γ' : PadicAlgCl p →ₐ[ℚ_[p]] ℂ_[p] := γ.extendScalarsOfIsLocalization ℚ_[p] ℤ_[p]⁰
  refine ⟨γ'.restrictNormal' (PadicAlgCl p), fun x ↦ ?_⟩
  -- The restriction followed by the inclusion into `ℂ_[p]` is `γ'`, which agrees with `γ`.
  simp [γ', restrictNormal', PadicComplex.coe_eq, AlgHom.restrictNormal_commutes]

variable (Γ) in
/-- The filter of neighbourhoods of `1` in `Gp p` is finer than the image under `j` of the filter
near `1` on `Γ`: a set whose preimage under `j` is near `1` is a neighbourhood of `1`. This uses
that the image of `j` is open. -/
lemma nhds_one_le_map_nearOne : 𝓝 1 ≤ map toGp (nearOne Γ) := by
  have h_range_mem : Set.range 𝒥.toGp ∈ 𝓝 (1 : Gp p) :=
    𝒥.isOpen_range.out.mem_nhds (one_mem 𝒥.toGp.range)
  exact (map_comap_of_mem h_range_mem).ge

end NearOne

end New.Period

/-!
## An order instance, and base change of bilinear pairings

The ideals of `O^♭` are linearly ordered, and a `ℤ_p`-bilinear pairing extends to `A ⊗ T`
compatibly with maps `ψ ⊗ f`.
-/

namespace New.Lift

open Period TensorProduct LinearMap

variable {p : ℕ} [ThePrime p] {T T' T'' A A' : Type} [AddCommGroup T] [Module ℤ_[p] T]
  [AddCommGroup T'] [Module ℤ_[p] T'] [AddCommGroup T''] [Module ℤ_[p] T''] [CommRing A]
  [CommRing A'] [Algebra ℤ_[p] A] [Algebra ℤ_[p] A']
  (b : T →ₗ[ℤ_[p]] T' →ₗ[ℤ_[p]] T'')

-- A shortcut instance: without it, the instance searches for `FaithfulSMul Ainf _` in later files
-- do not finish.
open scoped Classical in
/-- The ideals of `OFlat` (the tilt `O^♭`) are linearly ordered. -/
noncomputable instance : LinearOrder (Ideal OFlat) := by infer_instance

/-- The `A`-bilinear map `(A ⊗ T) × (A ⊗ T') → A ⊗ T''` obtained from a `ℤ_p`-bilinear map
`b : T × T' → T''` by extension of scalars. -/
noncomputable def baseChangePairing : A ⊗[ℤ_[p]] T →ₗ[A] A ⊗[ℤ_[p]] T' →ₗ[A] A ⊗[ℤ_[p]] T'' :=
  (baseChangeHom ℤ_[p] A T' T'' ∘ₗ b).liftBaseChange A

/-- Let `ψ : A → A'` be `ℤ_p`-linear and multiplicative (`hψ_mul`), and let the endomorphisms `f`,
`f'`, `f''` of `T`, `T'`, `T''` be compatible with `b`: `b (f t) (f' t') = f'' (b t t')`. Then the
extended pairings satisfy the same identity for the maps `ψ ⊗ f`, `ψ ⊗ f'` and `ψ ⊗ f''`. -/
lemma baseChangePairing_map_of_map_mul {ψ : A →ₗ[ℤ_[p]] A'} {f : T →ₗ[ℤ_[p]] T}
    {f' : T' →ₗ[ℤ_[p]] T'} {f'' : T'' →ₗ[ℤ_[p]] T''}
    (h_equiv : ∀ (t : T) (t' : T'), b (f t) (f' t') = f'' (b t t'))
    (hψ_mul : ∀ a a' : A, ψ (a * a') = ψ a * ψ a') (x : A ⊗[ℤ_[p]] T) (y : A ⊗[ℤ_[p]] T') :
    baseChangePairing b (map ψ f x) (map ψ f' y) = map ψ f'' (baseChangePairing b x y) := by
  -- Both sides are additive in `x` and in `y`; on pure tensors this is `h_equiv` and `hψ_mul`.
  induction x with
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | tmul a t =>
    induction y with
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
    | _ => simp [baseChangePairing, smul_tmul', h_equiv, hψ_mul]

/-- `New.Lift.baseChangePairing_map_of_map_mul` in the form in which `simp` proves the
multiplicativity `hψ_mul` of `ψ` by default. -/
lemma baseChangePairing_map {ψ : A →ₗ[ℤ_[p]] A'} {f : T →ₗ[ℤ_[p]] T} {f' : T' →ₗ[ℤ_[p]] T'}
    {f'' : T'' →ₗ[ℤ_[p]] T''} (h_equiv : ∀ (t : T) (t' : T'), b (f t) (f' t') = f'' (b t t'))
    (x : A ⊗[ℤ_[p]] T) (y : A ⊗[ℤ_[p]] T')
    (hψ_mul : ∀ a a' : A, ψ (a * a') = ψ a * ψ a' := by simp) :
    baseChangePairing b (map ψ f x) (map ψ f' y) = map ψ f'' (baseChangePairing b x y) :=
  baseChangePairing_map_of_map_mul b h_equiv hψ_mul x y

end New.Lift

namespace New.Period

/-!
## Admissibility: equivariant maps, finer filters, pull-back, Tate twists

* `New.Period.periodTensorMap`, `New.Period.tensorAction_periodTensorMap`: the map `b ⊗ x ↦ b ⊗ f x`
  and the diagonal actions.
* `New.Period.fixedPeriods.periodTensorMap_mem`,
  `New.Period.IsAdmissible.periodTensorMap_mem_span_fixedPeriods`: transfer along equivariant maps.
* `New.Period.IsAdmissible.mono`, `New.Period.IsAdmissible.tate_twist`,
  `New.Period.IsPotentiallyCrystalline.comp`: finer filters, Tate twists and pull-back.
-/

section Admissible

open TensorProduct Filter Submodule Module Function Set Multiplicative AlgebraTensorModule

variable {p : ℕ} [ThePrime p]
  {Γ R T R' T' : Type*} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R]
  [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [CommRing R'] [AddCommGroup T'] [Module R' T']
  [Algebra ℤ_[p] R'] [Module ℤ_[p] T'] [IsScalarTower ℤ_[p] R' T'] [𝒥 : OverGp Γ p]
  {ρ σ : Representation R Γ T} {ρ' : Representation R' Γ T'} {F F' : Filter Γ}
  {B B' M : Type*} [CommRing B] [Algebra ℤ_[p] B] [Monoid M] [MulSemiringAction M B]
  [SMulCommClass M ℤ_[p] B] [CommRing B'] [Algebra ℤ_[p] B'] [MulSemiringAction M B']
  [SMulCommClass M ℤ_[p] B'] [Algebra B B'] [IsScalarTower ℤ_[p] B B'] [SMulDistribClass M B B']
  {f : T →ₗ[ℤ_[p]] T'} {Γ' : Type*} [Group Γ'] (φ : Γ' →* Γ) (m n : M) (g k : End R T)

variable (ρ) in
/-- A representation over `R`, read as a representation over `ℤ_[p]`. -/
noncomputable abbrev overZp : Representation ℤ_[p] Γ T := actionRep ℤ_[p] T ρ

/-- `Bmax ⊗ T` is torsion-free over `Bmax`: it is free, being `Bmax ⊗_{ℚ_p} (ℚ_p ⊗ T)`. -/
instance : IsTorsionFree Bmax (Bmax ⊗[ℤ_[p]] T) :=
  (Free.of_equiv (cancelBaseChange ℤ_[p] ℚ_[p] Bmax Bmax T)).instIsTorsionFree

variable (B B' f) in
/-- The `B`-linear map `B ⊗ T → B' ⊗ T'`, `b ⊗ x ↦ b ⊗ f x`, along the algebra map `B → B'`. -/
noncomputable def periodTensorMap : B ⊗[ℤ_[p]] T →ₗ[B] B' ⊗[ℤ_[p]] T' :=
  AlgebraTensorModule.map (Algebra.linearMap B B') f

lemma baseChange_eq_periodTensorMap : f.baseChange B = periodTensorMap B B f := rfl

/-! ### The semilinear maps `tensorAction` -/

/-- The map `b ⊗ x ↦ m b ⊗ g x` on `B ⊗ T` is semilinear for the action of `m` on `B`. -/
lemma tensorAction_smul (b : B) (x : B ⊗[ℤ_[p]] T) :
    tensorAction B m g (b • x) = (m • b) • tensorAction B m g x := by
  induction x with
  | add y z hy hz => simp only [smul_add, map_add, hy, hz]
  | _ => simp [tensorAction, smul_tmul']

/-- Let `f : T → T'` be `ℤ_p`-linear with `f ∘ g = g' ∘ f`. Then for every `m` in `M`,
`New.Period.periodTensorMap` commutes with the actions `b ⊗ x ↦ m b ⊗ g x` on `B ⊗ T` and
`b ⊗ x ↦ m b ⊗ g' x` on `B' ⊗ T'`. This needs the action of `M` on `B'` to be compatible with the
`B`-algebra structure of `B'`. -/
lemma tensorAction_periodTensorMap {g : End R T} {g' : End R' T'}
    (hf : ∀ x : T, f (g x) = g' (f x)) (m : M) (x : B ⊗[ℤ_[p]] T) :
    tensorAction B' m g' (periodTensorMap B B' f x) =
      periodTensorMap B B' f (tensorAction B m g x) := by
  induction x with
  | add y z hy hz => simp only [map_add, hy, hz]
  | _ => simp [hf, tensorAction, periodTensorMap]

/-- Applying `tensorAction` (for `(m, g)`, the map `b ⊗ x ↦ (m • b) ⊗ g x` on `B ⊗ T`) for `(n, k)`
and then for `(m, g)` is `tensorAction` for `(m * n, g * k)`. -/
lemma tensorAction_tensorAction (x : B ⊗[ℤ_[p]] T) :
    tensorAction B m g (tensorAction B n k x) = tensorAction B (m * n) (g * k) x := by
  induction x with
  | add y z hy hz => simp only [map_add, hy, hz]
  | _ => simp [tensorAction, mul_smul]

/-! ### Criteria for admissibility and its stability -/

/-- An element `x` of `B ⊗ T` lies in `fixedPeriods ρ B F` if and only if `j(g) ⊗ ρ(g)` fixes it
for `F`-almost all `g`. -/
lemma mem_fixedPeriods_iff [MulSemiringAction (Gp p) B] [SMulCommClass (Gp p) ℤ_[p] B]
    {x : B ⊗[ℤ_[p]] T} :
    x ∈ fixedPeriods ρ B F ↔ ∀ᶠ g : Γ in F, tensorAction B (toGp g) (ρ g) x = x := Iff.rfl

/-- If `1 ⊗ x` lies in the `Bmax`-span of the periods fixed along `F` for every `x` in `T`, then
`ρ` is admissible along `F`. -/
lemma isAdmissible_of_one_tmul_mem_span
    (h_mem : ∀ x : T, (1 : Bmax) ⊗ₜ[ℤ_[p]] x ∈ span Bmax (fixedPeriods ρ Bmax F)) :
    IsAdmissible ρ F := by
  -- The elements `1 ⊗ x` span `Bmax ⊗ T` over `Bmax`.
  rw [IsAdmissible, eq_top_iff, ← baseChange_top, baseChange_eq_span, span_le]
  rintro _ ⟨x, -, rfl⟩
  exact h_mem x

/-- If `f` intertwines `ρ g` and `ρ' g` for all `g` in a set of `F` (hypothesis `hf`), then
`b ⊗ x ↦ b ⊗ f x` sends periods of `ρ` in `B` fixed along `F` to periods of `ρ'` in `Bmax` fixed
along `F`. -/
lemma fixedPeriods.periodTensorMap_mem (hf : ∀ᶠ g : Γ in F, ∀ x : T, f (ρ g x) = ρ' g (f x))
    [MulSemiringAction (Gp p) B] [SMulCommClass (Gp p) ℤ_[p] B]
    [Algebra B Bmax] [IsScalarTower ℤ_[p] B Bmax] [SMulDistribClass (Gp p) B Bmax]
    {x : B ⊗[ℤ_[p]] T} (hx : x ∈ fixedPeriods ρ B F) :
    periodTensorMap B Bmax f x ∈ fixedPeriods ρ' Bmax F := by
  filter_upwards [hx, hf] with g hx_fixed hf_equivariant
  rw [tensorAction_periodTensorMap hf_equivariant, hx_fixed]

/-- The prime `p` as a unit of `Bmax`: the image of `p`, which is a unit of `B⁺`. -/
noncomputable def Bmax.pUnit : Bmaxˣ := (BPlus.isUnit_p.map (algebraMap BPlus Bmax)).unit

lemma Bmax.coe_pUnit : (Bmax.pUnit : Bmax) = p := by simp [Bmax.pUnit]

/-- Let `ρ` and `σ` be representations on `T` of the group `Γ`, which maps to `Gp p` (`p` the
prime) by `j = toGp` of the instance `𝒥`; `χ g` is the cyclotomic character of `j(g)`. Let `σ` be
the twist `χ ^ c • ρ` (hypothesis `hσ`). Then some unit `t` of `Bmax` turns, by multiplication,
the action of `(n, j(g))` (that is, `φ ^ n ∘ j(g)` on `Bmax`) through `ρ` into the action through
`σ`, up to the factor `p ^ (-n c)`, with `p` the unit `Bmax.pUnit`. -/
lemma exists_tate_twist_unit (c : ℤ)
    (hσ : ∀ (g : Γ) (x : T), σ g x = ((χ g ^ c : ℤ_[p]ˣ) : ℤ_[p]) • ρ g x) :
    ∃ t : Bmaxˣ, ∀ (n : ℕ) (g : Γ) (y : Bmax ⊗[ℤ_[p]] T),
      tensorAction Bmax (ofAdd n, toGp g) (σ g) ((t : Bmax) • y) =
        ((t * Bmax.pUnit ^ (n * -c) : Bmaxˣ) : Bmax) •
          tensorAction Bmax (ofAdd n, toGp g) (ρ g) y := by
  -- Take `t = τ ^ (-c)`, where `φ τ = p τ` and `g τ = χ(g) τ` (`exists_tPeriod`): then
  -- `(n, toGp g)` multiplies `t` by `p ^ (-n c) χ(g) ^ (-c)`, whose second factor cancels the
  -- `χ(g) ^ c` in `σ`.
  obtain ⟨τ, h_assoc, h_phi, h_gal⟩ : ∃ τ : Amax, Associated (algebraMap Ainf Amax mu * p) τ ∧
      frobEnd τ = p * τ ∧ ∀ g : Gp p, g • τ = (cyclotomicGp g : ℤ_[p]) • τ :=
    exists_tPeriod
  -- `τ` is associated to the product `μ * p`, and both `μ` and `p` are units of `Bmax`
  have h_mu_unit : IsUnit (algebraMap Ainf Bmax mu) := by
    simpa only [one_smul] using isUnit_smul_of_dvd_mu (1 : FrobGal) (dvd_refl mu)
  obtain ⟨u, hu⟩ : IsUnit (algebraMap Amax Bmax τ) := by
    refine (h_assoc.map (algebraMap Amax Bmax)).isUnit ?_
    rw [map_mul, map_natCast, ← IsScalarTower.algebraMap_apply, ← Bmax.coe_pUnit]
    exact h_mu_unit.mul Bmax.pUnit.isUnit
  refine ⟨u ^ (-c), fun n g y ↦ ?_⟩
  -- `φ` commutes with `g` and with multiplication by `p`, so `φ ^ n (g τ) = p ^ n • g τ`
  have h_frob_smul : frobEnd (toGp g • τ) = p • (toGp g • τ) := by simp [← smul_frobEnd, h_phi]
  have h_iter : ((ofAdd n, toGp g) : FrobGal) • τ = (fun a : Amax ↦ p • a)^[n] (toGp g • τ) := by
    rw [FrobGal.smul_def]
    exact Commute.iterate_eq_of_map_eq (map_nsmul frobEnd p) n h_frob_smul
  -- `(n, toGp g)` multiplies `u` by `p ^ n χ(g)`
  have h_act : u * Bmax.pUnit ^ (n : ℤ) * (χ g).map (algebraMap ℤ_[p] Bmax).toMonoidHom =
      u.map (MulDistribMulAction.toMonoidHom _ (ofAdd n, toGp g)) := by
    ext
    -- By `hu`, `h_iter` and `h_gal`, both sides are products of `τ`, `p ^ n` and `χ(g)` in `Bmax`.
    suffices h_ring : algebraMap Amax Bmax τ * (p : Bmax) ^ n *
        algebraMap ℤ_[p] Bmax (cyclotomicGp (toGp g) : ℤ_[p]) =
        (p : Bmax) ^ n * (algebraMap ℤ_[p] Bmax (cyclotomicGp (toGp g) : ℤ_[p]) *
          algebraMap Amax Bmax τ) by
      simpa [hu, h_iter, h_gal, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, Bmax.coe_pUnit]
        using h_ring
    ring
  -- rewrite `t * p ^ (n * -c)` as `(((n, g) • u) * χ(g)⁻¹) ^ (-c)`
  rw [zpow_mul, ← mul_zpow, eq_mul_inv_of_mul_eq h_act]
  -- On `b ⊗ x`, both sides are `((n, g) • (u ^ (-c) * b)) χ(g) ^ c ⊗ ρ g x` by `hσ`.
  induction y with
  | add y z hy hz => simp only [smul_add, map_add, hy, hz]
  | _ => simp [hσ, mul_zpow, ← map_zpow, tensorAction, smul_tmul', mul_smul]

/-- `tensorAction` for the pair `(1, g)` of `FrobGal` is `tensorAction` for `g`: `φ ^ 0` is the
identity. -/
private lemma tensorAction_mk_one (g : Gp p) (f : End R T) :
    tensorAction Bmax ((1, g) : FrobGal) f = tensorAction Bmax g f := rfl

/-- Let `ρ` be a representation of `Γ` on `T`, where `Γ` maps to Gal(ℚ̄_p/ℚ_p) by `j`. Say `ρ` is
admissible along a filter `F` on `Γ` if the elements of `Bmax ⊗ T` fixed by `j(g) ⊗ ρ(g)` for
`F`-almost all `g` span `Bmax ⊗ T` over `Bmax`. If `ρ` is admissible along `F`, then so is every
Tate twist `σ = χ ^ c • ρ` (hypothesis `hσ`, with `χ` the cyclotomic character and `c` an integer).

For `F = ⊤` and `F = nearOne Γ`, this says that crystalline and potentially crystalline
representations are stable under twists by powers of the cyclotomic character. -/
lemma IsAdmissible.tate_twist (h_adm : IsAdmissible ρ F) (c : ℤ)
    (hσ : ∀ (g : Γ) (x : T), σ g x = ((χ g ^ c : ℤ_[p]ˣ) : ℤ_[p]) • ρ g x) :
    IsAdmissible σ F := by
  -- Multiplication by the unit `t` of `exists_tate_twist_unit` carries the periods of `ρ` fixed
  -- along `F` to those of `σ`.
  obtain ⟨t, h_twist⟩ := exists_tate_twist_unit c hσ
  -- for `n = 0` the pair `(0, toGp g)` acts as `toGp g`, and the factor `Bmax.pUnit ^ 0` is `1`
  have h_twist_zero (g : Γ) (y : Bmax ⊗[ℤ_[p]] T) :
      tensorAction Bmax (toGp g) (σ g) ((t : Bmax) • y) =
        (t : Bmax) • tensorAction Bmax (toGp g) (ρ g) y := by
    simpa [tensorAction_mk_one] using h_twist 0 g y
  have h_fix : ∀ y ∈ fixedPeriods ρ Bmax F, (t : Bmax) • y ∈ fixedPeriods σ Bmax F := by
    intro y hy
    filter_upwards [hy] with g hg
    rw [h_twist_zero, hg]
  have h_le : span Bmax (fixedPeriods ρ Bmax F) ≤ span Bmax (fixedPeriods σ Bmax F) :=
    span_le.mpr fun y hy ↦ (smul_mem_iff_of_isUnit _ t.isUnit).mp (subset_span (h_fix y hy))
  exact eq_top_mono h_le h_adm

/-- Here `ρ` is admissible along a filter `F` on `Γ` when the elements of `Bmax ⊗ T` fixed by
`j(g) ⊗ ρ(g)` for `F`-almost all `g` span `Bmax ⊗ T` over `Bmax`; `j : Γ → Gp p` is the map with
open image given by `OverGp Γ p`. If `ρ` is admissible along `F`, it is admissible along every finer
filter `F' ≤ F`, because an element fixed for `F`-almost all `g` is fixed for `F'`-almost all
`g`. -/
lemma IsAdmissible.mono (h_adm : IsAdmissible ρ F) (h_le : F' ≤ F) : IsAdmissible ρ F' := by
  have h_subset : fixedPeriods ρ Bmax F ⊆ fixedPeriods ρ Bmax F' :=
    fun y hy ↦ mem_fixedPeriods_iff.mpr ((mem_fixedPeriods_iff.mp hy).filter_mono h_le)
  exact eq_top_mono (span_mono h_subset) h_adm

/-- Let `ρ` be admissible along `F` and let `f` intertwine `ρ g` and `ρ' g` for all `g` in a set of
`F` (hypothesis `hf`). Then the map `1 ⊗ f` sends `Bmax ⊗ T` into the span of the periods of `ρ'`
fixed along `F`. -/
lemma IsAdmissible.periodTensorMap_mem_span_fixedPeriods (h_adm : IsAdmissible ρ F)
    {f : T →ₗ[ℤ_[p]] T'} (hf : ∀ᶠ g : Γ in F, ∀ x : T, f (ρ g x) = ρ' g (f x))
    (x : Bmax ⊗[ℤ_[p]] T) :
    periodTensorMap Bmax Bmax f x ∈ span Bmax (fixedPeriods ρ' Bmax F) := by
  -- `x` is in the span of the periods of `ρ`, which `1 ⊗ f` maps to periods of `ρ'`
  have hx : x ∈ span Bmax (fixedPeriods ρ Bmax F) := eq_top_iff'.mp h_adm x
  exact mapsTo_span (fun y hy ↦ fixedPeriods.periodTensorMap_mem hf hy) hx

/-- A crystalline representation is potentially crystalline: the filter `nearOne Γ` is finer than
`⊤`. -/
lemma IsCrystalline.isPotentiallyCrystalline (h_crys : IsCrystalline ρ) :
    IsPotentiallyCrystalline ρ := h_crys.mono le_top

/-- If `Γ` acts through the `c`-th power of the cyclotomic character (`χ g`, the cyclotomic
character of `j(g)`, with `j` = `toGp`), then `ρ` is admissible along every filter `F`. -/
lemma isAdmissible_of_cyclotomicGp_zpow (c : ℤ)
    (h_act : ∀ (g : Γ) (x : T), ρ g x = ((χ g ^ c : ℤ_[p]ˣ) : ℤ_[p]) • x) : IsAdmissible ρ F := by
  -- `ρ` is the twist by `χ ^ c` of the trivial representation, for which every `1 ⊗ x` is fixed.
  have h_trivial : IsAdmissible (1 : Representation R Γ T) F :=
    isAdmissible_of_one_tmul_mem_span fun x ↦ subset_span (by simp [fixedPeriods, tensorAction])
  exact h_trivial.tate_twist c (by simpa using h_act)

/-! ### Pull-back and the filter of elements near 1 -/

/-- Let `φ : Γ' →* Γ` be such that `toGp ∘ φ` has open image (`h_open`), which makes `Γ'` a group
over `Gp p`. Here a representation is admissible along a filter when the elements of `Bmax ⊗ T`
fixed by `j(g) ⊗ ρ(g)` for almost all `g` span `Bmax ⊗ T` over `Bmax`, where `j` is the map to
`Gp p` (`toGp` for `Γ`, `toGp ∘ φ` for `Γ'`). The pull-back `ρ ∘ φ` is admissible along a filter `F`
on `Γ'` if and only if `ρ` is admissible along the image filter `F.map φ`. -/
lemma isAdmissible_comp_iff (h_open : Fact (IsOpen ((𝒥.toGp.comp φ).range : Set (Gp p))))
    {F : Filter Γ'} :
    IsAdmissible (𝒥 := ⟨toGp.comp φ, h_open⟩) (ρ.comp φ) F ↔ IsAdmissible ρ (F.map φ) := Iff.rfl

/-- Let `toGp : Γ →* Gp p` be injective and let `φ : Γ' →* Γ` be such that `toGp ∘ φ` has open image
in `Gp p`. Then `φ` carries the filter `nearOne Γ'`, taken for `toGp ∘ φ`, to `nearOne Γ`. -/
lemma map_nearOne (h_inj : Injective 𝒥.toGp)
    (h_open : Fact (IsOpen ((𝒥.toGp.comp φ).range : Set (Gp p)))) :
    (nearOne Γ' (𝒥 := ⟨toGp.comp φ, h_open⟩)).map φ = nearOne Γ := by
  -- The left side pushed forward along `toGp` is the neighbourhood filter of `1`, as the image of
  -- `toGp ∘ φ` is open; pull it back along the injective map `toGp`.
  have h_push : ((nearOne Γ' (𝒥 := ⟨toGp.comp φ, h_open⟩)).map φ).map 𝒥.toGp = nhds 1 :=
    map_comap_of_mem (h_open.out.mem_nhds (one_mem (𝒥.toGp.comp φ).range))
  -- `nearOne.eq_1 Γ` unfolds `nearOne` on the right side only
  rw [nearOne.eq_1 Γ, ← h_push, comap_map h_inj]

/-- The pull-back of a potentially crystalline representation along `φ : Γ' →* Γ` is potentially
crystalline, where `Γ'` maps to `Gp p` by `toGp ∘ φ`, assumed to have open image (`h_open`). This
covers restriction to the Galois group of a finite extension of the base field. -/
lemma IsPotentiallyCrystalline.comp {h_open : Fact (IsOpen ((𝒥.toGp.comp φ).range : Set (Gp p)))}
    (h_crys : IsPotentiallyCrystalline ρ) :
    IsPotentiallyCrystalline (𝒥 := ⟨toGp.comp φ, h_open⟩) (ρ.comp φ) := by
  -- `φ` maps the elements near `1` to elements near `1`
  have h_le : (nearOne Γ' (𝒥 := ⟨toGp.comp φ, h_open⟩)).map φ ≤ nearOne Γ :=
    tendsto_comap_iff.mpr map_comap_le
  exact (isAdmissible_comp_iff φ h_open).mpr (h_crys.mono h_le)

end Admissible

/-!
## The action on B ⊗ T in the coordinates of a basis of T

* `New.Period.coordAction`: apply `toGp g` to each coordinate, then multiply by the matrix of `ρ g`.
-/

section PeriodCoordinates

open Algebra Module Matrix LinearMap

variable {p : ℕ} [ThePrime p]
  {Γ ι B R T : Type _} [Group Γ] [Fintype ι] [DecidableEq ι] [OverGp Γ p] [CommRing B]
  [Algebra ℤ_[p] B] [MulSemiringAction (Gp p) B] [SMulCommClass (Gp p) ℤ_[p] B] [CommRing R]
  [Algebra ℤ_[p] R] [AddCommGroup T] [Module R T] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T]
  (ρ : Representation R Γ T) (e : Basis ι ℤ_[p] T)

/-- The monoid homomorphism sending `g` in `Γ` to the matrix over `ℤ_[p]` of `ρ g` in a finite
`ℤ_[p]`-basis `e` of `T`. -/
noncomputable def repMatrix : Γ →* Matrix ι ι ℤ_[p] :=
  (toMatrixAlgEquiv e).toMonoidHom.comp (overZp ρ)

/-- The action on `B ⊗ T` in coordinates. `g` acts on a vector `y : ι → B` by applying `toGp g` to
each coordinate. It then multiplies by the matrix `New.Period.repMatrix ρ e g`, read over `B`. -/
noncomputable def coordAction : Representation ℤ_[p] Γ (ι → B) where
  toFun g := ((repMatrix ρ e g).map (algebraMap ℤ_[p] B)).mulVecLin ∘ₗ
    actionRep ℤ_[p] (ι → B) toGp g
  map_one' := by aesop
  -- `Gp p` fixes the entries of `repMatrix ρ e g`, which come from `ℤ_[p]`
  map_mul' := by simp [LinearMap.ext_iff, mul_smul, mulVec_eq_sum, Finset.smul_sum]

/-- For a `ℤ_[p]`-algebra `B` with an action of `Gp p` and a finite `ℤ_[p]`-basis `e` of `T`, the
map `b ⊗ x ↦ j(g) b ⊗ ρ(g) x` on `B ⊗ T` becomes, in the coordinates given by `e`, the action
`New.Period.coordAction` built from the matrices `New.Period.repMatrix ρ e g`. -/
lemma equivFun_tensorAction (g : Γ) (y : TensorProduct ℤ_[p] B T) :
    (e.baseChange B).equivFun (tensorAction B (toGp g) (ρ g) y) =
      coordAction ρ e g ((e.baseChange B).equivFun y) := by
  ext i
  -- Expand `y` on the left in the basis `e.baseChange B` and use semilinearity of `tensorAction`.
  nth_rw 1 [← (e.baseChange B).sum_repr y, map_sum]
  simp_rw [tensorAction_smul]
  -- Coordinate `i` of both sides is `∑ c, (e.repr (ρ g (e c))) i • toGp g (y_c)`, with `y_c` the
  -- coordinates of `y`: unfold `tensorAction`, `coordAction` and the matrix.
  simp [tensorAction, coordAction, repMatrix, toMatrixAlgEquiv_apply, mulVec_eq_sum, ← smul_def]

end PeriodCoordinates

end New.Period

end
