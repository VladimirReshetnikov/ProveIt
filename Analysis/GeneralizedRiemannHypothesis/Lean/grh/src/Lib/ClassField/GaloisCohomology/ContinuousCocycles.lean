import Lib.ClassField.Places.GaloisDefs

/-!
# Continuous cohomology of discrete modules: cocycles, H², cyclic classes, local Artin map

This file builds the part of continuous group cohomology used in this library, using explicit
cochains. It works with a representation `ρ` of a topological group `G` on a discrete `R`-module
`M`, and with discrete modules `New.DiscreteModule R Γ`. It also defines the cyclic class of a
character into `ℚ/ℤ` and an invariant, and the basic objects of local class field theory, where `Γ`
is a Galois group of `Ω` over `K`. It then treats restriction and short exact sequences of discrete
modules, and counts continuous 1-cocycles along exact sequences.

## Main definitions and results

* `New.Z2`, `New.B2`, `New.H2`: continuous 2-cocycles, coboundaries and their quotient.
* `New.QZ`, `New.QZ.carry`, `New.QZChar`: the discrete group `ℚ/ℤ`, the carry of two representatives
  in `[0, 1)`, and continuous characters into `ℚ/ℤ`.
* `New.cyclicClass`: the class of `(g, h) ↦ carry (χ g) (χ h) • w`, additive in `χ` and in `w`.
* `New.IsClassOfInvariant`, `New.Cohomology.classOfInvariant`: the map from `ℚ/ℤ` to `H²(Γ, Ωˣ)`
  normalised on unramified cyclic classes.
* `New.IsLocalArtin`, `New.localArtin`, `New.placeOver`: the local Artin map, defined by duality
  with the cyclic classes `New.cyclicClass`, its version on the completion of a number field at a
  prime, and a chosen place over that prime.
* `New.DiscreteModule R Γ`: a discrete `R`-module with a continuous `R`-linear action of `Γ`.

Notions from other files:
* `New.DiscreteUnits Ω`: the group `Ωˣ` written additively, with the discrete topology;
  `New.unitsRep` is the action of `Γ` on it.
* `New.IsFrob A q σ`: `σ` stabilises `A` and `σ • x ≡ x ^ q` modulo the maximal ideal of `A`;
  `New.inertiaGroup Γ A` is the case `q = 1`.
* `New.IsPlaceOver A v`: the valuation subring `A` of `Ω` lies over the prime `v` of the number
  field `K`: an integer of `K` lies in the maximal ideal of `A` exactly when it lies in `v`.

## Relation to the literature

Known; see `Lib.ClassField.GaloisCohomology.KummerCyclicClasses`, `Lib.ClassField.Local.ArtinMap`,
`Lib.ClassField.Places.LocalFields` and `Lib.ClassField.LocalDuality.CrystallineDuality` for
sources.
-/

noncomputable section

/-!
## Continuous cocycles, H² and compatible pairs

Cochains are functions `G → M` and `G × G → M` (inhomogeneous cochains).

* `New.actionRep`, `New.charRep`: the representation given by a homomorphism into a monoid acting on
  `M`, and the one in which a character `G → Rˣ` acts by scalars.
-/

namespace New

open Submodule DistribMulAction

variable {R G M H N : Type*} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R G M)
  [Group H] [TopologicalSpace H] [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [DiscreteTopology N] {ρ' : Representation R H N} (φ : H →ₜ* G) (u : M →ₗ[R] N)
  (h : ∀ (g : H) (m : M), u (ρ (φ g) m) = ρ' g (u m) := by bound)

/-- On a discrete module, scalar multiplication by each constant of `R` is continuous. -/
instance (priority := 100) : ContinuousConstSMul R M := ⟨by fun_prop⟩

/-- The continuous 1-cocycles of `ρ`: the `R`-submodule of continuous `f : G → M` with
`f (g * h) = f g + ρ g (f h)`. -/
def Z1 : Submodule R (G → M) :=
  Submodule.mk (R := R)
    { carrier := {f : G → M | Continuous f ∧ ∀ g h : G, f (g * h) = f g + ρ g (f h)}
      add_mem' := fun ⟨hf, hf_mul⟩ ⟨hf', hf'_mul⟩ ↦
        ⟨hf.add hf', by simp [hf_mul, hf'_mul, add_add_add_comm]⟩
      zero_mem' := ⟨continuous_zero, by simp⟩ }
    fun c f ⟨hf, hf_mul⟩ ↦ ⟨hf.const_smul c, by simp [hf_mul]⟩

/-- The coboundary map in degree 0: the `R`-linear map from `M` to functions `G → M` sending `m`
to `g ↦ ρ g m - m`. -/
abbrev coboundaryMap : M →ₗ[R] G → M := LinearMap.pi fun g ↦ ρ g - LinearMap.id

/-- The continuous 2-cocycles of `ρ`: continuous `f : G × G → M` with
`f (g * h, k) = f (g, h * k) - f (g, h) + ρ g (f (h, k))`. -/
def Z2 : Submodule R (G × G → M) :=
  ofLinearComb (R := R)
    {f : G × G → M | Continuous f ∧
      ∀ g h k : G, f (g * h, k) = f (g, h * k) - f (g, h) + ρ g (f (h, k))}
    ⟨0, continuous_zero, by simp⟩
    fun f ⟨hf, hf_eq⟩ f' ⟨hf', hf'_eq⟩ a b ↦ ⟨by fun_prop, fun g h k ↦ by
      simp only [Pi.add_apply, Pi.smul_apply, hf_eq, hf'_eq, map_add, map_smul]
      module⟩

/-- The 2-coboundaries of `ρ`: the functions `(g, h) ↦ ρ g (c h) - c (g * h) + c g` on `G × G`, for
continuous `c : G → M`. -/
def B2 : Submodule R (G × G → M) :=
  ofLinearComb
    {f : G × G → M | ∃ c : G → M,
      Continuous c ∧ ∀ g h : G, f (g, h) = ρ g (c h) - c (g * h) + c g}
    ⟨0, 0, continuous_zero, by simp⟩
    fun f ⟨c, hc, hf⟩ f' ⟨c', hc', hf'⟩ a b ↦ ⟨a • c + b • c', by fun_prop, fun g h ↦ by
      simp only [Pi.add_apply, Pi.smul_apply, hf, hf', map_add, map_smul]
      module⟩

/-- Continuous cohomology `H²(G, M)`: the continuous 2-cocycles of `ρ` modulo the coboundaries of
continuous 1-cochains `G → M`. -/
@[instance_reducible]
def H2 : Type _ := Z2 ρ ⧸ (B2 ρ).comap (Z2 ρ).subtype
  deriving AddCommGroup, Module R

variable {ρ}

/-! ### Maps induced by a compatible pair -/

/-- For a continuous homomorphism `φ : H →ₜ* G` and an `R`-linear `u : M → N` with
`u (ρ (φ g) m) = ρ' g (u m)` (the hypothesis `h`, proved by `bound` when it is not
given), the additive map `f ↦ u ∘ f ∘ φ` from continuous 1-cocycles of `ρ` to those of `ρ'`. -/
abbrev pairMapZ1 : Z1 ρ →+ Z1 ρ' where
  toFun f := ⟨fun g ↦ u (f.1 (φ.1 g)), f.2.imp (by continuity) (by aesop)⟩
  map_zero' := by bound
  map_add' := by bound

/-- The linear map `H²(G, M) → H²(H, N)` induced by a continuous homomorphism `φ : H →ₜ* G` and an
`R`-linear `u : M → N` with `u (ρ (φ g) m) = ρ' g (u m)` (the hypothesis `h`, proved by
`bound` when it is not given): the class of `f` goes to the class of
`(g, g') ↦ u (f (φ g, φ g'))`. -/
def pairMapH2 : H2 ρ →ₗ[R] H2 ρ' :=
  mapQ (comap (Z2 ρ).subtype (B2 ρ)) (comap (Z2 ρ').subtype (B2 ρ'))
    { toFun f :=
        ⟨fun p ↦ u (f.1 (p.map φ φ)), by have := f.2.1; fun_prop, fun g g' g'' ↦ by simp [f.2.2, h]⟩
      map_add' f f' := Subtype.ext (funext (by simp))
      map_smul' a f := Subtype.ext (funext (by simp)) }
    -- The coboundary of `c` goes to the coboundary of `u ∘ c ∘ φ`.
    fun f ⟨c, hc, hf⟩ ↦ ⟨u ∘ c ∘ φ, by fun_prop, by simp_all⟩

/-! ### Representations given by a homomorphism -/

variable (R) in
/-- The `R`-linear representation of a monoid `G` on `M` obtained from a homomorphism `χ : G →* S`
into a monoid `S` acting `R`-linearly on `M`: `g` acts as `χ g`. -/
abbrev actionRep (M : Type*) [AddCommMonoid M] [Module R M] {G S : Type*} [Monoid G] [Monoid S]
    [DistribMulAction S M] [SMulCommClass S R M] (χ : G →* S) : Representation R G M :=
  (toModuleEnd R M).comp χ

/-- For an `R`-module `M` and a character `χ : G →* Rˣ`, the representation of `G` on `M` in which
`g` acts as the scalar `χ g`. -/
def charRep (M : Type*) [AddCommGroup M] [Module R M] (χ : G →* Rˣ) : Representation R G M :=
  actionRep R M ((Units.coeHom R).comp χ)

end New

/-!
## Characters into ℚ/ℤ and the cyclic class of (χ, w)

Symbols in the second cohomology: for a character `χ` and an invariant `w`, the class of the cocycle
`(g, h) ↦ carry (χ g) (χ h) • w`. This class is defined directly by this cocycle; it is the cup
product of `w` with the image `δχ` of `χ` under the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`. This
identification is not proved here, and nothing in this file uses it.

* `New.QZ`: the discrete group `ℚ/ℤ`; `New.QZ.fracRep`: the representative in `[0, 1)`.
* `New.QZ.carry`: the integer `fracRep a + fracRep b - fracRep (a + b)` (`New.QZ.cast_carry`), which
  is 0 or 1 since both representatives lie in `[0, 1)`.
-/

section CyclicClass

open Int QuotientAddGroup

namespace New

/-- The group ℚ/ℤ; it is given the discrete topology. -/
def QZ : Type := AddCircle (1 : ℚ)
  deriving AddCommGroup, DivisibleBy _ ℤ

/-- `ℚ/ℤ` carries the discrete topology. -/
instance : TopologicalSpace QZ := ⊥

instance : DiscreteTopology QZ := ⟨rfl⟩

/-- The quotient homomorphism ℚ → ℚ/ℤ. -/
def QZ.mk : ℚ →+ QZ := mk' (AddSubgroup.zmultiples 1)

/-- For a class `a` in `ℚ/ℤ`, its unique rational representative in the interval `[0, 1)`. -/
def QZ.fracRep (a : QZ) : ℚ := (a.equivIco 1 0 : ℚ)

/-- For `a`, `b` in `ℚ/ℤ`, the integer part `⌊fracRep a + fracRep b⌋` of the sum of their
representatives in `[0, 1)`; it is `0` or `1`, as both representatives lie in `[0, 1)`. -/
def QZ.carry (a b : QZ) : ℤ := ⌊fracRep a + fracRep b⌋

@[simp]
lemma QZ.mk_fracRep (a : QZ) : mk a.fracRep = a := a.coe_equivIco

/-- The representative in `[0, 1)` of the class of a rational `r` is its fractional part. -/
lemma QZ.fracRep_mk (r : ℚ) : fracRep (mk r) = fract r :=
  show toIcoMod (zero_lt_one' ℚ) 0 r = fract r from toIcoMod_zero_one r

lemma QZ.fracRep_add (a b : QZ) : fracRep (a + b) = fract (fracRep a + fracRep b) := by
  rw [← fracRep_mk, map_add, mk_fracRep, mk_fracRep]

/-- The carry measures how far the representative in `[0, 1)` is from being additive:
`carry a b = fracRep a + fracRep b - fracRep (a + b)` in `ℚ`. -/
@[push_cast]
lemma QZ.cast_carry (a b : QZ) : carry a b = fracRep a + fracRep b - fracRep (a + b) := by
  rw [carry, fracRep_add, self_sub_fract]

/-- The carry is a 2-cocycle of `ℚ/ℤ` with values in `ℤ`:
`carry (a + b) c + carry a b = carry a (b + c) + carry b c`. -/
lemma QZ.carry_add_add_carry (a b c : QZ) :
    carry (a + b) c + carry a b = carry a (b + c) + carry b c := by
  -- in `ℚ`, by `QZ.cast_carry`, both sides are the sum of the three representatives minus that of
  -- `a + b + c`
  qify
  rw [← add_assoc a b c]
  ring

variable {R G M : Type*} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R G M)

variable (G) in
/-- Continuous characters `G → ℚ/ℤ`: the continuous 1-cocycles for the trivial action. -/
abbrev QZChar : Submodule ℤ (G → QZ) := Z1 (Representation.trivial ℤ G QZ)

/-- A continuous character `χ : G → ℚ/ℤ` turns products into sums. -/
lemma QZChar.apply_mul (χ : QZChar G) (g h : G) :
    (χ : G → QZ) (g * h) = (χ : G → QZ) g + (χ : G → QZ) h := by
  simpa using χ.prop.right g h

/-- For a continuous character `χ : G → ℚ/ℤ` and an invariant `w` of `ρ`, the function
`(g, h) ↦ carry (χ g) (χ h) • w` on `G × G` is a continuous 2-cocycle of `ρ`. -/
lemma carry_smul_mem_Z2 (χ : QZChar G) (w : ρ.invariants) :
    (fun p : G × G ↦ ((χ : G → QZ) p.fst).carry ((χ : G → QZ) p.snd) • (w : M)) ∈ Z2 ρ := by
  have hχ_cont : Continuous (χ : G → QZ) := χ.prop.left
  refine ⟨by fun_prop, fun g h k ↦ ?_⟩
  set f : G → QZ := (χ : G → QZ)
  show (f (g * h)).carry (f k) • (w : M) =
    (f g).carry (f (h * k)) • (w : M) - (f g).carry (f h) • (w : M) +
      ρ g ((f h).carry (f k) • (w : M))
  -- `w` is invariant, so this is the cocycle identity of the carry, times `w`
  have hf_mul (a b : G) : f (a * b) = f a + f b := QZChar.apply_mul χ a b
  have h_carry (a b c : QZ) : (a + b).carry c = a.carry (b + c) - a.carry b + b.carry c := by
    linarith [QZ.carry_add_add_carry a b c]
  have hw_inv : ρ g (w : M) = w := w.prop g
  rw [hf_mul, hf_mul, h_carry, map_zsmul, hw_inv, add_smul, sub_smul]

/-- The class in `H²(G, M)` of the cocycle `(g, h) ↦ carry (χ g) (χ h) • w`, additive in the
continuous character `χ : G → ℚ/ℤ` and in the invariant `w` of `ρ`. -/
def cyclicClass : QZChar G →+ ρ.invariants →+ H2 ρ :=
  AddMonoidHom.mk'
    (fun χ ↦
      AddMonoidHom.mk' (fun w ↦ ⟦⟨fun p ↦ (χ.1 p.1).carry (χ.1 p.2) • w, carry_smul_mem_Z2 ρ χ w⟩⟧)
        (fun w w' ↦ by aesop))
    (fun ⟨χ, hχ_cont, hχ⟩ ⟨ψ, hψ_cont, hψ⟩ ↦ by
      -- the cocycle of `χ + ψ` minus those of `χ` and `ψ` is the coboundary of
      -- `g ↦ -carry (χ g) (ψ g) • w`
      refine AddMonoidHom.ext fun w ↦ (Submodule.Quotient.eq _).mpr
        ⟨fun g ↦ (χ g).carry (ψ g) • -w, by fun_prop, fun g h ↦ ?_⟩
      have hw_inv : ρ g (w : M) = w := w.prop g
      show (χ g + ψ g).carry (χ h + ψ h) • (w : M) -
          ((χ g).carry (χ h) • (w : M) + (ψ g).carry (ψ h) • (w : M)) =
        ρ g ((χ h).carry (ψ h) • -(w : M)) - (χ (g * h)).carry (ψ (g * h)) • -(w : M) +
          (χ g).carry (ψ g) • -(w : M)
      simp only [hχ, hψ, Representation.trivial_apply, map_zsmul, map_neg, hw_inv]
      -- compare the integer coefficients of `w`: add up `χ g + ψ g + χ h + ψ h` in two orders
      match_scalars
      qify
      grind)

end New

end CyclicClass

/-!
## Definitions for local class field theory

`A` is a valuation subring of `Ω`. `A.valuation` is multiplicative and below `1` on the maximal
ideal.

Several objects are chosen by `epsilon` from their characteristic property. `New.DiscreteUnits Ω` is
`Ωˣ` written additively, with the action `New.unitsRep`.
-/

section LocalDefs

open NumberField Units
open scoped Classical

namespace New

variable {Γ K Ω : Type*} [Group Γ] [Field K] [Field Ω] [Algebra K Ω] [MulSemiringAction Γ Ω]
  (A : ValuationSubring Ω) [TopologicalSpace Γ]

/-- `π` is a uniformiser of `K` for `A`: an element `x` of `K` lies in the maximal ideal of `A`
exactly when its valuation is at most that of `π`. Here `valuationVia K A x` is the valuation of
`A` at the image of `x` in `Ω`. -/
def IsUniformiser (π : K) : Prop :=
  ∀ x : K, valuationVia K A x < 1 ↔ valuationVia K A x ≤ valuationVia K A π

/-- For a subgroup `H` of `Γ`, the intermediate field of `Ω / K` of the elements fixed by `H`. -/
abbrev fixedFieldOf [IsProGalois Γ K Ω] (H : Subgroup Γ) : IntermediateField K Ω :=
  FixedPoints.intermediateField H

variable (Ω) (χ : QZChar Γ)

/-- The cyclotomic character modulo `N`: the homomorphism `Γ →* (ZMod N)ˣ` giving the action of `Γ`
on the `N`-th roots of unity in `Ω`. -/
def cyclotomicCharMod (N : ℕ) [NeZero N] [HasEnoughRootsOfUnity Ω N] : Γ →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter Ω (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω N)).comp
    (MulSemiringAction.toRingAut Γ Ω)

/-! ### Characters as homomorphisms -/

/-- A continuous character `χ : Γ → ℚ/ℤ` as a group homomorphism to `ℚ/ℤ` written
multiplicatively. -/
def QZChar.toHom : Γ →* Multiplicative QZ :=
  MonoidHom.mk' (fun g ↦ Multiplicative.ofAdd ((χ : Γ → QZ) g)) (by simp [QZChar.apply_mul])

/-- The kernel of a continuous character `χ : Γ → ℚ/ℤ`, as a subgroup of `Γ`. -/
abbrev QZChar.ker : Subgroup Γ := (toHom χ).ker

/-- `QZChar.toHom χ` sends `g` to `χ g`, written multiplicatively. -/
lemma QZChar.toHom_apply (g : Γ) : toHom χ g = Multiplicative.ofAdd ((χ : Γ → QZ) g) := rfl

/-- An element `g` lies in the kernel of the character `χ` exactly when `χ g = 0`. -/
lemma QZChar.mem_ker_iff {g : Γ} : g ∈ QZChar.ker χ ↔ (χ : Γ → QZ) g = 0 := by
  rw [QZChar.ker, MonoidHom.mem_ker, toHom_apply, ofAdd_eq_one]

/-- The kernel of a continuous character `χ : Γ → ℚ/ℤ` is closed in `Γ`. -/
lemma QZChar.isClosed_ker : IsClosed (QZChar.ker χ : Set Γ) := by
  have h_ker : (QZChar.ker χ : Set Γ) = (χ : Γ → QZ) ⁻¹' {0} :=
    Set.ext fun g ↦ QZChar.mem_ker_iff χ
  rw [h_ker]
  exact (isClosed_discrete {0}).preimage χ.prop.left

/-- The homomorphism induced by the continuous character `χ` on the topological abelianisation of
`Γ`, with values in `ℚ/ℤ` written multiplicatively. -/
def QZChar.abelianLift [IsTopologicalGroup Γ] (χ : QZChar Γ) :
    TopologicalAbelianization Γ →* Multiplicative QZ :=
  -- the kernel is closed and contains the commutators
  QuotientGroup.lift (commutator Γ).topologicalClosure (toHom χ)
    (closure_minimal (Abelianization.commutator_subset_ker (toHom χ)) (QZChar.isClosed_ker χ))

variable (Γ)

/-- The homomorphism from `Kˣ` to the `Γ`-invariants of `Ωˣ` (both written additively) induced by
the map `K → Ω`. -/
def DiscreteUnits.ofBase [SMulCommClass Γ K Ω] :
    Additive Kˣ →+ (unitsRep (Γ := Γ) (Ω := Ω)).invariants :=
  (map (algebraMap K Ω)).toAdditive.codRestrict unitsRep.invariants
    fun x g ↦ ext (smul_algebraMap g (x.toMul : K))

end New

namespace New

variable (Γ K : Type*) {Ω : Type*} [Group Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] (A : ValuationSubring Ω) [TopologicalSpace Γ]

section

variable [IsTopologicalGroup Γ]

/-! ### The order, the class of an invariant and the local Artin map -/

/-- The number of elements of the residue field of the valuation ring `A ∩ K` of `K` (zero if it is
infinite). -/
abbrev residueCard : ℕ := Nat.card (IsLocalRing.ResidueField (valRingBelow K A))

/-- The order normalised on `K`: a chosen additive `f : Ωˣ → ℚ` with `n * f x = a` exactly when
`x ^ n` and `π ^ a` have equal valuation, for every uniformiser `π` of `K` (`New.IsUniformiser`: an
`x : K` lies in the maximal ideal of `A` exactly when its valuation is at most that of `π`);
valuations are those of `A`, taken in `Ω`. It is unspecified if no such map exists; see
`New.valuation_pow_eq_iff_mul_ordRat_eq_of_exists`. -/
def ordRat : DiscreteUnits Ω →+ ℚ :=
  Classical.epsilon fun f : DiscreteUnits Ω →+ ℚ ↦
    ∀ π : Kˣ, IsUniformiser A (π : K) → ∀ (x : DiscreteUnits Ω) (n : ℕ) (a : ℤ),
      A.valuation x.toMul ^ n = valuationVia K A π ^ a ↔ n * f x = a

/-- The defining property of `New.ordRat` (`x ^ n` and `π ^ a` have equal valuation in `A` exactly
when `n * ordRat K A x = a`, for each uniformiser `π`) holds as soon as some additive map has it. -/
lemma valuation_pow_eq_iff_mul_ordRat_eq_of_exists
    (h_exists : ∃ f : DiscreteUnits Ω →+ ℚ, ∀ π : Kˣ, IsUniformiser A (π : K) →
      ∀ (x : DiscreteUnits Ω) (n : ℕ) (a : ℤ),
        A.valuation x.toMul ^ n = valuationVia K A π ^ a ↔ n * f x = a)
    (π : Kˣ) (hπ : IsUniformiser A (π : K)) (x : DiscreteUnits Ω) (n : ℕ) (a : ℤ) :
    A.valuation x.toMul ^ n = valuationVia K A π ^ a ↔ n * ordRat K A x = a :=
  Classical.epsilon_spec h_exists π hπ x n a

/-- The property that a map `b : ℚ/ℤ → H²(Γ, Ωˣ)` sends `r` to the class of invariant `r`. First,
`b` is injective. Second, let the continuous character `χ : Γ → ℚ/ℤ` vanish on the inertia group
of `A`, let `φ` be a Frobenius element for `q = residueCard K A`, the number of elements of the
residue field, and let the invariant `w` of `Ωˣ` have normalised order `ordRat K A w = n`; then
`cyclicClass unitsRep χ w = n • b (χ φ)`. -/
def IsClassOfInvariant (b : QZ →+ H2 (unitsRep (Γ := Γ) (Ω := Ω))) : Prop :=
  Function.Injective b ∧
  ∀ χ : QZChar Γ,
    (∀ g ∈ inertiaGroup Γ A, (χ : Γ → QZ) g = 0) →
    ∀ φ : Γ, IsFrob A (residueCard K A) φ →
    ∀ (w : (unitsRep (Γ := Γ) (Ω := Ω)).invariants) (n : ℤ),
      ordRat K A (w : DiscreteUnits Ω) = n →
      cyclicClass unitsRep χ w = n • b ((χ : Γ → QZ) φ)

/-- A chosen additive map `ℚ/ℤ → H²(Γ, Ωˣ)` with the property `New.IsClassOfInvariant`; when such a
map exists, it sends `r` to the class of invariant `r`. See
`New.Cohomology.isClassOfInvariant_classOfInvariant_of_exists`, and for local fields
`New.IsLocalGalois.isClassOfInvariant_classOfInvariant`. -/
def Cohomology.classOfInvariant : QZ →+ H2 (unitsRep (Γ := Γ) (Ω := Ω)) :=
  Classical.epsilon (IsClassOfInvariant Γ K A)

omit [IsTopologicalGroup Γ] in
/-- `New.Cohomology.classOfInvariant` has the property `New.IsClassOfInvariant` as soon as some map
has it. -/
lemma Cohomology.isClassOfInvariant_classOfInvariant_of_exists
    (h_exists : ∃ b : QZ →+ H2 (unitsRep (Γ := Γ) (Ω := Ω)), IsClassOfInvariant Γ K A b) :
    IsClassOfInvariant Γ K A (Cohomology.classOfInvariant Γ K A) :=
  Classical.epsilon_spec h_exists

/-- The property that the homomorphism `f` from `Lˣ` to the topological abelianisation of `Γ`
satisfies `classOfInvariant (χ (f x)) = -cyclicClass unitsRep χ x` for every continuous character
`χ : Γ → ℚ/ℤ` and every `x` in `Lˣ`, where `x` is viewed as an invariant of `Ωˣ`, and `χ (f x)` is
the value at `f x` of `QZChar.abelianLift χ`, the map induced by `χ` on the topological
abelianisation. -/
def IsLocalArtin {L : Type*} [Field L] [Algebra L Ω] [SMulCommClass Γ L Ω]
    (f : Lˣ →* TopologicalAbelianization Γ) : Prop :=
  ∀ (χ : QZChar Γ) (x : Lˣ),
    Cohomology.classOfInvariant Γ K A (QZChar.abelianLift χ (f x)).toAdd =
      -cyclicClass unitsRep χ (DiscreteUnits.ofBase Γ Ω (Additive.ofMul x))

end

variable {K} [IsProGalois Γ K Ω] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-! ### The local Artin map at a prime of a number field -/

/-- The local Artin map at `v`: a chosen homomorphism from the units of the completion
`v.adicCompletion K` of `K` at `v` to the abelianised decomposition group of `A`, whose
restriction to `Kˣ` satisfies `New.IsLocalArtin` over the fixed field of the decomposition group;
unspecified if there is none (see `New.isLocalArtin_localArtin_comp_of_exists` and
`New.IsPlaceOver.isLocalArtin_localArtin`). -/
def localArtin : (v.adicCompletion K)ˣ →* TopologicalAbelianization (decompGroup Γ A) :=
  Classical.epsilon fun f : (v.adicCompletion K)ˣ →* TopologicalAbelianization (decompGroup Γ A) ↦
    IsLocalArtin (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A
      (f.comp (map (algebraMap K (v.adicCompletion K)).toMonoidHom))

/-- The restriction of `New.localArtin Γ A v` to `Kˣ` has its defining property as soon as the
restriction of some homomorphism has it. -/
lemma isLocalArtin_localArtin_comp_of_exists
    (h_exists : ∃ f : (v.adicCompletion K)ˣ →* TopologicalAbelianization (decompGroup Γ A),
      IsLocalArtin (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A
        (f.comp (map (algebraMap K (v.adicCompletion K)).toMonoidHom))) :
    IsLocalArtin (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A
      ((localArtin Γ A v).comp (map (algebraMap K (v.adicCompletion K)).toMonoidHom)) :=
  Classical.epsilon_spec h_exists

/-- For a finite prime `v` of the number field `K`, a chosen valuation subring of `New.Ω` (the
algebraic closure of `ℚ`) lying over `v`. It does lie over `v`
(`New.FinPlace.isPlaceOver_placeOver`). -/
def placeOver [Algebra K New.Ω] : ClosurePlace := Classical.epsilon fun A ↦ IsPlaceOver A v

omit [NumberField K] in
/-- `New.placeOver v` lies over `v`, provided some valuation subring of `New.Ω` does. -/
lemma isPlaceOver_placeOver_of_exists [Algebra K New.Ω]
    (h_exists : ∃ B : ClosurePlace, IsPlaceOver B v) :
    IsPlaceOver (placeOver v) v :=
  Classical.epsilon_spec h_exists

end New

end LocalDefs

/-!
## Discrete modules: restriction, short exact sequences, functions on a finite quotient

* `New.DiscreteModule.restrictAlong`, `New.DiscreteModule.restrictTo`: restriction along a
  continuous homomorphism, and to a subgroup.
* `New.DiscreteModule.submodule`, `New.DiscreteModule.quotient`: a stable submodule, and the
  quotient by it.
* `New.DiscreteModule.funModule`: the functions from the finite quotient `Γ ⧸ U` to `A`, with `g`
  sending `f` to `x ↦ g (f (g⁻¹ • x))`. The maps `New.DiscreteModule.const` go into it and
  `New.DiscreteModule.sum` out of it.
-/

section DiscreteModule

variable (R Γ : Type)
  {G : Type*} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group G] [TopologicalSpace G]

/-- A discrete Γ-module over R: an R-module with the discrete topology and a continuous R-linear
action of the topological group Γ. -/
structure New.DiscreteModule where of ::
  /-- The underlying type. -/
  {V : Type}
  /-- `V` is an abelian group. -/
  [addCommGroup : AddCommGroup V]
  /-- `V` is an `R`-module. -/
  [moduleR : Module R V]
  /-- The topology on `V`. -/
  [topologicalSpace : TopologicalSpace V]
  /-- The topology on `V` is discrete. -/
  [discrete : DiscreteTopology V]
  /-- The `R`-linear action of `Γ` on `V`. -/
  ρ : Representation R Γ V
  /-- The action map `Γ × V → V` is continuous. -/
  continuous : Continuous (ρ · ·).uncurry := by
    simp [continuous_prod_of_discrete_right, LinearMap.pi, LinearMap.restrict_apply]
    fun_prop

/-- The inclusion of a subgroup U in G, as a continuous homomorphism. -/
def New.subgroupIncl (U : Subgroup G) : U →ₜ* G := ContinuousMonoidHom.mk U.subtype

end DiscreteModule

namespace New.DiscreteModule

attribute [instance] addCommGroup moduleR topologicalSpace discrete

attribute [fun_prop] continuous

variable {R Γ : Type} {G : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group G]
  [TopologicalSpace G] (M A : DiscreteModule R Γ)

/-- A discrete module is read as its underlying type `V`. -/
instance : CoeSort (DiscreteModule R Γ) Type := ⟨V⟩

/-! ### Morphisms, cohomology and restriction -/

/-- For discrete Γ-modules M and A over R, the R-linear maps M → A commuting with the action of
Γ. -/
abbrev Hom : Type := M.ρ.IntertwiningMap A.ρ

variable {M} {N P : DiscreteModule R Γ} (ι : M.Hom N) (π : N.Hom P) (φ : G →ₜ* Γ)

/-- The linear map from a discrete Γ-module A to its continuous 1-cocycles sending m to
g ↦ gm − m. -/
abbrev coboundary : A.V →ₗ[R] Z1 A.ρ :=
  (coboundaryMap A.ρ).codRestrict (Z1 A.ρ) (by
    simp [Z1, LinearMap.pi]
    fun_prop)

/-- The R-submodule of elements of a discrete Γ-module A fixed by all of Γ. -/
abbrev H0 : Submodule R A.V := A.ρ.invariants

/-- The continuous cohomology H²(Γ,A) of a discrete Γ-module A. -/
abbrev H2 : Type := New.H2 A.ρ

/-- For a continuous homomorphism φ: G → Γ, the discrete Γ-module A viewed as a discrete
G-module through φ. -/
abbrev restrictAlong : DiscreteModule R G := of (A.ρ.comp φ.toMonoidHom)

/-- For a subgroup U of Γ, the discrete Γ-module A viewed as a discrete U-module. -/
abbrev restrictTo (U : Subgroup Γ) : DiscreteModule R U := A.restrictAlong (subgroupIncl U)

/-- For a subgroup U of Γ, the restriction map H²(Γ,A) → H²(U,A). -/
abbrev resH2 (U : Subgroup Γ) : A.H2 →ₗ[R] (A.restrictTo U).H2 :=
  pairMapH2 (subgroupIncl U) LinearMap.id

/-- The linear map H²(Γ,M) → H²(Γ,N) induced by composing cocycles with a Γ-equivariant linear
map M → N. -/
abbrev Hom.mapH2 : New.H2 M.ρ →ₗ[R] New.H2 N.ρ :=
  pairMapH2 (ContinuousMonoidHom.id Γ) ι.toLinearMap ι.isIntertwining

/-! ### Short exact sequences -/

/-- The equivariant maps `ι : M → N` and `π : N → P` form a short exact sequence. That is, `ι` is
injective, `π` is surjective, and the kernel of `π` is the image of `ι`. -/
def IsShortExact : Prop := (⇑ι).Injective ∧ (⇑ι).Exact π ∧ (⇑π).Surjective

variable {ι π} (W : Submodule R A.V) (h : ∀ (g : Γ), W ≤ Submodule.comap (A.ρ g) W)

/-- A short exact sequence of discrete `Γ`-modules stays short exact after restriction along a
continuous homomorphism `φ : G → Γ`. -/
lemma IsShortExact.restrictAlong (h_exact : IsShortExact ι π) :
    (M.restrictAlong φ).IsShortExact (N := N.restrictAlong φ) (P := P.restrictAlong φ)
      ⟨ι.toLinearMap, fun g : G ↦ ι.isIntertwining' (φ g)⟩
      ⟨π.toLinearMap, fun g : G ↦ π.isIntertwining' (φ g)⟩ :=
  h_exact

/-- A Γ-stable R-submodule W of a discrete Γ-module A, as a discrete Γ-module with the
restricted action. -/
abbrev submodule : DiscreteModule R Γ := of (A.ρ.subrepresentation W h)

private lemma discreteTopology_quotient : DiscreteTopology (A.V ⧸ W) :=
  discreteTopology_iff_forall_isOpen.mpr fun s ↦
    (W.isOpenQuotientMap_mkQ.isQuotientMap.isOpen_preimage (s := s)).mp (isOpen_discrete _)

/-- For a Γ-stable R-submodule W of a discrete Γ-module A, the quotient A ⧸ W as a discrete
Γ-module, with the action induced on cosets. -/
abbrev quotient : DiscreteModule R Γ :=
  of (A.ρ.quotient W h)
    -- The action on cosets is continuous, as `Γ × A → Γ × (A ⧸ W)` is an open quotient map.
    ((IsOpenQuotientMap.id.prodMap W.isOpenQuotientMap_mkQ).continuous_comp_iff.mp
      (W.mkQL.cont.comp A.continuous))
    (discrete := discreteTopology_quotient A W)

/-- For a `Γ`-stable submodule `W` of `A`, the inclusion and the quotient map form a short exact
sequence `0 → W → A → A ⧸ W → 0` of discrete `Γ`-modules. -/
lemma isShortExact_submodule (W : Submodule R A.V)
    (hW_stable : ∀ g : Γ, W ≤ Submodule.comap (A.ρ g) W) :
    (A.submodule W hW_stable).IsShortExact (P := A.quotient W hW_stable)
      ⟨W.subtype, fun _ : Γ ↦ rfl⟩ ⟨W.mkQ, fun _ : Γ ↦ rfl⟩ :=
  ⟨W.injective_subtype, LinearMap.exact_subtype_mkQ W, W.mkQ_surjective⟩

end New.DiscreteModule

namespace New.DiscreteModule

/-! ### Functions on a finite quotient `Γ ⧸ U` -/

variable {R Γ : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] (A : DiscreteModule R Γ)
  [IsTopologicalGroup Γ] (U : Subgroup Γ) [Finite (Γ ⧸ U)] [DiscreteTopology (Γ ⧸ U)]

/-- The discrete Γ-module of functions f: Γ/U → A, for a subgroup U of finite index with Γ/U
discrete, with action (gf)(x) = g·f(g⁻¹x). -/
abbrev funModule : DiscreteModule R Γ :=
  of
    { toFun g := LinearMap.pi fun x : Γ ⧸ U ↦ A.ρ g ∘ₗ LinearMap.proj (g⁻¹ • x)
      map_one' := by aesop
      map_mul' := by aesop (add simp mul_smul) }

/-- The Γ-equivariant linear map from A to A-valued functions on Γ/U sending m to the constant
function with value m. -/
def const : A.Hom (A.funModule U) := ⟨LinearMap.const, fun _ : Γ ↦ rfl⟩

attribute [local instance low] Fintype.ofFinite in
/-- The Γ-equivariant linear map from A-valued functions on the finite set Γ/U to A sending f to the
sum of its values. -/
def sum : (A.funModule U).Hom A :=
  ⟨∑ x : Γ ⧸ U, LinearMap.proj x, by
    -- For each `g`, translation by `g⁻¹` permutes `Γ ⧸ U`, so the sum of the values of a function
    -- `f` moved by `g`, that is of `x ↦ g (f (g⁻¹ • x))`, is `g` applied to the sum of `f`.
    simp [DFunLike.ext_iff, ← map_sum, (MulAction.bijective _).sum_comp]⟩

end New.DiscreteModule

/-!
## Counting continuous 1-cocycles along exact sequences

* `New.DiscreteModule.Hom.mapZ1`: the map on continuous 1-cocycles given by an equivariant map.
* `New.DiscreteModule.card_eq_mul_of_exact`: for an exact sequence of groups `0 → A → B → C`, a
  subgroup `W` of `B` has as many elements as its preimage in `A` times its image in `C`.
* `New.DiscreteModule.Hom.card_eq_card_comap_mul_card_map`: the same count for a group `W` of
  continuous 1-cocycles of `N`, along `0 → Z¹(M) → Z¹(N) → Z¹(P)` for `0 → M → N → P` exact.

Cardinalities are `Nat.card`, which is `0` on infinite types.
-/

section CocycleCounts

open Function Set AddSubgroup

namespace New.DiscreteModule

variable {R Γ : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
  {M N P : DiscreteModule R Γ} (ι : M.Hom N) {π : N.Hom P}

/-- For a morphism ι: M → N of Γ-modules, the map on continuous 1-cocycles Z¹(M) → Z¹(N) given
by composing with ι. -/
abbrev Hom.mapZ1 : New.Z1 M.ρ →+ New.Z1 N.ρ :=
  pairMapZ1 (ContinuousMonoidHom.id Γ) ι.toLinearMap ι.isIntertwining

/-- Let `f : A → B` be injective and `g : B → C` have kernel the image of `f`. Then for every
additive subgroup `W` of `B`, the cardinality of `W` is that of its preimage under `f` times that of
its image under `g`. -/
lemma card_eq_mul_of_exact {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C] (f : A →+ B)
    (g : B →+ C) (hf : Injective f) (h_exact : Exact f g) (W : AddSubgroup B) :
    Nat.card W = Nat.card (comap f W) * Nat.card (map g W) := by
  -- The kernel of `g` on `W` is `W` met with the range of `f`, a copy of `comap f W`; its
  -- index in `W` is the order of the image.
  have h_ker : Nat.card (comap f W) = Nat.card (g.ker.addSubgroupOf W) := by
    rw [← card_map_of_injective hf, map_comap_eq, h_exact.addMonoidHom_ker_eq,
      ← addSubgroupOf_map_subtype, card_subtype]
  rw [h_ker, ← relIndex_ker, relIndex, card_mul_index]

/-- In a short exact sequence `0 → M → N → P → 0` of discrete `Γ`-modules, given by `ι : M → N` and
`π : N → P`, the number of elements of `N` is that of `M` times that of `P`. -/
lemma IsShortExact.card_eq_card_mul_card {ι : M.Hom N} (h : M.IsShortExact ι π) :
    Nat.card N = Nat.card M * Nat.card P := by
  obtain ⟨h_inj, h_exact, h_surj⟩ : Injective ι ∧ Exact ι π ∧ Surjective π := h
  -- Count along `W = ⊤`: its preimage is all of `M` and, as `π` is onto, its image all of `P`.
  have h_card : Nat.card (⊤ : AddSubgroup N) =
      Nat.card (comap (ι : M →+ N) ⊤) * Nat.card (map (π : N →+ P) ⊤) :=
    card_eq_mul_of_exact (ι : M →+ N) (π : N →+ P) h_inj h_exact ⊤
  rwa [comap_top, map_top_of_surjective (π : N →+ P) h_surj, card_top, card_top, card_top] at h_card

/-- For an injective equivariant map `ι : M → N`, a function `f : Γ → M` is a continuous 1-cocycle
as soon as `ι ∘ f` is one. -/
private lemma mem_Z1_of_injective_of_comp_mem_Z1 (hι : Injective ι) (f : Γ → M)
    (hf : ⇑ι ∘ f ∈ New.Z1 N.ρ) : f ∈ New.Z1 M.ρ := by
  obtain ⟨hf_cont, hf_cocycle⟩ : Continuous (⇑ι ∘ f) ∧
      ∀ g g' : Γ, ι (f (g * g')) = ι (f g) + N.ρ g (ι (f g')) := hf
  refine ⟨?_, fun g g' ↦ hι ?_⟩
  · -- `M` is discrete, and each fibre of `f` is a fibre of `ι ∘ f` since `ι` is injective.
    refine continuous_discrete_rng.mpr fun m ↦ ?_
    have h_fibre : f ⁻¹' {m} = (⇑ι ∘ f) ⁻¹' {ι m} := by
      ext x
      simp [hι.eq_iff]
    rw [h_fibre]
    exact (isOpen_discrete {ι m}).preimage hf_cont
  · simpa [ι.isIntertwining] using hf_cocycle g g'

/-- Let `ι : M → N` be injective and `π : N → P` have kernel the image of `ι`. Then for every
additive subgroup `W` of the continuous 1-cocycles of `N`, the cardinality of `W` is that of its
preimage in the cocycles of `M` times that of its image in the cocycles of `P`. -/
lemma Hom.card_eq_card_comap_mul_card_map (hι : Injective ι) (h_exact : Exact ι π)
    (W : AddSubgroup (New.Z1 N.ρ)) :
    Nat.card W = Nat.card (comap ι.mapZ1 W) * Nat.card (map π.mapZ1 W) := by
  -- Injectivity and exactness pass from `M → N → P` to the cocycles.
  have h_inj_Z1 : Injective ⇑ι.mapZ1 := fun a b h_eq ↦
    Subtype.ext (funext fun x ↦ hι (congrFun (congrArg Subtype.val h_eq) x))
  have h_exact_Z1 : Exact ⇑ι.mapZ1 ⇑π.mapZ1 := by
    refine fun c ↦ ⟨fun h_zero ↦ ?_, ?_⟩
    · -- If `π ∘ c = 0`, every value of `c` comes from `M`, and the chosen preimages form a cocycle.
      have h_pt (x : Γ) : ∃ m : M, ι m = (c : Γ → N) x :=
        (h_exact _).mp (congrFun (congrArg Subtype.val h_zero) x)
      choose f hf using h_pt
      have h_comp : ⇑ι ∘ f = (c : Γ → N) := funext hf
      have hf_mem : f ∈ New.Z1 M.ρ :=
        mem_Z1_of_injective_of_comp_mem_Z1 ι hι f (by simp [h_comp])
      exact ⟨⟨f, hf_mem⟩, Subtype.ext h_comp⟩
    · -- A cocycle `ι ∘ a` goes to `π ∘ ι ∘ a = 0`.
      rintro ⟨a, rfl⟩
      ext x
      exact h_exact.apply_apply_eq_zero ((a : Γ → M) x)
  exact card_eq_mul_of_exact ι.mapZ1 π.mapZ1 h_inj_Z1 h_exact_Z1 W

end New.DiscreteModule

end CocycleCounts

end
