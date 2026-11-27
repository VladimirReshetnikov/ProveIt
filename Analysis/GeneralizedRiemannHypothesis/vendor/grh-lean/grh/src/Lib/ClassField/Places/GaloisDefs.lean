import Lib.Base

/-!
# Vocabulary of Galois theory: places, decomposition, Frobenius elements and inertia

This file sets up the vocabulary of Galois theory used by the cohomology files. A Galois group is an
abstract group `Γ` acting on a field `Ω`, and a place of `Ω` is a valuation subring `A`.
`New.IsFrob A q σ` says that `σ` stabilises `A` and that `σ • x - x ^ q` lies in the maximal ideal
for every `x` in `A`. Inertia is the case `q = 1`.

* `New.IsProGalois`, `New.IsLocalGalois`: `Γ` is the profinite Galois group of `Ω / K`; in the local
  case `Ω` is moreover algebraically closed of characteristic `0`, `Γ` stabilises `A`, and `A ∩ K`
  (`New.valRingBelow`) is a discrete valuation ring with finite residue field.
* `New.decompGroup`, `New.inertiaGroup`, `New.IsFrob`, `New.IsPlaceOver`: decomposition group,
  inertia group, Frobenius elements, and places over a nonzero prime of the ring of integers
  `𝓞 K` of a field `K`.
* `New.IsComplexConj`, `New.cyclotomicChar`, `New.cyclotomicCharIn`: complex conjugations and the
  `l`-adic cyclotomic character.

Notions from Mathlib used in the statements:
* `A : ValuationSubring Ω`: a subring that contains `x` or `x⁻¹` for every nonzero `x`, with its
  valuation `A.valuation`; `A.valuation x ≤ 1` means `x ∈ A`, and `< 1` means `x` lies in the
  maximal ideal.
* `IsGaloisGroup Γ K Ω`: `Γ` acts faithfully on `Ω`, fixing `K`, and the elements of `Ω` fixed by
  `Γ` are those of `K`.

## Relation to the literature

Known; see `Lib.ClassField.Places.LocalFields` for sources.
-/

noncomputable section

open NumberField Pointwise MulAction Units MulSemiringAction ValuationSubring SetLike

namespace New

/-- The field `Ω` is an algebraic closure of `ℚ`: it has characteristic zero, is algebraically
closed and is algebraic over `ℚ`. -/
def Ω : Type := AlgebraicClosure ℚ
  deriving Field, IsAlgClosed, CharZero

instance : Algebra.IsAlgebraic ℚ Ω := AlgebraicClosure.isAlgebraic ℚ

/-- The type of valuation subrings of `New.Ω`, the algebraic closure of `ℚ`. -/
abbrev ClosurePlace : Type := ValuationSubring Ω

/-- The element c of Γ is a complex conjugation: for some embedding j : Ω → ℂ, j(cx) is the
complex conjugate of j(x) for all x. -/
def IsComplexConj {Γ : Type*} [SMul Γ Ω] (c : Γ) : Prop :=
  ∃ j : Ω →+* ℂ, ∀ x : Ω, j (c • x) = star (j x)

variable (O Γ : Type*)
  (K Ω : outParam Type*) [Group Γ] [Field K] [Field Ω] [Algebra K Ω] [MulSemiringAction Γ Ω]
  (l : ℕ) [Fact l.Prime] [CommRing O] [Algebra ℤ_[l] O]

/-- The multiplicative group Ω^×, written additively; it is given the discrete topology. -/
abbrev DiscreteUnits : Type _ := Additive Ωˣ

instance : TopologicalSpace (DiscreteUnits Ω) := ⊥

instance : DiscreteTopology (DiscreteUnits Ω) := ⟨rfl⟩

/-! ### Profinite and local Galois groups -/

/-- The profinite group Γ acts on the Galois extension Ω/K as its Galois group, with open
stabilisers. -/
class IsProGalois [TopologicalSpace Γ] extends IsGaloisGroup Γ K Ω, IsGalois K Ω,
  IsTopologicalGroup Γ, CompactSpace Γ, TotallyDisconnectedSpace Γ where
  /-- The stabiliser of every element of `Ω` is open in `Γ`. -/
  isOpen_stabilizer (x : Ω) : IsOpen (stabilizer Γ x : Set Γ)

/-- A place `A` of `Ω` is read as its valuation: `A x`. -/
scoped instance : CoeFun (ValuationSubring Ω) (Ω → ·.ValueGroup) := ⟨(·.valuation)⟩

variable {Ω} (A : ValuationSubring Ω)

/-- The decomposition group of a valuation subring A of Ω: the elements of Γ mapping A onto
itself. -/
abbrev decompGroup : Subgroup Γ := stabilizer Γ A

/-- For a valuation subring A of Ω and x in K, the value of the image of x in Ω under the
multiplicative valuation attached to A. -/
abbrev valuationVia (x : K) : A.ValueGroup := A (algebraMap K Ω x)

/-- The valuation subring A ∩ K of K. -/
abbrev valRingBelow : ValuationSubring K := (A.valuation.comap (algebraMap K Ω)).valuationSubring

/-- Γ = Gal(Ω/K) with Ω algebraically closed of characteristic 0 stabilises A, and A ∩ K is a
discrete valuation ring with finite residue field. The field K need not be complete. -/
class IsLocalGalois (A : outParam (ValuationSubring Ω))
    [TopologicalSpace Γ] extends IsProGalois Γ K Ω, IsAlgClosed Ω, CharZero Ω where
  /-- Every element of `Γ` maps the valuation ring `A` to itself. -/
  mem_decompGroup (g : Γ) : g ∈ decompGroup Γ A
  /-- The valuation ring of `K` under `A` is a discrete valuation ring. -/
  isDiscreteValuationRing : IsDiscreteValuationRing (valRingBelow K A)
  /-- The residue field of the valuation ring of `K` under `A` is finite. -/
  finite_residue : Finite (IsLocalRing.ResidueField (valRingBelow K A))

variable {Γ K} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The ℤ-linear representation of Γ on Ω^× (written additively) coming from the action of Γ on
the field Ω by ring automorphisms. -/
def unitsRep : Representation ℤ Γ (DiscreteUnits Ω) :=
  letI : MulDistribMulAction Γ Ωˣ := mulDistribMulActionRight
  Representation.ofMulDistribMulAction Γ Ωˣ

/-! ### Frobenius elements, places and inertia -/

/-- `σ` stabilises the valuation subring `A` and `σ • x ≡ x ^ q` modulo the maximal ideal for all
`x ∈ A`. For `q` the order of the residue field of the base this is an arithmetic Frobenius;
for `q = 1` it is membership in the inertia group `New.inertiaGroup`. -/
def IsFrob (q : ℕ) (σ : Γ) : Prop :=
  σ ∈ decompGroup Γ A ∧ ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ • x - x ^ q) < 1

/-- The valuation subring `A` of `Ω` lies over the nonzero prime `v` of the ring of integers `𝓞 K`:
an element of `𝓞 K` is in the maximal ideal of `A` exactly when it lies in `v`. -/
def IsPlaceOver : Prop := ∀ x : 𝓞 K, A.valuation (algebraMap K Ω x) < 1 ↔ x ∈ v.asIdeal

end New

namespace New

variable (O : Type*) {Γ : Type*} {K Ω : outParam Type*} [Group Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] (l : ℕ) [Fact l.Prime] [CommRing O] [Algebra ℤ_[l] O]
  {A : ValuationSubring Ω} {q : ℕ} {σ τ g : Γ}
  {Γ' Ω' : Type*} [Group Γ'] [Field Ω'] [MulSemiringAction Γ' Ω']
  {φ : Γ' → Γ} {j : Ω →+* Ω'} {A' : ValuationSubring Ω'} {q' : ℕ}

lemma IsFrob.mem_decompGroup (h : IsFrob A q σ) : σ ∈ decompGroup Γ A := h.left

/-- A Frobenius element for `q` sends each `x` of `A` to `x ^ q` modulo the maximal ideal of `A`. -/
lemma IsFrob.valuation_sub_pow_lt_one (h : IsFrob A q σ) {x : Ω} (hx : A.valuation x ≤ 1) :
    A.valuation (σ • x - x ^ q) < 1 :=
  h.right x hx

lemma mem_decompGroup_iff : σ ∈ decompGroup Γ A ↔ ∀ x : Ω, σ • x ∈ A ↔ x ∈ A :=
  ext'_iff.trans mem_stabilizer_set

lemma smul_eq_comap : g • A = A.comap (toRingHom Γ Ω g⁻¹) :=
  ext' (Set.preimage_smul_inv g _).symm

lemma conj_mem_decompGroup_smul (hσ : σ ∈ decompGroup Γ A) :
    g * σ * g⁻¹ ∈ decompGroup Γ (g • A) := by
  simp [mem_stabilizer_iff, mul_smul, mem_stabilizer_iff.mp hσ]

lemma isEquiv_comap : (comap A' j).valuation.IsEquiv (A'.valuation.comap j) :=
  Valuation.isEquiv_of_val_le_one fun {x} ↦ by
    rw [valuation_le_one_iff, mem_comap, Valuation.comap_apply, valuation_le_one_iff]

lemma comap_apply_lt_one_iff {x : Ω} : (comap A' j) x < 1 ↔ A' (j x) < 1 :=
  isEquiv_comap.lt_one_iff_lt_one

lemma smul_apply_smul_lt_one_iff (g : Γ) {x : Ω} : (g • A) (g • x) < 1 ↔ A x < 1 := by
  rw [smul_eq_comap, comap_apply_lt_one_iff]
  simp

/-- Let `j : Ω → Ω'` be a ring map and `φ : Γ' → Γ` a map with `j (φ g • x) = g • j x`
(`h_equivariant`). If `s` stabilises `A'`, then `φ s` stabilises the pulled-back subring
`A'.comap j`. -/
lemma decompGroup.map (h_equivariant : ∀ (g : Γ') (x : Ω), j (φ g • x) = g • j x)
    {A' : ValuationSubring Ω'} {s : Γ'} (hs : s ∈ decompGroup Γ' A') :
    φ s ∈ decompGroup Γ (A'.comap j) := by
  rw [mem_decompGroup_iff] at hs ⊢
  intro x
  rw [mem_comap, mem_comap, h_equivariant s x, hs]

/-- Let `j : Ω → Ω'` be a ring map and `φ : Γ' → Γ` a map with `j (φ g • x) = g • j x`
(`h_equivariant`). If `s` is a Frobenius element for `q` at `A'`, then `φ s` is one at the
pulled-back subring `A'.comap j`. -/
lemma IsFrob.map (h_equivariant : ∀ (g : Γ') (x : Ω), j (φ g • x) = g • j x)
    {A' : ValuationSubring Ω'} {s : Γ'} (hs_frob : IsFrob A' q s) :
    IsFrob (A'.comap j) q (φ s) := by
  refine ⟨decompGroup.map h_equivariant hs_frob.mem_decompGroup, fun x hx ↦ ?_⟩
  have hjx : A'.valuation (j x) ≤ 1 := by
    rwa [valuation_le_one_iff, mem_comap, ← valuation_le_one_iff] at hx
  have h_image : j (φ s • x - x ^ q) = s • j x - j x ^ q := by
    rw [map_sub, map_pow, h_equivariant s x]
  rw [comap_apply_lt_one_iff, h_image]
  exact hs_frob.valuation_sub_pow_lt_one hjx

/-! ### The calculus of Frobenius elements -/

/-- If `σ` is a Frobenius element for `q` at `A`, then `g * σ * g⁻¹` is one at `g • A`. -/
lemma IsFrob.conj (h : IsFrob A q σ) (g : Γ) : IsFrob (g • A) q (g * σ * g⁻¹) := by
  refine ⟨conj_mem_decompGroup_smul h.mem_decompGroup, fun x hx ↦ ?_⟩
  -- Put `y = g⁻¹ • x`: it lies in `A`, and `(g σ g⁻¹) • x - x ^ q = g • (σ • y - y ^ q)`.
  have hy : A.valuation (g⁻¹ • x) ≤ 1 := by
    rwa [valuation_le_one_iff, mem_pointwise_smul_iff_inv_smul_mem, ← valuation_le_one_iff] at hx
  have h_eq : (g * σ * g⁻¹) • x - x ^ q = g • (σ • (g⁻¹ • x) - (g⁻¹ • x) ^ q) := by
    simp [smul_sub, smul_pow', mul_smul]
  rw [h_eq]
  exact (smul_apply_smul_lt_one_iff g).mpr (h.valuation_sub_pow_lt_one hy)

/-- Let `σ` be a Frobenius element for `q` at `A`. Then `σ τ` is a Frobenius element for `q * q'`
if and only if `τ` is one for `q'`. -/
lemma IsFrob.mul_iff (h : IsFrob A q σ) : IsFrob A (q * q') (σ * τ) ↔ IsFrob A q' τ := by
  refine (mul_mem_cancel_left h.mem_decompGroup).and (forall₂_congr fun x hx ↦ ?_)
  -- `σ τ x - x ^ (q * q') = σ (τ x - x ^ q') + (σ y - y ^ q)` with `y = x ^ q'`; the last term is
  -- small as `σ` is a Frobenius, and `σ` preserves smallness as it stabilises `A`
  have h_small : σ • x ^ q' - (x ^ q') ^ q ∈ A.nonunits :=
    h.valuation_sub_pow_lt_one (by simpa using pow_le_one' hx q')
  have h_split :
      (σ * τ) • x - x ^ (q * q') = σ • (τ • x - x ^ q') + (σ • x ^ q' - (x ^ q') ^ q) := by
    rw [mul_smul, smul_sub, pow_mul']
    abel
  have hσ_stab : σ • A = A := h.mem_decompGroup
  calc
    _ ↔ A.valuation (σ • (τ • x - x ^ q')) < 1 := by
      rw [h_split, ← ValuationSubring.mem_nonunits_iff, add_mem_cancel_right h_small,
        ValuationSubring.mem_nonunits_iff]
    _ ↔ (σ • A).valuation (σ • (τ • x - x ^ q')) < 1 := by rw [hσ_stab]
    _ ↔ A.valuation (τ • x - x ^ q') < 1 := smul_apply_smul_lt_one_iff σ

lemma isFrob_one_one : IsFrob A 1 (1 : Γ) :=
  ⟨one_mem _, fun x _ ↦ by simp⟩

lemma IsFrob.pow (h : IsFrob A q σ) (n : ℕ) : IsFrob A (q ^ n) (σ ^ n) := by
  induction n with
  | zero => simpa using isFrob_one_one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul_iff.mpr h

variable (Γ A) in
/-- The inertia group of A: the σ in Γ stabilising the valuation subring A with σx − x in the
maximal ideal for every x in A. -/
def inertiaGroup : Subgroup Γ where
  carrier := {σ : Γ | IsFrob A 1 σ}
  mul_mem' hσ hτ := hσ.mul_iff.2 hτ
  one_mem' := by simp [↓ IsFrob]
  inv_mem' hσ := hσ.mul_iff.1 (by simp [↓ IsFrob])

lemma mem_inertiaGroup_iff : σ ∈ inertiaGroup Γ A ↔ IsFrob A 1 σ := Iff.rfl

/-- Two Frobenius elements `σ`, `τ` for the same `q` at `A` differ by inertia: `σ⁻¹ τ` lies in the
inertia group. -/
lemma IsFrob.inv_mul_mem_inertiaGroup (h : IsFrob A q σ) (hτ : IsFrob A q τ) :
    σ⁻¹ * τ ∈ inertiaGroup Γ A := by
  rw [mem_inertiaGroup_iff, ← h.mul_iff, mul_one, _root_.mul_inv_cancel_left]
  exact hτ

variable (Ω)

/-- The `l`-adic cyclotomic character Γ → ℤ_l^× of a group Γ acting on the field Ω by ring
automorphisms. -/
def cyclotomicChar : Γ →* ℤ_[l]ˣ := (cyclotomicCharacter Ω l).comp (toRingAut Γ Ω)

/-- The `l`-adic cyclotomic character of Γ composed with ℤ_l^× → O^×, for a commutative
ℤ_l-algebra O. -/
abbrev cyclotomicCharIn : Γ →* Oˣ := (map (algebraMap ℤ_[l] O).toMonoidHom).comp
  (cyclotomicChar (Γ := Γ) Ω l)

end New

end
