import Lib.ClassField.Places.ProfiniteGalois
import Lib.General.Topology

/-!
# Decomposition and inertia groups, and cyclotomic characters at Frobenii and inertia

This file studies decomposition and inertia groups of valuation subrings in a Galois group, and the
values of cyclotomic characters at Frobenius elements and on inertia groups. For a valuation subring
`A` of `Ω`, `New.decompGroup Γ A` is the stabiliser of `A`. `New.inertiaGroup Γ A` consists of the
elements of `New.decompGroup Γ A` that act trivially modulo the maximal ideal.
`New.cyclotomicCharMod Ω N : Γ →* (ZMod N)ˣ` and `New.cyclotomicChar Ω l : Γ →* ℤ_[l]ˣ` give the
action on the `N`-th roots of unity and on the roots of unity of `l`-power order, and
`New.IsFrob A q σ` says that `σ` preserves `A` and acts as `x ^ q` modulo its maximal ideal.

## Main definitions and results

* `New.cyclotomicCharMod_eq_iff`: the value at `g` is `a` iff `g • ζ = ζ ^ a` whenever `ζ ^ N = 1`.
* `New.IsFrob.cyclotomicCharMod_eq`, `New.IsFrob.cyclotomicChar_eq`: the value at a Frobenius for
  `q` is `q`, away from `N` or `l`; the case `q = 1` is inertia. The reason is
  `New.eq_of_val_sub_lt_one`: distinct `N`-th roots of unity stay distinct modulo the maximal ideal.
* `New.cyclotomicCharMod_surjective`: for the Galois group of `New.Ω` over `ℚ`, the character modulo
  `N` is onto.

Notions from other files:
* `New.IsProGalois`: a profinite group acts on the Galois extension Ω/K as its Galois group, with
  open stabilisers.

## Relation to the literature

Known; see `Lib.ClassField.Places.LocalFields` for sources.
-/

noncomputable section

/-!
## Decomposition and inertia groups in a Galois group

Here `Γ` is the Galois group of `Ω / K` (`New.IsProGalois`) and `A` is a valuation subring of `Ω`.
-/

section DecompositionInertia

open MulSemiringAction Set

namespace New

variable {Γ Ω : Type*} [Group Γ] [Field Ω] [MulSemiringAction Γ Ω]
  {A : ValuationSubring Ω} {σ : Γ}
  {K : Type*} [Field K] [Algebra K Ω] [TopologicalSpace Γ] [IsProGalois Γ K Ω]

include K

/-- For the Galois group `Γ` of `Ω / K`, the decomposition group of `A` is closed. -/
instance isClosed_decompGroup : IsClosed (decompGroup Γ A : Set Γ) := by
  have h_eq : (decompGroup Γ A : Set Γ) = ⋂ x : Ω, {σ : Γ | σ • x ∈ A ↔ x ∈ A} := by
    ext σ
    simpa using mem_decompGroup_iff
  rw [h_eq]
  exact isClosed_iInter fun x ↦ isClosed_setOf_smul x fun y ↦ y ∈ A ↔ x ∈ A

/-- For `Γ` the Galois group of `Ω / K`, an element `σ` of the decomposition group of `A` preserves
the valuation of `A`: `σ • x` and `x` have the same valuation for every `x` in `Ω`. -/
lemma decompGroup.val_smul (hσ : σ ∈ decompGroup Γ A) (x : Ω) :
    A.valuation (σ • x) = A.valuation x := by
  -- Write `v = A.valuation`. It is enough to show `v y ≤ v (s • y)` for all `s` in
  -- `decompGroup Γ A`: use it for `σ` and for `σ⁻¹`.
  have le_smul {s : Γ} {y : Ω} (hs : s ∈ decompGroup Γ A) :
      A.valuation y ≤ A.valuation (s • y) := by
    -- The orbit of `y` is finite, so some `t` in `decompGroup Γ A` minimises `v (t • y)`.
    have h_fin : ((fun t : Γ ↦ A.valuation (t • y)) '' decompGroup Γ A).Finite :=
      ((isLocallyConstant_smul y).comp A.valuation).range_finite.subset (image_subset_range _ _)
    obtain ⟨t, ht⟩ := h_fin.exists_minimalFor' _ _ ⟨s, hs⟩
    have h_min : A.valuation (t • y) ≤ A.valuation (t • s • y) := by
      simpa [mul_smul] using ht.le (mul_mem ht.prop hs)
    -- Since `t` preserves `A`, the valuation `z ↦ v (t • z)` is equivalent to `v`.
    have h_equiv : (A.valuation.comap (toRingHom Γ Ω t)).IsEquiv A.valuation :=
      Valuation.isEquiv_of_val_le_one fun {z} ↦ by
        simpa [ValuationSubring.valuation_le_one_iff] using mem_decompGroup_iff.mp ht.prop z
    exact (h_equiv y (s • y)).mp h_min
  exact le_antisymm (by simpa using le_smul (y := σ • x) (inv_mem hσ)) (le_smul hσ)

/-- For the Galois group `Γ` of `Ω / K`, the inertia group of `A` is closed. -/
instance isClosed_inertiaGroup : IsClosed (inertiaGroup Γ A : Set Γ) := by
  -- inertia is cut out of `decompGroup Γ A` by one condition on `σ • x` for each `x`
  have h_closed : IsClosed {σ : Γ | ∀ x : Ω, A x ≤ 1 → A (σ • x - x ^ 1) < 1} := by
    rw [ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_setOf_smul x fun y ↦ A x ≤ 1 → A (y - x ^ 1) < 1
  exact isClosed_decompGroup.inter h_closed

end New

end DecompositionInertia

/-!
## Cyclotomic characters modulo N and ℓ-adic at Frobenii and inertia

Here a group `Γ` acts on a field `Ω` by ring automorphisms. `A N = 1` says that `N` is a unit of
`A`.
-/

namespace New

open Function NeZero ZMod HasEnoughRootsOfUnity PadicInt Units rootsOfUnity

variable {Γ Ω : Type*} [Group Γ] [Field Ω] [MulSemiringAction Γ Ω]
  {N q : ℕ} {σ g : Γ} {A : ValuationSubring Ω} (h_frob : IsFrob A q σ) (hN : A N = 1) {ζ : Ω}

section

/-! ### Roots of unity modulo a valuation -/

/-- Let `A` be a valuation subring of a field `Ω` and `x`, `y` in `Ω` with `x ^ N = y ^ N = 1`. If
the multiplicative `A`-valuation of `x - y` is strictly smaller than that of `N`, then `x = y`. -/
lemma eq_of_pow_eq_one_of_val_sub_lt {x y : Ω} (hx : x ^ N = 1) (hy : y ^ N = 1)
    (h_val_lt : A.valuation (x - y) < A.valuation N) : x = y := by
  -- Write `x = y + a N` with `a, y` in `A`. The binomial expansion of `x ^ (N + 1)` to second order
  -- gives `-(x - y) N = (x - y) ^ 2 b` with `b` in `A`, so `x - y` divides `N` if `x ≠ y`.
  have hN_ne : N ≠ 0 := by
    rintro rfl
    simp at h_val_lt
  have hy_mem : y ∈ A := by
    rw [← A.valuation_le_one_iff, ← pow_le_one_iff hN_ne, ← map_pow, hy, map_one]
  lift y to A using hy_mem
  obtain ⟨a, ha⟩ := (A.valuation_le_iff _ _).mp h_val_lt.le
  obtain ⟨b, hb⟩ :
      (a * N) ^ 2 ∣ (y + a * N) ^ (N + 1) - y ^ N * (a * N) * (N + 1 : ℕ) - y ^ (N + 1) :=
    sq_dvd_add_pow_sub_sub (a * N) y (N + 1)
  have h_expand : x ^ (N + 1) - (x - y) * (N + 1) - y ^ (N + 1) = (x - y) ^ 2 * b := by
    simp_all [Subtype.ext_iff]
  contrapose! h_val_lt
  -- so `N` is `-b` times `x - y`, with `-b` in `A`
  have h_dvd : -(b * (x - y)) = N := by grind
  exact (A.valuation_le_iff _ _).mpr ⟨-b, by simpa using h_dvd⟩

/-- If `N` is a unit of `A` (`hN`), two `N`-th roots of unity that are congruent modulo the maximal
ideal are equal. -/
lemma eq_of_val_sub_lt_one (hN : A N = 1) {x y : Ω} (hx : x ^ N = 1) (hy : y ^ N = 1)
    (h_lt : A (x - y) < 1) : x = y :=
  eq_of_pow_eq_one_of_val_sub_lt hx hy (h_lt.trans_eq hN.symm)

end

variable [IsAlgClosed Ω] [CharZero Ω] [NeZero N] {a M : ℕ} [NeZero M]

/-! ### The character modulo `N` -/

/-- `g` acts on an `N`-th root of unity `ζ` as the power of `ζ` given by the character modulo
`N`. -/
lemma smul_eq_pow_cyclotomicCharMod (g : Γ) (hζ : ζ ^ N = 1) :
    g • ζ = ζ ^ (cyclotomicCharMod Ω N g : ZMod N).val :=
  modularCyclotomicCharacter.spec Ω _ (MulSemiringAction.toRingAut Γ Ω g) (mkOfPowEq ζ hζ).property

/-- If `g • ζ = ζ ^ a` for a primitive `N`-th root of unity `ζ`, then the character modulo `N`
takes the value `a` at `g`. -/
lemma cyclotomicCharMod_eq_of_isPrimitiveRoot (hζ : IsPrimitiveRoot ζ N) (hg : g • ζ = ζ ^ a) :
    (cyclotomicCharMod Ω N g).val = a := by
  -- both values are exponents below `N` that give `g • ζ`, and `ζ` is primitive
  apply val_injective N
  have h_pow : ζ ^ (cyclotomicCharMod Ω N g : ZMod N).val = ζ ^ (a : ZMod N).val := by
    rw [← smul_eq_pow_cyclotomicCharMod g hζ.pow_eq_one, hg, val_natCast,
      ← pow_eq_pow_mod a hζ.pow_eq_one]
  exact hζ.pow_inj (val_lt _) (val_lt _) h_pow

/-- Let `Ω` be algebraically closed of characteristic zero and `N ≠ 0`. The character modulo `N`
takes the value `a` at `g` if and only if `g • ζ = ζ ^ a` for every `N`-th root of unity `ζ`. -/
lemma cyclotomicCharMod_eq_iff :
    (cyclotomicCharMod Ω N g).val = a ↔ ∀ ζ : Ω, ζ ^ N = 1 → g • ζ = ζ ^ a := by
  refine ⟨fun h_val ζ hζ ↦ ?_, fun h_all ↦ ?_⟩
  · rw [smul_eq_pow_cyclotomicCharMod g hζ, h_val, val_natCast, ← pow_eq_pow_mod a hζ]
  · -- test on a primitive `N`-th root of unity
    obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ N := prim
    exact cyclotomicCharMod_eq_of_isPrimitiveRoot hζ (h_all ζ hζ.pow_eq_one)

/-- If `M ∣ N`, a value of the character modulo `N` is also its value modulo `M`. -/
lemma cyclotomicCharMod_eq_of_dvd (h_dvd : M ∣ N) (h_val : (cyclotomicCharMod Ω N g).val = a) :
    (cyclotomicCharMod Ω M g).val = a := by
  obtain ⟨c, rfl⟩ := h_dvd
  rw [cyclotomicCharMod_eq_iff] at h_val ⊢
  -- an `M`-th root of unity is also an `(M * c)`-th root of unity
  exact fun ζ hζ ↦ h_val ζ (by rw [pow_mul, hζ, one_pow])

/-- If `M ∣ N`, the kernel of the character modulo `N` lies in that of the character modulo `M`. -/
lemma cyclotomicCharMod_eq_one_of_dvd (h_dvd : M ∣ N) (h_one : cyclotomicCharMod Ω N g = 1) :
    cyclotomicCharMod Ω M g = 1 := by
  simpa using cyclotomicCharMod_eq_of_dvd (a := 1) h_dvd (by simp [h_one])

/-- `New.cyclotomicCharMod_eq_iff` for the units of `Ω` written additively (`DiscreteUnits Ω`, on
which `g` acts by `New.unitsRep`): the value at `g` is `a` if and only if `g` acts on the
`N`-torsion as multiplication by `a`. -/
lemma cyclotomicCharMod_eq_iff_unitsRep :
    (cyclotomicCharMod Ω N g).val = a ↔ ∀ ⦃u : DiscreteUnits Ω⦄,
      N • u = 0 → unitsRep g u = a • u := by
  -- The `N`-torsion of the unit group, written additively, is the group of `N`-th roots of unity.
  refine cyclotomicCharMod_eq_iff.trans
    ⟨fun h u hu ↦ ext (h u.toMul.val (val_inj.mpr hu)), fun h ζ hζ ↦ ?_⟩
  exact val_inj.mpr (h (rootsOfUnity.mkOfPowEq ζ hζ).property)

/-- `g` is in the kernel of the character modulo `N` if and only if it fixes the `N`-torsion of
the units of `Ω`. -/
lemma cyclotomicCharMod_eq_one_iff :
    cyclotomicCharMod Ω N g = 1 ↔ ∀ y : DiscreteUnits Ω, N • y = 0 → unitsRep g y = y := by
  simpa using cyclotomicCharMod_eq_iff_unitsRep (a := 1)

section

include h_frob hN

/-- Let `σ` be a Frobenius for `q` at `A` (`h_frob : IsFrob A q σ`) and let `N` be a unit of `A`
(`hN : A N = 1`). Then the character modulo `N` takes the value `q` at `σ`. -/
lemma IsFrob.cyclotomicCharMod_eq : (cyclotomicCharMod Ω N σ).val = q := by
  -- `σ • ζ` and `ζ ^ q` are `N`-th roots of unity that are congruent modulo the maximal ideal.
  obtain ⟨-, h_cong⟩ := h_frob
  refine cyclotomicCharMod_eq_iff.mpr fun ζ hζ ↦ eq_of_val_sub_lt_one hN ?_ ?_ (h_cong ζ ?_)
  · simp [← smul_pow', hζ]
  · simp [pow_right_comm, hζ]
  · simp [← pow_le_one_iff (ne N), ← map_pow, hζ]

/-- Let `Ω` be algebraically closed of characteristic zero, `N ≠ 0` a unit of `A` (`hN`), and `σ`
stabilise `A` with `σ x ≡ x ^ q` on `A` (`h_frob`). Then `σ` fixes the `N`-th roots of unity if
and only if `q ≡ 1 [MOD N]`. -/
lemma IsFrob.mem_ker_cyclotomicCharMod_iff :
    σ ∈ (New.cyclotomicCharMod Ω N).ker ↔ q ≡ 1 [MOD N] := by
  simp [← h_frob.cyclotomicCharMod_eq hN, ← natCast_eq_natCast_iff]

end

/-- An element of the inertia group of `A` lies in the kernel of the character modulo any `N` that
is a unit of `A`. -/
lemma cyclotomicCharMod_eq_one_of_mem_inertiaGroup (hσ : σ ∈ inertiaGroup Γ A) (hN : A N = 1) :
    cyclotomicCharMod Ω N σ = 1 :=
  (hσ.mem_ker_cyclotomicCharMod_iff hN).mpr rfl

/-- A residue modulo `N` is the cast of its natural representative. -/
lemma zmod_eq_natCast_val {g : ZMod N} : g = g.val := by simp

/-- Every additive map from `ZMod N` to the units of `Ω` is equivariant, when `g` acts on `ZMod N`
through the character. -/
lemma map_cyclotomicCharMod_mul (μ : ZMod N →+ DiscreteUnits Ω) (g : Γ) (a : ZMod N) :
    μ ((cyclotomicCharMod Ω N g).val * a) = unitsRep g (μ a) := by
  simp [cyclotomicCharMod_eq_iff_unitsRep.mp (zmod_eq_natCast_val
    (g := (cyclotomicCharMod Ω N g : ZMod N))), ← map_nsmul, natCast_self]

variable {l : ℕ} [Fact (Nat.Prime l)] {K : Type*} [Field K] [Algebra K Ω]

/-! ### The `l`-adic character -/

/-- The character modulo `l ^ r` is the reduction of the `l`-adic character. -/
lemma cyclotomicCharMod_prime_pow_eq (r : ℕ) :
    cyclotomicCharMod (Γ := Γ) Ω (l ^ r) =
      (map (toZModPow r).toMonoidHom).comp (cyclotomicChar Ω l) := by
  ext
  exact (cyclotomicCharacter.toZModPow ..).symm

/-- `l ^ r` divides `χ_l(σ) - q` in `ℤ_l` if and only if the character modulo `l ^ r` takes the
value `q` at `σ`; here `χ_l` is the `l`-adic cyclotomic character `New.cyclotomicChar Ω l`. -/
lemma pow_dvd_cyclotomicChar_sub_iff (r : ℕ) :
    l.cast ^ r ∣ (cyclotomicChar Ω l σ).val - q ↔ (cyclotomicCharMod Ω (l ^ r) σ).val = q := by
  simp [← Ideal.mem_span_singleton, ← ker_toZModPow, cyclotomicCharMod_prime_pow_eq, sub_eq_zero]

/-- Let `Ω` be algebraically closed of characteristic `0`, let `A` be a `ℤ_l`-module (here not the
valuation subring) and `f : A → B` additive with image killed by `l ^ r` (`h_kill`). Then
`f (χ_l(σ) • x) = χ_{l^r}(σ) • f x`, where `χ_l` is the `l`-adic and `χ_{l^r}` the mod `l ^ r`
cyclotomic character. -/
lemma map_cyclotomicChar_smul {A B : Type*} [AddCommGroup A] [Module ℤ_[l] A] [AddCommGroup B]
    (f : A →+ B) (r : ℕ) (h_kill : ∀ x : A, l ^ r • f x = 0) (x : A) :
    f ((cyclotomicChar Ω l σ).val • x) =
      (cyclotomicCharMod Ω (l ^ r) σ : ZMod (l ^ r)).val • f x := by
  -- Write the value of `cyclotomicChar` as its residue plus a multiple of `l ^ r`, which `f` kills.
  obtain ⟨c, hc⟩ : (l : ℤ_[l]) ^ r ∣
      (cyclotomicChar Ω l σ).val - (cyclotomicCharMod Ω (l ^ r) σ : ZMod (l ^ r)).val :=
    (pow_dvd_cyclotomicChar_sub_iff r).mpr zmod_eq_natCast_val
  rw [eq_add_of_sub_eq hc, add_smul, mul_smul]
  norm_cast
  simp [h_kill]

variable (l)

/-- Let `Γ` act on the algebraically closed field `Ω` of characteristic `0`, let `σ ∈ Γ` be a
Frobenius for the natural number `q` at the valuation subring `A` of `Ω`, and let the prime `l` be
a unit of `A`. Then the `l`-adic cyclotomic character takes the value `q` at `σ`. -/
lemma IsFrob.cyclotomicChar_eq (h_frob : IsFrob A q σ) (hl : A l = 1) :
    (cyclotomicChar Ω l σ).val = q := by
  -- an `l`-adic integer is determined by its residues modulo the powers of `l`, and each residue is
  -- the value at `σ` of the character modulo `l ^ r`
  have h_res (r : ℕ) : (cyclotomicCharMod Ω (l ^ r) σ).val = q :=
    h_frob.cyclotomicCharMod_eq (by simp [hl])
  simpa [← ext_of_toZModPow, cyclotomicCharMod_prime_pow_eq] using h_res

/-- An element of the inertia group of `A` lies in the kernel of the `l`-adic cyclotomic character
when the prime `l` is a unit of `A`. -/
lemma cyclotomicChar_eq_one_of_mem_inertiaGroup (hσ : σ ∈ inertiaGroup Γ A) (hl : A l = 1) :
    cyclotomicChar Ω l σ = 1 :=
  ext (hσ.cyclotomicChar_eq l hl)

variable {Γ' Ω' : Type*} [Group Γ'] [Field Ω'] [MulSemiringAction Γ' Ω'] [IsAlgClosed Ω']
  [CharZero Ω'] {j : Ω →+* Ω'} {g' : Γ'}

/-- Let `Γ`, `Γ'` act on algebraically closed fields `Ω`, `Ω'` of characteristic `0`, let `g ∈ Γ`,
`g' ∈ Γ'` and let `N` be a non-zero natural number. If the ring homomorphism `j : Ω → Ω'`
intertwines `g` and `g'` (`h_comm`), the characters modulo `N` agree at `g` and `g'`. -/
lemma cyclotomicCharMod_eq_of_equivariant (h_comm : ∀ x : Ω, j (g • x) = g' • j x) :
    cyclotomicCharMod Ω N g = cyclotomicCharMod Ω' N g' := by
  -- If `ζ` is an `N`-th root of unity then so is `j ζ`, and `j (g • ζ) = g' • j ζ` is `j ζ` raised
  -- to the exponent given by `g'`.
  have h_val_eq : (cyclotomicCharMod Ω N g : ZMod N) =
      (cyclotomicCharMod Ω' N g' : ZMod N).val := by
    refine cyclotomicCharMod_eq_iff.mpr fun ζ hζ ↦ j.injective ?_
    have hζ' : j ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
    rw [h_comm, smul_eq_pow_cyclotomicCharMod (N := N) g' hζ', map_pow]
  exact ext (h_val_eq.trans zmod_eq_natCast_val.symm)

/-- Let `Γ`, `Γ'` act on algebraically closed fields `Ω`, `Ω'` of characteristic `0`, and let
`j : Ω → Ω'` be a ring homomorphism with `j (g • x) = g' • j x` for all `x` (`h_comm`). Then the
`l`-adic cyclotomic characters at `g` and `g'` agree, for the prime `l`. -/
lemma cyclotomicChar_eq_of_equivariant (h_comm : ∀ x : Ω, j (g • x) = g' • j x) :
    cyclotomicChar Ω l g = cyclotomicChar Ω' l g' := by
  -- An `l`-adic integer is determined by its residues modulo all `l ^ r`.
  simpa [cyclotomicCharMod_prime_pow_eq, ext_of_toZModPow, ← val_inj] using fun r : ℕ ↦
    cyclotomicCharMod_eq_of_equivariant h_comm (N := l ^ r)

variable [TopologicalSpace Γ] [G : IsProGalois Γ K Ω]

include G in
omit [IsAlgClosed Ω] [CharZero Ω] in
/-- For the Galois group `Γ` of `Ω / K`, with `l` a prime natural number, the `l`-adic cyclotomic
character is continuous. -/
lemma continuous_cyclotomicChar : Continuous (cyclotomicChar (Γ := Γ) Ω l) :=
  (cyclotomicCharacter.continuous l K Ω).comp
    (continuous_of_equivariant_emb (φ := MulSemiringAction.toAlgAut Γ K Ω) 1 fun _ _ ↦ rfl)

open IntermediateField Subgroup MonoidHom IsCyclotomicExtension

/-- For the Galois group `Γ` of `Ω / K`, with `Ω` algebraically closed of characteristic `0` and
`N ≠ 0` a natural number, the kernel of the character modulo `N` is open. -/
instance isOpen_ker_cyclotomicCharMod : Fact (cyclotomicCharMod (Γ := Γ) Ω N).ker.IsOpen := by
  -- the kernel contains the open stabiliser of a primitive `N`-th root of unity `ζ`
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ N := prim
  refine ⟨isOpen_mono (fun g (hg : g • ζ = ζ) ↦ ?_) (G.isOpen_stabilizer ζ)⟩
  simpa using cyclotomicCharMod_eq_of_isPrimitiveRoot (g := g) (a := 1) hζ (by simpa)

variable (Ω N)

/-! ### Roots of unity and the cyclotomic field -/

/-- An injective additive map from ℤ/N to Ω^× (written additively) whose image is the set of
elements killed by N. It sends a to ζ^a for a chosen primitive N-th root of unity ζ. Here `Ω` is
algebraically closed of characteristic 0, and `N ≠ 0`. -/
def rootPowHom :
    {f : ZMod N →+ DiscreteUnits Ω //
      Injective f ∧ ∀ y : DiscreteUnits Ω, y ∈ f.range ↔ N • y = 0} :=
  have hζ : IsPrimitiveRoot (IsUnit.unit _) N := (prim (M := Ω)).choose_spec.isUnit_unit out
  ⟨ZMod.lift N ⟨zmultiplesHom (DiscreteUnits Ω) (IsUnit.unit _), hζ.zpow_eq_one⟩,
    Subtype.val_injective.comp hζ.zmodEquivZPowers.injective,
    -- the powers of a primitive root are all the `N`-th roots of unity
    by simpa [intCast_surjective.exists, SetLike.ext_iff] using! hζ.zpowers_eq⟩

lemma isPrimitiveRoot_rootPowHom_one : IsPrimitiveRoot ((rootPowHom Ω N).val 1).toMul N := by
  obtain ⟨h_inj, -⟩ := (rootPowHom Ω N).property
  exact IsPrimitiveRoot.iff_orderOf.mpr ((addOrderOf_injective _ h_inj 1).trans (by simp))

/-- The subgroup of Gal(ℚ̄/ℚ) = `Gal(New.Ω/ℚ)` fixing all N-th roots of unity, for a natural number
`N ≠ 0`: the absolute Galois group of ℚ(ζ_N). -/
abbrev cycloGalGroup : Subgroup Gal(New.Ω/ℚ) := (cyclotomicCharMod New.Ω N).ker

/-- The cyclotomic field ℚ(ζ_N) inside ℚ̄, defined as the fixed field of `New.cycloGalGroup N`. -/
abbrev cycloField : IntermediateField ℚ New.Ω := fixedFieldOf (cycloGalGroup N)

/-- `New.cycloField N` is the cyclotomic extension of `ℚ` generated by the `N`-th roots of unity. -/
instance : IsCyclotomicExtension {N} ℚ (cycloField N) := by
  -- `cycloGalGroup N` is the group that fixes the field generated by the `N`-th roots of unity.
  have h_fix : cycloGalGroup N = _root_.fixingSubgroup Gal(New.Ω/ℚ)
      (adjoin ℚ {b : New.Ω | ∃ n ∈ ({N} : Set ℕ), n ≠ 0 ∧ b ^ n = 1} : Set New.Ω) := by
    ext g
    -- both sides say that `g` fixes the `N`-th roots of unity
    simp only [_root_.mem_fixingSubgroup_iff, SetLike.mem_coe, forall_mem_adjoin_smul_eq_self_iff]
    -- `using!`: `cyclotomicCharMod_eq_iff` writes `g • ζ`, which simp does not turn into the goal's
    -- `g ζ`
    simpa [ne] using! cyclotomicCharMod_eq_iff (g := g) (a := 1)
  rw [cycloField, h_fix, fixedFieldOf_fixingSubgroup]
  exact isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot _ _ _ (by simp [prim])

/-- For a natural number `N ≠ 0` and the Galois group of `New.Ω` (ℚ̄, an algebraically closed field
of characteristic `0`) over `ℚ`, the character modulo `N` is surjective. -/
lemma cyclotomicCharMod_surjective :
    Surjective (cyclotomicCharMod (Γ := Gal(New.Ω/ℚ)) New.Ω N) := by
  -- The image has as many elements as the index of the kernel, which is the degree `φ(N)` of the
  -- cyclotomic field that the kernel fixes.
  refine range_eq_top.mp (eq_top_of_card_eq _ ?_)
  rw [← index_ker, ← finrank_fixedFieldOf, Rat.finrank N]
  simp

end New

end
