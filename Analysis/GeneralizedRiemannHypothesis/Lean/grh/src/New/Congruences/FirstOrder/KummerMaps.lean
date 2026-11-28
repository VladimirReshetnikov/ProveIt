import Lib.ClassField.GreenbergWiles.RelationsModL
import Lib.GaloisRep.Main.Defs
import New.Congruences.FirstOrder.EvenClasses

/-!
# Kummer maps

Throughout, `ℓ` is a prime and `E` is a CM field in the algebraic closure `Ω` of `ℚ` that contains a
primitive `5040`-th root of unity (`New.CMFieldWithRoot5040`). We pass from `E` to its maximal real
subfield `F`. We write `G = Gal(Ω/E)` and `G_F = Gal(Ω/F)`, `c` for the chosen complex conjugation
and `G_ν` for the elements of `G` that fix the `ℓ ^ ν`-th roots of unity. A Kummer map is the
restriction to `G` of a relation over `F` for the module `ℤ/ℓ^ν` on which `G_F` acts by a power of
`cyc⁺`, the extension to `G_F` of the cyclotomic character of `G` that is `1` at `c`.

* `New.Selmer.IsNuSplitPlace`: a prime of degree one off `ℓ` with a Frobenius element in `G_ν`.
* `New.Selmer.IsKummerMap`, `New.Selmer.IsKummerMap.hasKummerType`: Kummer maps are odd
  homomorphisms on `G_ν`, and conjugation by `g` multiplies those of exponent `e` by
  `cyc(g) ^ (e + 1)`.
* `New.Selmer.IsKummerMap.sum_eq_zero`: the reciprocity law for Kummer maps and even classes;
  `New.Selmer.IsKummerMap.nsmul_apply_tameGenerator_eq_zero` is the case where one term is left.
* `New.Selmer.exists_card_lt_finrank_kummerReductions`: there are many Kummer maps modulo `ℓ`.

Notions from other files:
* `New.FrobeniusDatum`: a prime `w` of `E` of prime norm, a place `valuationSubring` of `Ω` above it
  and a geometric Frobenius element `frob` at that place.
* `New.RelationSetting`: a discrete Galois module with local conditions;
  `New.RelationSetting.relations` is the module of relations off a finite set `T` of primes, in
  place of dual cocycles; `New.Selmer.IsKummerMap` spells the notion out in the case used here.
* `New.Selmer.evenClasses`: for a coefficient ring `O` and a set `S` of primes of `E`, the even
  classes in `(O/ℓ^ν)(-e)` that are unramified off `ℓ`, `S` and `S̄` and vanish on
  `shaLocalSet ℓ E 1`, the elements of `ker cyc` in decomposition groups above `ℓ`.
* `New.cyclotomicCharMod`: the cyclotomic character modulo `N`; `New.cyclotomicChar` is the `ℓ`-adic
  one, written `cyc`.
-/

noncomputable section

namespace New.Selmer

open NumberField Cohomology IsCMField Function Fintype PadicInt Subgroup Finset DiscreteModule QZ

variable {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E] [CMFieldWithRoot5040 E]

/-- The datum `x` (a prime of degree one, a place above it and a Frobenius element) is `ν`-split if
its prime does not lie above `ℓ` and its Frobenius element fixes the `ℓ ^ ν`-th roots of unity. -/
def IsNuSplitPlace (ν : ℕ) (x : FrobeniusDatum E) : Prop :=
  (ℓ : 𝓞 E) ∉ x.place.asIdeal ∧ cyclotomicCharMod Ω (ℓ ^ ν) x.frob = 1

/-- The prime of the maximal real subfield `F` below a prime of `E`. -/
abbrev primeBelowPlus (w : FinPlace E) : FinPlace (maximalRealSubfield E) :=
  w.below (maximalRealSubfield E)

lemma primeBelowPlus_star (w : FinPlace E) : primeBelowPlus (star w) = primeBelowPlus w := by
  ext x
  have h_star : star (algebraMap _ (𝓞 E) x) = algebraMap _ (𝓞 E) x :=
    Subtype.ext (mem_maximalRealSubfield_iff_star_eq.1 (x : maximalRealSubfield E).property)
  change algebraMap _ (𝓞 E) x ∈ (star w).asIdeal ↔ algebraMap _ (𝓞 E) x ∈ w.asIdeal
  rw [mem_star_place, h_star]

lemma q_primeBelowPlus (x : FrobeniusDatum E) : (primeBelowPlus x.place).q = x.place.q :=
  (x.prime_q.pow_eq_iff.1
    (Ideal.absNorm_pow_inertiaDeg (primeBelowPlus x.place).asIdeal x.place.asIdeal)).left

/-! ### Passing to the maximal real subfield -/

variable (E) in
/-- The inclusion of `G = Gal(Ω/E)` in `G_F = Gal(Ω/F)`, for `F` the maximal real subfield of
`E`. -/
def toGalPlus : Gal(Ω/E) →* Gal(Ω/maximalRealSubfield E) :=
  AlgEquiv.restrictScalarsHom (maximalRealSubfield E)

variable (E) in
/-- The chosen complex conjugation `c` (`New.cmConj`) as an element of `G_F`. -/
def conjPlus : Gal(Ω/maximalRealSubfield E) :=
  { cmConj with
    commutes' x := by
      change cmConj (algebraMap E Ω x) = algebraMap E Ω x
      rw [cmConj_algebraMap, mem_maximalRealSubfield_iff_star_eq.1 x.property] }

lemma isOpenEmbedding_toGalPlus : Topology.IsOpenEmbedding (toGalPlus E) :=
  isOpenEmbedding_galois_restrict (toGalPlus E) fun _ _ ↦ rfl

lemma index_range_toGalPlus : (toGalPlus E).range.index = 2 := by
  obtain ⟨-, -, h_index⟩ := isClosedEmbedding_galois_restrict (K := maximalRealSubfield E)
    (L := E) (toGalPlus E) fun _ _ ↦ rfl
  rw [h_index, Algebra.IsQuadraticExtension.finrank_eq_two]

lemma isComplexConj_conjPlus : IsComplexConj (conjPlus E) := isComplexConj_cmConj

lemma conjPlus_mul_self : conjPlus E * conjPlus E = 1 := isComplexConj_conjPlus.mul_self

lemma isFrob_toGalPlus_iff {A : ClosurePlace} {q : ℕ} {g : Gal(Ω/E)} :
    IsFrob A q (toGalPlus E g) ↔ IsFrob A q g := Iff.rfl

/-- The inertia group in `G` of a place `A` of `Ω` is the preimage of the one in `G_F`. -/
lemma toGalPlus_mem_inertiaGroup_iff {A : ClosurePlace} {g : Gal(Ω/E)} :
    toGalPlus E g ∈ inertiaGroup Gal(Ω/maximalRealSubfield E) A ↔ g ∈ inertiaGroup Gal(Ω/E) A :=
  Iff.rfl

lemma cyclotomicChar_toGalPlus (g : Gal(Ω/E)) :
    cyclotomicChar Ω ℓ (toGalPlus E g) = cyclotomicChar Ω ℓ g := rfl

lemma toGalPlus_conjGal (g : Gal(Ω/E)) :
    toGalPlus E (conjGal g) = conjPlus E * toGalPlus E g * conjPlus E := rfl

/-- No complex conjugation lies in `Gal(Ω/E)`, because `E` is totally complex. -/
lemma notMem_range_toGalPlus {c : Gal(Ω/maximalRealSubfield E)} (hc : IsComplexConj c) :
    c ∉ (toGalPlus E).range := by
  rintro ⟨s, rfl⟩
  exact hc.false_of_isTotallyComplex (c := s)

open Classical in
/-- Let `F` be the maximal real subfield of `E` and `G_F = Gal(Ω/F)`. For `σ ∈ G_F`, either `σ` or
`σ c` is the image of some `g` in `G = Gal(Ω/E)` under `toGalPlus E`, where `c` (`conjPlus E`) is
the chosen complex conjugation. -/
lemma exists_toGalPlus_eq_ite (σ : Gal(Ω/maximalRealSubfield E)) :
    ∃ g : Gal(Ω/E), toGalPlus E g = if σ ∈ (toGalPlus E).range then σ else σ * conjPlus E := by
  rw [← MonoidHom.mem_range]
  split_ifs with hσ
  · exact hσ
  · rw [mul_mem_iff_of_index_two index_range_toGalPlus]
    exact iff_of_false hσ (notMem_range_toGalPlus isComplexConj_conjPlus)

/-- The map from `G_F = G ∪ G c` to `G = Gal(Ω/E)` that sends `g` and `g c` to `g`, for `g ∈ G` and
`c` the chosen complex conjugation. -/
def ofGalPlus (σ : Gal(Ω/maximalRealSubfield E)) : Gal(Ω/E) := (exists_toGalPlus_eq_ite σ).choose

open Classical in
lemma toGalPlus_ofGalPlus (σ : Gal(Ω/maximalRealSubfield E)) :
    toGalPlus E (ofGalPlus σ) = if σ ∈ (toGalPlus E).range then σ else σ * conjPlus E :=
  (exists_toGalPlus_eq_ite σ).choose_spec

lemma toGalPlus_ofGalPlus_of_mem {σ : Gal(Ω/maximalRealSubfield E)}
    (hσ : σ ∈ (toGalPlus E).range) : toGalPlus E (ofGalPlus σ) = σ :=
  (toGalPlus_ofGalPlus σ).trans (ite_eq_left hσ)

lemma toGalPlus_ofGalPlus_of_notMem {σ : Gal(Ω/maximalRealSubfield E)}
    (hσ : σ ∉ (toGalPlus E).range) : toGalPlus E (ofGalPlus σ) = σ * conjPlus E :=
  (toGalPlus_ofGalPlus σ).trans (ite_eq_right hσ)

@[simp] lemma ofGalPlus_toGalPlus (g : Gal(Ω/E)) : ofGalPlus (toGalPlus E g) = g :=
  isOpenEmbedding_toGalPlus.injective (toGalPlus_ofGalPlus_of_mem ⟨g, rfl⟩)

/-- Let `F` be the maximal real subfield of the CM field `E`, let `Ω` be the algebraic closure of
`ℚ` and `c` the chosen complex conjugation. The map `ofGalPlus : Gal(Ω/F) → Gal(Ω/E)`, which sends
`g` and `g c` to `g` for `g ∈ Gal(Ω/E)`, is continuous. -/
lemma continuous_ofGalPlus : Continuous (ofGalPlus (E := E)) := by
  classical
  -- The two cosets are open and closed, and the map is continuous on each.
  have h_open : IsOpen ((toGalPlus E).range : Set Gal(Ω/maximalRealSubfield E)) :=
    isOpenEmbedding_toGalPlus.isOpen_range
  have h_front : frontier {σ : Gal(Ω/maximalRealSubfield E) | σ ∈ (toGalPlus E).range} = ∅ :=
    IsClopen.frontier_eq ⟨(toGalPlus E).range.isClosed_of_isOpen h_open, h_open⟩
  have h_cont : Continuous fun σ : Gal(Ω/maximalRealSubfield E) ↦
      if σ ∈ (toGalPlus E).range then σ else σ * conjPlus E :=
    continuous_id.if (fun σ hσ ↦ (h_front.subset hσ).elim) (by fun_prop)
  exact isOpenEmbedding_toGalPlus.isInducing.continuous_iff.2
    (h_cont.congr fun σ ↦ (toGalPlus_ofGalPlus σ).symm)

/-- The map `ofGalPlus` from `G_F = G ∪ G c` to `G = Gal(Ω/E)`, which sends `g` and `g c` to `g`,
is multiplicative up to replacing the second factor `s` by `conjGal s = c s c`. Here `c` is the
chosen complex conjugation. -/
lemma ofGalPlus_mul_eq_or (g h : Gal(Ω/maximalRealSubfield E)) :
    ofGalPlus (g * h) = ofGalPlus g * ofGalPlus h ∨
      ofGalPlus (g * h) = ofGalPlus g * conjGal (ofGalPlus h) := by
  classical
  have h_mem : g * h ∈ (toGalPlus E).range ↔
      (g ∈ (toGalPlus E).range ↔ h ∈ (toGalPlus E).range) :=
    mul_mem_iff_of_index_two index_range_toGalPlus
  have h_cancel (σ : Gal(Ω/maximalRealSubfield E)) : conjPlus E * (conjPlus E * σ) = σ := by
    simp [← mul_assoc, conjPlus_mul_self]
  -- The first equation holds for `g ∈ G`, the second one for `g ∈ G c`; we compare in `G_F`.
  by_cases hg : g ∈ (toGalPlus E).range
  · refine .inl (isOpenEmbedding_toGalPlus.injective ?_)
    simp [-MonoidHom.mem_range, toGalPlus_ofGalPlus, h_mem, hg, mul_assoc]
  · refine .inr (isOpenEmbedding_toGalPlus.injective ?_)
    simp [-MonoidHom.mem_range, toGalPlus_conjGal, toGalPlus_ofGalPlus, h_mem, hg, mul_assoc,
      h_cancel, conjPlus_mul_self]

/-- Let `E` be a CM field in the algebraic closure `Ω` of `ℚ` that contains a primitive `5040`-th
root of unity, and let `F` be its maximal real subfield. Then `E / F` is unramified at the finite
places: the inertia group in `Gal(Ω/F)` of a place `A` of `Ω` above a prime `v` of `F` lies in the
image of the inclusion `toGalPlus E` of `Gal(Ω/E)` in `Gal(Ω/F)`. -/
lemma inertiaGroup_le_range_toGalPlus (A : ClosurePlace) {v : FinPlace (maximalRealSubfield E)}
    (hA : IsPlaceOver A v) :
    inertiaGroup Gal(Ω/maximalRealSubfield E) A ≤ (toGalPlus E).range := by
  intro g hg
  by_contra h_notMem
  -- Otherwise `g` acts on `E` as complex conjugation. There is an integer `y` of `E` such that
  -- `y - star y` is a unit, and this unit would lie in the prime below `A`.
  obtain ⟨w, hw, -⟩ := hA.exists_above (L := E)
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, IsUnit (y - star y) := HasPrimitiveRoot5040.exists_isUnit_sub_star
  have g_star : g (algebraMap E Ω (star (y : E))) = algebraMap E Ω y := by
    have h_fix : toGalPlus E (ofGalPlus g) (algebraMap E Ω y) = algebraMap E Ω y :=
      (ofGalPlus g).commutes y
    rw [toGalPlus_ofGalPlus_of_notMem h_notMem] at h_fix
    simpa [conjPlus] using h_fix
  obtain ⟨-, h_inertia : ∀ z : Ω, A.valuation z ≤ 1 → A.valuation (g • z - z ^ 1) < 1⟩ := hg
  have h_val : A.valuation (algebraMap E Ω (y - star y : 𝓞 E)) < 1 := by
    simpa [g_star] using h_inertia (algebraMap E Ω (star (y : E)))
      (A.valuation_le_one ⟨_, algebraMap_ringOfIntegers_mem A (star y)⟩)
  exact w.asIdeal.notMem_of_isUnit hy ((hw (y - star y)).1 h_val)

/-- Let `F` be the maximal real subfield of `E`, `G = Gal(Ω/E)` and `G_F = Gal(Ω/F)`. The map
`ofGalPlus : G_F → G`, a left inverse of the inclusion, sends the inertia groups above a set `W` of
primes of `F` into the inertia groups above the primes of `E` over `W`. -/
lemma ofGalPlus_mem_inertiaAbove {W : Set (FinPlace (maximalRealSubfield E))}
    {g : Gal(Ω/maximalRealSubfield E)} (hg : g ∈ inertiaAbove W) :
    ofGalPlus g ∈ inertiaAbove (primeBelowPlus ⁻¹' W) := by
  obtain ⟨v, hv, A, hA, hgA⟩ := hg
  obtain ⟨s, rfl⟩ : ∃ s : Gal(Ω/E), toGalPlus E s = g := inertiaGroup_le_range_toGalPlus A hA hgA
  obtain ⟨w, hw, rfl⟩ : ∃ w : FinPlace E, IsPlaceOver A w ∧ primeBelowPlus w = v := hA.exists_above
  exact ⟨w, hv, A, hw, by simpa using toGalPlus_mem_inertiaGroup_iff.1 hgA⟩

variable (ℓ E) in
/-- The character `cyc⁺` of `G_F`: the cyclotomic character times the quadratic character that
cuts out `E`. It is `cyc` on `G` and `1` at `c`. -/
def cyclotomicPlus : Gal(Ω/maximalRealSubfield E) →* ℤ_[ℓ]ˣ :=
  .mk' (fun g : Gal(Ω/maximalRealSubfield E) ↦ cyclotomicChar Ω ℓ (ofGalPlus g)) fun g h ↦ by
    rcases ofGalPlus_mul_eq_or g h with h_mul | h_mul <;> simp [h_mul]

lemma cyclotomicPlus_apply (g : Gal(Ω/maximalRealSubfield E)) :
    cyclotomicPlus ℓ E g = cyclotomicChar Ω ℓ (ofGalPlus g) := rfl

lemma continuous_cyclotomicPlus : Continuous (cyclotomicPlus ℓ E) :=
  ((continuous_cyclotomicChar ℓ).comp continuous_ofGalPlus).congr fun g ↦
    (cyclotomicPlus_apply g).symm

/-- The character `cyc⁺` is unramified off `ℓ`: it is `1` on the inertia groups above the primes of
`F` that do not divide `ℓ`. -/
lemma cyclotomicPlus_eq_one_of_mem_inertiaAbove {g : Gal(Ω/maximalRealSubfield E)}
    (hg : g ∈ inertiaAbove (placesDividing (maximalRealSubfield E) ℓ)ᶜ) :
    cyclotomicPlus ℓ E g = 1 := by
  have h_mem : ofGalPlus g ∈ inertiaAbove (placesDividing E ℓ)ᶜ := by
    simpa [placesDividing] using ofGalPlus_mem_inertiaAbove hg
  exact (cyclotomicPlus_apply g).trans (cyclotomicChar_eq_one_of_mem_inertiaAbove h_mem)

/-- The character `cyc⁺` of `G_F` is `1` at every complex conjugation. -/
lemma cyclotomicPlus_eq_one_of_isComplexConj {c : Gal(Ω/maximalRealSubfield E)}
    (hc : IsComplexConj c) : cyclotomicPlus ℓ E c = 1 := by
  rw [cyclotomicPlus_apply, ← cyclotomicChar_toGalPlus,
    toGalPlus_ofGalPlus_of_notMem (notMem_range_toGalPlus hc), map_mul,
    hc.cyclotomicChar_eq_neg_one ℓ, isComplexConj_conjPlus.cyclotomicChar_eq_neg_one ℓ,
    neg_mul_neg, one_mul]

variable (ℓ E) in
/-- The subgroup `G_ν` of the elements of `G` that fix the `ℓ ^ ν`-th roots of unity, as an open
normal subgroup of `G_F`. -/
def cyclotomicKerPlus (ν : ℕ) : OpenNormalSubgroup Gal(Ω/maximalRealSubfield E) :=
  haveI : (toGalPlus E).range.Normal := normal_of_index_eq_two index_range_toGalPlus
  .mk ⟨(toGalPlus E).range ⊓ (cyclotomicCharMod Ω (ℓ ^ ν)).ker,
    isOpenEmbedding_toGalPlus.isOpen_range.inter isOpen_ker_cyclotomicCharMod.out⟩

@[simp] lemma toGalPlus_mem_cyclotomicKerPlus_iff {ν : ℕ} {g : Gal(Ω/E)} :
    toGalPlus E g ∈ cyclotomicKerPlus ℓ E ν ↔ cyclotomicCharMod Ω (ℓ ^ ν) g = 1 :=
  and_iff_right ⟨g, rfl⟩

variable (ℓ E) in
/-- The character `cyc⁺` of `G_F` modulo `ℓ ^ ν`. -/
def cyclotomicPlusMod (ν : ℕ) : Gal(Ω/maximalRealSubfield E) →* (ZMod (ℓ ^ ν))ˣ :=
  (Units.map (toZModPow ν).toMonoidHom).comp (cyclotomicPlus ℓ E)

lemma cyclotomicPlusMod_apply (ν : ℕ) (g : Gal(Ω/maximalRealSubfield E)) :
    cyclotomicPlusMod ℓ E ν g = cyclotomicCharMod Ω (ℓ ^ ν) (ofGalPlus g) := by
  simp [cyclotomicPlusMod, cyclotomicCharMod_prime_pow_eq, cyclotomicPlus_apply]

lemma cyclotomicKerPlus_le_ker (ν : ℕ) :
    (cyclotomicKerPlus ℓ E ν).toSubgroup ≤ (cyclotomicPlusMod ℓ E ν).ker := by
  intro g hg
  obtain ⟨s, rfl⟩ := (mem_inf.1 hg).left
  simpa [cyclotomicPlusMod_apply] using toGalPlus_mem_cyclotomicKerPlus_iff.1 hg

lemma isOpen_ker_cyclotomicPlusMod (ν : ℕ) :
    IsOpen ((cyclotomicPlusMod ℓ E ν).ker : Set Gal(Ω/maximalRealSubfield E)) :=
  isOpen_mono (cyclotomicKerPlus_le_ker ν) (cyclotomicKerPlus ℓ E ν).isOpen

variable (ℓ E) in
/-- The module `ℤ/ℓ^ν` with `G_F` acting by `(cyc⁺) ^ (-e)`. -/
abbrev tateTwistPlus (ν e : ℕ) : DiscreteModule (ZMod (ℓ ^ ν)) Gal(Ω/maximalRealSubfield E) :=
  .of (charRep (ZMod (ℓ ^ ν)) (cyclotomicPlusMod ℓ E ν ^ e)⁻¹)
    (((Continuous.of_isOpen_ker _ (isOpen_ker_cyclotomicPlusMod ν)).pow e).inv.fst'.smul
      continuous_snd)

lemma tateTwistPlus_ρ (ν e : ℕ) (g : Gal(Ω/maximalRealSubfield E)) (a : ZMod (ℓ ^ ν)) :
    (tateTwistPlus ℓ E ν e).ρ g a = ((cyclotomicPlusMod ℓ E ν g ^ e)⁻¹).val * a := rfl

/-- An element of the kernel of `cyc⁺` modulo `ℓ ^ ν` acts trivially on `ℤ/ℓ^ν` twisted by
`(cyc⁺) ^ (-e)`. -/
lemma tateTwistPlus_ρ_eq_one {ν : ℕ} (e : ℕ) {g : Gal(Ω/maximalRealSubfield E)}
    (hg : cyclotomicPlusMod ℓ E ν g = 1) : (tateTwistPlus ℓ E ν e).ρ g = 1 :=
  LinearMap.ext fun a ↦ (tateTwistPlus_ρ ν e g a).trans (by simp [hg])

lemma cyclotomicPlusMod_eq_one (ν : ℕ) {g : Gal(Ω/maximalRealSubfield E)}
    (hg : cyclotomicPlus ℓ E g = 1) : cyclotomicPlusMod ℓ E ν g = 1 := by
  simp [cyclotomicPlusMod, hg]

section Kummer

variable {ν : ℕ} (e : ℕ) {I : Type}

open Classical in
/-- A place of `Ω` above each prime `u` of `F`; if `u` lies below a member of the family `x`, it is
the place of such a member. -/
def familyPlace (x : I → FrobeniusDatum E) (u : FinPlace (maximalRealSubfield E)) : ClosurePlace :=
  if h : ∃ i : I, primeBelowPlus (x i).place = u then (x h.choose).valuationSubring else placeOver u

/-- If the prime `u` of `F` lies below a member of the family `x`, then `familyPlace x u` is the
place of such a member. -/
lemma exists_familyPlace_eq {x : I → FrobeniusDatum E} {u : FinPlace (maximalRealSubfield E)}
    (hu : ∃ i : I, primeBelowPlus (x i).place = u) :
    ∃ i : I, primeBelowPlus (x i).place = u ∧ familyPlace x u = (x i).valuationSubring :=
  ⟨hu.choose, hu.choose_spec, dite_eq_left hu⟩

/-- The place `familyPlace x u` of `Ω` lies above the prime `u` of `F`. -/
lemma isPlaceOver_familyPlace {x : I → FrobeniusDatum E} (u : FinPlace (maximalRealSubfield E)) :
    IsPlaceOver (familyPlace x u) u := by
  by_cases hu : ∃ i : I, primeBelowPlus (x i).place = u
  · obtain ⟨i, rfl, h_place⟩ := exists_familyPlace_eq hu
    simpa [h_place] using (x i).isPlaceOver.isPlaceOver_below
  · simpa [familyPlace, hu] using u.isPlaceOver_placeOver

/-- If the prime `u` of `F` lies below a member of the family `x`, then for some `i` the inverse of
the geometric Frobenius element of `x i` is an arithmetic Frobenius element of `G_F` (for the norm
`u.q` of `u`) at `familyPlace x u`, the chosen place of `Ω` above `u`. -/
lemma exists_isFrob_familyPlace {x : I → FrobeniusDatum E} {u : FinPlace (maximalRealSubfield E)}
    (hu : ∃ i : I, primeBelowPlus (x i).place = u) :
    ∃ i : I, IsFrob (familyPlace x u) u.q (toGalPlus E (x i).frob⁻¹) := by
  obtain ⟨i, rfl, h_place⟩ := exists_familyPlace_eq hu
  exact ⟨i, by simpa [h_place, q_primeBelowPlus, isFrob_toGalPlus_iff, -map_inv]
    using (x i).isFrob_inv⟩

variable (ℓ) in
/-- The set `S₀` of the primes of `F` above `ℓ` or below a member of the finite family `x`. -/
def familyPrimes [Finite I] (x : I → FrobeniusDatum E) :
    Finset (FinPlace (maximalRealSubfield E)) :=
  (Set.toFinite (placesDividing (maximalRealSubfield E) ℓ ∪
    Set.range fun i : I ↦ primeBelowPlus (x i).place)).toFinset

lemma mem_familyPrimes [Finite I] {x : I → FrobeniusDatum E}
    {u : FinPlace (maximalRealSubfield E)} :
    u ∈ familyPrimes ℓ x ↔
      (ℓ : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal ∨ ∃ i : I, primeBelowPlus (x i).place = u :=
  Set.Finite.mem_toFinset _

/-- Let `F` be the maximal real subfield of `E`, `x` a finite family of `ν`-split places and `u` a
prime of `F` off `ℓ` below a member of `x`. Then the decomposition group of `familyPlace x u`, the
chosen place above `u`, lies in the kernel of `cyc⁺` modulo `ℓ ^ ν`, because inertia and a Frobenius
element do. -/
lemma cyclotomicPlusMod_eq_one_of_mem_decompGroup [Finite I] {x : I → FrobeniusDatum E}
    (hx : ∀ i : I, IsNuSplitPlace ν (x i)) {u : FinPlace (maximalRealSubfield E)}
    (hu : ∃ i : I, primeBelowPlus (x i).place = u)
    (hℓ : (ℓ : 𝓞 (maximalRealSubfield E)) ∉ u.asIdeal) {g : Gal(Ω/maximalRealSubfield E)}
    (hg : g ∈ decompGroup Gal(Ω/maximalRealSubfield E) (familyPlace x u)) :
    cyclotomicPlusMod ℓ E ν g = 1 := by
  have h_place : IsPlaceOver (familyPlace x u) u := isPlaceOver_familyPlace u
  obtain ⟨i, hi⟩ : ∃ i : I, IsFrob (familyPlace x u) u.q (toGalPlus E (x i).frob⁻¹) :=
    exists_isFrob_familyPlace hu
  obtain ⟨-, h_cyc : cyclotomicCharMod Ω (ℓ ^ ν) (x i).frob = 1⟩ := hx i
  have h_frob : toGalPlus E (x i).frob⁻¹ ∈ (cyclotomicPlusMod ℓ E ν).ker := by
    rw [MonoidHom.mem_ker, cyclotomicPlusMod_apply, ofGalPlus_toGalPlus, map_inv, h_cyc, inv_one]
  have h_inertia :
      inertiaGroup Gal(Ω/maximalRealSubfield E) (familyPlace x u) ≤ (cyclotomicPlusMod ℓ E ν).ker :=
    fun a ha ↦ cyclotomicPlusMod_eq_one ν
      (cyclotomicPlus_eq_one_of_mem_inertiaAbove ⟨u, hℓ, _, h_place, ha⟩)
  exact h_place.decompGroup_le hi (isOpen_ker_cyclotomicPlusMod ν) h_inertia h_frob hg

/-- The setting over `F` for the exponent `e` and a finite family `x` of `ν`-split places: the
module `ℤ/ℓ^ν` with the action `(cyc⁺) ^ (-e)`, the subgroup `G_ν`, and the set `S₀` of the primes
of `F` above `ℓ` or below `x`. The local condition at a prime `u` consists of the functions on the
decomposition group of `familyPlace x u` that vanish on its part in `ker cyc⁺` if `u` lies above
`ℓ`, and that vanish everywhere otherwise. -/
def kummerSetting [Finite I] {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i)) :
    RelationSetting (tateTwistPlus ℓ E ν e) (ℓ ^ ν) where
  nsmul_eq_zero a := by simp [CharP.cast_eq_zero]
  subgroup := cyclotomicKerPlus ℓ E ν
  apply_eq_of_mem g hg a := LinearMap.congr_fun
    (tateTwistPlus_ρ_eq_one e (cyclotomicKerPlus_le_ker ν hg)) a
  cyclotomicCharMod_eq_one _ hg := (mem_inf.1 hg).right
  notMem_of_isComplexConj hc hc_mem := notMem_range_toGalPlus hc (mem_inf.1 hc_mem).left
  ρ_eq_one_of_isComplexConj hc :=
    tateTwistPlus_ρ_eq_one e (cyclotomicPlusMod_eq_one ν
      (cyclotomicPlus_eq_one_of_isComplexConj hc))
  localPrimes := familyPrimes ℓ x
  unramified := by
    rintro g ⟨u, hu, hg⟩
    exact tateTwistPlus_ρ_eq_one e (cyclotomicPlusMod_eq_one ν
      (cyclotomicPlus_eq_one_of_mem_inertiaAbove
      ⟨u, fun hℓ ↦ hu (mem_familyPrimes.2 (.inl hℓ)), hg⟩))
  place := familyPlace x
  isPlaceOver := isPlaceOver_familyPlace
  allowed u := .pi {g | (ℓ : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal → cyclotomicPlus ℓ E g = 1} ⊥
  coboundary_le u hu := by
    rintro _ ⟨a, rfl⟩ g hg
    have g_triv : cyclotomicPlusMod ℓ E ν g = 1 := by
      by_cases hℓ : (ℓ : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
      exacts [cyclotomicPlusMod_eq_one ν (hg hℓ), cyclotomicPlusMod_eq_one_of_mem_decompGroup hx
        ((mem_familyPrimes.1 hu).resolve_left hℓ) hℓ g.property]
    change (tateTwistPlus ℓ E ν e).ρ g a - a = 0
    simp [tateTwistPlus_ρ_eq_one e g_triv]

/-- A Kummer map of exponent `e` off `T` for the family `x` of `ν`-split places: the restriction to
`G` of a relation off `T` in `kummerSetting e hx`, where `n ∈ ℤ/ℓ^ν` stands for the character
`a ↦ a n / ℓ ^ ν` of `ℤ/ℓ^ν`. It vanishes outside `G_ν`.

Let `M` be `ℤ/ℓ^ν` with the action `(cyc⁺) ^ (-e)`. A relation off `T`
(`New.RelationSetting.IsRelation`) is a locally constant homomorphism `y : G_ν → Hom(M, ℚ/ℤ)`,
extended by zero to `G_F`, with `y (g u g⁻¹) = cyc(g) · y u ∘ g⁻¹`, zero on inertia at the primes
outside `T`, and such that `∑ p, y(φ_p)(z(γ_p)) = 0`. This sum runs over any finite family of
distinct primes `p ∉ T` of `F` with Frobenius elements `φ_p ∈ G_ν` and tame generators `γ_p`, and
`z` is any cocycle in `M` that satisfies the local conditions at `S₀`, vanishes at complex
conjugations and is unramified off `S₀` and the `p`. These are properties of the restriction to
`G_ν` of a dual cocycle, with ramification allowed at the possibly larger set `T`. -/
def IsKummerMap [Finite I] {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (T : Finset (FinPlace (maximalRealSubfield E))) (ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)) : Prop :=
  ∃ y ∈ (kummerSetting e hx).relations T,
    ∀ (g : Gal(Ω/E)) (a : ZMod (ℓ ^ ν)), y (toGalPlus E g) a = ofZMod (ℓ ^ ν) (a * ψ g)

end Kummer

/-- A function `ψ : G → ℤ/ℓ^ν` has the Kummer type of exponent `e` if it is locally constant and, on
the kernel `G_ν` of the cyclotomic character modulo `ℓ ^ ν`, it is a homomorphism that complex
conjugation negates and that conjugation by `g ∈ G` multiplies by `cyc(g) ^ (e + 1)`. -/
structure HasKummerType (ν e : ℕ) (ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)) : Prop where
  /-- `ψ` is continuous for the discrete topology. -/
  isLocallyConstant : IsLocallyConstant ψ
  /-- `ψ` is a homomorphism on `G_ν`. -/
  map_mul {a b : Gal(Ω/E)} : cyclotomicCharMod Ω (ℓ ^ ν) a = 1 → cyclotomicCharMod Ω (ℓ ^ ν) b = 1 →
    ψ (a * b) = ψ a + ψ b
  /-- `ψᶜ = -ψ` on `G_ν`. -/
  map_conjGal {a : Gal(Ω/E)} : cyclotomicCharMod Ω (ℓ ^ ν) a = 1 → ψ (conjGal a) = -ψ a
  /-- `ψ (g a g⁻¹) = cyc(g) ^ (e + 1) ψ a` for `a ∈ G_ν`. -/
  map_conj (g : Gal(Ω/E)) {a : Gal(Ω/E)} : cyclotomicCharMod Ω (ℓ ^ ν) a = 1 →
    ψ (g * a * g⁻¹) = cyclotomicCharMod Ω (ℓ ^ ν) g ^ (e + 1) * ψ a

namespace HasKummerType

lemma map_one {ν e : ℕ} {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : HasKummerType ν e ψ) : ψ 1 = 0 := by
  simpa using hψ.map_mul (a := 1) (b := 1) (_root_.map_one _) (_root_.map_one _)

/-- A function of Kummer type takes inverses to negatives on the elements that fix the
`ℓ ^ ν`-th roots of unity. -/
lemma map_inv {ν e : ℕ} {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : HasKummerType ν e ψ) {a : Gal(Ω/E)}
    (ha : cyclotomicCharMod Ω (ℓ ^ ν) a = 1) : ψ a⁻¹ = -ψ a := by
  rw [eq_neg_iff_add_eq_zero, ← hψ.map_mul (by simp [ha]) ha, inv_mul_cancel, hψ.map_one]

/-- A function of Kummer type takes powers to multiples on the elements that fix the `ℓ ^ ν`-th
roots of unity. -/
lemma map_pow {ν e : ℕ} {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : HasKummerType ν e ψ) {a : Gal(Ω/E)}
    (ha : cyclotomicCharMod Ω (ℓ ^ ν) a = 1) (n : ℕ) : ψ (a ^ n) = n * ψ a := by
  induction n with
  | zero => simp [hψ.map_one]
  | succ n ih => rw [pow_succ, hψ.map_mul (by simp [ha]) ha, ih, Nat.cast_succ, add_one_mul]

end HasKummerType

/-- Let `ψ` be a Kummer map of exponent `e` off `T`: the value at `g ∈ G` of a relation `y` is the
character `a ↦ a ψ(g) / ℓ ^ ν` of `ℤ/ℓ^ν`. Then `ψ` is locally constant, and on `G_ν` it is a
homomorphism that complex conjugation negates and that conjugation by `g ∈ G` multiplies by
`cyc(g) ^ (e + 1)`. -/
theorem IsKummerMap.hasKummerType {ν e : ℕ} {I : Type} [Finite I] {x : I → FrobeniusDatum E}
    {hx : ∀ i : I, IsNuSplitPlace ν (x i)} {T : Finset (FinPlace (maximalRealSubfield E))}
    {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : IsKummerMap e hx T ψ) : HasKummerType ν e ψ := by
  obtain ⟨y, (hy : (kummerSetting e hx).IsRelation T y), hyψ⟩ := hψ
  have h_val (g : Gal(Ω/E)) : ofZMod (ℓ ^ ν) (ψ g) = y (toGalPlus E g) 1 := by rw [hyψ, one_mul]
  -- Conjugation by `g ∈ G_F` multiplies `ψ` by `cyc(g) cyc⁺(g) ^ e`.
  have h_conj (g : Gal(Ω/maximalRealSubfield E)) {a : Gal(Ω/E)}
      (ha : cyclotomicCharMod Ω (ℓ ^ ν) a = 1) : y (g * toGalPlus E a * g⁻¹) 1 =
        ofZMod (ℓ ^ ν) (cyclotomicCharMod Ω (ℓ ^ ν) g * cyclotomicPlusMod ℓ E ν g ^ e * ψ a) := by
    rw [hy.map_conj g _ (toGalPlus_mem_cyclotomicKerPlus_iff.2 ha), hyψ, tateTwistPlus_ρ]
    exact (map_nsmul (ofZMod (ℓ ^ ν)) _ _).symm.trans (congrArg _ (by simp [mul_assoc]))
  refine ⟨?_, fun {a b} ha hb ↦ ?_, fun {a} ha ↦ ?_, fun g a ha ↦ ?_⟩
  · refine .desc ψ (ofZMod (ℓ ^ ν)) ?_ ofZMod_injective
    rw [comp_def, funext h_val]
    exact (hy.isLocallyConstant.comp_continuous isOpenEmbedding_toGalPlus.continuous).comp (· 1)
  · apply ofZMod_injective
    rw [map_add, h_val, h_val, h_val, map_mul,
      hy.map_mul _ (toGalPlus_mem_cyclotomicKerPlus_iff.2 ha) _
        (toGalPlus_mem_cyclotomicKerPlus_iff.2 hb)]
    exact AddMonoidHom.add_apply _ _ _
  · -- At `c` the factor is `-1`.
    have h_cyc : cyclotomicPlusMod ℓ E ν (conjPlus E) = 1 :=
      cyclotomicPlusMod_eq_one ν (cyclotomicPlus_eq_one_of_isComplexConj isComplexConj_conjPlus)
    have h_conj_c : y (toGalPlus E (conjGal a)) 1 = ofZMod (ℓ ^ ν) (-ψ a) := by
      simpa [toGalPlus_conjGal, inv_eq_of_mul_eq_one_right conjPlus_mul_self, h_cyc,
        isComplexConj_conjPlus.cyclotomicCharMod_eq_neg_one] using h_conj (conjPlus E) ha
    exact ofZMod_injective ((h_val _).trans h_conj_c)
  · -- On `G` the factor is `cyc(g) ^ (e + 1)`.
    apply ofZMod_injective
    rw [h_val, map_mul, map_mul, map_inv, h_conj _ ha, cyclotomicPlusMod_apply, ofGalPlus_toGalPlus,
      show cyclotomicCharMod Ω (ℓ ^ ν) (toGalPlus E g) = cyclotomicCharMod Ω (ℓ ^ ν) g from rfl,
        pow_succ']

/-- Let `z` be a cocycle of `G` for `cyc ^ (-e)` modulo `ℓ ^ ν` that is invariant under complex
conjugation. Its extension `z⁺` to `G_F`, given by `z⁺ (g c) = z g`, is a cocycle for
`(cyc⁺) ^ (-e)`. -/
lemma comp_ofGalPlus_mem_Z1 {ν e : ℕ} {z : Gal(Ω/E) → ZMod (ℓ ^ ν)}
    (hz : z ∈ Z1 (charRep (ZMod (ℓ ^ ν)) (cyclotomicCharMod Ω (ℓ ^ ν) ^ e)⁻¹))
    (h_even : ∀ g : Gal(Ω/E), z (conjGal g) = z g) :
    z ∘ ofGalPlus ∈ Z1 (tateTwistPlus ℓ E ν e).ρ := by
  refine ⟨hz.1.comp continuous_ofGalPlus, fun g h ↦ ?_⟩
  obtain h_mul | h_mul := ofGalPlus_mul_eq_or g h <;>
    simp [h_mul, hz.2, h_even, charRep, cyclotomicPlusMod_apply]

/-- Let `Ω` be the algebraic closure of `ℚ`, `F` the maximal real subfield of the CM field `E`, `x`
a finite family of `ν`-split places, `S₀` the set of primes of `F` above `ℓ` or below `x`, and `P` a
set of primes of `F` disjoint from `S₀`. Let `z : Gal(Ω/E) → ℤ/ℓ^ν` be a cocycle for `cyc ^ (-e)`
that is invariant under complex conjugation `c`, unramified off `ℓ` and the primes above `P`, zero
on the part in `ker cyc` of the decomposition groups above `ℓ`, and zero at the Frobenius elements
of `x`. Extend `z` to `z⁺ = z ∘ ofGalPlus` on `G_F = Gal(Ω/F)` by `z⁺ (g c) = z g`, and `cyc` to
`cyc⁺` by `cyc⁺ c = 1`. Then `2 z⁺` lies in `(kummerSetting e hx).cocycles P`: it is a cocycle of
`G_F` in `ℤ/ℓ^ν` for `(cyc⁺) ^ (-e)`, is unramified off `S₀ ∪ P`, vanishes at complex conjugations,
and for `u ∈ S₀` vanishes on the decomposition group of the chosen place `familyPlace x u` (only on
its part in `ker cyc⁺` if `u` lies above `ℓ`). -/
lemma two_nsmul_comp_ofGalPlus_mem_cocycles {ν e : ℕ} {I : Type} [Finite I]
    {x : I → FrobeniusDatum E} {hx : ∀ i : I, IsNuSplitPlace ν (x i)} {z : Gal(Ω/E) → ZMod (ℓ ^ ν)}
    (hz : z ∈ Z1 (charRep (ZMod (ℓ ^ ν)) (cyclotomicCharMod Ω (ℓ ^ ν) ^ e)⁻¹))
    (h_even : ∀ g : Gal(Ω/E), z (conjGal g) = z g) {P : Set (FinPlace (maximalRealSubfield E))}
    (hP : ∀ u ∈ familyPrimes ℓ x, u ∉ P)
    (h_unr : ∀ g ∈ inertiaAbove (primeBelowPlus ⁻¹'
      (placesDividing (maximalRealSubfield E) ℓ ∪ P)ᶜ), z g = 0)
    (h_loc : ∀ g ∈ shaLocalSet ℓ E 1, z g = 0) (h_frob : ∀ i : I, z (x i).frob = 0) :
    2 • (z ∘ ofGalPlus) ∈ (kummerSetting e hx).cocycles P := by
  -- `X` is `z⁺` as a cocycle.
  let X : Z1 (tateTwistPlus ℓ E ν e).ρ := ⟨z ∘ ofGalPlus, comp_ofGalPlus_mem_Z1 hz h_even⟩
  obtain ⟨-, h_coc⟩ := X.2
  have h_ine (g : Gal(Ω/maximalRealSubfield E))
      (hg : g ∈ inertiaAbove (placesDividing _ ℓ ∪ P)ᶜ) : (2 • X).1 g = 0 := by
    simp [X, h_unr _ (ofGalPlus_mem_inertiaAbove hg)]
  -- For `g ∈ ker cyc⁺` we have `2 z⁺ g = z⁺ (g ^ 2)`.
  have h_sq (g : Gal(Ω/maximalRealSubfield E)) (hg : cyclotomicPlus ℓ E g = 1) :
      (2 • X).1 g = X.1 (g * g) := by
    rw [h_coc g g, tateTwistPlus_ρ_eq_one e (cyclotomicPlusMod_eq_one ν hg)]
    exact two_nsmul _
  have h_complex (c : Gal(Ω/maximalRealSubfield E)) (hc : IsComplexConj c) : (2 • X).1 c = 0 := by
    rw [h_sq c (cyclotomicPlus_eq_one_of_isComplexConj hc), hc.mul_self]
    simpa using h_coc 1 1
  -- Above `ℓ`: `g ^ 2` lies in `G`, in the decomposition group and in the kernel of `cyc`.
  have h_above {u : FinPlace (maximalRealSubfield E)}
      (hℓ : (ℓ : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal) {g : Gal(Ω/maximalRealSubfield E)}
      (hg : g ∈ decompGroup Gal(Ω/maximalRealSubfield E) (familyPlace x u))
      (hg_cyc : cyclotomicPlus ℓ E g = 1) : (2 • X).1 g = 0 := by
    obtain ⟨s, hs⟩ := mul_self_mem_of_index_two index_range_toGalPlus g
    have hs_dec : toGalPlus E s ∈ decompGroup Gal(Ω/maximalRealSubfield E) (familyPlace x u) := by
      simpa only [hs] using mul_mem hg hg
    have hs_cyc : cyclotomicChar Ω ℓ s = 1 := by
      rw [← ofGalPlus_toGalPlus s, ← cyclotomicPlus_apply, hs, map_mul, hg_cyc, one_mul]
    have hs_zero : z s = 0 :=
      h_loc s ⟨_, (isPlaceOver_familyPlace u).valuation_natCast_lt_one_iff.2 hℓ, hs_dec, hs_cyc⟩
    rw [h_sq g hg_cyc, ← hs]
    simpa [X] using hs_zero
  -- Below `x`: inertia and a Frobenius element topologically generate the decomposition group.
  have h_below {u : FinPlace (maximalRealSubfield E)} (hu : u ∈ familyPrimes ℓ x)
      (hℓ : (ℓ : 𝓞 (maximalRealSubfield E)) ∉ u.asIdeal) {g : Gal(Ω/maximalRealSubfield E)}
      (hg : g ∈ decompGroup Gal(Ω/maximalRealSubfield E) (familyPlace x u)) :
      (2 • X).1 g = 0 := by
    have h_place : IsPlaceOver (familyPlace x u) u := isPlaceOver_familyPlace u
    obtain ⟨i, hi⟩ := exists_isFrob_familyPlace ((mem_familyPrimes.1 hu).resolve_left hℓ)
    refine Z1.eq_zero_on_decompGroup (2 • X) h_place hi
      (fun a ha ↦ h_ine a ⟨u, not_or.2 ⟨hℓ, hP u hu⟩, _, h_place, ha⟩) ?_ g hg
    -- `map_inv` would move the inverse outside `toGalPlus`, hiding `ofGalPlus_toGalPlus`.
    simp [X, -map_inv, show z (x i).frob⁻¹ = 0 from (cocycleKer _ hz.2).inv_mem (h_frob i)]
  refine ⟨⟨(2 • X).2, ?_⟩, ?_, h_complex⟩
  · -- Off `S₀ ∪ P` the prime lies in particular off `ℓ` and `P`.
    rintro g ⟨u, hu, hg⟩
    exact h_ine g ⟨u, fun h ↦ hu (h.imp_left fun hℓ ↦ mem_familyPrimes.2 (.inl hℓ)), hg⟩
  rintro u hu ⟨g, hg⟩ hg_cyc
  by_cases hℓ : (ℓ : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
  exacts [h_above hℓ hg (hg_cyc hℓ), h_below hu hℓ hg]

omit [ThePrime ℓ] in
/-- Let `F` be the maximal real subfield of `E`. If a prime `t` of `E` lies above `ℓ`, or is the
place of one of the `w j` or a complex conjugate of one, then the prime of `F` below `t`
(`primeBelowPlus t`) lies above `ℓ` or is below the place of one of the `w j`. -/
lemma primeBelowPlus_mem_of_mem_conjClosure {J : Type} {w : J → FrobeniusDatum E} {t : FinPlace E}
    (ht : t ∈ placesDividing E ℓ ∪ Set.conjClosure (Set.range fun j : J ↦ (w j).place)) :
    primeBelowPlus t ∈ placesDividing (maximalRealSubfield E) ℓ ∪
      Set.range fun j : J ↦ primeBelowPlus (w j).place := by
  obtain hℓ | ⟨j, hj⟩ | ⟨j, hj⟩ : (ℓ : 𝓞 E) ∈ t.asIdeal ∨ (∃ j : J, (w j).place = t) ∨
      ∃ j : J, (w j).place = star t := by
    simpa [placesDividing] using ht
  · exact .inl (by simpa [placesDividing] using hℓ)
  · exact .inr ⟨j, by simp [hj]⟩
  · exact .inr ⟨j, by simp [hj, primeBelowPlus_star]⟩

/-- Let `x` and `w` be finite families of `ν`-split places and `T` a finite set of primes of `F`
containing those above `ℓ` or below `x`, such that the `w j` lie above distinct primes of `F`
outside `T`. Let `γ j` be tame generators at the `w j` normalised over `F`. Let `ψ` be a Kummer map
off `T`: it comes from an equivariant homomorphism from `G_ν` to the Cartier dual of a twist of
`ℤ/ℓ^ν` over `F`, unramified outside `T`, that satisfies reciprocity against the `ℤ/ℓ^ν`-valued
cocycles of `Gal(Ω/F)` in `(kummerSetting e hx).cocycles`. Let `z` be an even class of exponent `e`
for `w` that vanishes at the Frobenius elements of `x`. Then `∑ j, ψ(φ_j) · 2 z(γ_j) = 0`, where
`φ_j` is the Frobenius element of `w j`. -/
theorem IsKummerMap.sum_eq_zero {ν e : ℕ} {I : Type} [Finite I] {x : I → FrobeniusDatum E}
    {hx : ∀ i : I, IsNuSplitPlace ν (x i)} {T : Finset (FinPlace (maximalRealSubfield E))}
    {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : IsKummerMap e hx T ψ) (hT : familyPrimes ℓ x ⊆ T)
    {J : Type} [Fintype J] {w : J → FrobeniusDatum E} (hw : ∀ j : J, IsNuSplitPlace ν (w j))
    (w_inj : Injective fun j : J ↦ primeBelowPlus (w j).place)
    (w_notMem : ∀ j : J, primeBelowPlus (w j).place ∉ T) {γ : J → Gal(Ω/E)}
    (hγ : ∀ j : J, IsTameGeneratorFor (K := maximalRealSubfield E) (ℓ ^ ν) (w j).valuationSubring
      (toGalPlus E (γ j)))
    {O : CoeffRing ℓ} {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)}
    (hz : z ∈ evenClasses O (Set.range fun j : J ↦ (w j).place) ν e)
    (h_frob : ∀ i : I, z (x i).frob = 0) :
    ∑ j : J, (ψ (w j).frob).val • 2 • z (γ j) = 0 := by
  -- The additive maps `f` to `ℤ/ℓ^ν` separate points, so we may replace `z` by `f ∘ z`.
  refine eq_zero_of_forall_mem_Z1_of_mem_evenClasses hz fun f hf ↦ ?_
  obtain ⟨⟨-, h_unr, -⟩, h_even, h_loc⟩ := hz.imp_left mem_selmerModule_iff.1
  have h_mem : 2 • ((fun g ↦ f (z g)) ∘ ofGalPlus) ∈
      (kummerSetting e hx).cocycles (Set.range fun j ↦ primeBelowPlus (w j).place) := by
    refine two_nsmul_comp_ofGalPlus_mem_cocycles hf (by simp [h_even]) ?_
      (fun g ⟨t, ht, h_inertia⟩ ↦ ?_) (fun g hg ↦ by simp [h_loc g hg]) (by simp [h_frob])
    · rintro u hu ⟨j, rfl⟩
      exact w_notMem j (hT hu)
    · simp [h_unr g ⟨t, fun h ↦ ht (primeBelowPlus_mem_of_mem_conjClosure h), h_inertia⟩]
  -- The primes below the `w j` are split, with the arithmetic Frobenius elements `φ_j⁻¹`.
  let p (j : J) : SplitPrime (ℓ ^ ν) (kummerSetting e hx).subgroup :=
    { prime := primeBelowPlus (w j).place
      place := (w j).valuationSubring
      isPlaceOver := (w j).isPlaceOver.isPlaceOver_below
      frob := toGalPlus E (w j).frob⁻¹
      isFrob := by simpa [q_primeBelowPlus, isFrob_toGalPlus_iff, -map_inv] using (w j).isFrob_inv
      frob_mem := toGalPlus_mem_cyclotomicKerPlus_iff.2 (by simpa using (hw j).2)
      tameGenerator := toGalPlus E (γ j)
      isTameGeneratorFor := hγ j }
  have h_inv (j : J) : ψ (w j).frob⁻¹ = -ψ (w j).frob := hψ.hasKummerType.map_inv (hw j).2
  obtain ⟨y, (hy : (kummerSetting e hx).IsRelation T y), hyψ⟩ := hψ
  have h_term (j : J) : y (p j).frob ((2 • (fun g ↦ f (z g)) ∘ ofGalPlus) (p j).tameGenerator) =
      ofZMod (ℓ ^ ν) (2 • f (z (γ j)) * ψ (w j).frob⁻¹) := by
    change y (toGalPlus E (w j).frob⁻¹) (2 • f (z (ofGalPlus (toGalPlus E (γ j))))) = _
    rw [ofGalPlus_toGalPlus, hyψ]
  have h_sum : ∑ j, 2 • f (z (γ j)) * ψ (w j).frob⁻¹ = 0 := by
    apply ofZMod_injective
    rw [map_sum, map_zero]
    exact (sum_congr rfl fun j _ ↦ (h_term j).symm).trans
      (hy.sum_eq_zero p w_inj w_notMem _ h_mem)
  suffices h_image : ∑ j, (ψ (w j).frob).val • 2 • f (z (γ j)) = 0 by
    simpa only [map_sum, map_nsmul] using h_image
  simpa [h_inv, mul_comm] using h_sum

/-- At a prime of degree one of `E` there is a tame generator in `G` normalised over `F`: an element
of inertia that moves an `m`-th root of a uniformiser of `F` by the fixed root of unity. -/
lemma exists_isTameGeneratorFor_toGalPlus (m : ℕ) [NeZero m] (w : FrobeniusDatum E) :
    ∃ γ : Gal(Ω/E),
      IsTameGeneratorFor (K := maximalRealSubfield E) m w.valuationSubring (toGalPlus E γ) := by
  have h_place := w.isPlaceOver.isPlaceOver_below (K := maximalRealSubfield E)
  obtain ⟨δ, hδ⟩ := exists_isTameGeneratorFor Gal(Ω/maximalRealSubfield E) m h_place
  obtain ⟨γ, rfl⟩ := inertiaGroup_le_range_toGalPlus _ h_place hδ.1
  exact ⟨γ, hδ⟩

/-- Let `w` consist of a prime of `E` of prime norm not above `ℓ`, a place of `Ω` above it and a
Frobenius element, and let `γ ∈ G` be a tame generator at that place, normalised over `F`. Let `O`
be the ring of integers of a finite Galois extension of `ℚ_ℓ` and `z` an even class for `S`: a
locally constant cocycle of `G` in `(O/ℓ^ν)(-e)`, invariant under complex conjugation, unramified
off `ℓ`, `S` and `S̄`, and zero on the elements of `ker cyc` in decomposition groups above `ℓ`; its
values are vectors of length one (indexed by `Unit`) over `QuotSpan (ℓ ^ ν) = O/ℓ^ν`. Then the value
of `z` at an element `τ` of the inertia group at that place is a multiple of `z γ`. -/
lemma exists_apply_eq_nsmul_of_mem_evenClasses {ν e : ℕ} {w : FrobeniusDatum E}
    (hℓ : (ℓ : 𝓞 E) ∉ w.place.asIdeal) {γ τ : Gal(Ω/E)}
    (hγ : IsTameGeneratorFor (K := maximalRealSubfield E) (ℓ ^ ν) w.valuationSubring
      (toGalPlus E γ))
    (hτ : τ ∈ inertiaGroup Gal(Ω/E) w.valuationSubring) {O : CoeffRing ℓ} {S : Set (FinPlace E)}
    {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)} (hz : z ∈ evenClasses O S ν e) :
    ∃ n : ℕ, z τ = n • z γ := by
  have h_place : IsPlaceOver w.valuationSubring (primeBelowPlus w.place) :=
    w.isPlaceOver.isPlaceOver_below
  have h_notMem : ↑(ℓ ^ ν) ∉ (primeBelowPlus w.place).asIdeal :=
    fun h ↦ hℓ (w.place.isPrime.mem_of_pow_mem ν (by simpa using h))
  let : Module (ZMod (ℓ ^ ν)) (Unit → QuotSpan (ℓ ^ ν : ↑O)) :=
    AddCommGroup.zmodModule fun _ ↦ funext fun _ ↦ nsmul_quot_eq_zero rfl.dvd _
  obtain ⟨h_coc, -, -, h_locallyConstant⟩ := mem_selmerModule_iff.1 hz.1
  have h_add : ∀ g ∈ inertiaGroup Gal(Ω/maximalRealSubfield E) w.valuationSubring,
      ∀ k ∈ inertiaGroup Gal(Ω/maximalRealSubfield E) w.valuationSubring,
      z (ofGalPlus (g * k)) = z (ofGalPlus g) + z (ofGalPlus k) := by
    intro g hg k hk
    obtain ⟨a, rfl⟩ := inertiaGroup_le_range_toGalPlus _ h_place hg
    obtain ⟨b, rfl⟩ := inertiaGroup_le_range_toGalPlus _ h_place hk
    simp [← map_mul, h_coc, tateTwist, cyclotomicInv,
      cyclotomicChar_eq_one_of_mem_inertiaAbove ⟨w.place, hℓ, _, w.isPlaceOver, hg⟩]
  simpa using hγ.exists_apply_eq_nsmul h_place h_notMem (τ := toGalPlus E τ) hτ
    (fun g ↦ z (ofGalPlus g)) (h_locallyConstant.comp_continuous continuous_ofGalPlus) h_add

/-- The reciprocity law `New.Selmer.IsKummerMap.sum_eq_zero` with one term left. Let `x` and `w` be
finite families of `ν`-split places. Let `T` contain the primes of `F` above `ℓ` or below `x`, and
let the `w i` lie above distinct primes of `F` outside `T`. Let `ψ` be a Kummer map off `T` that
vanishes at the Frobenius elements of `w` except at `w j`. Let `O` be the ring of integers of a
finite Galois extension of `ℚ_ℓ` and `z` an even class: a cocycle in `(O/ℓ^ν)(-e)` that is invariant
under complex conjugation, unramified off `ℓ`, the `w i` and their conjugates, and zero on the
elements of `ker cyc` in decomposition groups above `ℓ`. Suppose that `z` vanishes at the Frobenius
elements of `x`. Then every `n` divisible by `2 ψ(φ_j)` in `ℤ/ℓ^ν`, with `φ_j` the Frobenius element
at `w j`, kills the value of `z` at the chosen generator `(w j).isPlaceOver.tameGenerator` of tame
inertia at `w j`. -/
theorem IsKummerMap.nsmul_apply_tameGenerator_eq_zero {ν e : ℕ} {I : Type} [Finite I]
    {x : I → FrobeniusDatum E} {hx : ∀ i : I, IsNuSplitPlace ν (x i)}
    {T : Finset (FinPlace (maximalRealSubfield E))}
    {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : IsKummerMap e hx T ψ) (hT : familyPrimes ℓ x ⊆ T)
    {J : Type} [Fintype J] {w : J → FrobeniusDatum E} (hw : ∀ i : J, IsNuSplitPlace ν (w i))
    (w_inj : Injective fun i : J ↦ primeBelowPlus (w i).place)
    (w_notMem : ∀ i : J, primeBelowPlus (w i).place ∉ T)
    {j : J} (h_zero : ∀ i : J, i ≠ j → ψ (w i).frob = 0)
    {O : CoeffRing ℓ} {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)}
    (hz : z ∈ evenClasses O (Set.range fun i : J ↦ (w i).place) ν e)
    (h_frob : ∀ i : I, z (x i).frob = 0)
    {n : ℕ} (hn : 2 * ψ (w j).frob ∣ n) : n • z (w j).isPlaceOver.tameGenerator = 0 := by
  choose γ hγ using fun i : J ↦ exists_isTameGeneratorFor_toGalPlus (ℓ ^ ν) (w i)
  have h_term : (ψ (w j).frob).val • 2 • z (γ j) = 0 := by
    rw [← hψ.sum_eq_zero hT hw w_inj w_notMem hγ hz h_frob, Fintype.sum_eq_single j]
    exact fun i hi ↦ by simp [h_zero i hi]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, z (w j).isPlaceOver.tameGenerator = m • z (γ j) :=
    exists_apply_eq_nsmul_of_mem_evenClasses (hw j).1 (hγ j) (w j).isPlaceOver.tameGenerator.2 hz
  -- The values of `z` form a module over `ℤ/ℓ^ν`, in which `n = 2 ψ(φ_j) a`.
  let : Module (ZMod (ℓ ^ ν)) (Unit → QuotSpan (ℓ ^ ν : ↑O)) :=
    AddCommGroup.zmodModule fun _ ↦ funext fun _ ↦ nsmul_quot_eq_zero rfl.dvd _
  obtain ⟨a, ha⟩ : ∃ a : ZMod (ℓ ^ ν), (n : ZMod (ℓ ^ ν)) = 2 * ψ (w j).frob * a := hn
  have h_kill : (2 * ψ (w j).frob) • z (γ j) = 0 := by
    rwa [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ ν)), ZMod.natCast_zmod_val,
      ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ ν)), smul_smul, Nat.cast_ofNat, mul_comm] at h_term
  rw [hm, smul_comm, ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ ν)) n, ha, mul_comm, mul_smul, h_kill,
    smul_zero, smul_zero]

/-- The reduction `G_ν → 𝔽_ℓ` of a map to `ℤ/ℓ^ν`. -/
def reductionModL {ν : ℕ} (ψ : Gal(Ω/E) → ZMod (ℓ ^ ν))
    (g : (cyclotomicCharMod (Γ := Gal(Ω/E)) Ω (ℓ ^ ν)).ker) : ZMod ℓ :=
  (ψ g).cast

/-- The space spanned by the reductions `G_ν → 𝔽_ℓ` of the Kummer maps of exponent `e` for the
family `x`, off `T`. -/
def kummerReductions {ν : ℕ} (e : ℕ) {I : Type} [Finite I] {x : I → FrobeniusDatum E}
    (hx : ∀ i : I, IsNuSplitPlace ν (x i)) (T : Finset (FinPlace (maximalRealSubfield E))) :
    Submodule (ZMod ℓ) ((cyclotomicCharMod (Γ := Gal(Ω/E)) Ω (ℓ ^ ν)).ker → ZMod ℓ) :=
  Submodule.span (ZMod ℓ) (reductionModL '' {ψ | IsKummerMap e hx T ψ})

/-- Elements of `ℤ/ℓ^ν` with the same image in `ℤ/ℓ` differ by a multiple of `ℓ`. -/
lemma natCast_dvd_sub_of_cast_eq {ν : ℕ} {a b : ZMod (ℓ ^ ν)}
    (h : (a.cast : ZMod ℓ) = b.cast) : (ℓ : ZMod (ℓ ^ ν)) ∣ a - b := by
  rw [← ZMod.natCast_val, ← ZMod.natCast_val, ZMod.natCast_eq_natCast_iff] at h
  simpa using map_dvd (Int.castRingHom (ZMod (ℓ ^ ν))) h.symm.dvd

/-- Let `x` be a finite family of `ν`-split places, and let `y` be a relation off the finite set `T`
of primes of the maximal real subfield `F`: an equivariant homomorphism from `G_ν` to the characters
`ℤ/ℓ^ν → ℚ/ℤ`, extended by zero to `G_F = Gal(Ω/F)`, unramified outside `T` and subject to a
reciprocity law. There is a function `ψ : G → ℤ/ℓ^ν` such that the value of `y` at each `g ∈ G` is
the character `a ↦ a ψ(g) / ℓ ^ ν`. -/
lemma exists_apply_toGalPlus_eq_ofZMod {ν : ℕ} (e : ℕ) {I : Type} [Finite I]
    {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (T : Finset (FinPlace (maximalRealSubfield E))) (y : (kummerSetting e hx).relations T) :
    ∃ ψ : Gal(Ω/E) → ZMod (ℓ ^ ν), ∀ (g : Gal(Ω/E)) (a : ZMod (ℓ ^ ν)),
      y.val (toGalPlus E g) a = ofZMod (ℓ ^ ν) (a * ψ g) := by
  have h_tors (g : Gal(Ω/E)) : ℓ ^ ν • y.val (toGalPlus E g) 1 = 0 := by
    simp [← map_nsmul, CharP.cast_eq_zero]
  choose ψ hψ using fun g ↦ exists_ofZMod (h_tors g)
  refine ⟨ψ, fun g a ↦ ?_⟩
  -- Both sides are additive in `a` and agree at `1`.
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [← nsmul_eq_mul, map_nsmul, hψ, ← nsmul_one, map_nsmul]
  rfl

/-- Let `ℓ` be a prime, `E` a CM field that contains a primitive `5040`-th root of unity, `G_ν` the
subgroup of `Gal(Ω/E)` that fixes the `ℓ ^ ν`-th roots of unity, `x` a finite family of `ν`-split
places and `T` a finite set of primes of the maximal real subfield `F`. The Kummer maps
`ψ : Gal(Ω/E) → ℤ/ℓ^ν` of exponent `e` off `T` come from the equivariant homomorphisms from `G_ν` to
the Cartier dual of a twist of `ℤ/ℓ^ν` over `F` that are unramified outside `T` and satisfy a
reciprocity law. Then `kummerReductions e hx T`, the span over `𝔽_ℓ` of the functions
`ψ mod ℓ : G_ν → 𝔽_ℓ`, is finite. -/
lemma finite_kummerReductions {ν : ℕ} (e : ℕ) {I : Type} [Finite I]
    {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (T : Finset (FinPlace (maximalRealSubfield E))) : Finite (kummerReductions e hx T) := by
  -- A relation determines its Kummer map, and there are finitely many relations.
  choose ψ hψ using exists_apply_toGalPlus_eq_ofZMod e hx T
  have h_fin : {ψ' | IsKummerMap e hx T ψ'}.Finite := by
    refine (Set.finite_range ψ).subset ?_
    rintro ψ' ⟨y, hy, hyψ⟩
    refine ⟨⟨y, hy⟩, funext fun g ↦ ofZMod_injective ?_⟩
    rw [← one_mul (ψ _ g), ← one_mul (ψ' g)]
    exact (hψ ⟨y, hy⟩ g 1).symm.trans (hyψ g 1)
  have : Module.Finite (ZMod ℓ) (kummerReductions e hx T) := .span_of_finite _ (h_fin.image _)
  exact Module.finite_of_finite (ZMod ℓ)

/-- Let `G_ν` be the subgroup of `G = Gal(Ω/E)` that fixes the `ℓ ^ ν`-th roots of unity, `x` a
finite family of `ν`-split places and `T` a finite set of primes of the maximal real subfield `F`.
Let `M*` be the group of characters `ℤ/ℓ^ν → ℚ/ℤ`. A relation off `T` is an equivariant homomorphism
`y : G_ν → M*`, extended by zero to `Gal(Ω/F)`, unramified outside `T` and subject to a reciprocity
law; its Kummer map `ψ : G → ℤ/ℓ^ν` is given by `y g a = a ψ(g) / ℓ ^ ν`. There are no more
reductions `Gal(Ω/F) → M* / ℓ M*` of relations than elements in the `𝔽_ℓ`-span of the reductions
`G_ν → 𝔽_ℓ` of Kummer maps, because the reduction of `y` is determined by that of `ψ`. -/
lemma card_reductions_le {ν : ℕ} (e : ℕ) {I : Type} [Finite I]
    {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (T : Finset (FinPlace (maximalRealSubfield E))) :
    Nat.card ((kummerSetting e hx).reductions ℓ T) ≤ Nat.card (kummerReductions e hx T) := by
  have : Finite (kummerReductions e hx T) := finite_kummerReductions e hx T
  choose ψ hψ using exists_apply_toGalPlus_eq_ofZMod e hx T
  -- Choose a relation for each reduction; taking the reduction of its Kummer map is injective.
  have h_lift (f : (kummerSetting e hx).reductions ℓ T) :
      ∃ y : (kummerSetting e hx).relations T, ∀ σ, Submodule.Quotient.mk (y.1 σ) = f.1 σ := by
    obtain ⟨y, hy, h_red⟩ := Submodule.mem_map.1 f.2
    exact ⟨⟨y, hy⟩, congr_fun h_red⟩
  choose y h_red using h_lift
  have h_kummer (f : (kummerSetting e hx).reductions ℓ T) : IsKummerMap e hx T (ψ (y f)) :=
    ⟨(y f).1, (y f).2, hψ (y f)⟩
  let reduction (f : (kummerSetting e hx).reductions ℓ T) : kummerReductions e hx T :=
    ⟨reductionModL (ψ (y f)), Submodule.subset_span (Set.mem_image_of_mem _ (h_kummer f))⟩
  refine Nat.card_le_card_of_injective reduction fun f f' h ↦ Subtype.ext (funext fun σ ↦ ?_)
  rw [← h_red f σ, ← h_red f' σ, Submodule.Quotient.eq]
  by_cases hσ : σ ∈ (kummerSetting e hx).subgroup
  · -- On `G_ν` the two Kummer maps differ by `ℓ t`.
    obtain ⟨g, rfl⟩ := hσ.1
    have h_cast : ((ψ (y f) g).cast : ZMod ℓ) = (ψ (y f') g).cast :=
      congr_fun (congr_arg Subtype.val h) ⟨g, toGalPlus_mem_cyclotomicKerPlus_iff.1 hσ⟩
    obtain ⟨t, ht⟩ := natCast_dvd_sub_of_cast_eq h_cast
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨(ofZMod (ℓ ^ ν)).comp (.mulRight t), Submodule.mem_top, CharacterModule.ext _ fun a ↦ ?_⟩
    change ofZMod (ℓ ^ ν) (ℓ * a * t) = (y f).1 (toGalPlus E g) a - (y f').1 (toGalPlus E g) a
    rw [hψ (y f), hψ (y f'), mul_comm _ a, mul_assoc, ← ht, mul_sub, map_sub]
    rfl
  · simp [(y f).2.eq_zero_of_notMem σ hσ, (y f').2.eq_zero_of_notMem σ hσ]

/-- Let `ℓ` be a prime, `ν > 0`, `E` a CM field in the algebraic closure `Ω` of `ℚ` that contains a
primitive `5040`-th root of unity, `F` its maximal real subfield and `G_ν` the subgroup of
`G = Gal(Ω/E)` that fixes the `ℓ ^ ν`-th roots of unity. Let the `x i` be finitely many `ν`-split
places above distinct primes of `F`, and let `E` have at least four infinite places. A Kummer map
`ψ : G → ℤ/ℓ^ν` of exponent `e` off `T` comes from an equivariant homomorphism from `G_ν` to the
Cartier dual of a twist of `ℤ/ℓ^ν` over `F`, unramified outside `T` and subject to a reciprocity
law; conjugation by `g ∈ G` multiplies it by `cyc(g) ^ (e + 1)`. Then there is a finite set `T` of
primes of `F`, containing those above `ℓ` or below the `x i`, such that the functions
`ψ mod ℓ : G_ν → 𝔽_ℓ` span a space of dimension greater than the number of the `x i`. -/
theorem exists_card_lt_finrank_kummerReductions {ν : ℕ} (hν : 0 < ν) (e : ℕ)
    (h_places : 4 ≤ card (InfinitePlace E)) {I : Type} [Fintype I] {x : I → FrobeniusDatum E}
    (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (x_inj : Injective fun i : I ↦ primeBelowPlus (x i).place) :
    ∃ T : Finset (FinPlace (maximalRealSubfield E)), familyPrimes ℓ x ⊆ T ∧
      card I < Module.finrank (ZMod ℓ) (kummerReductions e hx T) := by
  classical
  let D := kummerSetting e hx
  have hℓ_dvd : ℓ ∣ ℓ ^ ν := dvd_pow_self ℓ hν.ne'
  -- The kernel of `cyc⁺` lies in `G_ν ∪ G_ν c`.
  have h_ker (g : Gal(Ω/maximalRealSubfield E)) (hg : cyclotomicPlus ℓ E g = 1) :
      g ∈ D.subgroup ∨ g * conjPlus E ∈ D.subgroup := by
    have h_mem : toGalPlus E (ofGalPlus g) ∈ D.subgroup :=
      toGalPlus_mem_cyclotomicKerPlus_iff.2
        ((cyclotomicPlusMod_apply ν g).symm.trans (cyclotomicPlusMod_eq_one ν hg))
    rw [toGalPlus_ofGalPlus] at h_mem
    split at h_mem <;> simp [h_mem]
  have h_torsion : Nat.card {a : tateTwistPlus ℓ E ν e // ℓ • a = 0} = ℓ :=
    (IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod (ℓ ^ ν)) ℓ).trans
      (by simp [Nat.gcd_eq_right hℓ_dvd])
  obtain ⟨T, hT, h_count⟩ : ∃ T : Finset (FinPlace (maximalRealSubfield E)),
      familyPrimes ℓ x ⊆ T ∧
        ℓ ^ (#{u ∈ D.localPrimes | ↑ℓ ∉ u.1} + 1) ≤ Nat.card (D.reductions ℓ T) :=
    -- The last argument is the definition of the local conditions above `ℓ` in `kummerSetting`.
    D.exists_pow_le_card_reductions hℓ_dvd (by rwa [card_infinitePlace_eq_card_infinitePlace E])
      continuous_cyclotomicPlus (fun g ↦ four_dvd_cyclotomicChar_sub_one _) h_ker h_torsion fun _ ↦
        rfl
  refine ⟨T, hT, ?_⟩
  have h_primes : card I ≤ #{u ∈ D.localPrimes | ↑ℓ ∉ u.1} :=
    card_le_card_of_injOn (fun i ↦ primeBelowPlus (x i).place)
      (by simp [D, kummerSetting, mem_familyPrimes, (hx _).1]) x_inj.injOn
  have h_pow : ℓ ^ (card I + 1) ≤ ℓ ^ Module.finrank (ZMod ℓ) (kummerReductions e hx T) := calc
    _ ≤ ℓ ^ (#{u ∈ D.localPrimes | ↑ℓ ∉ u.1} + 1) := Nat.pow_le_pow_right NeZero.one_le (by gcongr)
    _ ≤ Nat.card (D.reductions ℓ T) := h_count
    _ ≤ Nat.card (kummerReductions e hx T) := card_reductions_le e hx T
    _ = _ := have := finite_kummerReductions e hx T
      by simp [Module.natCard_eq_pow_finrank (K := ZMod ℓ)]
  exact (Nat.pow_le_pow_iff_right (Fact.out : ℓ.Prime).one_lt).1 h_pow

end New.Selmer

end
