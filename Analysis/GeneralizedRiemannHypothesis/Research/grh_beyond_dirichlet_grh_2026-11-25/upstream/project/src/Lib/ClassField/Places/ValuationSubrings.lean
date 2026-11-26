import Lib.Adelic.Adeles.Basic
import Lib.ClassField.Places.ProfiniteGalois
import Lib.General.Algebra.AdicCompletion
import Lib.General.Topology

/-!
# Valuation subrings over primes, primes from p-adic embeddings, and the efg formula

Places of an extension `Ω` of a number field `K` are treated as valuation subrings of `Ω` lying over
primes of `𝓞 K`. An embedding `σ` of a number field `E` into an ultrametric normed field over `ℚ_p`
induces a prime of `E` above `p` and extends to the finite adeles of `E`. The formula
`g * (e * f) = [L : K]` is restated in terms of finite places.

## Main definitions and results

* `New.IsPlaceOver.isEquiv`, `New.IsPlaceOver.unique`: `A` induces the `v`-adic valuation up to
  equivalence, and determines `v`.
* `New.FinPlace.isPlaceOver_placeOver`, `New.exists_isPlaceOver_of_val_ne_one`: every `v` has a
  valuation subring of `New.Ω` over it; for `Ω/K` algebraic, every `A` whose valuation is not `1` at
  some nonzero element lies over some `v`.
* `New.finite_ramified`: almost all inertia groups lie in a given open subgroup of `Γ`.
* `New.IsPlaceOver.exists_smul`: the Galois group `Γ` is transitive on the `A` over `v`.
* `New.placeOfEmb`: the prime induced by `σ`; it consists of the integers with `‖σ x‖ < 1`
  (`New.mem_placeOfEmb`) and contains `p` (`New.natCast_mem_placeOfEmb`).
* `New.exists_placeOfEmb_extension`, `New.placeOfEmbExtension`: `σ` extends continuously to the
  completion of `E` at that prime.
* `New.adeleExtension`: the resulting ring homomorphism on finite adeles; it is continuous, extends
  `σ` and sends integral adeles to elements of norm at most one (`New.norm_adeleExtension_le_one`).

Notions from other files:
* `New.FinPlace K`: a nonzero prime of `𝓞 K`; `v.q` is its absolute norm; a `New.ClosurePlace` is a
  valuation subring of `New.Ω`, the algebraic closure of `ℚ`.
* `A x`, for a valuation subring `A` of `Ω`: the value `A.valuation x`; for `x : K`,
  `valuationVia K A x` is `A.valuation (algebraMap K Ω x)`.
* `New.IsProGalois Γ K Ω`: `Γ` is a profinite Galois group of `Ω / K` with open stabilisers.
* `New.inertiaGroup Γ A`: the `σ` in `Γ` that stabilise `A` and act trivially modulo its maximal
  ideal.
* `New.PadicField`: a normed field that is a normed algebra over `ℚ_p`, not necessarily complete.

## Relation to the literature

Known; see `Lib.ClassField.Places.LocalFields` for sources.
-/

noncomputable section

/-!
## Places of extensions of number fields as valuation subrings over primes

Places of an extension `Ω` of a number field `K` are handled as valuation subrings `A` of `Ω`.
`New.IsPlaceOver A v` says that an integer of `K` is in the maximal ideal of `A` exactly when it
lies in the prime `v`. The tool is the centre `New.Cohomology.centrePrime K A`, a prime ideal of
`𝓞 K`.
-/

section Places

open New NumberField IsDedekindDomain.HeightOneSpectrum Pointwise Ideal Cohomology WithZero
  Valuation Nat IsScalarTower RingOfIntegers IsLocalRing Algebra IsGaloisGroup
variable {K Ω Γ : Type*} [Field K] [Field Ω] [Algebra K Ω] [Group Γ] [MulSemiringAction Γ Ω]
  {A A' : ValuationSubring Ω} {w : Valuation K ℤᵐ⁰}

namespace New.Cohomology

/-! ### The centre of a valuation subring -/

variable (A) in
/-- The image in `Ω` of an integer of `K` lies in every valuation subring `A` of `Ω`: it is
integral over `ℤ`, and a valuation subring is integrally closed. -/
theorem algebraMap_ringOfIntegers_mem (x : 𝓞 K) : algebraMap K Ω x ∈ A :=
  Subring.isIntegrallyClosedIn_iff.mp inferInstance x.prop.algebraMap.tower_top

/-- The centre of the valuation subring `A` on `K`: the ideal of those integers of `K` whose image
in `Ω` lies in the maximal ideal of `A`. -/
def centrePrime (K : Type*) [Field K] [Algebra K Ω] (A : ValuationSubring Ω) : Ideal (𝓞 K) :=
  (maximalIdeal A).comap
    (((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A (algebraMap_ringOfIntegers_mem A))

lemma mem_centrePrime {x : 𝓞 K} : x ∈ centrePrime K A ↔ valuationVia K A x < 1 :=
  A.valuation_lt_one_iff _

/-- For a tower `K ⊆ k ⊆ Ω`, the valuation of `A` on `k` extends the one on `K` (here
`algebraMap K _` is the map from `K` to `Ω`). -/
instance {k : Type*} [Field k] [Algebra K k] [Algebra k Ω] [IsScalarTower K k Ω] :
    (A.valuation.comap <| algebraMap K _).HasExtension (A.valuation.comap (algebraMap k Ω)) := by
  constructor
  rw [algebraMap_eq K k Ω]
  exact Valuation.IsEquiv.refl

/-- If `A` induces on `K` a valuation equivalent to `w`, and `w` takes the value `exp (-1)`, then
the uniformisers for `A` in `K` (the `π` with `valuationVia K A x < 1 ↔ valuationVia K A
x ≤ valuationVia K A π` for all `x : K`) are the elements with `w π = exp (-1)`. -/
theorem isUniformiser_iff_of_isEquiv (h_equiv : (A.valuation.comap (algebraMap K Ω)).IsEquiv w)
    (h_exists : ∃ p : K, w p = exp (-1)) {π : K} :
    IsUniformiser A π ↔ w π = exp (-1) := by
  -- Both sides of `IsUniformiser` transfer to `w`, where `w x < 1` means `w x ≤ exp (-1)`.
  have h_lt (x : K) : A.valuation (algebraMap K Ω x) < 1 ↔ w x ≤ exp (-1) :=
    h_equiv.lt_one_iff_lt_one.trans (lt_mul_exp_iff_le (exp_ne_zero (a := -1)))
  have h_le (x : K) :
      A.valuation (algebraMap K Ω x) ≤ A.valuation (algebraMap K Ω π) ↔ w x ≤ w π :=
    h_equiv x π
  simp only [IsUniformiser, valuationVia, h_lt, h_le]
  obtain ⟨p, hp⟩ := h_exists
  refine ⟨fun h_unif ↦ ?_, fun h_π x ↦ by rw [h_π]⟩
  -- Test with `x = π` and with `x = p`, of valuation `exp (-1)`.
  have h_π_le : w π ≤ exp (-1) := (h_unif π).mpr le_rfl
  have h_le_π : exp (-1) ≤ w π := hp.ge.trans ((h_unif p).mp hp.le)
  exact le_antisymm h_π_le h_le_π

end Cohomology

instance : (centrePrime K A).IsPrime := .comap _

variable {v v' : FinPlace K} (h : IsPlaceOver A v)
  {L : Type*} [Field L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]

namespace IsPlaceOver

/-! ### Properties of a valuation subring over a prime -/

/-- As `v` is maximal, `A` lies over `v` as soon as its centre contains `v`. -/
theorem of_le_centrePrime [NumberField K]
    (h_le : v.asIdeal ≤ centrePrime K A) : IsPlaceOver A v := by
  -- The maximal ideal `v` lies in the proper ideal `centrePrime K A`, so the two are equal.
  have h_eq : v.asIdeal = centrePrime K A := v.isMaximal.eq_of_le IsPrime.ne_top' h_le
  exact fun x ↦ by rw [h_eq, mem_centrePrime]

/-- If `A` lies over a prime `u` of `L`, it lies over the prime of `K` below `u`. -/
lemma isPlaceOver_below {u : FinPlace L} (hu : IsPlaceOver A u) : IsPlaceOver A (u.below K) :=
  fun x ↦ by simpa [algebraMap_apply K L Ω] using hu (mapRingHom (algebraMap K L) x)

/-- If `A` lies over `v`, then its centre in `𝓞 Ω` lies over the prime `v` of `𝓞 K`. -/
lemma centrePrime_liesOver (h : IsPlaceOver A v) : (centrePrime Ω A).LiesOver v.asIdeal :=
  ⟨(ext fun x ↦ mem_centrePrime.trans (h x)).symm⟩

/-- If `A` lies over `v`, its valuation restricted to `K` is equivalent to the `v`-adic one. -/
lemma isEquiv [NumberField K] (h : IsPlaceOver A v) :
    (A.valuation.comap (algebraMap K Ω)).IsEquiv (v.valuation K) := by
  -- The pullback of `A` to `K` is proper and contains the local ring of `v`, which is a maximal
  -- proper valuation subring of `K`; so the two are equal.
  -- An integer of `K` lies in `v` exactly when it is `0` in `Ω` or its inverse is not in `A`.
  have h_mem_iff (y : 𝓞 K) :
      y ∈ v.asIdeal ↔ algebraMap K Ω y = 0 ∨ (algebraMap K Ω y)⁻¹ ∉ A :=
    (h y).symm.trans A.mem_nonunits_iff_or
  have h_le : v.valuationSubringAtPrime K ≤ A.comap (algebraMap K Ω) := by
    -- A denominator `s ∉ v` has its inverse in `A`, so the fraction `a / s` lies in `A`.
    rintro _ ⟨a, s, hs, rfl⟩
    have hs_inv : (algebraMap K Ω s)⁻¹ ∈ A := by simp_all [Ideal.primeCompl]
    simp_all [mul_mem, algebraMap_ringOfIntegers_mem]
  -- If the pullback were all of `K`, no nonzero integer would be a nonunit of `A`, so `v = 0`.
  have h_ne : A.comap (algebraMap K Ω) ≠ ⊤ := fun h_top ↦ by
    refine v.ne_bot ((Submodule.eq_bot_iff _).mpr fun y hy ↦ ?_)
    have h_in : (algebraMap K Ω y)⁻¹ ∈ A := by
      simpa using SetLike.ext_iff.mp h_top (y : K)⁻¹
    simpa [h_in] using (h_mem_iff y).mp hy
  have h_eq : v.valuationSubringAtPrime K = A.comap (algebraMap K Ω) :=
    ValuationSubring.eq_of_le_of_ne_top _ h_le h_ne
  simp [isEquiv_iff_valuationSubring, ← v.valuationSubringAtPrime_eq_valuationSubring,
    SetLike.ext_iff, h_eq]

lemma valuationVia_eq_one_iff [NumberField K] (h : IsPlaceOver A v) {x : K} :
    valuationVia K A x = 1 ↔ v.valuation K x = 1 :=
  h.isEquiv.eq_one_iff_eq_one

/-- A valuation subring lies over at most one prime of `K`. -/
lemma unique (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : v = v' :=
  -- Both primes are the centre of `A` in `𝓞 Ω`, pulled back to `𝓞 K`.
  v.ext (h.centrePrime_liesOver.over.trans h'.centrePrime_liesOver.over.symm)

lemma valuation_natCast_lt_one_iff (h : IsPlaceOver A v) {n : ℕ} : A n < 1 ↔ ↑n ∈ v.asIdeal :=
  mod_cast h n

lemma valuation_natCast_eq_one_iff (h : IsPlaceOver A v) {n : ℕ} : A n = 1 ↔ ↑n ∉ v.asIdeal := by
  simp [← h n, le_antisymm_iff]

lemma valuation_q_lt_one [NumberField K] (h : IsPlaceOver A v) : A v.q < 1 :=
  h.valuation_natCast_lt_one_iff.mpr (absNorm_mem _)

/-- If `A` lies over `v`, its uniformisers in `K` are the elements of `v`-adic valuation
`exp (-1)`. -/
lemma isUniformiser_iff [NumberField K] (h : IsPlaceOver A v) {π : K} :
    IsUniformiser A π ↔ v.valuation K π = exp (-1) :=
  isUniformiser_iff_of_isEquiv h.isEquiv (v.valuation_exists_uniformizer K)

/-- An element `g` of `Γ` whose action commutes with `K` carries a place over `v` to a place over
`v`. -/
lemma smul (h : IsPlaceOver A v) [SMulCommClass Γ K Ω] (g : Γ) : IsPlaceOver (g • A) v :=
  fun x ↦ by simpa using (smul_apply_smul_lt_one_iff g).trans (h x)

end IsPlaceOver

/-- The chosen place `placeOver v` of `New.Ω`, the algebraic closure of `ℚ`, lies over `v`. -/
lemma FinPlace.isPlaceOver_placeOver [NumberField K] [Algebra K New.Ω] (v : FinPlace K) :
    IsPlaceOver (placeOver v) v := by
  -- It is enough to find one valuation subring over `v`; take one dominating the local ring of `v`.
  suffices h_ex : ∃ A : ClosurePlace, IsPlaceOver A v from
    isPlaceOver_placeOver_of_exists v h_ex
  obtain ⟨B, hB, h_loc⟩ :=
    exists_factor_valuationRing (algebraMap (v.valuationSubringAtPrime K) New.Ω)
  refine ⟨B, .of_le_centrePrime fun x hx hx_unit ↦ ?_⟩
  -- `x ∈ v` is a nonunit of the local ring, and a local map keeps it a nonunit in `B`.
  have hx_max : algebraMap (𝓞 K) (v.valuationSubringAtPrime K) x ∈ maximalIdeal _ :=
    (over_def (maximalIdeal _) v.asIdeal).le hx
  exact hx_max (h_loc.map_nonunit _ hx_unit)

private lemma absNorm_span_natCast_rat {p : ℕ} : absNorm (span {(p : 𝓞 ℚ)}) = p := by
  -- `↓`: `absNorm_span_natCast` applies before simp turns the norm into `Algebra.norm`.
  simp [↓absNorm_span_natCast, rank]

/-- For a prime number `p`, the ideal `(p)` of `𝓞 ℚ` is prime, as its norm `p` is prime. -/
private lemma prime_span_natCast_rat {p : ℕ} (hp : p.Prime) : _root_.Prime (span {(p : 𝓞 ℚ)}) := by
  have h_irred : Irreducible (absNorm (span {(p : 𝓞 ℚ)})) := by rwa [absNorm_span_natCast_rat]
  exact (irreducible_of_irreducible_absNorm h_irred).prime

/-- The place of `ℚ` at a prime number `p`: the prime ideal `(p)` of `𝓞 ℚ`. -/
def ratPlace {p : ℕ} (hp : p.Prime) : FinPlace ℚ := ofPrime (prime_span_natCast_rat hp)

lemma q_ratPlace {p : ℕ} (hp : p.Prime) : (ratPlace hp).q = p := absNorm_span_natCast_rat

/-- `p` is a unit at every place of `ℚ` other than the place at `p`. -/
lemma valuation_eq_one_of_ne_ratPlace {p : ℕ} (hp : p.Prime) {w : FinPlace ℚ}
    (hw : w ≠ ratPlace hp) : w.valuation ℚ p = 1 := by
  -- A prime `w` containing `p` divides the prime `(p)`, so it is the place at `p`.
  refine (w.valuation_eq_one_iff_notMem (K := ℚ)).mpr fun hp_mem : (p : 𝓞 ℚ) ∈ w.asIdeal ↦ ?_
  apply hw
  have h_dvd : w.asIdeal ∣ span {(p : 𝓞 ℚ)} := dvd_span_singleton.mpr hp_mem
  exact w.ext ((prime_dvd_prime_iff_eq w.prime (ratPlace hp).prime).mp h_dvd)

/-- `p` is a uniformiser at the place of `ℚ` at `p`. -/
lemma valuation_ratPlace {p : ℕ} (hp : p.Prime) : (ratPlace hp).valuation ℚ p = exp (-1) := by
  exact ((ratPlace hp).valuation_of_algebraMap _).trans
    ((ratPlace hp).intValuation_singleton (Nat.cast_ne_zero.mpr hp.ne_zero) rfl)

/-- Every `New.ClosurePlace` whose valuation at `p` is less than `1` lies over the place of `ℚ`
at `p`. -/
lemma isPlaceOver_ratPlace_of_valuation_lt_one {p : ℕ} (hp : p.Prime) {A : ClosurePlace}
    (hA : A.valuation p < 1) : IsPlaceOver A (ratPlace hp) := by
  -- The place is the ideal `(p)`, so it is enough that `p` lies in the centre of `A`.
  refine .of_le_centrePrime ((span_singleton_le_iff_mem _).mpr ?_)
  simpa [mem_centrePrime, valuationVia] using hA

/-- The place of `ℚ` attached to a prime number `p`: (a) it has norm `p`, and `p` is a unit at every
other place; (b) `p` is a uniformiser there; (c) every `New.ClosurePlace` whose valuation at `p` is
less than `1` lies over it. -/
lemma exists_rat_place_of_prime {p : ℕ} (hp : p.Prime) :
    ∃ v : FinPlace ℚ,
      -- (a)
      (v.q = p ∧ ∀ w : FinPlace ℚ, w ≠ v → w.valuation ℚ p = 1) ∧
      -- (b)
      v.valuation ℚ p = exp (-1) ∧
      -- (c)
      ∀ A : ClosurePlace, A.valuation p < 1 → IsPlaceOver A v :=
  ⟨ratPlace hp, ⟨q_ratPlace hp, fun _ hw ↦ valuation_eq_one_of_ne_ratPlace hp hw⟩,
    valuation_ratPlace hp, fun _ hA ↦ isPlaceOver_ratPlace_of_valuation_lt_one hp hA⟩

variable [NumberField K] [NumberField L]

variable (K) [TopologicalSpace Γ] [G : IsProGalois Γ K Ω] [Algebra.IsAlgebraic K Ω]

instance : Algebra.IsAlgebraic (𝓞 K) Ω :=
  IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic K Ω)

instance : IsGaloisGroup Γ (𝓞 K) (𝓞 Ω) := by
  have h_frac : IsFractionRing (𝓞 Ω) Ω :=
    IsIntegralClosure.isFractionRing_of_algebraic (𝓞 K) (𝓞 Ω) (by simp)
  exact G.of_isFractionRing ..

/-- For `Ω / K` algebraic, a valuation subring `A` whose valuation is not `1` at some nonzero `x`
lies over a prime of `K`. -/
lemma exists_isPlaceOver_of_val_ne_one {x : Ω} (hx : x ≠ 0) (hx_val : A x ≠ 1) :
    ∃ v : FinPlace K, IsPlaceOver A v := by
  -- The place is the centre of `A`, once that prime is known to be nonzero.
  refine ⟨{ asIdeal := centrePrime K A, isPrime := inferInstance, ne_bot := fun h_cen ↦ ?_ },
    .of_le_centrePrime le_rfl⟩
  -- If the centre is zero, every nonzero integer is a unit of `A`; a valuation trivial on `𝓞 K`
  -- is `1` on nonzero algebraic elements.
  have h_trivial : A.valuation.IsTrivialOn (𝓞 K) := ⟨fun y hy ↦ by
    have hy_unit : IsUnit (⟨algebraMap K Ω y, algebraMap_ringOfIntegers_mem A y⟩ : A) :=
      by_contra fun hy_cen ↦ hy (h_cen.le hy_cen)
    exact (A.valuation_eq_one_iff _).mp hy_unit⟩
  exact transcendental_of_ne_one (𝓞 K) x hx hx_val (IsAlgebraic.isAlgebraic x)

variable {K}

/-! ### The action of the Galois group on places -/

/-- Only finitely many places ramify in a finite extension: for an open subgroup `U` of `Γ`, for
all but finitely many primes `v` of `K` the inertia group of every `A` over `v` lies in `U`. Here
`Γ` is a profinite Galois group of the Galois extension `Ω / K` (`New.IsProGalois`). -/
lemma finite_ramified {U : Subgroup Γ} (hU : U.IsOpen) :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ A : ValuationSubring Ω, IsPlaceOver (K := K) A v → inertiaGroup Γ A ≤ U := by
  -- The inertia groups above `v` tend to `1` as `v` leaves every finite set: as `Γ` is compact, it
  -- is enough that `1` is their only cluster point. Then almost all of them lie in the open `U`.
  let l : Filter Γ := .bind .cofinite fun v : FinPlace K ↦
    .principal {g | ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ g ∈ inertiaGroup Γ A}
  suffices h_lim : l ≤ nhds 1 from
    Filter.Eventually.mono (h_lim (hU.mem_nhds U.one_mem)) fun v hv A hA σ hσ ↦ hv ⟨A, hA, hσ⟩
  refine le_nhds_of_unique_clusterPt fun g hg ↦
    (faithful (𝓞 K)).eq_of_smul_eq_smul fun x : 𝓞 Ω ↦ ?_
  -- If a cluster point `g` moves an integer `x`, so do all `σ` near `g`, in the same way.
  by_contra hx
  refine hg.frequently ((isLocallyConstant_smul (x : Ω)).eventually_eq g) ?_
  -- But an inertia element `σ` above `v` with `σ x = g x` makes `v` divide the nonzero ideal `I`.
  let I : Ideal (𝓞 K) := (span {g • x - (1 : Γ) • x}).under (𝓞 K)
  have hI : I ≠ ⊥ := under_ne_bot _ (span_singleton_eq_bot.ne.mpr (sub_ne_zero.mpr hx))
  refine (finite_factors hI).eventually_cofinite_notMem.mono ?_
  rintro v hv σ ⟨A, hA, -, h_ine⟩ hσ
  -- Inertia is the Frobenius condition with exponent `1`: `σ • x - x` lies in the maximal ideal.
  have h_small : A.valuation (σ • (x : Ω) - (x : Ω) ^ 1) < 1 :=
    h_ine x (A.valuation_le_one ⟨_, algebraMap_ringOfIntegers_mem A x⟩)
  have h_mem : g • x - (1 : Γ) • x ∈ centrePrime Ω A := by
    simpa [mem_centrePrime, hσ, valuationVia, ← RingOfIntegers.coe_eq_algebraMap,
      New.smul_algebraMap_eq_algebraMap_smul] using h_small
  -- So `v`, the prime of `𝓞 K` under the centre of `A`, contains `I`.
  have hI_le : I ≤ v.asIdeal := by
    rw [hA.centrePrime_liesOver.over]
    exact comap_mono ((span_singleton_le_iff_mem _).mpr h_mem)
  exact hv (dvd_iff_le.mpr hI_le)

variable (Γ)

include h

omit [Algebra.IsAlgebraic K Ω] in
/-- If `A` lies over the prime `v` of `K` (the section hypothesis `h : IsPlaceOver A v`), it lies
over some prime `u` of `L` above `v`, for `Ω / L` algebraic. -/
lemma IsPlaceOver.exists_above [Algebra.IsAlgebraic L Ω] :
    ∃ u : FinPlace L, IsPlaceOver A u ∧ u.below K = v := by
  -- The norm of `v` is nonzero and of value below `1`, so `A` lies over some place `u` of `L`.
  -- `↓`: `map_ne_zero` applies before simp unfolds the casts.
  have h_ne : algebraMap K Ω (absNorm v.asIdeal : 𝓞 K) ≠ 0 := by simp [↓map_ne_zero]
  have h_val : A.valuation (algebraMap K Ω (absNorm v.asIdeal : 𝓞 K)) < 1 :=
    (h _).mpr (absNorm_mem _)
  obtain ⟨u, hu⟩ : ∃ u : FinPlace L, IsPlaceOver A u :=
    exists_isPlaceOver_of_val_ne_one L h_ne h_val.ne
  exact ⟨u, hu, hu.isPlaceOver_below.unique h⟩

/-- The Galois group acts transitively on the places over `v`: if `A` lies over `v` (the section
hypothesis `h : IsPlaceOver A v`) and so does `A'`, then `g • A = A'` for some `g` in `Γ`. Here
`Γ` is a profinite Galois group of `Ω / K` (`G : IsProGalois Γ K Ω`) and `Ω / K` is algebraic. -/
lemma IsPlaceOver.exists_smul (hA' : IsPlaceOver A' v) : ∃ g : Γ, g • A = A' := by
  -- Some `g` carries the centre of `A` in `𝓞 Ω` to that of `A'`, both over `v`. Then `g • A` and
  -- `A'` lie over the same prime of any finite extension `F` of `K` in `Ω`, so they agree on `F`.
  -- Give `𝓞 Ω` the discrete uniformity; the action is then continuous as stabilisers are open.
  let discreteUniformity : UniformSpace (𝓞 Ω) := ⊥
  have h_cont : ContinuousSMul Γ (𝓞 Ω) := continuousSMul_iff_stabilizer_isOpen.mpr fun x ↦
    Subgroup.isOpen_mono (fun σ hσ ↦ RingOfIntegers.ext hσ) (G.isOpen_stabilizer (x : Ω))
  obtain ⟨g, hg⟩ : ∃ g : Γ, centrePrime Ω A' = g • centrePrime Ω A :=
    IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 K) _ _
      (h.centrePrime_liesOver.over.symm.trans hA'.centrePrime_liesOver.over)
  refine ⟨g, SetLike.ext fun x ↦ ?_⟩
  -- `x` lies in the fixed field `F` of its open stabilizer, a number field.
  have h_open : Fact (IsOpen (MulAction.stabilizer Γ x : Set Γ)) := ⟨G.isOpen_stabilizer x⟩
  let F : IntermediateField K Ω := fixedFieldOf (MulAction.stabilizer Γ x)
  obtain ⟨w, hw_A', -⟩ : ∃ w : FinPlace F, IsPlaceOver A' w ∧ w.below K = v := hA'.exists_above
  have hw_gA : IsPlaceOver (g • A) w := fun y ↦ by
    -- Both sides say that the image of `y` in `𝓞 Ω` lies in the centre of `A'`, which is the
    -- centre of `A` moved by `g`.
    have h_centre : algebraMap (𝓞 F) (𝓞 Ω) y ∈ g • centrePrime Ω A ↔
        algebraMap (𝓞 F) (𝓞 Ω) y ∈ centrePrime Ω A' := by rw [hg]
    have h_coe : ((algebraMap (𝓞 F) (𝓞 Ω) y : 𝓞 Ω) : Ω) = ((y : F) : Ω) := rfl
    simpa [mem_centrePrime, ← hw_A' _, mem_pointwise_smul_iff_inv_smul_mem,
      ← smul_apply_smul_lt_one_iff g (A := A), algebraMap.smul', valuationVia,
      ← RingOfIntegers.coe_eq_algebraMap, h_coe] using h_centre
  -- Both valuations restrict on `F` to one equivalent to that of `w`; compare `x` with `1`.
  simpa using hw_gA.isEquiv.trans hw_A'.isEquiv.symm ⟨x, fun σ ↦ σ.property⟩ 1

end New

end Places

/-!
## The prime induced by a p-adic embedding and its extension to finite adeles

Conventions: `New.FinPlace E` is the type of nonzero primes of `𝓞 E`, `New.LocField w` the
completion at `w` with valuation `v`, and `New.Ô E` the ring of integral finite adeles. The field
`F` is a normed field over `ℚ_p` (`New.PadicField F p`) whose norm is ultrametric.
-/

section PadicEmbedding

open NumberField Valued NormedField Valuation ComplexConjugate IntermediateField Module
  IsDenseInducing NNReal

namespace New

variable {E : Type*} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime]
  {F : Type*} [NormedField F] [IsUltrametricDist F] [CharZero F] [PadicField F p] (σ : E →+* F)

omit [Fact p.Prime] [CharZero F] [PadicField F p] in
lemma norm_le_one_of_isIntegral {R : Type*} [CommRing R] (ι : R →+* F) {x : R}
    (hx : IsIntegral ℤ x) : ‖ι x‖ ≤ 1 :=
  -- The valuation ring of `‖ι ·‖` is integrally closed in `R`.
  (integer.integers (valuation.comap ι)).mem_of_integral hx.tower_top

omit [NumberField E] [CharZero F] in
lemma norm_ringOfIntegers_le (x : 𝓞 E) : ‖σ x‖ ≤ 1 := norm_le_one_of_isIntegral σ x.prop

/-! ### The prime induced by an embedding -/

/-- The prime of `E` induced by an embedding `σ : E →+* F` into an ultrametric normed field over
`ℚ_p`: the centre on the integers of `E` of the valuation ring `{x : E | ‖σ x‖ ≤ 1}`. An integer `x`
of `E` lies in it exactly when `‖σ x‖ < 1` (`New.mem_placeOfEmb`). -/
def placeOfEmb : FinPlace E where
  asIdeal := Cohomology.centrePrime E (valuation.comap σ).valuationSubring
  isPrime := Ideal.IsPrime.comap _
  ne_bot h_bot := by
    -- The centre is not zero: it contains `p ≠ 0`, as `‖p‖ < 1`.
    have h_norm_p : valuation.comap σ (p : E) < 1 := by
      simpa [← NNReal.coe_lt_coe] using norm_p_lt_one
    have h_mem : (p : 𝓞 E) ∈ Cohomology.centrePrime E (valuation.comap σ).valuationSubring :=
      (mem_maximalIdeal_iff E (valuation.comap σ)).mpr h_norm_p
    exact NeZero.ne (p : 𝓞 E) (h_bot.le h_mem)

omit [CharZero F] in
/-- The valuation `‖σ ·‖` on `E` is equivalent to the valuation of `E` at the prime
`New.placeOfEmb σ`. -/
lemma isEquiv_placeOfEmb : (valuation.comap σ).IsEquiv ((placeOfEmb σ).valuation E) :=
  (isEquiv_valuation_valuationSubring _).trans (IsPlaceOver.of_le_centrePrime le_rfl).isEquiv

omit [CharZero F] in
@[simp]
lemma mem_placeOfEmb (x : 𝓞 E) : x ∈ (placeOfEmb σ).asIdeal ↔ ‖σ x‖ < 1 :=
  mem_maximalIdeal_iff E (valuation.comap σ)

attribute [irreducible] placeOfEmb

/-- The ring homomorphism from `ℂ` to `ℂ_p` obtained by composing an isomorphism `ι` from `ℂ` onto
the algebraic closure of `ℚ_p` with the inclusion into `ℂ_p`. -/
abbrev complexToCp (ι : ℂ ≃+* PadicAlgCl p) : ℂ →+* ℂ_[p] :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).comp ι.toRingHom

/-- The prime of `E` above `p` induced by the complex embedding `σ` followed by the isomorphism
`ιℓ` from `ℂ` to the algebraic closure of `ℚ_p` that `[PadicIso p]` fixes. -/
abbrev inducedPrime [PadicIso p] (σ : E →+* ℂ) : FinPlace E := placeOfEmb (ιℓ.toRingHom.comp σ)

omit [CharZero F] in
/-- The prime `New.placeOfEmb σ` contains `p`, as `‖p‖ < 1` in `F`. -/
@[simp high]
lemma natCast_mem_placeOfEmb : (p : 𝓞 E) ∈ (placeOfEmb σ).asIdeal := by simp [norm_p_lt_one]

/-- The subfield `ℚ_p(σ E)` of `F` generated over `ℚ_p` by the image of `σ` is finite over `ℚ_p`. -/
instance : FiniteDimensional ℚ_[p] (adjoin ℚ_[p] (Set.range σ)) := by
  -- The degree of `ℚ_p(σ E)` over `ℚ_p` is at most that of `σ E` over `ℚ`, which is finite.
  let σE : IntermediateField ℚ F := σ.toRatAlgHom.fieldRange
  have h_finite : FiniteDimensional ℚ σE :=
    σ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional
  exact rank_lt_aleph0_iff.mp
    ((σE.adjoin_rank_le_of_isAlgebraic_right ℚ_[p]).trans_lt (rank_lt_aleph0 ℚ σE))

/-! ### Extension to the completion and to finite adeles -/

/-- Let `F` be an ultrametric normed field of characteristic 0 that is a normed `ℚ_p`-algebra, not
necessarily complete. Let `σ` be an embedding of the number field `E` into `F`, and let
`New.placeOfEmb σ` be the prime of `E` made of the integers `x` with `‖σ x‖ < 1`. Then `σ` extends
to a continuous ring homomorphism `φ` on the completion of `E` at that prime. Its values lie in the
subfield `ℚ_p(σ E)` of `F`, and `‖φ x‖ ≤ ‖φ y‖` holds exactly when `v x ≤ v y` for the valuation
`Valued.v` of the completion. The chosen extension is `New.placeOfEmbExtension σ`. -/
lemma exists_placeOfEmb_extension :
    ∃ φ : LocField (placeOfEmb σ) →+* F,
      Continuous φ ∧
      (∀ x : E, φ (algebraMap E (LocField (placeOfEmb σ)) x) = σ x) ∧
      (∀ x : LocField (placeOfEmb σ), φ x ∈ adjoin ℚ_[p] (Set.range σ)) ∧
      (valuation.comap φ).IsEquiv Valued.v := by
  -- The field `L = ℚ_p(σ E)` is finite over `ℚ_p`, hence complete. The map `σ : E → L` is uniformly
  -- continuous for the norm of the place `placeOfEmb σ`, so it extends from `E` to the completion.
  set L : IntermediateField ℚ_[p] F := adjoin ℚ_[p] (Set.range σ)
  have h_complete : CompleteSpace L := FiniteDimensional.complete ℚ_[p] L
  let σL : E →+* L := σ.codRestrict L fun x ↦ subset_adjoin _ _ ⟨x, rfl⟩
  -- The norm of the completion and `‖σ ·‖` order the elements of `E` alike.
  have h_place_equiv : (place (algebraMap E (LocField (placeOfEmb σ)))).IsEquiv (place σ) := by
    intro x y
    simpa [Valued.toNormedField.norm_le_iff, v_algebraMap_eq_valuation, ← coe_le_coe]
      using (isEquiv_placeOfEmb σ).symm x y
  -- Equivalent absolute values are powers of each other.
  obtain ⟨c, hc_pos, h_pow⟩ : ∃ c : ℝ, 0 < c ∧
      (fun x : E ↦ ‖algebraMap E (LocField (placeOfEmb σ)) x‖ ^ c) = fun x : E ↦ ‖σ x‖ :=
    AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp h_place_equiv
  -- Give `E` the norm of the completion. As `‖σ x‖ = ‖x‖ ^ c`, the map `σL` is uniformly
  -- continuous.
  let seminormed_E : SeminormedRing E :=
    SeminormedRing.induced E (LocField (placeOfEmb σ)) (FinitePlace.embedding (placeOfEmb σ))
  have h_unif : UniformContinuous σL := uniformContinuous_of_tendsto_zero
    (squeeze_zero_norm (fun x ↦ (congrFun h_pow x).ge)
      (tendsto_norm_zero.rpow_const_nhds_zero hc_pos))
  -- The uniform structure of `E` is induced from the completion.
  have h_inducing : IsUniformInducing (algebraMap E (LocField (placeOfEmb σ))) := ⟨rfl⟩
  have h_dense : DenseRange (algebraMap E (LocField (placeOfEmb σ))) :=
    (placeOfEmb σ).denseRange_algebraMap E
  let φ : LocField (placeOfEmb σ) →+* L := extendRingHom h_inducing h_dense h_unif
  have hφ_cont : Continuous φ :=
    (uniformContinuous_uniformly_extend h_inducing h_dense h_unif).continuous
  have hφ_ext (x : E) : (φ (algebraMap E (LocField (placeOfEmb σ)) x) : F) = σ x := by
    simp [φ, σL, extendRingHom, extend_eq, h_unif.continuous]
  -- The relation `‖σ x‖ = ‖x‖ ^ c` passes to the completion by density.
  have hφ_norm : ∀ y : LocField (placeOfEmb σ), ‖(φ y : F)‖ = ‖y‖ ^ c :=
    h_dense.eq (fun x ↦ (congrArg norm (hφ_ext x)).trans (congrFun h_pow x).symm) hφ_cont.norm
      (continuous_norm.rpow_const fun _ ↦ .inr hc_pos.le)
  refine ⟨(algebraMap L F).comp φ, continuous_subtype_val.comp hφ_cont, hφ_ext,
    fun x ↦ (φ x).prop, fun x y ↦ ?_⟩
  -- `‖φ x‖ ≤ ‖φ y‖` holds iff `‖x‖ ^ c ≤ ‖y‖ ^ c`, iff `‖x‖ ≤ ‖y‖`, iff `v x ≤ v y`.
  simp [← coe_le_coe, hφ_norm, Real.rpow_le_rpow_iff, hc_pos, Valued.toNormedField.norm_le_iff]

/-- The extension of `σ` to the completion of `E` at the prime `New.placeOfEmb σ`, chosen by
`New.exists_placeOfEmb_extension`: continuous, extending `σ`, with values in `ℚ_p(σ E)`. -/
def placeOfEmbExtension : LocField (placeOfEmb σ) →+* F := (exists_placeOfEmb_extension σ).choose

lemma continuous_placeOfEmbExtension : Continuous (placeOfEmbExtension σ) :=
  (exists_placeOfEmb_extension σ).choose_spec.1

lemma placeOfEmbExtension_algebraMap (x : E) :
    placeOfEmbExtension σ (algebraMap E (LocField (placeOfEmb σ)) x) = σ x :=
  let ⟨_, h_ext, _⟩ := (exists_placeOfEmb_extension σ).choose_spec
  h_ext x

/-- The extension of `σ` to the completion takes values in the subfield `ℚ_p(σ E)` of `F`. -/
lemma placeOfEmbExtension_mem_adjoin (x : LocField (placeOfEmb σ)) :
    placeOfEmbExtension σ x ∈ adjoin ℚ_[p] (Set.range σ) :=
  let ⟨_, _, h_image, _⟩ := (exists_placeOfEmb_extension σ).choose_spec
  h_image x

/-- The norm valuation of `F` pulled back along `New.placeOfEmbExtension σ` is equivalent to the
valuation `Valued.v` of the completion at `New.placeOfEmb σ`. -/
lemma valuation_comap_placeOfEmbExtension_isEquiv :
    (valuation.comap (placeOfEmbExtension σ)).IsEquiv Valued.v :=
  let ⟨_, _, _, h_equiv⟩ := (exists_placeOfEmb_extension σ).choose_spec
  h_equiv

/-- The extension of `σ` to the finite adeles of `E`: take the component at the prime
`New.placeOfEmb σ`, then apply `New.placeOfEmbExtension σ`. -/
def adeleExtension : 𝔸f E →+* F :=
  (placeOfEmbExtension σ).comp (evalAt (placeOfEmb σ))

@[simp]
lemma adeleExtension_algebraMap (x : E) : adeleExtension σ x = σ x :=
  placeOfEmbExtension_algebraMap σ x

@[fun_prop]
lemma continuous_adeleExtension : Continuous (adeleExtension σ) :=
  (continuous_placeOfEmbExtension σ).comp (by fun_prop)

/-- Two finite adeles `x` and `y` have images of the same norm under the extension of `σ`
exactly when their components at the prime `New.placeOfEmb σ` have the same valuation. -/
lemma norm_adeleExtension_eq_iff {x : 𝔸f E} (y : 𝔸f E) :
    ‖adeleExtension σ x‖ = ‖adeleExtension σ y‖ ↔ v (x (placeOfEmb σ)) = v (y (placeOfEmb σ)) :=
  -- Equal norms are equal values of the valuation `‖placeOfEmbExtension σ ·‖₊`.
  coe_inj.trans (valuation_comap_placeOfEmbExtension_isEquiv σ).eq_iff

/-- The extension of `σ` sends every finite adele `x` that is integral at all primes to an element
of norm at most one. -/
lemma norm_adeleExtension_le_one {x : 𝔸f E} (hx : x ∈ Ô E) : ‖adeleExtension σ x‖ ≤ 1 :=
  (valuation_comap_placeOfEmbExtension_isEquiv σ).le_one_iff_le_one.mpr
    (mem_Ô.mp hx (placeOfEmb σ))

variable [IsCMField E]

/-! ### Compatibility with complex conjugation -/

omit [CharZero F] in
/-- For a CM field `E`, the prime induced by `σ` composed with complex conjugation is the complex
conjugate of the prime induced by `σ`. -/
lemma placeOfEmb_comp_star : placeOfEmb (σ.comp conj) = star (placeOfEmb σ) := by
  -- An integer `x` lies in either prime exactly when `‖σ (star x)‖ < 1`.
  ext x
  rw [mem_placeOfEmb, mem_star_place, mem_placeOfEmb, coe_star_ringOfIntegers]
  rfl

/-- For a CM field `E`, applying the extension of `σ` to the complex conjugate of a finite adele
gives the extension of `σ` composed with complex conjugation. -/
lemma adeleExtension_star :
    ∀ x : 𝔸f E, adeleExtension σ (star x) = adeleExtension (σ.comp conj) x :=
  -- Both sides are continuous and agree on `E`, which is dense in the finite adeles.
  denseRange_algebraMap_finAdele.eq fun a ↦ by
    rw [star_algebraMap_finAdele, adeleExtension_algebraMap, adeleExtension_algebraMap]
    rfl

/-- The embedding `x ↦ ι (Φ v (conj x))` of `E` into `F`, for `ι : ℂ →+* F` and an infinite
place `v` with chosen complex embedding `Φ v`. -/
abbrev weightEmbedding {E : Type*} [Field E] [CMType E]
    (ι : ℂ →+* F) (v : InfinitePlace E) : E →+* F :=
  (ι.comp (Φ v)).comp (starRingEnd E)

end New

end PadicEmbedding

/-!
## The formula efg = n for Galois extensions of number fields

`New.FinPlace.ncard_mul_ramificationIdx_mul_inertiaDeg` restates Mathlib's formula
`g * (e * f) = [L : K]` for a finite place `w` of a Galois extension `L / K` of number fields,
counting places (`New.FinPlace`) over `w.below K` instead of prime ideals.
-/

section EfgFormula

open NumberField IsDedekindDomain HeightOneSpectrum Ideal New

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]
  [IsGalois K L] (w : FinPlace L)

/-- The place `w` of `L` lies over the place of `K` below it. -/
instance : w.asIdeal.LiesOver (w.below K).asIdeal := ⟨rfl⟩

/-- For a Galois extension `L / K` of number fields and a finite place `w` of `L`: the number of
places of `L` over the place of `K` below `w`, times the ramification index and the inertia
degree of `w`, is `[L : K]`. -/
lemma New.FinPlace.ncard_mul_ramificationIdx_mul_inertiaDeg :
    {u : FinPlace L | u.below K = w.below K}.ncard *
        (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) =
      Module.finrank K L := by
  -- This is Mathlib's formula for the prime ideals over `w.below K`: the places over it correspond
  -- to these ideals, and all of them have the ramification index and inertia degree of `w`.
  have h_iff (u : FinPlace L) :
      u.below K = w.below K ↔ u.asIdeal ∣ (w.below K).asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [← liesOver_iff_dvd_map u.isPrime.ne_top]
    refine ⟨fun hu ↦ ?_, fun hu ↦ asIdeal_injective hu.over.symm⟩
    rw [← hu]
    infer_instance
  have h_card : {u : FinPlace L | u.below K = w.below K}.ncard =
      ((w.below K).asIdeal.primesOver (𝓞 L)).ncard :=
    Set.ncard_congr' ((Equiv.subtypeEquivRight h_iff).trans (equivPrimesOver _ (ne_bot _)))
  rw [h_card, ← IsGalois.card_aut_eq_finrank,
    ← (w.below K).asIdeal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (𝓞 L),
    ramificationIdxIn_eq_ramificationIdx _ w Gal(L/K), inertiaDegIn_eq_inertiaDeg _ w Gal(L/K)]

end EfgFormula

end
