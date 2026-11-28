import New.Congruences.Selmer.Line
import New.Congruences.Selmer.RootsOfUnity

/-!
# Twisting, general form

For finitely many Selmer data and Stickelberger systems (under the hypotheses of
`New.Selmer.exists_anticyclotomic_twist`) there is one anticyclotomic character whose first `m`
powers have short Selmer groups, values of small valuation at the elements of the systems, and
values far from `1` at the tame generators. The character is `∏ ζ_𝔮 ^ λ_𝔮`, with the `λ_𝔮` of
`New.Selmer.exists_twistPolynomials` and roots of unity `ζ_𝔮` from
`New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add`.

* `New.Selmer.IsSmallTwist`: the bounds for one character.
* `New.Selmer.exists_rootsOfUnity_ellVal_eval_le`: roots of unity that serve all powers up to `m`.
* `New.Selmer.exists_anticyclotomic_twist`: one twist that works for all powers up to `m`.

Notions from other files:
* `New.Selmer.SelmerDatum ℓ S₀ g₀ O n`: a lattice `T = O ^ n` with an action of `Gal(Ω/E)`
  unramified outside `S₀`, local conditions above `ℓ`, and the number `β_T`, which includes the
  valuations of `det(ρ g - 1)` for `g = g₀` and its conjugate inverse. `TwistedLengthLe Q ψ b`
  says that its Selmer group `Sel_Q(T ψ)` has normalised length at most `b` over all large
  coefficient rings (`CoeffRing.normLength`: `len (O / ℓ) = 1`).
* `New.Selmer.StickelbergerSystem ℓ S₀ g₀`: a character `ϑ` unramified outside `S₀` with
  `ϑ g₀ ≠ 1`, elements `Θ_Q` of the group rings of class groups `Cl_Q` with a norm relation, and
  the number `β`.
* `New.Selmer.TwistPolynomials T Y s₀ r N`: an auxiliary set `Q` of at most `s₀ / 2` primes,
  homomorphisms `λ_𝔮` to `ℤ / ℓ ^ N` for `𝔮 ∈ Q`, and for each datum and system a polynomial in
  variables indexed by `Q` with a point whose coordinates have valuation at least `r`.
* `New.ellVal`: the valuation `v` on `PadicAlgCl ℓ` with `v(ℓ) = 1`, read in `[0, ∞]`.
-/

noncomputable section

namespace New.Selmer

open Finset Filter Module MvPolynomial IsDiscreteValuationRing IsLocalRing

open scoped NNReal ENNReal NNRat

variable {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  {S₀ : Finset (FinPlace E)}
  {g₀ : Gal(Ω/E)} {ι κ : Type} {n : ι → Type} [∀ i : ι, Fintype (n i)] [∀ i : ι, DecidableEq (n i)]
  {O : CoeffRing ℓ} (T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O.1 (n i))
  (Y : κ → StickelbergerSystem ℓ S₀ g₀)

open scoped Classical in
/-- The conclusions of the general twisting theorem for Selmer data `T i`, Stickelberger systems
`Y k`, a bound `ε`, a set of primes `Q` and one character `ψ`. The datum `T i` is a lattice
`O ^ n i` with a Galois action unramified outside `S₀`, local conditions above `ℓ` and a finite
number `β_T = (T i).β`, a sum of lengths of `O`-modules. The system `Y k` has elements
`Θ_Q = (Y k).element Q` of the group rings of class groups `Cl_Q` and a finite number
`β = (Y k).β`, a sum of valuations. The element `g₀` enters the bounds through `β_T` and `β`.
Below, `v` is the valuation `ellVal` with `v(ℓ) = 1`. -/
structure IsSmallTwist (ε : ℝ≥0) (Q : Finset (FinPlace E)) (ψ : Gal(Ω/E) →* PadicAlgCl ℓ) :
    Prop where
  /-- `ψ` comes by `y ↦ y / ȳ` from an idele class character of tame level `Q` trivial above `ℓ`;
  so it is locally constant, anticyclotomic, unramified outside `Q ∪ Q̄` and trivial on the
  decomposition groups above `ℓ`. -/
  isFromU1 : IsFromU1 (placesDividing E ℓ) Q ψ
  /-- The order of `ψ` is a power of `ℓ`. -/
  exists_pow_eq_one : ∃ h : ℕ, ψ ^ ℓ ^ h = 1
  /-- `ψ` is ramified at every prime of `Q`. -/
  ramified : ∀ v ∈ Q, ∃ g ∈ inertiaAbove {v}, ψ g ≠ 1
  /-- (a) `len Sel_Q(T ψ) ≤ β_T + ε` for each datum, with lengths scaled so that
  `len (O / ℓ) = 1`. -/
  length_le (i : ι) : (T i).TwistedLengthLe Q ψ (O.normLength (T i).β + ε)
  /-- (b) `v(ψ(Θ_Q)) ≤ β + ε` for each system. -/
  ellVal_value_le (k : κ) : ellVal (groupRingEval ψ ((Y k).element Q)) ≤ (Y k).β + ε
  /-- (c) `∑ v(ψ(γ_w) - 1) ≤ ε`, over `w ∈ Q ∪ Q̄`, for any tame generators `γ_w` at any places
  `A w` above `w`. -/
  sum_le_of_isTameGenerator (A : FinPlace E → ClosurePlace)
    (hA : ∀ w : FinPlace E, IsPlaceOver (A w) w)
    (γ : ∀ w : FinPlace E, inertiaGroup Gal(Ω/E) (A w))
    (hγ : ∀ w : FinPlace E, IsTameGenerator (γ w)) :
    ∑ w ∈ Q ∪ Q.image star, ellVal (ψ (γ w) - 1) ≤ ε

/-- If `ψ` satisfies `IsSmallTwist T Y ε Q ψ` (the conclusions of the general twisting theorem with
bound `ε`), then it satisfies `IsSmallTwist T Y ε' Q ψ` for every `ε' ≥ ε`. -/
lemma IsSmallTwist.mono {ε ε' : ℝ≥0} {Q : Finset (FinPlace E)} {ψ : Gal(Ω/E) →* PadicAlgCl ℓ}
    (hψ : IsSmallTwist T Y ε Q ψ) (hε : ε ≤ ε') : IsSmallTwist T Y ε' Q ψ :=
  { hψ with
    length_le i := (hψ.length_le i).mono (by gcongr)
    ellVal_value_le k := (hψ.ellVal_value_le k).trans (by gcongr)
    sum_le_of_isTameGenerator A hA γ hγ :=
      (hψ.sum_le_of_isTameGenerator A hA γ hγ).trans (by gcongr) }

variable {T Y} in
open scoped Classical in
/-- If `ψ` is a small twist (`IsSmallTwist T Y ε Q ψ`), then the sum of `ellVal (ψ γ_w - 1)` over
`w ∈ Q ∪ Q.image star` is at most `ε`. Here `γ_w` is the chosen tame generator
(`(hA w).tameGenerator`) at the place `A w` above `w`. -/
lemma IsSmallTwist.sum_ellVal_tameGenerator_sub_one_le {ε : ℝ≥0} {Q : Finset (FinPlace E)}
    {ψ : Gal(Ω/E) →* PadicAlgCl ℓ} (hψ : IsSmallTwist T Y ε Q ψ) (A : FinPlace E → ClosurePlace)
    (hA : ∀ w : FinPlace E, IsPlaceOver (A w) w) :
    ∑ w ∈ Q ∪ Q.image star, ellVal (ψ (hA w).tameGenerator - 1) ≤ ε :=
  hψ.sum_le_of_isTameGenerator A hA _ fun w ↦ (hA w).isTameGenerator_tameGenerator

open Pointwise in
omit [NumberField.IsCMField E] in
/-- Let `ψ` be a locally constant character of `Gal(Ω/E)` with `ψ ^ q = 1`. Let `A` be a place of
`Ω` (a valuation subring) above `w` at which `q` is a unit. Let `γ` be a tame generator of the
inertia group of `A`: for each `n` that is a unit at `A`, it multiplies an `n`-th root of some
uniformiser of `E` by a primitive `n`-th root of unity. Then `ψ` maps every element of an inertia
group above `w` to a power of `ψ γ`. -/
lemma exists_map_eq_map_pow_of_isTameGenerator {C : Type} [CommMonoid C] {ψ : Gal(Ω/E) →* C}
    (hψ : IsLocallyConstant ψ) {q : ℕ} (hq : ψ ^ q = 1) {w : FinPlace E} {A : ClosurePlace}
    (hA : IsPlaceOver A w) (hqA : A.valuation q = 1) {γ : inertiaGroup Gal(Ω/E) A}
    (hγ : IsTameGenerator γ) {g : Gal(Ω/E)} (hg : g ∈ inertiaAbove {w}) :
    ∃ a : ℕ, ψ g = ψ γ ^ a := by
  -- The inertia groups above `w` are conjugate, and `ψ` is constant on conjugacy classes.
  obtain ⟨w', rfl, A', hA', hg⟩ := hg
  obtain ⟨s, rfl⟩ : ∃ s : Gal(Ω/E), s • A' = A := hA'.exists_smul Gal(Ω/E) hA
  have h_conj : ψ (s * g * s⁻¹) = ψ g := by
    rw [map_mul, map_mul, mul_right_comm, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have h_near : ∀ᶠ u : Gal(Ω/E) in nhds 1, u ∈ inertiaGroup Gal(Ω/E) (s • A') → ψ u = 1 :=
    (hψ.eventually_eq 1).mono fun u hu _ ↦ hu.trans (map_one ψ)
  have h_power : ∃ a : ℕ, ψ (s * g * s⁻¹) = ψ γ ^ a :=
    (hA.exists_eq_pow_and_apply_conj_eq_pow hγ ψ h_near hqA (fun u _ ↦ DFunLike.congr_fun hq u)
      ⟨s * g * s⁻¹, hg.conj s⟩).left
  rwa [h_conj] at h_power

/-- Evaluation at `x` of `P` with `f j` put for the variable `j` is evaluation of `P` at the values
of the `f j` at `x`. -/
lemma eval_aeval {σ R : Type*} [CommSemiring R] (x : σ → R) (f : σ → MvPolynomial σ R)
    (P : MvPolynomial σ R) :
    eval x (aeval f P) = eval (fun j : σ ↦ eval x (f j)) P := by
  rw [map_aeval, algebraMap_eq, show (eval x).comp C = RingHom.id R from RingHom.ext eval_C]
  rfl

/-- A finite length `b` has finite normalised length `O.normLength b` (the multiple of `b` by the
valuation of a uniformiser of `O`). -/
lemma normLength_ne_top {b : ℕ∞} (hb : b ≠ ⊤) : O.normLength b ≠ ⊤ := by
  lift b to ℕ using hb
  exact ENNReal.coe_ne_top

/-- For a natural number `s` and `ε > 0` there is a rational `r > 0` with `s r ≤ ε`. -/
lemma exists_nnrat_mul_le (s : ℕ) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ r : ℚ≥0, 0 < r ∧ s * (r : ℝ≥0) ≤ ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_pos_mul_lt hε (s : ℝ≥0)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ_pos
  have h_le : ((1 / (k + 1) : ℚ≥0) : ℝ≥0) ≤ δ := by simpa using hk.le
  exact ⟨1 / (k + 1), by positivity, le_trans (by gcongr) hδ.le⟩

namespace TwistPolynomials

variable {T Y} {s₀ N : ℕ} {r : ℚ≥0} (X : TwistPolynomials T Y s₀ r N) {ζ : X.auxPrimes → intQpBar ℓ}

/-- The character `ψ = ∏ ζ_𝔮 ^ λ_𝔮`, a product over the primes `𝔮` of `X.auxPrimes`, for twist
polynomials `X` with homomorphisms `λ_𝔮 = X.primeChar 𝔮` to `ℤ / ℓ ^ N`, and for roots of unity
`ζ_𝔮` of order dividing `ℓ ^ N` in the ring `intQpBar ℓ` of integers of `PadicAlgCl ℓ`. The
parameters `s₀` (at least twice the number of primes) and `r` (a lower bound for the valuations of
the points of `X`) play no part in the definition. -/
abbrev twist (hζ : ∀ v : X.auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1) :
    Gal(Ω/E) →* PadicAlgCl ℓ :=
  pointChar X.primeChar (fun v ↦ (ζ v : PadicAlgCl ℓ)) hζ

/-- The value of the twist at `g` is `∏ ζ_𝔮 ^ λ_𝔮(g)`, with `λ_𝔮(g)` read in `[0, ℓ ^ N)`. -/
lemma twist_apply (hζ : ∀ v : X.auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1) (g : Gal(Ω/E)) :
    X.twist hζ g = ∏ v : X.auxPrimes, (ζ v : PadicAlgCl ℓ) ^ (X.primeChar v g).toAdd.val :=
  rfl

/-- If each `ζ_𝔮` has order dividing `ℓ ^ N`, then so does each `ζ_𝔮 ^ j`. -/
lemma coe_pow_apply_pow_eq_one (hζ : ∀ v : X.auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1) (j : ℕ)
    (v : X.auxPrimes) : ((ζ ^ j) v : PadicAlgCl ℓ) ^ ℓ ^ N = 1 := by
  rw [Pi.pow_apply, SubmonoidClass.coe_pow, pow_right_comm, hζ v, one_pow]

/-- The power `ψ ^ j` of the twist `ψ = ∏ ζ_𝔮 ^ λ_𝔮` by roots of unity `ζ_𝔮` of order dividing
`ℓ ^ N` is the twist by the `ζ_𝔮 ^ j`, which again have order dividing `ℓ ^ N`. -/
lemma twist_pow (hζ : ∀ v : X.auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1) (j : ℕ) :
    X.twist hζ ^ j = X.twist (ζ := ζ ^ j) (X.coe_pow_apply_pow_eq_one hζ j) := by
  ext g
  simp [← prod_pow, pow_right_comm]

/-- The twist by roots of unity of order dividing `ℓ ^ N` has order dividing `ℓ ^ N`. -/
lemma twist_pow_eq_one (hζ : ∀ v : X.auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1) :
    X.twist hζ ^ ℓ ^ N = 1 := by
  ext g
  simp [← prod_pow, pow_right_comm, hζ]

/-- Let `Q = X.auxPrimes` be the auxiliary primes of the twist polynomials `X`, and let
`ψ = X.twist hζ` be the twist by `ℓ ^ N`-th roots of unity `ζ v`, for `v ∈ Q`. Then `ψ` is locally
constant and `ψ(Art y) = η(y / ȳ)` for a character `η` of the finite ideles of `E` that is trivial
on `Eˣ` and on the ideles that are units away from `ℓ`, arbitrary above `ℓ` and congruent to `1` at
the primes of `Q` not above `ℓ`. -/
lemma isFromU1_twist (hζ : ∀ v : X.auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1) :
    IsFromU1 (placesDividing E ℓ) X.auxPrimes (X.twist hζ) :=
  isFromU1_pointChar hζ fun v _ ↦ (X.isFromU1_primeChar v).mono (by simp)

/-- Let `X` be twist polynomials for the Selmer data `T` and the Stickelberger systems `Y`. Of `X`
only two parts enter: the set of primes `X.auxPrimes` of `E` and, for each prime `u` in it, a
homomorphism `λ_u = X.primeChar u` from `Gal(Ω/E)` to `ℤ / ℓ ^ N` that is onto on inertia at `u`
and unramified outside `u` and its conjugate. Let `ζ u` be `ℓ ^ N`-th roots of unity in the ring
`intQpBar ℓ` of integers of `PadicAlgCl ℓ`, and let `ψ = X.twist hζ = ∏ (ζ u) ^ λ_u`. For a prime
`v` of `X.auxPrimes` and `w` equal to `v` or to its conjugate `star v`, the character `ψ` takes
the value `ζ v` on some element of an inertia group above `w`. -/
lemma exists_mem_inertiaAbove_twist_eq (hζ : ∀ v : X.auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1)
    (v : X.auxPrimes) {w : FinPlace E} (hw : w = v ∨ w = star (v : FinPlace E)) :
    ∃ g ∈ inertiaAbove {w}, X.twist hζ g = ζ v := by
  obtain ⟨g, ⟨v', rfl, A, hA, hg⟩, h_one⟩ :
      ∃ g ∈ inertiaAbove {v.val}, X.primeChar v g = Multiplicative.ofAdd 1 :=
    X.exists_eq_ofAdd_one v
  -- The other `X.primeChar u` are unramified at `v`, because `v` is neither `u` nor its conjugate.
  have h_other (u : X.auxPrimes) (hu : u ≠ v) : X.primeChar u g = 1 := by
    refine (X.isFromU1_primeChar u).eq_one_of_mem_inertiaAbove g ⟨v, ?_, A, hA, hg⟩
    obtain ⟨-, -, hv_star : star v.val ∉ X.auxPrimes, -⟩ := X.auxiliary v v.property
    have h_star : star v.val ≠ u.val := (ne_of_mem_of_not_mem u.property hv_star).symm
    simp [Set.conjClosure, Subtype.coe_ne_coe.2 hu.symm, h_star]
  have h_value : X.twist hζ g = ζ v := by
    rw [twist_apply, Fintype.prod_eq_single v fun u hu ↦ by simp [h_other u hu], h_one, toAdd_ofAdd,
      ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 (hζ v), pow_one]
  obtain rfl | rfl := hw
  · exact ⟨g, ⟨v, rfl, A, hA, hg⟩, h_value⟩
  · -- The element `idOrConjInv false g = (c g c)⁻¹`, for complex conjugation `c`, is inertial at
    -- the conjugate of `v`, and `ψ` takes the same value on it.
    have h_mem : idOrConjInv false g ∈ inertiaAbove {star v.val} :=
      ⟨star v.val, rfl, conjPlace A, hA.conjPlace_star, inv_mem hg.conjPlace_conjGal⟩
    have h_conj : X.twist hζ (idOrConjInv false g) = X.twist hζ g :=
      (X.isFromU1_twist hζ).apply_idOrConjInv false g
    exact ⟨idOrConjInv false g, h_mem, h_conj.trans h_value⟩

/-- Let `X` be twist polynomials, with auxiliary primes `X.auxPrimes` and homomorphisms `λ_u` from
`Gal(Ω/E)` to `ℤ / ℓ ^ N`, one for each prime `u` of `X.auxPrimes`. Let `ζ u` be `ℓ ^ N`-th roots of
unity and `ψ = X.twist hζ = ∏ (ζ u) ^ λ_u`. Let `S₀` contain the places above `ℓ`, let `v` be an
auxiliary prime and `w` be `v` or its conjugate. For a generator `γ` of tame inertia at a place `A`
of `Ω` above `w`, the valuation of `ψ γ - 1` is at most that of `ζ v - 1`, since `ζ v` is a power of
`ψ γ`. -/
lemma ellVal_twist_tameGenerator_sub_one_le
    (hζ : ∀ v : X.auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1)
    (hS₀ : placesDividing E ℓ ⊆ S₀) (v : X.auxPrimes) {w : FinPlace E}
    (hw : w = v ∨ w = star (v : FinPlace E)) {A : ClosurePlace} (hA : IsPlaceOver A w)
    {γ : inertiaGroup Gal(Ω/E) A} (hγ : IsTameGenerator γ) :
    ellVal (X.twist hζ γ - 1) ≤ ellVal (ζ v - 1).val := by
  have hwℓ : w ∉ placesDividing E ℓ := by
    obtain ⟨hv : v.val ∉ S₀, -, -, hv_star : star v.val ∉ S₀⟩ := X.auxiliary v v.property
    obtain rfl | rfl := hw
    exacts [fun hvℓ ↦ hv (hS₀ hvℓ), fun hvℓ ↦ hv_star (hS₀ hvℓ)]
  obtain ⟨g, hg, h_value⟩ : ∃ g ∈ inertiaAbove {w}, X.twist hζ g = ζ v :=
    X.exists_mem_inertiaAbove_twist_eq hζ v hw
  obtain ⟨a, ha⟩ : ∃ a : ℕ, X.twist hζ g = X.twist hζ γ ^ a :=
    exists_map_eq_map_pow_of_isTameGenerator (X.isFromU1_twist hζ).isLocallyConstant
      (X.twist_pow_eq_one hζ) hA (by simp [hA.valuation_natCast_eq_one_iff.2 hwℓ]) hγ hg
  have h_fin : IsOfFinOrder (X.twist hζ γ) := isOfFinOrder_iff_pow_eq_one.2
    ⟨ℓ ^ N, NeZero.pos _, DFunLike.congr_fun (X.twist_pow_eq_one hζ) _⟩
  refine ellVal_le_ellVal ?_
  calc
    ‖(ζ v - 1).val‖ = ‖X.twist hζ γ ^ a - 1‖ := by
      rw [← ha, h_value, AddSubgroupClass.coe_sub, OneMemClass.coe_one]
    _ ≤ ‖X.twist hζ γ - 1‖ :=
      Period.norm_pow_sub_one_le_norm_sub_one h_fin.norm_eq_one.le a

open scoped Classical in
/-- Let `X` be twist polynomials, with a set `X.auxPrimes` of at most `s₀ / 2` auxiliary primes and
homomorphisms `λ_v` from `Gal(Ω/E)` to `ℤ / ℓ ^ N`, one for each prime `v` of `X.auxPrimes`. Let
`ζ v` be `ℓ ^ N`-th roots of unity and `ψ = X.twist hζ = ∏ (ζ v) ^ λ_v`. Let `S₀` contain the
places above `ℓ`, and let all `ζ v - 1` have valuation at most `r`, for the valuation `ellVal`
that is `1` at `ℓ`. For any generators `γ w` of tame inertia at places `A w` of `Ω` above `w`, the
sum of the valuations of `ψ (γ w) - 1`, over the primes `w` of `X.auxPrimes` and their conjugates,
is at most `s₀ r`. -/
lemma sum_ellVal_twist_tameGenerator_sub_one_le
    (hζ : ∀ v : X.auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1)
    (hS₀ : placesDividing E ℓ ⊆ S₀) (h_far : ∀ v : X.auxPrimes, ellVal (ζ v - 1).val ≤ (r : ℝ≥0))
    {A : FinPlace E → ClosurePlace} (hA : ∀ w : FinPlace E, IsPlaceOver (A w) w)
    {γ : ∀ w : FinPlace E, inertiaGroup Gal(Ω/E) (A w)}
    (hγ : ∀ w : FinPlace E, IsTameGenerator (γ w)) :
    ∑ w ∈ X.auxPrimes ∪ X.auxPrimes.image star, ellVal (X.twist hζ (γ w) - 1) ≤ s₀ * (r : ℝ≥0) := by
  have h_term : ∀ w ∈ X.auxPrimes ∪ X.auxPrimes.image star,
      ellVal (X.twist hζ (γ w) - 1) ≤ (r : ℝ≥0) := by
    intro w hw
    obtain ⟨v, hv⟩ : ∃ v : X.auxPrimes, w = v ∨ w = star v.val := by
      obtain hw | hw := mem_union.1 hw
      · exact ⟨⟨w, hw⟩, .inl rfl⟩
      · obtain ⟨v, hv, rfl⟩ := mem_image.1 hw
        exact ⟨⟨v, hv⟩, .inr rfl⟩
    exact (X.ellVal_twist_tameGenerator_sub_one_le hζ hS₀ v hv (hA w) (hγ w)).trans (h_far v)
  have h_card : #(X.auxPrimes ∪ X.auxPrimes.image star) ≤ s₀ := by
    grw [card_union_le, card_image_le, ← two_mul, X.two_mul_card_le]
  grw [sum_le_card_nsmul _ _ _ h_term, h_card, nsmul_eq_mul]

open scoped Classical in
/-- Let `T i` be Selmer data and `Y k` Stickelberger systems. Let `X` be twist polynomials with
primes `Q = X.auxPrimes`, let `ζ v` be `ℓ ^ N`-th roots of unity for `v ∈ Q`, let `ψ = X.twist hζ`
and let `x` be the point `(ζ v - 1)_v`. The valuation of `X.datumPoly i` at `x` bounds the length of
the Selmer group of `T i` twisted by `ψ` when it is below `O.normLength (T i).β + 1`, and the value
of `X.systemPoly k` at `x` is `ψ(Θ_Q)`. Suppose that `S₀` contains the places above `ℓ`, that all
`ζ v - 1` have valuation at most `r`, with `s₀ r ≤ ε < 1`, and that these polynomials have at `x`
valuation at most `O.normLength (T i).β + ε` and `(Y k).β + ε`. Then `ψ` satisfies `IsSmallTwist`:
it is anticyclotomic of tame level `Q`, of `ℓ`-power order and ramified at every prime of `Q`; the
Selmer lengths are at most `O.normLength (T i).β + ε`; the valuations of the `ψ(Θ_Q)` are at most
`(Y k).β + ε`; and the valuations of `ψ(γ_w) - 1`, for generators `γ_w` of tame inertia above the
primes `w` of `Q` and their conjugates, have sum at most `ε`. -/
lemma isSmallTwist_twist (hζ : ∀ v : X.auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1)
    (hS₀ : placesDividing E ℓ ⊆ S₀) {ε : ℝ≥0} (hε : ε < 1) (hr : s₀ * (r : ℝ≥0) ≤ ε)
    (h_far : ∀ v : X.auxPrimes, ellVal (ζ v - 1).val ≤ (r : ℝ≥0))
    (h_datum : ∀ i : ι,
      ellVal (eval (fun v : X.auxPrimes ↦ ζ v - 1) (X.datumPoly i)).val ≤ O.normLength (T i).β + ε)
    (h_system : ∀ k : κ,
      ellVal (eval (fun v : X.auxPrimes ↦ ζ v - 1) (X.systemPoly k)).val ≤ (Y k).β + ε) :
    IsSmallTwist T Y ε X.auxPrimes (X.twist hζ) where
  isFromU1 := X.isFromU1_twist hζ
  exists_pow_eq_one := ⟨N, X.twist_pow_eq_one hζ⟩
  ramified v hv := by
    obtain ⟨g, hg, h_value⟩ : ∃ g ∈ inertiaAbove {v}, X.twist hζ g = ζ ⟨v, hv⟩ :=
      X.exists_mem_inertiaAbove_twist_eq hζ ⟨v, hv⟩ (.inl rfl)
    have h_finite : ellVal (ζ ⟨v, hv⟩ - 1).val ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (h_far _)
    exact ⟨g, hg, by simpa [h_value, ellVal_eq_top_iff, sub_eq_zero] using h_finite⟩
  length_le i := by
    have h_lt : O.normLength (T i).β + ε < O.normLength (T i).β + 1 :=
      ENNReal.add_lt_add_left (normLength_ne_top (T i).β_ne_top) (mod_cast hε)
    exact (X.length_le ζ hζ i ((h_datum i).trans_lt h_lt)).mono (h_datum i)
  ellVal_value_le k := (congrArg ellVal (X.groupRingEval_eq_eval ζ hζ k)).trans_le (h_system k)
  sum_le_of_isTameGenerator _ hA _ hγ :=
    (X.sum_ellVal_twist_tameGenerator_sub_one_le hζ hS₀ h_far hA hγ).trans (mod_cast hr)

end TwistPolynomials

/-- Let natural numbers `s₀` and `m ≥ 1`, a rational `r > 0`, finitely many finite bounds `β i` and
`ε > 0` be given, and write `v` for the valuation `ellVal` on the ring `intQpBar ℓ` of integers of
`PadicAlgCl ℓ`. There is an `h₀` with the following property. If the `P i` are integral polynomials
in at most `s₀` variables and the coordinates of the points `x i` have valuation at least `r`, with
`v(P i (x i)) ≤ β i`, then there are roots of unity `ζ_u` of order dividing `ℓ ^ h₀`, one for each
variable `u`, with `v(ζ_u - 1) ≤ r / m` and `v(P i ((ζ_u ^ j - 1)_u)) ≤ v(P i (x i)) + ε` for
`1 ≤ j ≤ m`. -/
lemma exists_rootsOfUnity_ellVal_eval_le (s₀ : ℕ) {m : ℕ} (hm : 1 ≤ m) {r : ℚ≥0} (hr : 0 < r)
    [Finite ι] {β : ι → ℝ≥0∞} (hβ : ∀ i : ι, β i ≠ ⊤) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ h₀ : ℕ, ∀ (σ : Type) [Fintype σ] (P : ι → MvPolynomial σ (intQpBar ℓ))
      (x : ι → σ → intQpBar ℓ), Fintype.card σ ≤ s₀ →
      (∀ (i : ι) (u : σ), (r : ℝ≥0) ≤ ellVal (x i u).val) →
      (∀ i : ι, ellVal (eval (x i) (P i)).val ≤ β i) →
      ∃ ζ : σ → intQpBar ℓ,
        (∀ u : σ, ζ u ^ ℓ ^ h₀ = 1) ∧
        (∀ u : σ, ellVal (ζ u - 1).val ≤ (↑(r / m) : ℝ≥0)) ∧
        ∀ i : ι, ∀ j ∈ Set.Icc 1 m,
          ellVal (eval (fun u : σ ↦ ζ u ^ j - 1) (P i)).val ≤
            ellVal (eval (x i) (P i)).val + ε := by
  -- Apply the case of one exponent to the polynomials `P^{(j)}` that arise from `P` by putting
  -- `(1 + X) ^ j - 1` for each variable `X`, with points `x'` such that `(1 + x') ^ j = 1 + x`.
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0, (B : ℝ≥0∞) = ∑ p : ι × Set.Icc 1 m, β p.1 :=
    ENNReal.canLift.prf _ (ENNReal.sum_ne_top.2 fun p _ ↦ hβ p.1)
  obtain ⟨h₀, h_roots⟩ :=
    exists_rootsOfUnity_ellVal_eval_le_add (ℓ := ℓ) s₀ (show 0 < r / m by positivity) B hε
  refine ⟨h₀, fun σ _ P x h_card hx hP ↦ ?_⟩
  let Ppow (p : ι × Set.Icc 1 m) : MvPolynomial σ (intQpBar ℓ) :=
    aeval (fun u : σ ↦ ((1 + X u) ^ (p.2 : ℕ) - 1 : MvPolynomial σ (intQpBar ℓ))) (P p.1)
  have eval_Ppow (p : ι × Set.Icc 1 m) (y : σ → intQpBar ℓ) :
      eval y (Ppow p) = eval (fun u : σ ↦ (1 + y u) ^ (p.2 : ℕ) - 1) (P p.1) := by
    simp only [Ppow, eval_aeval, map_sub, map_pow, map_add, map_one, eval_X]
  have h_point : ∀ (p : ι × Set.Icc 1 m) (u : σ), ∃ x' : intQpBar ℓ,
      (1 + x') ^ (p.2 : ℕ) - 1 = x p.1 u ∧ (↑(r / m) : ℝ≥0) ≤ ellVal x'.val :=
    fun p u ↦ exists_one_add_pow_eq p.2.property (hx p.1 u)
  choose x' hx'_pow hx'_val using h_point
  have h_eq (p : ι × Set.Icc 1 m) : eval (x' p) (Ppow p) = eval (x p.1) (P p.1) := by
    simp only [eval_Ppow, hx'_pow]
  have h_sum : ∑ p : ι × Set.Icc 1 m, ellVal (eval (x' p) (Ppow p)).val ≤ B := by
    simpa only [hB, h_eq] using sum_le_sum fun p _ ↦ hP p.1
  obtain ⟨ζ, hζ, hζ_far, hζ_val⟩ : ∃ ζ : σ → intQpBar ℓ,
      (∀ u : σ, ζ u ^ ℓ ^ h₀ = 1) ∧
      (∀ u : σ, ellVal (ζ u - 1).val ≤ (↑(r / m) : ℝ≥0)) ∧
      ∀ p : ι × Set.Icc 1 m, ellVal (eval (fun u : σ ↦ ζ u - 1) (Ppow p)).val ≤
        ellVal (eval (x' p) (Ppow p)).val + ε :=
    h_roots σ (ι × Set.Icc 1 m) Ppow x' h_card hx'_val h_sum
  refine ⟨ζ, hζ, hζ_far, fun i j hj ↦ ?_⟩
  simpa only [h_eq, eval_Ppow, add_sub_cancel] using hζ_val (i, ⟨j, hj⟩)

/-- The twisting theorem, general form. Let `E` be a CM number field inside the algebraic closure
`Ω` of `ℚ`, let `ℓ` be a prime, `v` the valuation of `PadicAlgCl ℓ` with `v(ℓ) = 1`, and `O` the
ring of integers of a finite Galois extension of `ℚ_ℓ`; lengths are scaled so that
`len (O / ℓ) = 1`. Let `S₀` be a finite set of places of `E` that contains those above `ℓ`, and let
`g₀` be inertial at a place of `S₀` prime to `ℓ`. Finitely many objects of two kinds are given.
* A Selmer datum `T i` is a lattice over `O` with an action `ρ` of `Gal(Ω/E)` unramified outside
  `S₀` and local conditions above `ℓ`. Its number `β_T` is a finite sum of lengths: a global term,
  local terms at places of `S₀` prime to `ℓ`, and the valuations of `det(ρ g - 1)` for `g = g₀` and
  for the inverse of its complex conjugate.
* A Stickelberger system `Y k` has a character `ϑ` and elements `Θ_Q` of the group rings of class
  groups `Cl_Q` with a norm relation. Its number `β` is the valuation of the trivial character at
  `Θ_∅` plus a multiple of `v(ϑ g₀ - 1)`.

The ring `O` is large enough: `IsTorsionLevel T M` says that `M > β_T + 1` for each datum and that
the residue field of `O` has more than `2 rank(T i) a + 1` elements, where `a` is the unscaled
length of `O / ℓ ^ M` (`frequently_lt_card_residueField` gives such rings). Let `m ≥ 1` and `ε > 0`.
Then there are an auxiliary set `Q` (primes of prime norm such that neither they nor their
conjugates lie in `S₀` and their conjugates lie outside `Q`) and a character `ψ` of `Gal(Ω/E)` such
that each `χ` among `ψ, …, ψ ^ m` satisfies `IsSmallTwist`. That is, `χ` comes by `y ↦ y / ȳ` from
an idele class character of tame level `Q` trivial above `ℓ`, has `ℓ`-power order, is ramified at
every prime of `Q`, and
* the Selmer group of each `T i` twisted by `χ` has length at most `β_T + ε`;
* `v(χ(Θ_Q)) ≤ β + ε` for each `Y k`;
* `∑ v(χ(γ_w) - 1) ≤ ε`, over the primes `w` of `Q` and their conjugates, for any generators `γ_w`
  of tame inertia above `w`. -/
theorem exists_anticyclotomic_twist [Finite ι] [Finite κ] (hS₀ : placesDividing E ℓ ⊆ S₀)
    (hg₀ : g₀ ∈ inertiaAbove (S₀ \ placesDividing E ℓ)) {M : ℕ} (hM : IsTorsionLevel T M)
    {m : ℕ} (hm : 1 ≤ m) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ (Q : Finset (FinPlace E)) (ψ : Gal(Ω/E) →* PadicAlgCl ℓ),
      IsAuxiliary S₀ Q ∧ ∀ j ∈ Set.Icc 1 m, IsSmallTwist T Y ε Q (ψ ^ j) := by
  -- The polynomials of the twists come with points at which they have small valuation. Roots of
  -- unity `ζ` are found such that, for all data, systems and exponents `j ≤ m` at once, the
  -- valuations at `ζ ^ j - 1` exceed these by at most `ε / 2`.
  wlog hε_one : ε < 1 generalizing ε with h_small
  · obtain ⟨Q, ψ, hQ, hψ⟩ := h_small one_half_pos one_half_lt_one
    exact ⟨Q, ψ, hQ, fun j hj ↦ (hψ j hj).mono T Y (one_half_lt_one.le.trans (not_lt.1 hε_one))⟩
  -- Choose `s₀`, then `r`, then `h₀`, and only then the level `N ≥ h₀` and the polynomials.
  obtain ⟨s₀, hs₀, h_eventually⟩ : ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ r : ℚ≥0, 0 < r → s₀ * r < 1 →
      ∀ᶠ N : ℕ in atTop, Nonempty (TwistPolynomials T Y s₀ r N) :=
    exists_twistPolynomials T Y hg₀ hM
  obtain ⟨r, hr_pos, hr_ε⟩ : ∃ r : ℚ≥0, 0 < r ∧ s₀ * (r : ℝ≥0) ≤ ε / 2 :=
    exists_nnrat_mul_le s₀ (half_pos hε)
  have hr_one : s₀ * r < 1 := mod_cast (hr_ε.trans (half_le_self hε.le)).trans_lt hε_one
  let β : ι ⊕ κ → ℝ≥0∞ := Sum.elim (fun i ↦ O.normLength (T i).β) fun k ↦ (Y k).β
  have hβ : ∀ s : ι ⊕ κ, β s ≠ ⊤ :=
    Sum.forall.2 ⟨fun i ↦ normLength_ne_top (T i).β_ne_top, fun k ↦ (Y k).β_ne_top⟩
  obtain ⟨h₀, h_roots⟩ := exists_rootsOfUnity_ellVal_eval_le (ℓ := ℓ) s₀ hm hr_pos
    (β := fun s ↦ β s + 1) (fun s ↦ ENNReal.add_ne_top.2 ⟨hβ s, ENNReal.one_ne_top⟩) (half_pos hε)
  obtain ⟨N, ⟨X⟩, hN⟩ : ∃ N : ℕ, Nonempty (TwistPolynomials T Y s₀ r N) ∧ h₀ ≤ N :=
    ((h_eventually r hr_pos hr_one).and (eventually_ge_atTop h₀)).exists
  let P : ι ⊕ κ → MvPolynomial X.auxPrimes (intQpBar ℓ) := Sum.elim X.datumPoly X.systemPoly
  let x : ι ⊕ κ → X.auxPrimes → intQpBar ℓ := Sum.elim X.datumPoint X.systemPoint
  have hx : ∀ (s : ι ⊕ κ) (v : X.auxPrimes), (r : ℝ≥0) ≤ ellVal (x s v).val :=
    Sum.forall.2 ⟨X.le_ellVal_datumPoint, X.le_ellVal_systemPoint⟩
  have hP : ∀ s : ι ⊕ κ, ellVal (eval (x s) (P s)).val ≤ β s + s₀ * (r : ℝ≥0) :=
    Sum.forall.2 ⟨X.ellVal_datumPoly_le, X.ellVal_systemPoly_le⟩
  have h_card : Fintype.card X.auxPrimes ≤ s₀ := by
    simpa using (Nat.le_mul_of_pos_left _ two_pos).trans X.two_mul_card_le
  have hP_one (s : ι ⊕ κ) : ellVal (eval (x s) (P s)).val ≤ β s + 1 :=
    (hP s).trans (add_le_add_right (mod_cast hr_one.le) (β s))
  obtain ⟨ζ, hζ, hζ_far, hζ_val⟩ : ∃ ζ : X.auxPrimes → intQpBar ℓ,
      (∀ v : X.auxPrimes, ζ v ^ ℓ ^ h₀ = 1) ∧
      (∀ v : X.auxPrimes, ellVal (ζ v - 1).val ≤ (↑(r / m) : ℝ≥0)) ∧
      ∀ s : ι ⊕ κ, ∀ j ∈ Set.Icc 1 m, ellVal (eval (fun v : X.auxPrimes ↦ ζ v ^ j - 1) (P s)).val ≤
        ellVal (eval (x s) (P s)).val + (ε / 2 : ℝ≥0) :=
    h_roots X.auxPrimes P x h_card hx hP_one
  have hζ_N (v : X.auxPrimes) : (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1 := by
    rw [← Nat.add_sub_of_le hN, pow_add, pow_mul, ← SubmonoidClass.coe_pow, hζ]
    simp
  have h_value (s : ι ⊕ κ) {j : ℕ} (hj : j ∈ Set.Icc 1 m) :
      ellVal (eval (fun v ↦ (ζ ^ j) v - 1) (P s)).val ≤ β s + ε :=
    calc
      ellVal (eval (fun v ↦ (ζ ^ j) v - 1) (P s)).val
          ≤ ellVal (eval (x s) (P s)).val + (ε / 2 : ℝ≥0) := hζ_val s j hj
      _ ≤ β s + s₀ * (r : ℝ≥0) + (ε / 2 : ℝ≥0) := by grw [hP]
      _ ≤ β s + (ε / 2 : ℝ≥0) + (ε / 2 : ℝ≥0) := by
        gcongr
        exact_mod_cast hr_ε
      _ = β s + ε := by rw [add_assoc, ← ENNReal.coe_add, add_halves]
  have hr_lt : r < 1 := (le_mul_of_one_le_left hr_pos.le (mod_cast hs₀)).trans_lt hr_one
  refine ⟨X.auxPrimes, X.twist hζ_N, X.auxiliary, fun j hj ↦ ?_⟩
  have h_far : ∀ v : X.auxPrimes, ellVal ((ζ ^ j) v - 1).val ≤ (r : ℝ≥0) :=
    fun v ↦ ellVal_pow_sub_one_le hr_lt hj (hζ v) (hζ_far v)
  rw [X.twist_pow hζ_N j]
  exact X.isSmallTwist_twist _ hS₀ hε_one (hr_ε.trans (half_le_self hε.le)) h_far
    (fun i ↦ h_value (.inl i) hj) fun k ↦ h_value (.inr k) hj

end New.Selmer

end
