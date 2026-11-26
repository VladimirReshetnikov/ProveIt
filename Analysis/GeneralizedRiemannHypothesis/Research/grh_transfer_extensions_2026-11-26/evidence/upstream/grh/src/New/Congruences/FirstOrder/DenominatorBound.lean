import New.Congruences.FirstOrder.AuxiliaryPrimeTie
import New.Congruences.FirstOrder.HeckeStrings
import New.Congruences.FirstOrder.RibetElement
import New.Congruences.FirstOrder.TrianglePrimes
import New.Congruences.GaloisRepresentations.BaseLevelOfLabel

/-!
# The bound for denominators

The bound that Ribet's method gives for the denominator of the orthogonal projection to `Z`: an
operator on `Z`, with eigenvalues of bounded valuation, takes the projection of every integral form
orthogonal to the false lifts to an integral form. `O` is a descent pair of hermitian spaces of
ranks `r < n` (`New.DescentPair`). `Z` is a subspace of its forms spanned by vectors in the ranges
of the idempotents `New.Selmer.typeProjection O c` of types `c` in lift setting.

The *chain* at a place of norm `q` is `∏ (X - q ^ i)`, `i < t'`, with `t' = O.rankDiff`.

* `New.Selmer.typeProjection_sub_starProjection_mem_of_isOrthogonalToFalseLifts`: a form orthogonal
  to the false lifts differs from its projection to `Z`, in each type, only outside the weak lifts.
* `New.Selmer.exists_operator_ellVal_le_liftValuationBound`: the bound for denominators. An operator
  on `Z` preserves the Hecke eigenspaces, has eigenvalues of valuation at most
  `New.Selmer.liftValuationBound` and takes projections of integral forms orthogonal to the false
  lifts to integral forms.
* `New.Selmer.denominatorLe_clearingBound`: if `Z` is spanned by lifts whose twisted main summands
  have small Selmer groups with divisible coefficients (`New.Selmer.IsLiftGenerator`), then
  `New.Selmer.DenominatorLe` holds with exponent `β log ℓ`, where
  `β = New.Selmer.clearingBound D ℓ`. Its operator is `D.chosenGroupOrder` times that of
  `exists_operator_ellVal_le_liftValuationBound` (`New.Selmer.exists_operator_det_clearingBound`).

Notions from other files:
* `New.Selmer.AbsGal`: the absolute Galois group of the CM field `D.E` of the data `D`.
* `New.Data.chosenGroupOrder`: the product, over the chosen places above `D.levelPrime 0` and
  `D.levelPrime 1`, of the orders of the groups `GL (D.r * D.t)` over the residue fields.
* `New.Patching.Isotypic`: a system, that is the space of forms with given Hecke eigenvalues at
  almost all places. `B.Eigensystem L` is the set of systems that contain a nonzero form of level
  `L` over the base data `B`; the base level is `L = ![]`.
* `New.Selmer.normalisedRep`: the twist of a Galois representation by the character
  `normalizingAvatar O`.
* `New.Selmer.IsAuxTwist`: the character is anticyclotomic, its modulus avoids the given places and
  its ramification has bounded valuation.

## Relation to the literature

For a twist with short Selmer groups, an operator of bounded ℓ-adic valuation clears the denominator
of the projection to theta lifts on integral forms orthogonal to the false lifts. The bound counts
local losses, class number, level, odd classes and congruences between the characters; the orders of
the even classes, where Vandiver's conjecture lives, do not enter. Ribet-type bounds, Taylor–Wiles
primes in the residually reducible case and the mass formula case are treated in the following
works. Related work: Dasgupta–Kakde–Silliman–Wang, The residually indistinguishable case of Ribet's
method for GL2, 2023; Dotto–Thorne, Modularity of residually reducible representations of rank 2,
2026; Martin–Wakatsuki, Mass formulas and Eisenstein congruences in higher rank, 2024.
-/

namespace New.Selmer

open Polynomial Fintype Module Filter Patching Isotypic Real LinearMap LevelPlaces.LevelForm
  Submodule IsLiftSetting NeZero OddPart PadicInt Units

/-- Let the prime `ℓ` exceed the square of `D.halfGap = D.r ^ 8`. Then some element `γ` of the
absolute Galois group of `D.E` has an `ℓ`-adic cyclotomic character `u` with `u ^ a - 1` a unit of
`ℤ_ℓ` for `0 < a < D.t`, where `D.t = 5 * D.r`. -/
lemma exists_isUnit_cyclotomicChar_pow_sub_one {P : Parameters} (D : Data P) {ℓ : ℕ} [ThePrime ℓ]
    (hℓ : D.halfGap ^ 2 < ℓ) :
    ∃ γ : AbsGal D, ∀ a ∈ Set.Ioo 0 D.t, IsUnit ((cyclotomicChar Ω ℓ γ ^ a).val - 1) := by
  -- Take `γ` in an inertia group of `ℚ` at `ℓ` whose cyclotomic character reduces to a generator
  -- `b` of `(ZMod ℓ)ˣ`.
  obtain ⟨b, hb⟩ : ∃ b : (ZMod ℓ)ˣ, orderOf b = Nat.card (ZMod ℓ)ˣ :=
    IsCyclic.exists_ofOrder_eq_natCard
  let A : ClosurePlace := (intQpBar ℓ).comap (IsAlgClosed.lift : Ω →ₐ[ℚ] PadicAlgCl ℓ).toRingHom
  have hA : A.valuation ℓ < 1 := valuation_comap_intQpBar_lt_one _
  obtain ⟨γ, hγ, hγb⟩ : ∃ γ ∈ inertiaGroup Gal(Ω/ℚ) A,
      (cyclotomicChar Ω ℓ γ).val = (b : ZMod ℓ).val :=
    exists_inertia_cyclotomicChar_eq hA (ZMod.val_coe_unit_coprime b).symm
  -- `E` lies in the cyclotomic field of level `D.cyclotomicConductor`, prime to `ℓ`, so `γ` fixes
  -- `E`.
  have h_cond : D.cyclotomicConductor ≤ D.halfGap ^ 2 := D.nat_le_of_hasLogBound
  have h_coprime : ℓ.Coprime D.cyclotomicConductor :=
    Nat.coprime_of_lt_prime (NeZero.ne _) (h_cond.trans_lt hℓ) Fact.out
  have h_fixes (x : D.E) : γ (algebraMap D.E Ω x) = algebraMap D.E Ω x :=
    D.algebraMap_mem_cycloField x
      ⟨γ, cyclotomicCharMod_eq_one_of_mem_inertiaGroup hγ (h_coprime.valuation_eq_one hA)⟩
  let σ : AbsGal D := {γ with commutes' := h_fixes}
  -- `σ` and `γ` are the same ring automorphism of `Ω`.
  have hσb : (cyclotomicChar Ω ℓ σ).val = (b : ZMod ℓ).val := hγb
  refine ⟨σ, fun a ⟨ha_pos, ha_lt⟩ ↦ IsUnit.of_map toZMod _ ?_⟩
  -- `b` has order `ℓ - 1` and `0 < a < t ≤ halfGap ^ 2 < ℓ`, so `b ^ a ≠ 1`.
  have h_order : orderOf (b : ZMod ℓ) = ℓ - 1 := by
    rw [orderOf_units, hb, Nat.card_units, Nat.card_zmod]
  have ht : D.t ≤ D.halfGap ^ 2 := D.nat_le_of_hasLogBound
  have h_ne : (b : ZMod ℓ) ^ a ≠ 1 := pow_ne_one_of_lt_orderOf ha_pos.ne' (by lia)
  simpa [hσb, sub_eq_zero] using h_ne

/-- Some element `φ` of the absolute Galois group of `D.E` has an `ℓ`-adic cyclotomic character `u`
such that for `0 < a < D.t` the number `u ^ a - 1` divides, in `ℤ_ℓ`, the `ℓ`-part of
`D.chosenGroupOrder`, the product of the orders of `GL (D.r * D.t)` over the residue fields of the
chosen places. -/
lemma exists_cyclotomicChar_pow_sub_one_dvd_pow_padicValNat {P : Parameters} (D : Data P) (ℓ : ℕ)
    [ThePrime ℓ] :
    ∃ φ : AbsGal D, ∀ a ∈ Set.Ioo 0 D.t,
      (cyclotomicChar Ω ℓ φ ^ a).val - 1 ∣ ℓ ^ padicValNat ℓ D.chosenGroupOrder := by
  -- Take a Frobenius at a place `v` of norm `D.levelPrime i` not above `ℓ`.
  obtain ⟨v, i, -, ⟨-, hv⟩, hq⟩ : ∃ (v : FinPlace D.E) (i : Fin 2),
      D.IsChosen v ∧ v ∈ placesAboveM D \ placesDividing D.E ℓ ∧ v.q = D.levelPrime i :=
    exists_chosen_notMem_placesDividing D ℓ
  obtain ⟨φ, hφ⟩ : ∃ φ : AbsGal D, IsFrob (placeOver v) v.q φ :=
    v.isPlaceOver_placeOver.exists_isFrob (AbsGal D)
  have h_cyc : (cyclotomicChar Ω ℓ φ).val = D.levelPrime i := by
    rw [hφ.cyclotomicChar_eq ℓ (v.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2 hv), hq]
  refine ⟨φ, fun a ⟨ha_pos, ha_lt⟩ ↦ ?_⟩
  have h_dvd : D.levelPrime i ^ a - 1 ∣ D.chosenGroupOrder :=
    levelPrime_pow_sub_one_dvd_chosenGroupOrder D ⟨ha_pos, ha_lt.le.trans D.nat_le_of_hasLogBound⟩
  calc (cyclotomicChar Ω ℓ φ ^ a).val - 1
      = ((D.levelPrime i ^ a - 1 : ℕ) : ℤ_[ℓ]) := by simp [h_cyc, NeZero.pos]
    _ ∣ (D.chosenGroupOrder : ℤ_[ℓ]) := Nat.cast_dvd_cast h_dvd
    _ ∣ ℓ ^ padicValNat ℓ D.chosenGroupOrder := by
      -- a nonzero `ℓ`-adic integer is a unit times the power of `ℓ` given by its valuation
      have h_ne : (D.chosenGroupOrder : ℤ_[ℓ]) ≠ 0 := NeZero.out
      simpa [PadicInt.valuation] using (unitCoeff_spec h_ne).dvd

/-- There are `h`, at most the `ℓ`-adic valuation of `D.chosenGroupOrder` and zero unless
`ℓ ≤ D.halfGap ^ 2`, and a topological generator `γ` of the Galois group of `D.E` modulo the kernel
of the cyclotomic character such that `u ^ a - 1` divides `ℓ ^ h` in `ℤ_ℓ` for `0 < a < D.t`, where
`u` is the cyclotomic character of `γ`. -/
lemma exists_cyclotomicChar_pow_sub_one_dvd {P : Parameters} (D : Data P) (ℓ : ℕ) [ThePrime ℓ] :
    ∃ h ≤ padicValNat ℓ D.chosenGroupOrder,
      (ℓ ≤ D.halfGap ^ 2 ∨ h = 0) ∧
      ∃ γ : AbsGal D, (cyclotomicChar Ω ℓ).IsGeneratorModKer γ ∧
        ∀ a ∈ Set.Ioo 0 D.t, (cyclotomicChar Ω ℓ γ ^ a).val - 1 ∣ ℓ ^ h := by
  have h_four : (2 ^ 2 : ℤ_[ℓ]) = 4 := by norm_num
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : AbsGal D, (cyclotomicChar Ω ℓ).IsGeneratorModKer g₀ :=
    exists_isGeneratorModKer (continuous_cyclotomicChar ℓ) fun g ↦ by
      simpa [h_four] using four_dvd_cyclotomicChar_sub_one g
  -- Any `γ` with the divisibility may be replaced by the generator `g₀`.
  have h_gen (a : ℕ) (γ : AbsGal D) :
      (cyclotomicChar Ω ℓ g₀ ^ a).val - 1 ∣ (cyclotomicChar Ω ℓ γ ^ a).val - 1 :=
    hg₀.pow_sub_one_dvd (continuous_cyclotomicChar ℓ) a γ
  rcases lt_or_ge (D.halfGap ^ 2) ℓ with hℓ | hℓ
  · obtain ⟨γ, hγ⟩ := exists_isUnit_cyclotomicChar_pow_sub_one D hℓ
    exact ⟨0, bot_le, .inr rfl, g₀, hg₀, fun a ha ↦ (h_gen a γ).trans (hγ a ha).dvd⟩
  · obtain ⟨φ, hφ⟩ := exists_cyclotomicChar_pow_sub_one_dvd_pow_padicValNat D ℓ
    exact ⟨padicValNat ℓ D.chosenGroupOrder, le_rfl, .inl hℓ, g₀, hg₀,
      fun a ha ↦ (h_gen a φ).trans (hφ a ha)⟩

/-- The system `x` (an isotypic space of forms for the descent pair `O`) is a weak lift: at every
Galois element the characteristic polynomial of its normalised representation has the root `1`. -/
def IsWeakLift {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {r n : Type}
    [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] (O : DescentPair D.E r n)
    (x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)) : Prop :=
  ∀ g : AbsGal D, (normalisedRep O x.galRep g).val.charpoly.IsRoot 1

/-- The form `v` of the descent pair `O` is a nonzero form of the isotypic space `x`. -/
structure IsNonzeroIn {P : Parameters} {D : Data P} {r n : Type} [Fintype r] [DecidableEq r]
    [Fintype n] [DecidableEq n] {O : DescentPair D.E r n} (v : O.FormV)
    (x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)) : Prop where
  /-- The algebraic form `v.toSmoothForm` of `v` lies in `x`. -/
  mem : v.toSmoothForm ∈ x.val
  /-- The algebraic form `v.toSmoothForm` of `v` is not zero. -/
  ne_zero : v.toSmoothForm ≠ 0
/-- The system `x` lifts a row `R` (`IsMainSummandLike`: a representation of rank `r` with the
properties of a main summand): the trace of its normalised representation is that of `R` twisted
by `ϑ.invAvatar` plus the powers `e < O.rankDiff` of the inverse cyclotomic character. The twist
has a lattice on which some `γ` acts by a scalar `y` and, if `x = x₀`, its Selmer group with
divisible coefficients has length at most `sel`. -/
abbrev IsLiftWithTwistedLattice {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
    {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] (O : DescentPair D.E r n)
    (ϑ : D.Twist) (sel : ENNReal)
    (x₀ x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)) : Prop :=
  ∃ (wt : (D.E →+* ℂ) → Multiset ℤ) (R : GalRep ℓ D.E r),
    IsMainSummandLike (n := r) D O.rankDiff wt R ∧
    HasLiftTrace ϑ.invAvatar R O.rankDiff (normalisedRep O x.galRep) ∧
    ∃ (γ : Gal(Ω/D.E)) (y : intQpBar ℓ), HasTwistedLattice ϑ.invAvatar R γ y ∧
      (x = x₀ → HasDivisibleSelmerLengthLe ϑ.invAvatar R ϑ.Q γ y sel)


/-- The bound `sel + 2 t′ ram + r′ loc + err` for the valuations of the eigenvalues of the operator
that clears denominators. Here `r′ = card r`, `t′ = O.rankDiff`, `loc = localDefectBound D ℓ` and
`err = denominatorError D ℓ`; `ram` bounds the ramification of the twist and `sel` the lengths of
the Selmer groups. -/
noncomputable def liftValuationBound {P : Parameters} {D : Data P} (ℓ : ℕ) [ThePrime ℓ]
    {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] (O : DescentPair D.E r n)
    (ram sel : ENNReal) : ENNReal :=
  sel + 2 * O.rankDiff * ram + card r * localDefectBound D ℓ + denominatorError D ℓ

/-- Let `ϑ` be an auxiliary twist of the data `D`, with ramification at most `ram` (`IsAuxTwist`):
the places of `ϑ.Q` and their conjugates avoid `badPlaces D ℓ`, and `ϑ.invAvatar`, the `ℓ`-adic
Galois character of `ϑ⁻¹`, is anticyclotomic with modulus `ϑ.Q`. Then `ϑ.invAvatar` kills the
inertia groups at the places in `placesAboveM D`, those above the two primes `D.levelPrime i`. -/
lemma invAvatar_eq_one_of_mem_inertiaAbove {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] {ϑ : D.Twist} {ram : ENNReal}
    (hϑ : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar ram) {γ : AbsGal D}
    (hγ : γ ∈ inertiaAbove (placesAboveM D)) : ϑ.invAvatar γ = 1 := by
  obtain ⟨v, hv, h_inertia⟩ := hγ
  obtain ⟨h_aux : IsAuxiliary (badPlaces D ℓ) ϑ.Q,
    h_anti : IsFromU1 (placesDividing D.E ℓ) ϑ.Q ϑ.invAvatar, -⟩ := hϑ
  -- The place `v` is bad, and neither a place of an auxiliary set nor its conjugate is.
  have h_bad : v ∈ badPlaces D ℓ := placesDividing_union_subset_badPlaces D ℓ (.inr hv)
  have h_off : v ∉ Set.conjClosure (ϑ.Q : Set (FinPlace D.E)) := by
    rintro (h_mem | h_mem_star)
    · obtain ⟨h_notMem : v ∉ badPlaces D ℓ, -⟩ := h_aux v h_mem
      exact h_notMem h_bad
    · obtain ⟨-, -, -, h_notMem : star (star v) ∉ badPlaces D ℓ⟩ := h_aux (star v) h_mem_star
      exact h_notMem (by rwa [star_star])
  exact h_anti.eq_one_of_mem_inertiaAbove γ ⟨v, h_off, h_inertia⟩

/-- Let `ϑ` be an auxiliary twist of ramification at most `ram` and `B` base data whose systems, the
Hecke eigenspaces of level `![]`, have normalised Galois representations with integral
characteristic polynomials. Let `R` be a row of weights `wt` (`IsMainSummandLike`). For every `ν`
and `g` there is `δ` with trivial cyclotomic character such that, along the filter `mostFrobeniiAt`
at `δ ^ ℓ ^ ν * g`, a place `y.place` with Frobenius `y.frob` satisfies: (a) the place avoids
`badPlaces D ℓ` and is off the base level; (b) if the system `x` is a weak lift and its polynomial
at the Frobenius is congruent to `∏ (X - cyclotomicInv φ ^ i)`, `φ = y.frob`, `i < O.rankDiff`,
times some `S` with `1 ≤ ‖S 1‖`, then its Hecke polynomial at the place, with the variable rescaled
by `normalizingAvatar O φ` read in `ℂ` by the fixed isomorphism `ιℓ`, is the chain `∏ (X - q ^ i)`,
`q` the norm of the place, times a divisor of an integral `e` with `e 1 = 1`; (c) the characteristic
polynomial of the twist of `R` by `ϑ.invAvatar` at the Frobenius has a value of norm at least `1` at
`1`. -/
lemma exists_eventually_hasRootChain_mostFrobeniiAt {P : Parameters} {D : Data P} {ℓ : ℕ}
    [ThePrime ℓ]
    [PadicIso ℓ] {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] [Nonempty n]
    {O : DescentPair D.E r n} {ϑ : D.Twist} {ram : ENNReal}
    (hϑ : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar ram)
    (B : BaseLevel (stdSpace D.E n) (O.columnCount, O.detExp) D.chosenGroupOrder)
    (h_int : ∀ (x : B.Eigensystem ![]) (g : Gal(Ω/D.E)) (i : ℕ),
      ‖(normalisedRep O x.val.galRep g).val.charpoly.coeff i‖ ≤ 1)
    {wt : (D.E →+* ℂ) → Multiset ℤ} {R : GalRep ℓ D.E r} (hR : IsMainSummandLike D O.rankDiff wt R)
    (ν : ℕ) (g : AbsGal D) :
    ∃ δ : Gal(Ω/D.E), cyclotomicChar Ω ℓ δ = 1 ∧
      ∀ᶠ y : FrobeniusDatum D.E in mostFrobeniiAt D.E (δ ^ ℓ ^ ν * g),
        -- (a)
        y.place ∉ badPlaces D ℓ ∧
        B.IsOffLevel ![] y.place ∧
        -- (b)
        (∀ x : B.Eigensystem ![], IsWeakLift O x.val →
          ∀ S : (PadicAlgCl ℓ)[X], 1 ≤ ‖S.eval 1‖ →
          (∀ k : ℕ, ‖(normalisedRep O x.val.galRep y.frob).val.charpoly.coeff k -
            (S * ∏ i ∈ Finset.range O.rankDiff,
              (X - C (cyclotomicInv ℓ D.E (PadicAlgCl ℓ) y.frob ^ i))).coeff k‖ < 1) →
          ∃ e : EllAdicIntegers[X],
            HasRootChain (x.val.heckePolyAt y.place) (e.map (algebraMap EllAdicIntegers ℂ))
              y.place.q (ιℓ.symm (normalizingAvatar O y.frob).val)⁻¹ O.rankDiff ∧
            e.eval 1 = 1) ∧
        -- (c)
        1 ≤ ‖(ϑ.invAvatar y.frob • (R y.frob).val).charpoly.eval 1‖ := by
  -- The inertial `γ` acts on `R` by a scalar `y` of residually large order and is killed by the
  -- twist and by the cyclotomic character.
  obtain ⟨γ, ⟨v, ⟨hv_above, hv_off⟩, h_inertia⟩, y, hγy, hy⟩ :
      ∃ γ ∈ inertiaAbove (placesAboveM D \ placesDividing D.E ℓ),
      ∃ y : PadicAlgCl ℓ, (R γ : Matrix r r (PadicAlgCl ℓ)) = y • 1 ∧
        ∀ a j : ℕ, j ∈ Set.Icc 1 (4 * card r + 2) → ‖(y ^ ℓ ^ a) ^ j - 1‖ = 1 := by
    simpa only [pow_mul] using hR.exists_scalar_inertia
  have h_twist : ϑ.invAvatar γ = 1 :=
    invAvatar_eq_one_of_mem_inertiaAbove hϑ ⟨v, hv_above, h_inertia⟩
  have h_cyc : cyclotomicChar Ω ℓ γ = 1 :=
    cyclotomicChar_eq_one_of_mem_inertiaAbove ⟨v, hv_off, h_inertia⟩
  -- Multiplying by a suitable power of `γ` moves the eigenvalues of the twist `T` away from `1`.
  let T (φ : AbsGal D) : Matrix r r (PadicAlgCl ℓ) := ϑ.invAvatar φ • (R φ).val
  have hT_cont : Continuous T := by
    obtain ⟨-, h_anti : IsFromU1 (placesDividing D.E ℓ) ϑ.Q ϑ.invAvatar, -⟩ := hϑ
    exact h_anti.isLocallyConstant.continuous.smul (continuous_val.comp hR.continuous)
  have hT_scale (i : ℕ) : T ((γ ^ i) ^ ℓ ^ ν * g) = (y ^ ℓ ^ ν) ^ i • T g := by
    simp [T, h_twist, hγy, _root_.smul_pow, smul_comm (ϑ.invAvatar g), pow_right_comm y]
  obtain ⟨i, hi⟩ : ∃ i : ℕ, ∀ᶠ φ : AbsGal D in nhds ((γ ^ i) ^ ℓ ^ ν * g),
      1 ≤ ‖(T φ).charpoly.eval 1‖ :=
    exists_eventually_one_le_norm_eval_charpoly hT_cont _ hT_scale (hy ν)
  let F : Filter (FrobeniusDatum D.E) := mostFrobeniiAt D.E ((γ ^ i) ^ ℓ ^ ν * g)
  have hF : F ≤ mostFrobenii D.E := inf_le_left
  have h_good : ∀ᶠ z : FrobeniusDatum D.E in F, z.place ∉ badPlaces D ℓ :=
    hF (eventually_mostFrobenii (badPlaces D ℓ).eventually_cofinite_notMem fun _ hz ↦ hz)
  have h_offLevel : ∀ᶠ z : FrobeniusDatum D.E in F, B.IsOffLevel ![] z.place :=
    hF (eventually_mostFrobenii B.eventually_isOffLevel fun _ hz ↦ hz)
  have h_away : ∀ᶠ z : FrobeniusDatum D.E in F, 1 ≤ ‖(T z.frob).charpoly.eval 1‖ :=
    mem_inf_of_right (preimage_mem_comap hi)
  refine ⟨γ ^ i, by simp [h_cyc], h_good.and (h_offLevel.and (.and ?_ h_away))⟩
  -- (b) concerns finitely many systems `x`.
  refine eventually_all.2 fun x ↦ eventually_imp_distrib_left.2 fun h_weak ↦ ?_
  obtain ⟨f, ⟨hf, -⟩, hf_ne⟩ := x.prop
  exact hF (eventually_exists_hasRootChain hf hf_ne h_weak (h_int x))

/-- The auxiliary places of the Taylor–Wiles method. Let the types `c` form a lift setting for the
pair of hermitian spaces `O` and the auxiliary twist `ϑ` of ramification at most `ram`, and let the
systems of the base data `B` have integral characteristic polynomials. Let `x₀` lift the row `R` of
weights `wt`: the trace of its normalised representation is that of the twist of `R` plus the powers
`cyclotomicInv ^ e`, `e < O.rankDiff` (`HasLiftTrace`). Let `g₁` generate the Galois group of `D.E`
topologically modulo the kernel of the cyclotomic character, let `u ^ a - 1` divide `ℓ ^ h` in `ℤ_ℓ`
for `0 < a < D.t = 5 * D.r`, where `u` is the cyclotomic character of `g₁`, and let
`ℓ ≤ D.halfGap ^ 2` (`D.halfGap = D.r ^ 8`) or `h = 0`. Then there are a finite linear order `J` and
a monotone map `exponent` to the exponents `0 < e < O.rankDiff` such that for each `ν > 0` some
places `Q` of norm `1` modulo `ℓ ^ ν`, indexed by `J`, satisfy: (a) they form a triangle for the
generator `g₁⁻¹` (`IsPrimeTriangle`): the Frobenius elements of exponent `e` and finitely many test
points detect the Galois cohomology classes of twist `-e` unramified off `ℓ`, the powers `u ^ e`
being separated up to `ℓ ^ (D.halfGap * h)`, with total loss `D.halfGap ^ 22 * h`; (b) they avoid
`badPlaces D ℓ` and are off the base level, so are unramified for the forms of `B`; (c) for every
weak lift `x` of base level congruent to `x₀`, the Hecke polynomial at the place of index `j` and
norm `q`, with the variable rescaled by the normalising character, is the chain `∏ (X - q ^ i)`,
`i < O.rankDiff`, times a divisor of an integral `e j` that has value `1` at `1` and does not depend
on `x`. -/
lemma exists_taylorWilesPlaces_hasRootChain {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] [Nonempty n]
    {O : DescentPair D.E r n} {ϑ : D.Twist}
    {c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X]} (hc : IsLiftSetting O c ϑ)
    {ram : ENNReal} (hϑ : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar ram)
    (B : BaseLevel (stdSpace D.E n) (O.columnCount, O.detExp) D.chosenGroupOrder)
    (h_int : ∀ (x : B.Eigensystem ![]) (g : Gal(Ω/D.E)) (i : ℕ),
      ‖(normalisedRep O x.val.galRep g).val.charpoly.coeff i‖ ≤ 1)
    {x₀ : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)} {wt : (D.E →+* ℂ) → Multiset ℤ}
    {R : GalRep ℓ D.E r} (hR : IsMainSummandLike D O.rankDiff wt R)
    (h_trace : HasLiftTrace ϑ.invAvatar R O.rankDiff (normalisedRep O x₀.galRep))
    {h : ℕ} {g₁ : AbsGal D} (hℓ : ℓ ≤ D.halfGap ^ 2 ∨ h = 0)
    (hg₁_gen : (cyclotomicChar Ω ℓ).IsGeneratorModKer g₁)
    (hg₁ : ∀ a ∈ Set.Ioo 0 D.t, (cyclotomicChar Ω ℓ g₁ ^ a).val - 1 ∣ ℓ ^ h) :
    ∃ (J : Type) (_ : Fintype J) (_ : LinearOrder J)
      (exponent : J →o {e : Fin O.rankDiff // 0 < (e : ℕ)}),
      ∀ ν > (0 : ℕ), ∃ Q : TaylorWilesPlaces D.E J (ℓ ^ ν),
      -- (a)
      IsPrimeTriangle ν Q.place (fun j : J ↦ (Q.frobData j).isPlaceOver.tameGenerator)
        (fun j : J ↦ (Q.frobData j).frob) g₁⁻¹ O.rankDiff exponent (D.halfGap * h)
        (D.halfGap ^ 22 * h) ∧
      -- (b)
      (∀ j : J, Q.place j ∉ badPlaces D ℓ) ∧
      (∀ j : J, B.IsOffLevel ![] (Q.place j)) ∧
      -- (c)
      ∃ e : J → EllAdicIntegers[X], (∀ j : J, (e j).eval 1 = 1) ∧
        ∀ (j : J) (x : B.Eigensystem ![]),
        (∀ (g : Gal(Ω/D.E)) (k : ℕ), ‖(normalisedRep O x.val.galRep g).val.charpoly.coeff k -
          (normalisedRep O x₀.galRep g).val.charpoly.coeff k‖ < 1) →
        IsWeakLift O x.val →
        HasRootChain (x.val.heckePolyAt (Q.place j)) ((e j).map (algebraMap EllAdicIntegers ℂ))
          (Q.place j).q (ιℓ.symm (normalizingAvatar O (Q.frobData j).frob).val)⁻¹ O.rankDiff := by
  -- Apply `exists_isPrimeTriangle` to the set `W` of
  -- `exists_eventually_hasRootChain_mostFrobeniiAt`, and take for `e j` the product of the
  -- polynomials that `W` gives for the finitely many `x`.
  let χ (x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)) (g : Gal(Ω/D.E)) :
    (PadicAlgCl ℓ)[X] :=
    (normalisedRep O x.galRep g).val.charpoly
  let chain (g : Gal(Ω/D.E)) : (PadicAlgCl ℓ)[X] :=
    ∏ i ∈ Finset.range O.rankDiff, (X - C (cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ i))
  let twisted (g : Gal(Ω/D.E)) : (PadicAlgCl ℓ)[X] := (ϑ.invAvatar g • (R g).val).charpoly
  let Near : Type := {x : B.Eigensystem ![] //
    (∀ (g : Gal(Ω/D.E)) (k : ℕ), ‖(χ x g).coeff k - (χ x₀ g).coeff k‖ < 1) ∧ IsWeakLift O x.val}
  let HasShape (x : B.Eigensystem ![]) (y : FrobeniusDatum D.E) (e : EllAdicIntegers[X]) : Prop :=
    HasRootChain (x.val.heckePolyAt y.place) (e.map (algebraMap EllAdicIntegers ℂ)) y.place.q
      (ιℓ.symm (normalizingAvatar O y.frob).val)⁻¹ O.rankDiff
  let W : Set (FrobeniusDatum D.E) := {y | y.place ∉ badPlaces D ℓ ∧ B.IsOffLevel ![] y.place ∧
    (∀ x : B.Eigensystem ![], IsWeakLift O x.val → ∀ S : (PadicAlgCl ℓ)[X], 1 ≤ ‖S.eval 1‖ →
      (∀ k : ℕ, ‖(χ x y.frob).coeff k - (S * chain y.frob).coeff k‖ < 1) →
      ∃ e : EllAdicIntegers[X], HasShape x y e ∧ e.eval 1 = 1) ∧
    1 ≤ ‖(twisted y.frob).eval 1‖}
  have hW (ν : ℕ) (g : AbsGal D) : ∃ δ : Gal(Ω/D.E), cyclotomicChar Ω ℓ δ = 1 ∧
      W ∈ mostFrobeniiAt D.E (δ ^ ℓ ^ ν * g) :=
    exists_eventually_hasRootChain_mostFrobeniiAt hϑ B h_int hR ν g
  obtain ⟨-, h_rank⟩ : card r ≤ D.r ∧ O.rankDiff ≤ D.t := hc.rank_le
  have h_gap : D.cyclotomicConductor + O.rankDiff < D.halfGap := by
    grw [h_rank]
    exact D.nat_lt_of_hasLogBound
  have h_inf_places : 4 ≤ D.f :=
    calc 4 ≤ D.m ^ 22 := D.nat_le_of_hasLogBound
      _ ≤ D.f := D.f_mem_Icc.1
  obtain ⟨J, hJ_fin, hJ_ord, exponent, h_places⟩ := exists_isPrimeTriangle O.rankDiff
    D.algebraMap_mem_cycloField h_gap hg₁_gen
    (fun a ha ↦ hg₁ a (Set.Ioo_subset_Ioo_right h_rank ha)) hℓ h_inf_places hW
  refine ⟨J, hJ_fin, hJ_ord, exponent, fun ν hν ↦ ?_⟩
  obtain ⟨Q, h_triangle, hQ : ∀ j : J, Q.frobData j ∈ W⟩ := h_places ν hν
  -- The polynomials of `x₀` are those of the twist of `R` times the chain, as the traces of all
  -- powers agree.
  have hx₀ (g : AbsGal D) : χ x₀ g = twisted g * chain g := by
    refine charpoly_eq_mul_of_trace_pow_add _ _ _ fun k ↦ ?_
    simpa [_root_.smul_pow, pow_right_comm] using h_trace (g ^ k)
  have h_good (j : J) : Q.place j ∉ badPlaces D ℓ := by
    obtain ⟨h_notMem, -⟩ := hQ j
    exact h_notMem
  have h_offLevel (j : J) : B.IsOffLevel ![] (Q.place j) := by
    obtain ⟨-, h_off, -⟩ := hQ j
    exact h_off
  -- So the condition in `W` applies with `S` the polynomial of the twist.
  have h_shape (j : J) (x : Near) :
      ∃ e : EllAdicIntegers[X], HasShape x.val (Q.frobData j) e ∧ e.eval 1 = 1 := by
    obtain ⟨-, -, h_hecke, h_away⟩ := hQ j
    obtain ⟨h_congr, h_weak⟩ := x.prop
    refine h_hecke x h_weak (twisted (Q.frobData j).frob) h_away fun k ↦ ?_
    rw [← hx₀]
    exact h_congr _ k
  choose e h_string he using h_shape
  have : Fintype Near := Fintype.ofFinite Near
  refine ⟨Q, h_triangle, h_good, h_offLevel, fun j ↦ ∏ x : Near, e j x,
    by simp [eval_prod, he], fun j x h_congr h_weak ↦ ?_⟩
  obtain ⟨S, hS, h_dvd⟩ := h_string j ⟨x, h_congr, h_weak⟩
  exact ⟨S, hS, h_dvd.trans (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)))⟩

/-- A continuous representation of a compact group over `ℚ̄_ℓ` keeps a lattice, so its
characteristic polynomials have integral coefficients. -/
lemma norm_charpoly_coeff_le_one_of_continuous {ℓ : ℕ} [ThePrime ℓ] {G n : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [Fintype n] [DecidableEq n]
    {ρ : G →* GL n (PadicAlgCl ℓ)} (hρ : Continuous ρ) (g : G) (i : ℕ) :
    ‖(ρ g).val.charpoly.coeff i‖ ≤ 1 := by
  obtain ⟨O, u, hu⟩ : ∃ (O : CoeffRing ℓ) (u : G →* Matrix n n O), IsLatticeIn ρ u :=
    (eventually_exists_isLatticeIn hρ).exists
  simp [hu.charpoly_eq_map]

/-- Let `u x g` be matrices over `ℚ̄_ℓ` with integral characteristic polynomials, and suppose that
for each `x` some `u x g` does not have the eigenvalue `1`. Then for each `x` there is `elt x` such
that `det (1 - u x (elt x))` is a nonzero element `value x` of the valuation ring of `ℚ̄_ℓ`. -/
lemma exists_det_one_sub_ne_zero {ℓ : ℕ} [ThePrime ℓ] {Y G n : Type} [Fintype n] [DecidableEq n]
    (u : Y → G → Matrix n n (PadicAlgCl ℓ))
    (h_int : ∀ (x : Y) (g : G) (i : ℕ), ‖(u x g).charpoly.coeff i‖ ≤ 1)
    (h_reg : ∀ x : Y, ∃ g : G, ¬(u x g).charpoly.IsRoot 1) :
    ∃ (elt : Y → G) (value : Y → EllAdicIntegers),
      (∀ x : Y, algebraMap EllAdicIntegers (PadicAlgCl ℓ) (value x) = (1 - u x (elt x)).det) ∧
      ∀ x : Y, value x ≠ 0 := by
  have h_eval (M : Matrix n n (PadicAlgCl ℓ)) : (1 - M).det = M.charpoly.eval 1 := by
    rw [Matrix.eval_charpoly, map_one]
  have h_exists (x : Y) : ∃ g : G, (1 - u x g).det ≠ 0 := by
    simpa only [h_eval, Polynomial.IsRoot.def] using h_reg x
  choose elt h_elt using h_exists
  have h_mem (x : Y) : (1 - u x (elt x)).det ∈ intQpBar ℓ := by
    rw [h_eval, Polynomial.eval_eq_sum_range]
    have h_coeff (i : ℕ) : (u x (elt x)).charpoly.coeff i ∈ intQpBar ℓ := h_int x (elt x) i
    exact sum_mem fun i _ ↦ mul_mem (h_coeff i) (pow_mem (one_mem _) i)
  let value (x : Y) : EllAdicIntegers := ⟨(1 - u x (elt x)).det, h_mem x⟩
  have h_value (x : Y) :
      algebraMap EllAdicIntegers (PadicAlgCl ℓ) (value x) = (1 - u x (elt x)).det := rfl
  refine ⟨elt, value, h_value, fun x h_zero ↦ h_elt x ?_⟩
  rw [← h_value, h_zero, map_zero]

/-- Let `u x g` be matrices over `ℚ̄_ℓ` with integral characteristic polynomials, `x` in a finite
type. There are finitely many elements `elt k` and nonzero elements `value k` of the valuation ring
of `ℚ̄_ℓ` such that the product of the `value k - det (1 - u x (elt k))` vanishes at every `x` for
which some `u x g` does not have the eigenvalue `1`. -/
lemma exists_prod_sub_det_one_sub_eq_zero {ℓ : ℕ} [ThePrime ℓ] {Y G n : Type} [Finite Y] [Fintype n]
    [DecidableEq n] (u : Y → G → Matrix n n (PadicAlgCl ℓ))
    (h_int : ∀ (x : Y) (g : G) (i : ℕ), ‖(u x g).charpoly.coeff i‖ ≤ 1) :
    ∃ (K : Type) (_ : Fintype K) (elt : K → G) (value : K → EllAdicIntegers),
      (∀ k : K, value k ≠ 0) ∧
      ∀ x : Y, (∃ g : G, ¬(u x g).charpoly.IsRoot 1) →
        ∏ k : K,
          (algebraMap EllAdicIntegers (PadicAlgCl ℓ) (value k) - (1 - u x (elt k)).det) = 0 := by
  -- One factor for each such `x`.
  let Reg : Type := {x : Y // ∃ g : G, ¬(u x g).charpoly.IsRoot 1}
  obtain ⟨elt, value, h_value, h_ne⟩ : ∃ (elt : Reg → G) (value : Reg → EllAdicIntegers),
      (∀ x : Reg,
        algebraMap EllAdicIntegers (PadicAlgCl ℓ) (value x) = (1 - u x.val (elt x)).det) ∧
      ∀ x : Reg, value x ≠ 0 :=
    exists_det_one_sub_ne_zero (fun (x : Reg) (g : G) ↦ u x.val g) (fun x ↦ h_int x.val)
      fun x ↦ x.prop
  refine ⟨Reg, Fintype.ofFinite Reg, elt, value, h_ne, fun x hx ↦ ?_⟩
  exact Finset.prod_eq_zero (i := ⟨x, hx⟩) (by simp) (sub_eq_zero.2 (h_value ⟨x, hx⟩))

/-- A nonzero `ℓ`-adic integer divides a positive power of `ℓ`. -/
lemma exists_dvd_prime_pow_succ {ℓ : ℕ} [ThePrime ℓ] {b : EllAdicIntegers} (hb : b.val ≠ 0) :
    ∃ ν : ℕ, b ∣ (ℓ : EllAdicIntegers) ^ (ν + 1) := by
  have h_finite : ellVal (ℓ := ℓ) b.val ≠ ⊤ := by simpa [ellVal] using hb
  obtain ⟨ν, hν⟩ : ∃ ν : ℕ, ellVal (ℓ := ℓ) b.val < ν := ENNReal.exists_nat_gt h_finite
  have coe_eq (a : EllAdicIntegers) : a.val = algebraMap EllAdicIntegers (PadicAlgCl ℓ) a := rfl
  exact ⟨ν, dvd_iff_ellVal_le.mpr (hν.le.trans (by simp [coe_eq]))⟩

/-- The character `normalizingAvatar O` is unramified away from `ℓ`, so it is trivial at the tame
generator of a place `A` over `w ∤ ℓ`. -/
lemma normalizingAvatar_tameGenerator {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ]
    {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] (O : DescentPair D.E r n)
    {w : FinPlace D.E} {A : ClosurePlace} (hA : IsPlaceOver A w) (hw : ↑ℓ ∉ w.asIdeal) :
    (normalizingAvatar O hA.tameGenerator : PadicAlgCl ℓ) = 1 := by
  rw [normalizingAvatar_eq_of_isFrob_inv hA hw 0 (inv_mem hA.tameGenerator.prop), pow_zero]

/-- There is a common Ribet element for a finite family `sys` of systems, with normalised Galois
representations `N x`. Assume the following. The types `c` form a lift setting for `O` and the twist
`ϑ`, whose ramification is at most `ram`. The places `w j`, with tame generators `tame j` and
Frobenius elements `φ j`, form a triangle (`IsPrimeTriangle`) with bounds `D.halfGap * h` and
`D.halfGap ^ 22 * h`, where `h` is at most the valuation of `D.chosenGroupOrder`, the product of the
orders of general linear groups over the chosen residue fields. Each `N x` has the weights `wt` and
the type made from `c` and `O.rankDiff` eigenvalues `1` (`IsRepOfType`), and
`(N x g - ϑ.invAvatar g) (N x g - 1) = 0` on inertia above `ϑ.Q` and its conjugate. Each system in
`𝓧` lifts a row with a twisted lattice, and for `sys x₀` the Selmer length of the twisted row is at
most the finite `sel` (`IsLiftWithTwistedLattice`). The module `𝒥` holds `ℓ ^ ν` times all traces of
the `N x`, and the traces of the relations, with polynomials `e j` of value `1` at `1`, that tie
`tame j` to `φ j` (`IsTraceIdeal`). Then one family `f` of polynomials in the `X j` multiplies every
family `x ↦ det (1 - N x g)` into `𝒥`, has on `𝓧` no monomial properly dividing `∏ X j`, and has at
`x₀` a coefficient `d` of `∏ X j` with `D.chosenGroupOrder ^ 2 * d` of valuation at most
`liftValuationBound ℓ O ram sel`. -/
lemma exists_isCommonRibetElement_ellVal_le {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
    {O : DescentPair D.E r n} {ϑ : D.Twist}
    {c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X]} (hc : IsLiftSetting O c ϑ)
    {ram : ENNReal} (hϑ : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar ram)
    {J : Type} [Fintype J] [LinearOrder J] {ν h : ℕ} {w : J → FinPlace D.E} {tame φ : J → AbsGal D}
    {exponent : J →o {e : Fin O.rankDiff // 0 < (e : ℕ)}} {g₀ : AbsGal D}
    (h_le : h ≤ padicValNat ℓ D.chosenGroupOrder)
    (h_tri : IsPrimeTriangle ν w tame φ g₀ O.rankDiff exponent (D.halfGap * h) (D.halfGap ^ 22 * h))
    {Y : Type} [Fintype Y] {sys : Y → Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)}
    {wt : (D.E →+* ℂ) → Multiset ℤ}
    (h_isRepOfType : ∀ x : Y, IsRepOfType O O.rankDiff wt
      (fun i : O.ChosenIndex ↦ scaledTypePoly O c i * (X - 1) ^ O.rankDiff)
      (Set.conjClosure ϑ.Q ∪ (Set.range w).conjClosure) (normalisedRep O (sys x).galRep))
    (h_quad : ∀ x : Y, ∀ g ∈ inertiaAbove (Set.conjClosure ϑ.Q),
      ((normalisedRep O (sys x).galRep g).val - ϑ.invAvatar g • 1) *
        ((normalisedRep O (sys x).galRep g).val - 1) = 0)
    {𝓧 : Set (Isotypic (stdSpace D.E n) (O.columnCount, O.detExp))} (x₀ : sys ⁻¹' 𝓧) {sel : ENNReal}
    (h_lift : ∀ x ∈ 𝓧, IsLiftWithTwistedLattice O ϑ sel (sys x₀) x)
    (h_sel_ne_top : sel ≠ ⊤) {S : Subalgebra EllAdicIntegers (Y → MvPolynomial J (PadicAlgCl ℓ))}
    {𝒥 : Submodule S (Y → MvPolynomial J (PadicAlgCl ℓ))} {e : J → EllAdicIntegers[X]}
    (h𝒥 : IsTraceIdeal 𝒥 (fun (x : Y) (g : AbsGal D) ↦ (normalisedRep O (sys x).galRep g).val)
      (ℓ ^ ν : EllAdicIntegers) tame φ (fun j : J ↦ j) e)
    (he : ∀ j : J, (e j).eval 1 = 1) :
    ∃ d : PadicAlgCl ℓ,
      IsCommonRibetElement 𝒥
        (fun (g : AbsGal D) (x : Y) ↦ (1 - (normalisedRep O (sys x).galRep g).val).det) x₀ d ∧
      ellVal (ℓ := ℓ) (D.chosenGroupOrder ^ 2 * d) ≤ liftValuationBound ℓ O ram sel := by
  choose jumps R hR h_trace γ y h_lattice h_selmer using
    fun x : sys ⁻¹' 𝓧 ↦ h_lift (sys x) x.prop
  obtain ⟨d, hd, hd_le⟩ :=
    ribet_columns hc hϑ h_le h_tri h_isRepOfType h_quad hR h_trace h_lattice h𝒥 he
    x₀ (h_selmer x₀ rfl) h_sel_ne_top
  refine ⟨d, hd, ?_⟩
  calc ellVal (ℓ := ℓ) (D.chosenGroupOrder ^ 2 * d)
      ≤ ellVal ((D.chosenGroupOrder : PadicAlgCl ℓ) ^ 2) + ellVal d := ellVal_mul_le
    _ = ellVal d + 2 * padicValNat ℓ D.chosenGroupOrder := by
        rw [ellVal_pow, ellVal_natCast (NeZero.ne _), add_comm, Nat.cast_ofNat]
    _ ≤ liftValuationBound ℓ O ram sel := hd_le

/-- The operator at a base system `x₀ ∈ 𝓧`. Let the types `c` form a lift setting for the pair `O`
and the twist `ϑ`, of ramification at most `ram`. Let each system in `𝓧` lift a row with a twisted
lattice, the Selmer length for `x₀` being at most the finite `sel`. Let `B` be base data. At every
level made of places outside `badPlaces D ℓ`, let each system of `B` have as normalised
representation `N x` one of the weights `wt` and the type made from `c` (`IsRepOfType`), with
`(N x g - ϑ.invAvatar g) (N x g - 1)` zero on inertia above `ϑ.Q` and its conjugate. Then at some
level `L` there are eigenvalues `s` such that: (a) `D.chosenGroupOrder ^ 2 * s x₀` has valuation at
most `liftValuationBound ℓ O ram sel = sel + 2 * O.rankDiff * ram + card r * localDefectBound D
ℓ + denominatorError D ℓ`; (b) if `l` and `y` are forms of base level, `D.chosenGroupOrder • l` is
integral, `y` is supported on `𝓧` and `l`, `y` have the same components outside the base systems
that are not weak lifts (weak lift: all characteristic polynomials have the root `1`), then
`D.chosenGroupOrder • D.chosenGroupOrder • B.diagOp s y` is integral. Here `B.diagOp s` scales each
system `x` by `s x`, and `D.chosenGroupOrder` is the product of the orders of general linear groups
over the chosen residue fields. -/
lemma exists_ellVal_le_and_diagOp_mem_ellIntegralForms {P : Parameters} {D : Data P} {ℓ : ℕ}
    [ThePrime ℓ]
    [PadicIso ℓ] {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] [Nonempty n]
    {O : DescentPair D.E r n} {ϑ : D.Twist}
    {c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X]} (hc : IsLiftSetting O c ϑ)
    {ram : ENNReal} (hϑ : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar ram)
    {𝓧 : Set (Isotypic (stdSpace D.E n) (O.columnCount, O.detExp))} {sel : ENNReal}
    {x₀ : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)}
    (h_lift : ∀ x ∈ 𝓧, IsLiftWithTwistedLattice O ϑ sel x₀ x)
    (h_sel_ne_top : sel ≠ ⊤) {wt : (D.E →+* ℂ) → Multiset ℤ}
    (B : BaseLevel (stdSpace D.E n) (O.columnCount, O.detExp) D.chosenGroupOrder)
    (h_isRepOfType : ∀ (K : Type) [Finite K] (u : K → FinPlace D.E),
      (∀ k : K, u k ∉ badPlaces D ℓ) →
      ∀ x ∈ B.Eigensystem u, IsRepOfType O O.rankDiff wt
        (fun i : O.ChosenIndex ↦ scaledTypePoly O c i * (X - 1) ^ O.rankDiff)
        (Set.conjClosure ϑ.Q ∪ (Set.range u).conjClosure) (normalisedRep O x.galRep))
    (h_quad : ∀ (K : Type) [Finite K] (u : K → FinPlace D.E), (∀ k : K, u k ∉ badPlaces D ℓ) →
      ∀ x ∈ B.Eigensystem u, ∀ g ∈ inertiaAbove (Set.conjClosure ϑ.Q),
        ((normalisedRep O x.galRep g).val - ϑ.invAvatar g • 1) *
          ((normalisedRep O x.galRep g).val - 1) = 0)
    (hx₀ : x₀ ∈ 𝓧) (hx₀B : x₀ ∈ B.Eigensystem ![]) :
    ∃ J : Type, ∃ (_ : Finite J) (L : J → FinPlace D.E) (s : B.Eigensystem L → PadicAlgCl ℓ),
      -- (a)
      (∀ x : B.Eigensystem L, x.val = x₀ →
        ellVal (ℓ := ℓ) (D.chosenGroupOrder ^ 2 * s x) ≤ liftValuationBound ℓ O ram sel) ∧
      -- (b)
      ∀ l ∈ B.formsOfLevel ![], D.chosenGroupOrder • l ∈ BaseLevel.ellIntegralForms →
        ∀ y ∈ B.formsOfLevel ![],
        (∀ s₁ : B.Eigensystem L → PadicAlgCl ℓ,
          (∀ x : B.Eigensystem L, x.val ∈ 𝓧 → s₁ x = 0) → B.diagOp s₁ y = 0) →
        (∀ s₁ : B.Eigensystem L → PadicAlgCl ℓ,
          (∀ x : B.Eigensystem L, x.val ∈ B.Eigensystem ![] → ¬IsWeakLift O x.val → s₁ x = 0) →
          B.diagOp s₁ l = B.diagOp s₁ y) →
        D.chosenGroupOrder • D.chosenGroupOrder • B.diagOp s y ∈ BaseLevel.ellIntegralForms := by
  -- Apply `exists_diagOp_mem_ellIntegralForms` to the functions `δ g x = det (1 - N x g)` and the
  -- product `δ₀ = ∏ k, (value k - δ (elt k))`, which vanishes at the base systems that are not weak
  -- lifts.
  let N (x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)) : GalRep ℓ D.E n :=
    normalisedRep O x.galRep
  have h_int {K : Type} [Finite K] {u : K → FinPlace D.E} (hu : ∀ k : K, u k ∉ badPlaces D ℓ)
      (x : B.Eigensystem u) (g : Gal(Ω/D.E)) (i : ℕ) : ‖(N x g).val.charpoly.coeff i‖ ≤ 1 :=
    norm_charpoly_coeff_le_one_of_continuous (h_isRepOfType K u hu x x.prop).continuous g i
  have h_int_base : ∀ (x : B.Eigensystem ![]) (g : Gal(Ω/D.E)) (i : ℕ),
      ‖(N x g).val.charpoly.coeff i‖ ≤ 1 := h_int (by simp)
  obtain ⟨K, _, elt, value, h_value_ne, h_factor⟩ :
      ∃ (K : Type) (_ : Fintype K) (elt : K → Gal(Ω/D.E)) (value : K → EllAdicIntegers),
        (∀ k : K, value k ≠ 0) ∧ ∀ x : B.Eigensystem ![], ¬IsWeakLift O x.val →
          ∏ k : K, (algebraMap EllAdicIntegers (PadicAlgCl ℓ) (value k) -
            (1 - (N x (elt k)).val).det) = 0 := by
    simpa only [IsWeakLift, not_forall] using
      exists_prod_sub_det_one_sub_eq_zero (fun (x : B.Eigensystem ![]) g ↦ (N x g).val) h_int_base
  -- A triangle of places of level `ℓ ^ (ν + 1)`, a power that the constant `bound` divides.
  choose h h_le h_small g₁ hg₁_gen hg₁_dvd using exists_cyclotomicChar_pow_sub_one_dvd D ℓ
  choose τ₀ R₀ hR₀ h_trace₀ _ using h_lift x₀ hx₀
  choose J _ _ exponent h_places using
    exists_taylorWilesPlaces_hasRootChain hc hϑ B h_int_base hR₀ h_trace₀ h_small hg₁_gen hg₁_dvd
  let bound : EllAdicIntegers := (2 * (card n).factorial : ℕ) *
    ((∏ k : K, value k) * D.chosenGroupOrder ^ 2) ^ (card J + 1)
  have h_bound_ne : bound.val ≠ 0 := by
    have coe_eq (a : EllAdicIntegers) : a.val = algebraMap EllAdicIntegers (PadicAlgCl ℓ) a := rfl
    have h_prod : ∏ k : K, (value k).val ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ h_zero ↦ h_value_ne k (Subtype.ext h_zero)
    simpa [bound, NeZero.ne, coe_eq, map_ofNat] using h_prod
  choose ν h_dvd using exists_dvd_prime_pow_succ h_bound_ne
  choose Q h_tri h_good h_offLevel e he h_string using h_places (ν + 1) ν.succ_pos
  -- `N x` is the twist of `x.galRep` by `normalizingAvatar O`, which is continuous, so integral.
  let a : AbsGal D →* EllAdicIntegers :=
    ((coeHom (PadicAlgCl ℓ)).comp (normalizingAvatar O)).codRestrict (intQpBar ℓ)
      fun g ↦ (norm_eq_one_of_continuous (by fun_prop) g).le
  have h_twist : BaseLevel.IsGalRepTwist N a := fun _ _ ↦ rfl
  have h_tame (j : J) : a (Q.frobData j).isPlaceOver.tameGenerator = 1 := by
    obtain ⟨h_notMem, -⟩ := h_tri.isTameGeneratorFamily j
    exact Subtype.ext (normalizingAvatar_tameGenerator O (Q.frobData j).isPlaceOver h_notMem)
  have hx₀Q : x₀ ∈ B.Eigensystem Q.place := by
    obtain ⟨f, ⟨hf_sys, hf_level⟩, hf_ne⟩ := hx₀B
    exact ⟨f, ⟨hf_sys, B.formsOfLevel_base_le Q.place hf_level⟩, hf_ne⟩
  let 𝓨 : Set (B.Eigensystem Q.place) := Subtype.val ⁻¹' 𝓧
  let x₁ : 𝓨 := ⟨⟨x₀, hx₀Q⟩, hx₀⟩
  -- A base system at which `δ₀` does not vanish is a weak lift.
  have h_string' (j : J) (x : B.Eigensystem Q.place) (hx : x.val ∈ B.Eigensystem ![])
      (h_ne : ∏ k : K, (algebraMap EllAdicIntegers (PadicAlgCl ℓ) (value k) -
        (1 - (N x (elt k)).val).det) ≠ 0)
      (h_cong : BaseLevel.IsCongruent N x.val x₀) :
      HasRootChain (x.val.heckePolyAt (Q.place j)) ((e j).map (algebraMap EllAdicIntegers ℂ))
        (Q.place j).q (algebraMap EllAdicIntegers ℂ (a (Q.frobData j).frob))⁻¹ O.rankDiff :=
    h_string j ⟨x, hx⟩ h_cong (not_not.1 (mt (h_factor ⟨x, hx⟩) h_ne))
  have h_rankDiff : O.rankDiff ≠ 0 := by simpa [Nat.sub_eq_zero_iff_le] using O.rank_lt
  have h_ribet
      (S : Subalgebra EllAdicIntegers (B.Eigensystem Q.place → MvPolynomial J (PadicAlgCl ℓ)))
      (𝒥 : Submodule S (B.Eigensystem Q.place → MvPolynomial J (PadicAlgCl ℓ)))
      (h𝒥 : IsTraceIdeal 𝒥 (fun x g ↦ (N x.val g).val) (ℓ ^ (ν + 1) : EllAdicIntegers)
        (fun j ↦ (Q.frobData j).isPlaceOver.tameGenerator) (fun j ↦ (Q.frobData j).frob)
        (fun j ↦ j) e) :
      ∃ d : PadicAlgCl ℓ, IsCommonRibetElement 𝒥
          (fun (g : Gal(Ω/D.E)) (x : B.Eigensystem Q.place) ↦ (1 - (N x.val g).val).det) x₁ d ∧
        ellVal (ℓ := ℓ) (D.chosenGroupOrder ^ 2 * d) ≤ liftValuationBound ℓ O ram sel :=
    exists_isCommonRibetElement_ellVal_le hc hϑ h_le h_tri (𝓧 := 𝓧)
      (sys := fun x : B.Eigensystem Q.place ↦ x.val)
      (fun x ↦ h_isRepOfType J Q.place h_good x x.prop) (fun x ↦ h_quad J Q.place h_good x x.prop)
      x₁ h_lift h_sel_ne_top h𝒥 he
  refine (B.exists_diagOp_mem_ellIntegralForms Q h_offLevel h_twist h_tame
    (fun (g : Gal(Ω/D.E)) (x : B.Eigensystem Q.place) ↦ (1 - (N x.val g).val).det) elt value 𝓨 x₁ e
    h_rankDiff (h_int h_good) h_string' h_dvd h_ribet).elim fun s ⟨h_val, h_op⟩ ↦ ?_
  refine ⟨J, inferInstance, Q.place, s, fun x hx ↦ ?_, fun l hl hl_int y hy h_supp h_agree ↦ ?_⟩
  · obtain rfl : x = x₁ := Subtype.ext hx
    exact h_val
  · refine h_op l hl D.chosenGroupOrder hl_int y hy h_supp fun s' hs' ↦ ?_
    exact h_agree s' fun x hx h_not_weak ↦ hs' x (h_factor ⟨x, hx⟩ h_not_weak)

/-- There is a split place `w`, off the places of `O` and their conjugates, at which the Hecke
polynomial operator, evaluated at the number `O.liftHeckeRoot w` (the inverse of the largest root
`υ q ^ (O.rankDiff - 1)` of the chain that a theta lift has in its Hecke polynomial, with `q` the
norm of `w` and `υ` the Frobenius value of `O.charW`), kills every nonzero form `v` of base level
that lies in a system `x` which is a weak lift: at every Galois element the characteristic
polynomial of the normalised representation of `x` has the root `1`. -/
lemma exists_heckePolyOnForms_eq_zero {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] [Nonempty n]
    {O : DescentPair D.E r n} (B : BaseLevel (stdSpace D.E n) (O.columnCount, O.detExp)
      D.chosenGroupOrder) :
    ∃ (w : FinPlace D.E) (hw : star w ≠ w) (hS : w ∉ O.places.conjClosure),
      ∀ (x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)) (v : O.FormV),
      v.toSmoothForm ∈ x.val ⊓ B.formsOfLevel ![] →
      v.toSmoothForm ≠ 0 →
      IsWeakLift O x →
      O.heckePolyOnForms hw hS (O.liftHeckeRoot w) v = 0 := by
  obtain ⟨w, ⟨-, -, hℓ, h_eigen⟩, hw, hS⟩ :
      ∃ w : FinPlace D.E, B.IsOffLevel ![] w ∧ w.IsSplit ∧ w ∉ O.places.conjClosure :=
    ((B.eventually_isOffLevel (L := ![])).and_frequently
      (frequently_isSplit_notMem_places O)).exists
  refine ⟨w, hw, hS, fun x v hv hv₀ h_weak ↦ ?_⟩
  have h_hecke : HasHeckePolyAt (toSmoothForm v :
    Gf D.E n → WeylIndex n (O.columnCount, O.detExp).1 → ℂ) w hw
      (x.heckePolyAt w) :=
    hasHeckePolyAt_of_mem_eigenformsAt (h_eigen x ⟨v.toSmoothForm, hv, hv₀⟩ hv) hw
  -- The numbers `O.charW.frobValue r w * q ^ i`, `i < O.rankDiff`, are roots of the Hecke
  -- polynomial of `v` at `w`. The last of them is `(O.liftHeckeRoot w)⁻¹`, so the reversed
  -- polynomial, by which `O.heckePolyOnForms` acts, vanishes at `O.liftHeckeRoot w`.
  have h_root : (x.heckePolyAt w).IsRoot (O.charW.frobValue r w * w.q ^ (O.rankDiff - 1)) :=
    isRoot_hecke_chain (mem_inf.1 hv).1 hv₀ h_weak hℓ h_hecke (by simp [O.rank_lt])
  obtain ⟨h_fix, t, h_poly, ht⟩ := h_hecke
  have h_root_ne : O.charW.frobValue r w * w.q ^ (O.rankDiff - 1) ≠ 0 := by
    simp [AutChar.frobValue, HeckeChar.atUniformizer]
  have h_eval : heckePolyEval n w t (O.liftHeckeRoot w) = 0 := by
    rw [h_poly, IsRoot.def, eval_heckePoly w t h_root_ne] at h_root
    rw [DescentPair.liftHeckeRoot]
    exact (mul_eq_zero.1 h_root).resolve_left (pow_ne_zero _ h_root_ne)
  rw [O.heckePolyOnForms_eq_smul hw hS (hasHeckePolynomial_of_heckeSplit h_fix ht), h_eval,
    zero_smul]

-- Keeps definitional checks from unfolding the finite products.
seal Finset.prod in
/-- Let `typeProjection O c` be the action on forms of the idempotent of the tuple of types `c`,
with range in the image of the element `E` of the group algebra. Let `Z` be stable under it and
under the Hecke polynomial operators `O.heckePolyOnForms`, and let `y` be orthogonal to the false
lifts: the forms in `Zᗮ` and the image of `E` that, at some split place, the Hecke polynomial
operator at its lift Hecke root `O.liftHeckeRoot`, the value expected of a lift, kills. If at one
split place `w` this operator kills the nonzero isotypic forms in the range of `typeProjection O c`
that lie outside `M`, then `typeProjection O c` takes the component of `y` orthogonal to `Z` into
`M`. -/
lemma typeProjection_sub_starProjection_mem {P : Parameters} {D : Data P} {r n : Type} [Fintype r]
    [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair D.E r n}
    {c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X]}
    {E : MonoidAlgebra ℂ (O.ChosenGL r)} {Z M : Submodule ℂ O.FormV} {y : O.FormV}
    (hZ_hecke : ∀ (w : FinPlace D.E) (hw : star w ≠ w) (hS : w ∉ O.places.conjClosure) (ξ : ℂ),
      Z ∈ (O.heckePolyOnForms (w := w) hw hS ξ).invtSubmodule)
    (hZ_type : Z ∈ (typeProjection O c).invtSubmodule)
    (h_le : (typeProjection O c).range ≤ (O.groupAlgAction E).range)
    (hy : O.IsOrthogonalToFalseLifts E Zᗮ y)
    {w : FinPlace D.E} {hw : star w ≠ w} {hS : w ∉ O.places.conjClosure}
    (h_kill : ∀ x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp),
      ∀ v ∈ (typeProjection O c).range,
      IsNonzeroIn v x → v ∉ M → O.heckePolyOnForms hw hS (O.liftHeckeRoot w) v = 0) :
    typeProjection O c (y - Z.starProjection y) ∈ M := by
  -- Let `U` be the part of the range orthogonal to `Z`, and `K` the forms in `U` that the Hecke
  -- polynomial kills, which are false lifts. Then `U ⊓ Kᗮ ≤ M`, and the form lies in `U ⊓ Kᗮ`.
  let U : Submodule ℂ O.FormV := (typeProjection O c).range ⊓ Zᗮ
  let K : Submodule ℂ O.FormV := U ⊓ (O.heckePolyOnForms hw hS (O.liftHeckeRoot w)).ker
  have hU (u : FinPlace D.E) (hu : star u ≠ u) (hu_off : u ∉ O.places.conjClosure) (ξ : ℂ) :
      U ∈ (O.heckePolyOnForms hu hu_off ξ).invtSubmodule :=
    Sublattice.inf_mem (range_typeProjection_mem_invtSubmodule hu hu_off ξ)
      (orthogonal_mem_invtSubmodule_heckePolyOnForms hZ_hecke u hu hu_off ξ)
  have hK (u : FinPlace D.E) (hu : star u ≠ u) (hu_off : u ∉ O.places.conjClosure) (ξ : ℂ) :
      K ∈ (O.heckePolyOnForms hu hu_off ξ).invtSubmodule := by
    refine Sublattice.inf_mem (hU u hu hu_off ξ) fun v ↦ ?_
    -- The operators at `u` and `w` commute.
    simp +contextual [O.heckePolyOnForms_comm hw]
  have h_inf_le : U ⊓ Kᗮ ≤ M := by
    refine le_of_isotypic_mem (fun u hu hu_off ξ ↦ Sublattice.inf_mem (hU u hu hu_off ξ)
      (orthogonal_mem_invtSubmodule_heckePolyOnForms hK u hu hu_off ξ)) ?_
    rintro x v ⟨⟨hv_range, hv_orth⟩, hv_perp⟩ ⟨hx_mem, hx_ne⟩
    -- An isotypic `v` outside `M` would lie in `K`, so be orthogonal to itself.
    by_contra hM
    have hvK : v ∈ K := ⟨⟨hv_range, hv_orth⟩, h_kill x v hv_range ⟨hx_mem, hx_ne⟩ hM⟩
    exact inner_self_ne_zero.2 (ne_zero_of_map hx_ne) (hv_perp v hvK)
  have h_mem_U : typeProjection O c (y - Z.starProjection y) ∈ U :=
    ⟨mem_range_self _ _,
      isSymmetric_typeProjection.orthogonalComplement_mem_invtSubmodule hZ_type (by simp)⟩
  refine h_inf_le ⟨h_mem_U, ?_⟩
  rintro u ⟨⟨hu_range, hu_orth⟩, hu_ker⟩
  -- `typeProjection O c` is symmetric and fixes `u`; both `y` and its projection to `Z` are
  -- orthogonal to the false lifts at `w`, among which is `u`.
  have h_test : y - Z.starProjection y ∈ (O.falseLiftsAt hw hS E Zᗮ)ᗮ :=
    sub_mem (hy w hw hS) (orthogonal_le inf_le_right (by simp))
  have hu_false : u ∈ O.falseLiftsAt hw hS E Zᗮ := ⟨⟨h_le hu_range, hu_ker⟩, hu_orth⟩
  rw [← isSymmetric_typeProjection, typeProjection_eq_self_of_mem_range hu_range, h_test u hu_false]

/-- A lift generator of `Z`: a form in `Z`, in the range of an apt projection inside the image of
`E`, that lifts a system with a main summand whose twist by `ϑ.invAvatar` has a Selmer group with
divisible coefficients of length at most `sel` (`HasDivisibleSelmerLengthLe`). -/
structure IsLiftGenerator {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
    (ϑ : D.Twist) {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
    (O : DescentPair D.E r n) (E : MonoidAlgebra ℂ (O.ChosenGL r)) (Z : Submodule ℂ O.FormV)
    (sel : ENNReal) (y : O.FormV) : Prop where
  /-- The form lies in `Z`. -/
  mem : y ∈ Z
  /-- The form is in the range of `typeProjection O c` for a type `c` in lift setting, inside the
  image of `E`. -/
  exists_type : ∃ c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X],
    y ∈ (typeProjection O c).range ∧ IsLiftSetting O c ϑ ∧
    (typeProjection O c).range ≤ (O.groupAlgAction E).range
  /-- The form lifts a system with a main summand `R` for a pair `V` with
  `O.u1Char = V.u1Char * ϑ.toAutChar`, and the Selmer group with divisible coefficients of the
  twisted main summand has length at most `sel`. -/
  exists_hasLiftHeckePolynomial : ∃ z : FinPlace D.E → ℕ → ℂ, O.HasLiftHeckePolynomial y z ∧
    ∃ (R : GalRep ℓ D.E r) (V : DescentPair D.E r n),
      IsMainSummand V z R ∧ O.u1Char = V.u1Char * ϑ.toAutChar ∧
      ∃ (γ : AbsGal D) (s : intQpBar ℓ), HasDivisibleSelmerLengthLe ϑ.invAvatar R ϑ.Q γ s sel

/-- A lift generator for the bound `sel` on the length of its Selmer group is one for every larger
bound. -/
lemma IsLiftGenerator.mono {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
    {ϑ : D.Twist} {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
    {O : DescentPair D.E r n} {E : MonoidAlgebra ℂ (O.ChosenGL r)} {Z : Submodule ℂ O.FormV}
    {sel sel' : ENNReal} {y : O.FormV} (hy : IsLiftGenerator ϑ O E Z sel y) (h_le : sel ≤ sel') :
    IsLiftGenerator ϑ O E Z sel' y := by
  obtain ⟨z, hz, R, V, hR, hμ, γ, s, h_sel⟩ := hy.exists_hasLiftHeckePolynomial
  exact ⟨hy.mem, hy.exists_type, z, hz, R, V, hR, hμ, γ, s, h_sel.mono h_le⟩

/-- A lift (`O.HasLiftHeckePolynomial`: a form whose Hecke polynomials are those of the lift of some
eigenvalues `z`) is an eigenvector of every Hecke polynomial operator, so the span of a set of lifts
is stable under these operators. -/
lemma span_mem_invtSubmodule_heckePolyOnForms {P : Parameters} {D : Data P} {r n : Type}
    [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair D.E r n}
    {S : Set O.FormV} (hS : ∀ y ∈ S, ∃ z : FinPlace D.E → ℕ → ℂ, O.HasLiftHeckePolynomial y z)
    (w : FinPlace D.E) (hw : star w ≠ w) (hw_off : w ∉ O.places.conjClosure) (ξ : ℂ) :
    span ℂ S ∈ (O.heckePolyOnForms (w := w) hw hw_off ξ).invtSubmodule := by
  refine span_le.2 fun y hy ↦ ?_
  obtain ⟨z, hz⟩ : ∃ z : FinPlace D.E → ℕ → ℂ, O.HasLiftHeckePolynomial y z := hS y hy
  change O.heckePolyOnForms hw hw_off ξ y ∈ span ℂ S
  rw [O.heckePolyOnForms_eq_smul hw hw_off (hz w hw hw_off) ξ]
  exact smul_mem _ _ (subset_span hy)

/-- Let `v` be a lift generator (`IsLiftGenerator`) for the pair of hermitian spaces `O`: a form in
`Z`, in the range of `typeProjection O c'` for some tuple of types `c'` compatible with the twist
`ϑ` (a lift setting) and with this range in the image of `E`, that lifts Hecke eigenvalues of a
rank-`r` main summand whose twisted Selmer group has length at most `sel`. Then for every `c`,
either `typeProjection O c` kills `v`, or `v` lies in its range and is a nonzero form of some system
`x`, a space of forms with given Hecke eigenvalues. -/
lemma IsLiftGenerator.typeProjection_eq_zero_or_mem_range {P : Parameters} {D : Data P} {ℓ : ℕ}
    [ThePrime ℓ] [PadicIso ℓ] {ϑ : D.Twist} {r n : Type} [Fintype r] [DecidableEq r] [Fintype n]
    [DecidableEq n]
    {O : DescentPair D.E r n} {E : MonoidAlgebra ℂ (O.ChosenGL r)} {Z : Submodule ℂ O.FormV}
    {sel : ENNReal} {v : O.FormV} (hv : IsLiftGenerator ϑ O E Z sel v)
    (c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X]) :
    typeProjection O c v = 0 ∨
      v ∈ (typeProjection O c).range ∧
      ∃ x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp), IsNonzeroIn v x := by
  classical
  refine or_iff_not_imp_left.2 fun h_ne ↦ ⟨?_, ?_⟩
  · obtain ⟨c', hc', -⟩ := hv.exists_type
    obtain rfl : c = c' := by
      by_contra h_label_ne
      have h_orth : typeProjection O c * typeProjection O c' = 0 := by
        rw [← map_mul, tupleIdem_orthogonal.ortho h_label_ne, map_zero]
      apply h_ne
      rw [← typeProjection_eq_self_of_mem_range hc', ← End.mul_apply, h_orth, LinearMap.zero_apply]
    exact hc'
  · -- Otherwise the line of `v` has no nonzero isotypic form, so it lies in the kernel.
    by_contra h_none
    obtain ⟨z, hz, -⟩ := hv.exists_hasLiftHeckePolynomial
    have h_lifts : ∀ y ∈ ({v} : Set O.FormV), ∃ z : FinPlace D.E → ℕ → ℂ,
      O.HasLiftHeckePolynomial y z := by
      rintro y rfl
      exact ⟨z, hz⟩
    have h_line : span ℂ {v} ≤ (typeProjection O c).ker := by
      refine le_of_isotypic_mem (span_mem_invtSubmodule_heckePolyOnForms h_lifts) ?_
      rintro x y hy ⟨hy_mem, hy_ne⟩
      obtain ⟨a, rfl⟩ : ∃ a : ℂ, a • v = y := mem_span_singleton.1 hy
      rw [map_smul] at hy_mem hy_ne
      obtain ⟨ha, hv_ne⟩ := smul_ne_zero_iff.1 hy_ne
      exact absurd ⟨x, (smul_mem_iff _ ha).1 hy_mem, hv_ne⟩ h_none
    exact h_ne (h_line (mem_span_singleton_self v))

/-- Let `v` be a lift generator (`IsLiftGenerator`): a form in `Z`, of a type forming a lift setting
for `ϑ` whose forms all lie in the image of `E`, that lifts Hecke eigenvalues with a main summand
whose twist has a Selmer group of length at most `sel`. Let `v` be a nonzero form of the system `x`.
Then `x` lifts an `r`-dimensional Galois representation `R` with the properties of a main summand
for weights `wt` (`IsMainSummandLike`): the trace of the normalised representation of `x` is that of
`R` twisted by `ϑ.invAvatar`, the avatar of `ϑ⁻¹`, plus the first `O.rankDiff` powers of the inverse
cyclotomic character (`HasLiftTrace`). For some Galois element `γ` that acts on a lattice in the
twist by the scalar `y`, the Selmer group with divisible coefficients of the twist, with auxiliary
places `ϑ.Q`, has length at most `sel`. -/
lemma IsLiftGenerator.exists_isMainSummandLike {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] {ϑ : D.Twist} {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
    [Nonempty n] {O : DescentPair D.E r n} {E : MonoidAlgebra ℂ (O.ChosenGL r)}
    {Z : Submodule ℂ O.FormV} {sel : ENNReal} {v : O.FormV} (hv : IsLiftGenerator ϑ O E Z sel v)
    {x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)} (hvx : IsNonzeroIn v x) :
    ∃ (wt : (D.E →+* ℂ) → Multiset ℤ) (R : GalRep ℓ D.E r),
      IsMainSummandLike (n := r) D O.rankDiff wt R ∧
      HasLiftTrace ϑ.invAvatar R O.rankDiff (normalisedRep O x.galRep) ∧
      ∃ (γ : AbsGal D) (y : intQpBar ℓ), HasDivisibleSelmerLengthLe ϑ.invAvatar R ϑ.Q γ y sel := by
  obtain ⟨z, hz, R, V, ⟨⟨τ, hR⟩, h_trace⟩, hμ, γ, y, h_sel⟩ := hv.exists_hasLiftHeckePolynomial
  have h_lift : HasLiftTrace ϑ.invAvatar R O.rankDiff (normalisedRep O x.galRep) :=
    h_trace hμ hz (isEigenform hvx.mem hvx.ne_zero) (attached_galRep hvx.mem hvx.ne_zero)
  -- `V.rankDiff` and `O.rankDiff` are both `card n - card r` by definition.
  have hR_O : IsMainSummandLike D O.rankDiff τ R := hR
  exact ⟨τ, R, hR_O, h_lift, γ, y, h_sel⟩

/-- Let `w` be a split place such that neither `w` nor its conjugate lies in `O.places`, the places
of the level of the pair `O`, and let `ξ` be any complex number. The Hecke polynomial operator at
`w`, evaluated at `ξ`, preserves the span of the lift generators (`IsLiftGenerator`): the forms in
`Z`, of a type compatible with the twist `ϑ` (a lift setting) whose forms all lie in the image of
`E`, that lift Hecke eigenvalues of a rank-`r` main summand whose twist has a Selmer group of length
at most `sel`. -/
lemma span_isLiftGenerator_mem_invtSubmodule_heckePolyOnForms {P : Parameters} {D : Data P}
    {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {ϑ : D.Twist} {r n : Type} [Fintype r] [DecidableEq r]
    [Fintype n] [DecidableEq n] {O : DescentPair D.E r n} {E : MonoidAlgebra ℂ (O.ChosenGL r)}
    {Z : Submodule ℂ O.FormV} {sel : ENNReal} (w : FinPlace D.E) (hw : star w ≠ w)
    (hw_off : w ∉ O.places.conjClosure) (ξ : ℂ) :
    span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z sel y} ∈
      (O.heckePolyOnForms (w := w) hw hw_off ξ).invtSubmodule := by
  refine span_mem_invtSubmodule_heckePolyOnForms (fun y hy ↦ ?_) w hw hw_off ξ
  obtain ⟨z, hz, -⟩ := IsLiftGenerator.exists_hasLiftHeckePolynomial hy
  exact ⟨z, hz⟩

/-- For every tuple `c` of types, the action `typeProjection O c` on forms of the idempotent of `c`
preserves the span of the lift generators (`IsLiftGenerator`): the forms in `Z`, of a type
compatible with the twist `ϑ` (a lift setting) whose forms all lie in the image of `E`, that lift
Hecke eigenvalues of a rank-`r` main summand whose twist has a Selmer group of length at most
`sel`. -/
lemma span_isLiftGenerator_mem_invtSubmodule_typeProjection {P : Parameters} {D : Data P} {ℓ : ℕ}
    [ThePrime ℓ] [PadicIso ℓ] {ϑ : D.Twist} {r n : Type} [Fintype r] [DecidableEq r] [Fintype n]
    [DecidableEq n] {O : DescentPair D.E r n} {E : MonoidAlgebra ℂ (O.ChosenGL r)}
    {Z : Submodule ℂ O.FormV} {sel : ENNReal}
    (c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X]) :
    span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z sel y} ∈ (typeProjection O c).invtSubmodule := by
  refine span_le.2 fun v hv ↦ ?_
  change typeProjection O c v ∈ span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z sel y}
  obtain h_zero | ⟨h_range, -⟩ := IsLiftGenerator.typeProjection_eq_zero_or_mem_range hv c
  · rw [h_zero]
    exact zero_mem _
  · rw [typeProjection_eq_self_of_mem_range h_range]
    exact subset_span hv

/-- Consider the span of the lift generators (`IsLiftGenerator`): the forms in `Z`, of a type
compatible with the twist `ϑ` (a lift setting) whose forms all lie in the image of `E`, that lift
Hecke eigenvalues of a rank-`r` main summand whose twist has a Selmer group of length at most
`sel`. It is stable under the Hecke polynomial operators `O.heckePolyOnForms`, at every value `ξ`
and every split place `w` (`star w ≠ w`) such that neither `w` nor its conjugate lies in
`O.places`, the places of the level. It is also stable under `typeProjection O c`, the action on
forms of the idempotent of the tuple of types `c`. -/
lemma span_isLiftGenerator_mem_invtSubmodule {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] {ϑ : D.Twist} {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
    {O : DescentPair D.E r n} {E : MonoidAlgebra ℂ (O.ChosenGL r)} {Z : Submodule ℂ O.FormV}
    {sel : ENNReal} (c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X]) :
    (∀ (w : FinPlace D.E) (hw : star w ≠ w) (hS : w ∉ O.places.conjClosure) (ξ : ℂ),
      span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z sel y} ∈
        (O.heckePolyOnForms (w := w) hw hS ξ).invtSubmodule) ∧
    span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z sel y} ∈ (typeProjection O c).invtSubmodule :=
  ⟨span_isLiftGenerator_mem_invtSubmodule_heckePolyOnForms,
    span_isLiftGenerator_mem_invtSubmodule_typeProjection c⟩

/-- Let the types `c` form a lift setting for the pair `O` and the twist `ϑ`, auxiliary for the bad
places with ramification at most `ram`. Let `Z` be stable under the Hecke polynomials and under
`typeProjection O c`, whose range lies in the image of `E`, and let `y` be orthogonal to the false
lifts: the forms in `Zᗮ` and the image of `E` that a Hecke polynomial at its lift Hecke root kills.
If every nonzero isotypic form in the range of `typeProjection O c` outside `M` belongs to a weak
lift, then `typeProjection O c (y - Z.starProjection y)` lies in `M`. -/
lemma typeProjection_sub_starProjection_mem_of_isOrthogonalToFalseLifts {P : Parameters}
    {D : Data P} {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] (ϑ : D.Twist) {ram : ENNReal}
    (hϑ : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar ram)
    {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair D.E r n}
    {c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X]} (hc : IsLiftSetting O c ϑ)
    {E : MonoidAlgebra ℂ (O.ChosenGL r)} {Z M : Submodule ℂ O.FormV} {y : O.FormV}
    (hZ_hecke : ∀ (w : FinPlace D.E) (hw : star w ≠ w) (hS : w ∉ O.places.conjClosure) (ξ : ℂ),
      Z ∈ (O.heckePolyOnForms (w := w) hw hS ξ).invtSubmodule)
    (hZ_type : Z ∈ (typeProjection O c).invtSubmodule)
    (h_le : (typeProjection O c).range ≤ (O.groupAlgAction E).range)
    (hy : O.IsOrthogonalToFalseLifts E Zᗮ y)
    (h_weak : ∀ x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp),
      ∀ v ∈ (typeProjection O c).range,
      IsNonzeroIn v x → v ∉ M → IsWeakLift O x) :
    typeProjection O c (y - Z.starProjection y) ∈ M := by
  -- One Hecke polynomial kills the forms of base level whose systems are weak lifts.
  have : Nonempty n := card_pos_iff.1 O.rank_lt.pos
  obtain ⟨h_aux, -⟩ := hϑ
  obtain ⟨B, h_base⟩ : ∃ B : BaseLevel (stdSpace D.E n) (O.columnCount, O.detExp)
    D.chosenGroupOrder,
      ∀ v ∈ (typeProjection O c).range, v.toSmoothForm ∈ B.formsOfLevel ![] := by
    obtain ⟨_, B, h_base, -⟩ := exists_baseLevel hc h_aux
    exact ⟨B, h_base⟩
  obtain ⟨w, hw, hS, h_kill⟩ := exists_heckePolyOnForms_eq_zero B
  exact typeProjection_sub_starProjection_mem hZ_hecke hZ_type h_le hy fun x v hv hx hM ↦
    h_kill x v ⟨hx.mem, h_base v hv⟩ hx.ne_zero (h_weak x v hv hx hM)

/-- A form is integral at the place of `ℂ_ℓ` given by `ιℓ` (gauge at most `1` everywhere) if and
only if its algebraic form has `ℓ`-integral coordinates at the points integral above `ℓ`. -/
lemma mem_integralForms_ofIso_iff {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
    {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair D.E r n}
    {y : O.FormV} :
    y ∈ integralForms (PadicPlace.ofIso ιℓ) ↔ y.toSmoothForm ∈ BaseLevel.ellIntegralForms := by
  constructor
  · intro hy g hg
    -- `using!` reads the value `y g` as the value of the algebraic form of `y`
    simpa [PadicPlace.ιₚ_ofIso]
      using! (weylGauge_le_one_iff (ι := PadicPlace.ofIso ιℓ) (y g) hg).1 (hy g)
  · intro hy
    refine weylGauge_le_one_of_integralAbove (ι := PadicPlace.ofIso ιℓ) _ fun g hg ↦ ?_
    simpa [PadicPlace.ιₚ_ofIso] using! hy g hg

/-- Let `v₀` be a lift generator for the bound `sel` on the Selmer length, and a nonzero form
(`IsNonzeroIn`) of the system `x₀`. Every system `x` that contains a nonzero lift generator, with no
bound on the Selmer length, lifts a row `R` (`IsMainSummandLike`) with a twisted lattice
(`HasTwistedLattice`): the trace of the normalised representation of `x` is that of `R` twisted by
`ϑ.invAvatar`, the avatar of `ϑ⁻¹`, plus the powers `e < O.rankDiff` of the inverse cyclotomic
character, some Galois element acts on a lattice in this twist by a scalar, and for `x = x₀` the
Selmer group with divisible coefficients of the twist can be taken of length at most `sel`. -/
lemma IsLiftGenerator.exists_isMainSummandLike_hasTwistedLattice {P : Parameters} {D : Data P}
    {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {ϑ : D.Twist} {r n : Type} [Fintype r] [DecidableEq r]
    [Fintype n] [DecidableEq n] [Nonempty n] {O : DescentPair D.E r n}
    {E : MonoidAlgebra ℂ (O.ChosenGL r)} {Z : Submodule ℂ O.FormV} {sel : ENNReal} {v₀ v : O.FormV}
    {x₀ x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)}
    (hv₀ : IsLiftGenerator ϑ O E Z sel v₀) (hx₀ : IsNonzeroIn v₀ x₀)
    (hv : IsLiftGenerator ϑ O E Z ⊤ v) (hx : IsNonzeroIn v x) :
    ∃ (wt : (D.E →+* ℂ) → Multiset ℤ) (R : GalRep ℓ D.E r),
      IsMainSummandLike (n := r) D O.rankDiff wt R ∧
      HasLiftTrace ϑ.invAvatar R O.rankDiff (normalisedRep O x.galRep) ∧
      ∃ (γ : AbsGal D) (y : intQpBar ℓ), HasTwistedLattice ϑ.invAvatar R γ y ∧
        (x = x₀ → HasDivisibleSelmerLengthLe ϑ.invAvatar R ϑ.Q γ y sel) := by
  by_cases h_eq : x = x₀
  · subst h_eq
    obtain ⟨τ, R, hR, h_trace, γ, y, h_sel⟩ := hv₀.exists_isMainSummandLike hx₀
    exact ⟨τ, R, hR, h_trace, γ, y, h_sel.hasTwistedLattice, fun _ ↦ h_sel⟩
  · obtain ⟨τ, R, hR, h_trace, γ, y, h_sel⟩ := hv.exists_isMainSummandLike hx
    exact ⟨τ, R, hR, h_trace, γ, y, h_sel.hasTwistedLattice, fun h ↦ absurd h h_eq⟩

/-- At each system `x`, `B.diagOp s' ∘ toSmoothForm ∘ typeProjection O c` multiplies a form of `x`
in the range of `typeProjection O c` by `ιℓ.symm (s' x)`. -/
lemma diagOp_toSmoothForm_typeProjection {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
    {O : DescentPair D.E r n} {B : BaseLevel (stdSpace D.E n) (O.columnCount,
      O.detExp) D.chosenGroupOrder}
    {J : Type} [Finite J] {L : J → FinPlace D.E}
    {c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X]}
    (s' : B.Eigensystem L → PadicAlgCl ℓ) (x : B.Eigensystem L) {v : O.FormV}
    (hv : v ∈ (typeProjection O c).range) (hx : IsNonzeroIn v x.val) :
    B.diagOp s' (typeProjection O c v).toSmoothForm = ιℓ.symm (s' x) • v.toSmoothForm := by
  rw [typeProjection_eq_self_of_mem_range hv]
  exact B.diagOp_apply s' x hx.mem

/-- Let `L` be a family of places and `s` a function on `B.Eigensystem L`, the systems that contain
a nonzero form of level `L` over the base data `B`; the operator `B.diagOp s` scales each such
system `x` by `ιℓ.symm (s x)`. Let the forms of type `c`, the range of `typeProjection O c`, have
base level, and let `s` vanish at every system that contains a nonzero lift generator of `Z` for the
twist `ϑ`. Then `B.diagOp s` kills the component `typeProjection O c z` of type `c` of every form
`z` in the span of these lift generators. -/
lemma diagOp_typeProjection_eq_zero_of_mem_span {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] {ϑ : D.Twist} {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
    {O : DescentPair D.E r n} {E : MonoidAlgebra ℂ (O.ChosenGL r)} {Z : Submodule ℂ O.FormV}
    {sel : ENNReal} {B : BaseLevel (stdSpace D.E n) (O.columnCount, O.detExp) D.chosenGroupOrder}
    {J : Type} [Finite J] {L : J → FinPlace D.E}
    {c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X]}
    (h_base : ∀ y ∈ (typeProjection O c).range, y.toSmoothForm ∈ B.formsOfLevel ![])
    {s : B.Eigensystem L → PadicAlgCl ℓ}
    (hs : ∀ x : B.Eigensystem L,
      (∃ v : O.FormV, IsLiftGenerator ϑ O E Z sel v ∧ IsNonzeroIn v x.val) → s x = 0)
    {z : O.FormV} (hz : z ∈ span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z sel y}) :
    B.diagOp s (typeProjection O c z).toSmoothForm = 0 := by
  have h_ker : span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z sel y} ≤
      (B.diagOp s ∘ₗ toSmoothForm ∘ₗ typeProjection O c).ker := by
    refine span_le.2 fun v hv ↦ mem_ker.2 ?_
    rcases IsLiftGenerator.typeProjection_eq_zero_or_mem_range hv c with h_zero | ⟨hvc, x, hvx⟩
    · simp [h_zero]
    · let x' : B.Eigensystem L :=
        ⟨x, v.toSmoothForm, ⟨hvx.mem, B.formsOfLevel_base_le L (h_base v hvc)⟩, hvx.ne_zero⟩
      simp [diagOp_toSmoothForm_typeProjection s x' hvc hvx, hs x' ⟨v, hv, hvx⟩]
  exact mem_ker.1 (h_ker hz)

/-- An operator for one lift generator. Let `ϑ` have ramification at most `ram` (`IsAuxTwist`), let
`Z` be spanned by lift generators for the bound `⊤`, and let `v₀ ≠ 0` be one for the finite `sel`.
Then a linear map `G` from the forms `O.FormV` to their algebraic forms has every lift generator as
an eigenvector, with an eigenvalue at `v₀` of `ℓ`-adic valuation at most
`liftValuationBound ℓ O ram sel`, which is `sel + 2 * O.rankDiff * ram + card r * localDefectBound D
ℓ + denominatorError D ℓ`. Let `y` be integral at `ιℓ` and orthogonal to the false lifts: the forms
in `Zᗮ` and the image of `E` that, at some split place, the Hecke polynomial at `O.liftHeckeRoot`
kills. Then every form whose algebraic form is `G` of the projection of `y` to `Z` is integral at
`ιℓ`. -/
lemma exists_linearMap_eq_smul_mem_integralForms {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] (ϑ : D.Twist) {ram sel : ENNReal}
    (hϑ : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar ram) (h_sel_ne_top : sel ≠ ⊤)
    {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair D.E r n}
    {E : MonoidAlgebra ℂ (O.ChosenGL r)} {Z : Submodule ℂ O.FormV}
    (h_span : Z ≤ span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z ⊤ y})
    {v₀ : O.FormV} (hv₀ : IsLiftGenerator ϑ O E Z sel v₀) (hv₀_ne : v₀ ≠ 0) :
    ∃ G : O.FormV →ₗ[ℂ] (stdSpace D.E n).forms (O.columnCount, O.detExp),
      (∀ v : O.FormV, IsLiftGenerator ϑ O E Z ⊤ v → ∃ μ : ℂ, G v = μ • v.toSmoothForm) ∧
      (∀ μ : ℂ, G v₀ = μ • v₀.toSmoothForm →
        ellVal (ℓ := ℓ) (ιℓ μ) ≤ liftValuationBound ℓ O ram sel) ∧
      ∀ y : O.FormV, y ∈ integralForms (PadicPlace.ofIso ιℓ) → O.IsOrthogonalToFalseLifts E Zᗮ y →
        ∀ w : O.FormV, w.toSmoothForm = G (Z.starProjection y) →
          w ∈ integralForms (PadicPlace.ofIso ιℓ) := by
  -- For a type `c` of `v₀`, `G` is `D.chosenGroupOrder ^ 2` times
  -- `B.diagOp s ∘ toSmoothForm ∘ typeProjection O c`, with `s` from
  -- `exists_ellVal_le_and_diagOp_mem_ellIntegralForms`.
  set A : Set O.FormV := {y : O.FormV | IsLiftGenerator ϑ O E Z ⊤ y} with hA
  have hZ : span ℂ A = Z := span_eq_of_le _ (fun y hy ↦ IsLiftGenerator.mem hy) h_span
  let 𝓧 : Set (Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)) :=
    {x | ∃ v ∈ A, IsNonzeroIn v x}
  choose c hv₀c hc h_le using hv₀.exists_type
  have h_system : ∃ x₀ : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp),
    IsNonzeroIn v₀ x₀ := by
    have h_ne : typeProjection O c v₀ ≠ 0 :=
      (typeProjection_eq_self_of_mem_range hv₀c).trans_ne hv₀_ne
    obtain ⟨-, h_system⟩ := (hv₀.typeProjection_eq_zero_or_mem_range c).resolve_left h_ne
    exact h_system
  choose x₀ hx₀ using h_system
  have : Nonempty n := card_pos_iff.1 O.rank_lt.pos
  choose _ B h_base h_int h_col h_quad using exists_baseLevel hc hϑ.1
  have hx₀_mem : x₀ ∈ 𝓧 := ⟨v₀, hv₀.mono le_top, hx₀⟩
  have hx₀_base : x₀ ∈ B.Eigensystem ![] :=
    ⟨v₀.toSmoothForm, ⟨hx₀.mem, h_base v₀ hv₀c⟩, hx₀.ne_zero⟩
  choose J _ L s h_val h_op using exists_ellVal_le_and_diagOp_mem_ellIntegralForms hc hϑ (𝓧 := 𝓧)
    (x₀ := x₀)
    (fun x ⟨v, hv, hvx⟩ ↦ hv₀.exists_isMainSummandLike_hasTwistedLattice hx₀ hv hvx)
    h_sel_ne_top B h_col h_quad hx₀_mem hx₀_base
  -- `G s'` multiplies a form of type `c` at the system `x` by `s'` at `sys x`.
  let sys {x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)} {v : O.FormV}
      (hv : v ∈ (typeProjection O c).range) (hx : IsNonzeroIn v x) : B.Eigensystem L :=
    ⟨x, v.toSmoothForm, ⟨hx.mem, B.formsOfLevel_base_le L (h_base v hv)⟩, hx.ne_zero⟩
  let G (s' : B.Eigensystem L → PadicAlgCl ℓ) :
      O.FormV →ₗ[ℂ] (stdSpace D.E n).forms (O.columnCount, O.detExp) :=
    B.diagOp s' ∘ₗ toSmoothForm ∘ₗ typeProjection O c
  obtain ⟨hT, hZc⟩ :=
    span_isLiftGenerator_mem_invtSubmodule (ϑ := ϑ) (E := E) (Z := Z) (sel := ⊤) c
  rw [← hA, hZ] at hT hZc
  refine ⟨(D.chosenGroupOrder : ℂ) ^ 2 • G s, fun v hv ↦ ?_, fun μ hμ ↦ ?_,
    fun y hy_int hy w hw_eq ↦ ?_⟩
  · rcases hv.typeProjection_eq_zero_or_mem_range c with h_zero | ⟨hvc, x, hvx⟩
    · exact ⟨0, by simp [G, h_zero]⟩
    · exact ⟨(D.chosenGroupOrder : ℂ) ^ 2 * ιℓ.symm (s (sys hvc hvx)),
        by simp [G, diagOp_toSmoothForm_typeProjection s (sys hvc hvx) hvc hvx, smul_smul]⟩
  · -- the eigenvalue at `v₀` is `D.chosenGroupOrder ^ 2` times the value of `s` at `x₀`
    have h_eq : μ = (D.chosenGroupOrder : ℂ) ^ 2 * ιℓ.symm (s (sys hv₀c hx₀)) := by
      refine smul_left_injective ℂ hx₀.ne_zero (hμ.symm.trans ?_)
      simp [G, diagOp_toSmoothForm_typeProjection s (sys hv₀c hx₀) hv₀c hx₀, smul_smul]
    rw [h_eq, map_mul, map_pow, map_natCast, RingEquiv.apply_symm_apply]
    exact h_val (sys hv₀c hx₀) rfl
  -- The component of type `c` of the projection of `y` is supported on `𝓧`.
  have h_supp (s' : B.Eigensystem L → PadicAlgCl ℓ)
      (hs' : ∀ x : B.Eigensystem L, x.val ∈ 𝓧 → s' x = 0) : G s' (Z.starProjection y) = 0 :=
    diagOp_typeProjection_eq_zero_of_mem_span h_base hs' (h_span (Z.starProjection_apply_mem y))
  -- It agrees with the component of type `c` of `y` at the weak lifts.
  have h_agree (s' : B.Eigensystem L → PadicAlgCl ℓ)
      (hs' : ∀ x : B.Eigensystem L, x.val ∈ B.Eigensystem ![] → ¬IsWeakLift O x.val → s' x = 0) :
      G s' y = G s' (Z.starProjection y) := by
    refine (LinearMap.sub_mem_ker_iff (f := G s')).1
      (typeProjection_sub_starProjection_mem_of_isOrthogonalToFalseLifts ϑ hϑ hc
      (M := (B.diagOp s' ∘ₗ toSmoothForm).ker) hT hZc h_le hy fun x v hv hx h_notMem ↦ ?_)
    by_contra h_notWeak
    have h_zero : s' (sys hv hx) = 0 :=
      hs' (sys hv hx) ⟨v.toSmoothForm, ⟨hx.mem, h_base v hv⟩, hx.ne_zero⟩ h_notWeak
    exact h_notMem (by simp [B.diagOp_apply s' (sys hv hx) hx.mem, h_zero])
  have h_ell : D.chosenGroupOrder • D.chosenGroupOrder • G s (Z.starProjection y) ∈
      BaseLevel.ellIntegralForms :=
    h_op _ (h_base _ ⟨y, rfl⟩) (h_int y (mem_integralForms_ofIso_iff.1 hy_int)) _
      (h_base _ ⟨Z.starProjection y, rfl⟩) h_supp h_agree
  rw [mem_integralForms_ofIso_iff, hw_eq]
  simpa [sq, mul_smul, Nat.cast_smul_eq_nsmul ℂ] using h_ell

/-- The operator `Λ` on `Z` preserves every eigenspace in `Z` of every Hecke polynomial at a split
place off the places of `O` and their conjugates. -/
def PreservesHeckeEigenspaces {P : Parameters} {D : Data P} {r n : Type} [Fintype r]
    [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair D.E r n} {Z : Submodule ℂ O.FormV}
    (Λ : Module.End ℂ Z) : Prop :=
  ∀ (w : FinPlace D.E) (hw : star w ≠ w) (hw_off : w ∉ O.places.conjClosure) (ξ a : ℂ) (z : Z),
    O.heckePolyOnForms hw hw_off ξ z = a • (z : O.FormV) →
      O.heckePolyOnForms hw hw_off ξ (Λ z) = a • (Λ z : O.FormV)

/-- An operator on `Z` that is diagonal in a basis of lifts (`O.HasLiftHeckePolynomial`: Hecke
eigenforms that lift some system `z`) preserves the eigenspaces of the Hecke polynomials. -/
lemma preservesHeckeEigenspaces_toLin_diagonal {P : Parameters} {D : Data P} {r n : Type}
    [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair D.E r n}
    {Z : Submodule ℂ O.FormV} {m : ℕ} (b : Basis (Fin m) ℂ Z)
    (hb : ∀ k : Fin m, ∃ z : FinPlace D.E → ℕ → ℂ, O.HasLiftHeckePolynomial (b k : O.FormV) z)
      (μ : Fin m → ℂ) :
    PreservesHeckeEigenspaces (Matrix.toLin b b (Matrix.diagonal μ)) := by
  intro w hw hw_off ξ a z hz
  -- On `Z` the Hecke polynomial is diagonal in `b` as well, and diagonal operators commute.
  have h_eig (k : Fin m) : ∃ e : ℂ, O.heckePolyOnForms hw hw_off ξ (b k) = e • (b k : O.FormV) := by
    obtain ⟨z_k, hz_k⟩ := hb k
    exact ⟨_, O.heckePolyOnForms_eq_smul hw hw_off (hz_k w hw hw_off) ξ⟩
  choose e he using h_eig
  let T : Module.End ℂ Z := Matrix.toLin b b (Matrix.diagonal e)
  have h_lin : O.heckePolyOnForms hw hw_off ξ ∘ₗ Z.subtype = Z.subtype ∘ₗ T :=
    b.ext fun k ↦ by simp [T, Matrix.diagonal, he]
  have hT (z' : Z) : O.heckePolyOnForms hw hw_off ξ z' = T z' := LinearMap.congr_fun h_lin z'
  have h_comm :
      T * Matrix.toLin b b (Matrix.diagonal μ) = Matrix.toLin b b (Matrix.diagonal μ) * T :=
    b.ext fun k ↦ by simp [T, Matrix.diagonal, smul_smul, mul_comm]
  have hTz : T z = a • z := Subtype.ext ((hT z).symm.trans hz)
  rw [hT, ← Module.End.mul_apply, h_comm, Module.End.mul_apply, hTz, map_smul, Submodule.coe_smul]

/-- Bound for denominators. Let the twist `ϑ` have ramification at most `ram` (`IsAuxTwist`), let
`sel` be finite, and let `Z` be spanned by lift generators: forms in `Z`, of a type compatible with
`ϑ` (a lift setting) inside the image of the group-algebra element `E`, that lift Hecke eigenvalues
with main summands whose twisted Selmer groups with divisible coefficients have length at most
`sel`. Then an operator `Λ` on `Z` preserves the eigenspaces of the Hecke polynomials at the split
places off `O.places.conjClosure`, has eigenvalues of valuation at most
`liftValuationBound ℓ O ram sel`, which is `sel + 2 * O.rankDiff * ram + card r * localDefectBound D
ℓ + denominatorError D ℓ`, and takes to forms integral at `ιℓ` the projections to `Z` of forms
integral at `ιℓ` and orthogonal to the false lifts, which are the forms in `Zᗮ` and the image of `E`
that, at some split place, the Hecke polynomial at `O.liftHeckeRoot`, the value expected of a lift,
kills. Here `ιℓ` is the fixed isomorphism from `ℂ` to the algebraic closure of `ℚ_ℓ`. -/
theorem exists_operator_ellVal_le_liftValuationBound {P : Parameters} {D : Data P} {ℓ : ℕ}
    [ThePrime ℓ] [PadicIso ℓ] (ϑ : D.Twist) {ram sel : ENNReal}
    (hϑ : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar ram) (h_sel_ne_top : sel ≠ ⊤)
    {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair D.E r n}
    {E : MonoidAlgebra ℂ (O.ChosenGL r)} {Z : Submodule ℂ O.FormV}
    (h_span : Z ≤ span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z sel y}) :
    ∃ Λ : Module.End ℂ Z,
      PreservesHeckeEigenspaces Λ ∧
      (∀ μ : ℂ, Λ.HasEigenvalue μ → ellVal (ℓ := ℓ) (ιℓ μ) ≤ liftValuationBound ℓ O ram sel) ∧
      ∀ y : O.FormV, y ∈ integralForms (PadicPlace.ofIso ιℓ) → O.IsOrthogonalToFalseLifts E Zᗮ y →
        (Λ (Z.orthogonalProjectionOnto y) : O.FormV) ∈ integralForms (PadicPlace.ofIso ιℓ) := by
  -- Choose a basis `b` of `Z` among the lift generators. The operators of
  -- `exists_linearMap_eq_smul_mem_integralForms` for the basis vectors, moved to `Z`, are diagonal
  -- in `b`, and one integral combination of them serves all basis vectors at once
  -- (`exists_diagonal_mem_norm_ge`).
  set A : Set O.FormV := {y : O.FormV | IsLiftGenerator ϑ O E Z sel y}
  let ι : Type := Fin (finrank ℂ (span ℂ A))
  obtain ⟨ω, hωA, hω_span, h_indep⟩ : ∃ ω : ι → O.FormV, (∀ k : ι, ω k ∈ A) ∧
      span ℂ (Set.range ω) = span ℂ A ∧ LinearIndependent ℂ ω :=
    exists_fun_fin_finrank_span_eq ℂ A
  have h_eq : span ℂ (Set.range ω) = Z :=
    hω_span.trans (span_eq_of_le _ (fun y hy ↦ IsLiftGenerator.mem hy) h_span)
  let b : Basis ι ℂ Z := (Basis.span h_indep).map (LinearEquiv.ofEq _ _ h_eq)
  have hb (k : ι) : (b k : O.FormV) = ω k := by simp [b, Basis.span_apply]
  have h_span_top : Z ≤ span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z ⊤ y} :=
    h_span.trans (span_mono fun y hy ↦ IsLiftGenerator.mono hy le_top)
  choose G hG_eig hG_bound hG_int using fun k : ι ↦
    exists_linearMap_eq_smul_mem_integralForms ϑ hϑ h_sel_ne_top h_span_top (hωA k)
      (h_indep.ne_zero k)
  have h_eigenvalue (k p : ι) : ∃ μ : ℂ, G k (ω p) = μ • (ω p).toSmoothForm :=
    hG_eig k (ω p) (IsLiftGenerator.mono (hωA p) le_top)
  choose eig h_eig using h_eigenvalue
  let Good : Set (Module.End ℂ Z) := {Λ | ∀ y : O.FormV,
    y ∈ integralForms (PadicPlace.ofIso ιℓ) → O.IsOrthogonalToFalseLifts E Zᗮ y →
      (Λ (Z.orthogonalProjectionOnto y) : O.FormV) ∈ integralForms (PadicPlace.ofIso ιℓ)}
  have h_good (k : ι) : Matrix.toLin b b (Matrix.diagonal (eig k)) ∈ Good := by
    intro y hy_int hy
    -- both sides are linear in the vector of `Z` and agree on the basis `b`
    have h_lin : (toSmoothForm : O.FormV →ₗ[ℂ] (stdSpace D.E n).forms (O.columnCount, O.detExp)) ∘ₗ
        Z.subtype ∘ₗ Matrix.toLin b b (Matrix.diagonal (eig k)) = G k ∘ₗ Z.subtype :=
      b.ext fun p ↦ by simp [Matrix.diagonal, hb, h_eig]
    exact hG_int k y hy_int hy _ (LinearMap.congr_fun h_lin (Z.orthogonalProjectionOnto y))
  have h_comb (G' : ι → Module.End ℂ Z) (d : ι → PadicAlgCl ℓ) (hG' : ∀ p : ι, G' p ∈ Good)
      (hd : ∀ p : ι, ‖d p‖ ≤ 1) : ∑ p : ι, ιℓ.symm (d p) • G' p ∈ Good := by
    intro y hy_int hy
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
    have h_nnnorm (p : ι) : ‖d p‖₊ ≤ 1 := hd p
    exact sum_mem fun p _ ↦
      (integralForms _).smul_mem ⟨ιℓ.symm (d p), by simpa [PadicPlace.ιₚ_ofIso] using h_nnnorm p⟩
        (hG' p y hy_int hy)
  obtain ⟨μ, hμ_good, hμ_ge⟩ : ∃ μ : ι → ℂ, Matrix.toLin b b (Matrix.diagonal μ) ∈ Good ∧
      ∀ k : ι, ‖ιℓ (eig k k)‖ ≤ ‖ιℓ (μ k)‖ :=
    exists_diagonal_mem_norm_ge b h_comb eig h_good
  refine ⟨Matrix.toLin b b (Matrix.diagonal μ), ?_, fun ν hν ↦ ?_, hμ_good⟩
  · refine preservesHeckeEigenspaces_toLin_diagonal b (fun k ↦ ?_) μ
    obtain ⟨z, hz, -⟩ := IsLiftGenerator.exists_hasLiftHeckePolynomial (hωA k)
    exact ⟨z, by rwa [hb]⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ι, μ k = ν := (hasEigenvalue_toLin_diagonal_iff μ b).1 hν
    calc ellVal (ιℓ (μ k)) ≤ ellVal (ιℓ (eig k k)) := ellVal_le_ellVal (hμ_ge k)
      _ ≤ liftValuationBound ℓ O ram sel := hG_bound k (eig k k) (h_eig k k)

/-- If `N * ιℓ μ` has `ℓ`-adic valuation at most `B` for every eigenvalue `μ` of `Λ`, then the
determinant of `N • Λ` has `ℓ`-adic norm at least `exp (-(finrank ℂ Z * (B * log ℓ)))`. -/
lemma exp_le_norm_det_smul_of_ellVal_le {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {Z : Type}
    [AddCommGroup Z] [Module ℂ Z] [Module.Finite ℂ Z] (N : ℕ) (Λ : Module.End ℂ Z) (B : NNReal)
    (h_eig : ∀ μ : ℂ, Λ.HasEigenvalue μ → ellVal ((N : PadicAlgCl ℓ) * ιℓ μ) ≤ B) :
    exp (-(finrank ℂ Z * (B * log ℓ))) ≤ ‖ιℓ (LinearMap.det ((N : ℂ) • Λ))‖ := by
  -- The determinant is the product of the eigenvalues, each of norm at least `ε = ℓ ^ (-B)`.
  let ε : NNReal := ⟨exp (-(B * log ℓ)), (exp_pos _).le⟩
  have h_rpow : exp (-(B * log ℓ)) = (ℓ : ℝ) ^ (-(B : ℝ)) := by
    simp [rpow_def_of_pos, NeZero.pos, mul_comm]
  have h_eig' (μ : ℂ) (hμ : Λ.HasEigenvalue μ) : ε ≤ ‖(N : PadicAlgCl ℓ) * ιℓ μ‖₊ := by
    change exp (-(B * log ℓ)) ≤ ‖(N : PadicAlgCl ℓ) * ιℓ μ‖
    rw [h_rpow]
    exact ellVal_le_iff.1 (h_eig μ hμ)
  have h_pow : exp (-(finrank ℂ Z * (B * log ℓ))) = exp (-(B * log ℓ)) ^ finrank ℂ Z := by
    rw [← exp_nat_mul, mul_neg]
  rw [h_pow, LinearMap.det_smul, map_mul, map_pow, map_natCast]
  exact_mod_cast pow_finrank_le_nnnorm_det Λ _ h_eig'

/-- The operator form of the bound for denominators with the clearing bound. Let the twist `ϑ` have
ramification at most `twistError ℓ D`, the small number `(4 f + 3) r v_ℓ(N) + 2 ^ (-ℓ)` with
`N = D.chosenGroupOrder`, with respect to the places above `ℓ` and the level (`badPlaces D ℓ`), and
let `Z` be spanned by lift generators (`IsLiftGenerator`): forms in `Z` of suitable type that lift
Hecke eigenvalues with main summands whose twisted Selmer groups have length at most
`twistError ℓ D`. Then some operator `Λ` on `Z` has a determinant of `ℓ`-adic norm at least
`exp (-(finrank ℂ Z * (card r * (β * log ℓ))))`, where `β = clearingBound D ℓ` adds the local
losses, error terms and `v_ℓ(N)`. It takes the projection to `Z` of every form `y'` integral at `ιℓ`
and orthogonal to the false lifts to a form integral at `ιℓ`, whose pairings with the forms integral
at all places above `ℓ` are integral. -/
theorem exists_operator_det_clearingBound {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] (ϑ : D.Twist) (hϑ : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (twistError ℓ D))
    {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair D.E r n}
    {E : MonoidAlgebra ℂ (O.ChosenGL r)} {Z : Submodule ℂ O.FormV}
    (h_span : Z ≤ span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z (twistError ℓ D) y}) :
    ∃ Λ : Module.End ℂ Z,
      exp (-(finrank ℂ Z * (card r * (clearingBound D ℓ * log ℓ)))) ≤ ‖ιℓ (LinearMap.det Λ)‖ ∧
      (∀ y' : O.FormV, y' ∈ integralForms (PadicPlace.ofIso ιℓ) → O.IsOrthogonalToFalseLifts E Zᗮ y'
        →
        (Λ (Z.orthogonalProjectionOnto y') : O.FormV) ∈ integralForms (PadicPlace.ofIso ιℓ)) ∧
      ∀ y y' : O.FormV, (∀ j : PadicPlace ℓ, y ∈ integralForms j) →
        y' ∈ integralForms (PadicPlace.ofIso ιℓ) → O.IsOrthogonalToFalseLifts E Zᗮ y' →
        ‖ιℓ (inner ℂ y (Λ (Z.orthogonalProjectionOnto y') : O.FormV))‖ ≤ 1 := by
  -- If no generator is nonzero, then `Z = ⊥` and the identity serves. Otherwise some generator
  -- exists; its lift-setting type bounds the rank and the automorphism groups, and
  -- `D.chosenGroupOrder • Λ` serves, with `Λ` of `exists_operator_ellVal_le_liftValuationBound`.
  set A : Set O.FormV := {y : O.FormV | IsLiftGenerator ϑ O E Z (twistError ℓ D) y}
  by_cases! h_gen : ∀ v ∈ A, v = 0
  · have h_bot : Z ≤ ⊥ := h_span.trans (span_eq_bot.2 h_gen).le
    have h_rank : finrank ℂ Z = 0 := Submodule.finrank_eq_zero.2 (eq_bot_iff.2 h_bot)
    have h_zero (z : Z) : (z : O.FormV) = 0 := (mem_bot ℂ).1 (h_bot z.prop)
    refine ⟨1, by simp [h_rank], fun y' _ _ ↦ ?_, fun y y' _ _ _ ↦ ?_⟩
    · rw [h_zero]
      exact zero_mem _
    · rw [h_zero, inner_zero_right, map_zero, norm_zero]
      exact zero_le_one
  obtain ⟨v, hv, -⟩ := h_gen
  obtain ⟨c, -, hc, -⟩ := IsLiftGenerator.exists_type hv
  have h_rank_pos : 1 ≤ card r := hc.odd.1.pos
  obtain ⟨h_r_le, h_rankDiff_le⟩ := hc.rank_le
  have h_budget : liftValuationBound ℓ O (twistError ℓ D) (twistError ℓ D) +
      padicValNat ℓ D.chosenGroupOrder ≤ card r * clearingBound D ℓ :=
    add_denominatorError_le_mul_clearingBound ⟨h_rank_pos, h_r_le⟩ h_rankDiff_le le_rfl le_rfl
  obtain ⟨Λ, -, h_eig, h_int⟩ :=
    exists_operator_ellVal_le_liftValuationBound ϑ hϑ ENNReal.coe_ne_top h_span
  refine ⟨(D.chosenGroupOrder : ℂ) • Λ, ?_, fun y' hy' hy'_test ↦ ?_, fun y y' hy hy' hy'_test ↦ ?_⟩
  · -- the determinant is the product of the eigenvalues, each of valuation at most
    -- `card r * clearingBound D ℓ`
    have h_val (μ : ℂ) (hμ : Λ.HasEigenvalue μ) :
        ellVal ((D.chosenGroupOrder : PadicAlgCl ℓ) * ιℓ μ) ≤ card r * clearingBound D ℓ := by
      grw [ellVal_mul_le, ellVal_natCast (NeZero.ne _), h_eig μ hμ, add_comm]
      exact h_budget
    calc exp (-(finrank ℂ Z * (card r * (clearingBound D ℓ * log ℓ))))
        = exp (-(finrank ℂ Z * (((card r * clearingBound D ℓ : NNReal) : ℝ) * log ℓ))) := by
          push_cast
          ring_nf
      _ ≤ ‖ιℓ (LinearMap.det ((D.chosenGroupOrder : ℂ) • Λ))‖ :=
          exp_le_norm_det_smul_of_ellVal_le _ Λ _ h_val
  · -- an integer multiple of an integral form is integral
    rw [LinearMap.smul_apply, Submodule.coe_smul, Nat.cast_smul_eq_nsmul ℂ]
    exact nsmul_mem (h_int y' hy' hy'_test) _
  · -- with the factor `D.chosenGroupOrder` the pairing is integral
    have h_pair : ‖(PadicPlace.ofIso ιℓ).ιₚ
        (D.chosenGroupOrder • inner ℂ y (Λ (Z.orthogonalProjectionOnto y') : O.FormV))‖ ≤ 1 :=
      y.norm_nsmul_inner_le_one _ (PadicPlace.ofIso ιℓ)
        (D.card_classAut_dvd_chosenGroupOrder hc.card_le levelOf_le_stdLevel) (hy _)
        (h_int y' hy' hy'_test)
    rw [LinearMap.smul_apply, Submodule.coe_smul, inner_smul_right_eq_smul,
      Nat.cast_smul_eq_nsmul ℂ]
    simpa [PadicPlace.ιₚ_ofIso, ← PadicComplex.norm_extends ℓ D.chosenGroupOrder] using h_pair

/-- Denominators for a good twist. Let `ι.ιℓ` be the isomorphism from `ℂ` to the algebraic closure
of `ℚ_ℓ` that `ι` chooses, and `ψ = ϑ.invAvatar` the `ℓ`-adic avatar of `ϑ⁻¹` for it. Let
`β = clearingBound D ℓ`, the sum of the local losses, the error terms and the valuation of
`D.chosenGroupOrder`; the small number `twistError ℓ D` is one of these terms. Assume: (i) the set
`ϑ.Q` is auxiliary for `ψ` and the places above `ℓ` and the level (`badPlaces D ℓ`), with
ramification at most `twistError ℓ D` (`IsAuxTwist`); (ii) `Z` is spanned by lift generators
(`IsLiftGenerator`): vectors of `Z` of a type `c` that forms a lift setting inside the image of `E`,
each lifting Hecke eigenvalues `z` with a main summand `R` for some pair `V` with
`O.u1Char = V.u1Char * ϑ.toAutChar`, where the Selmer group of `ψ R` with divisible coefficients has
length at most `twistError ℓ D`. Then `DenominatorLe` holds for `E` and `Z` with exponent `β log ℓ`:
some operator on `Z` with determinant of `ℓ`-adic norm at least
`exp (-(finrank ℂ Z * (card r * (β * log ℓ))))` takes the projection to `Z` of each form integral at
`ι.ιℓ` and orthogonal to the false lifts to a form that is integral at `ι.ιℓ` and has integral
pairings with the forms integral at all places above `ℓ`. -/
theorem denominatorLe_clearingBound {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    (ι : PadicIso ℓ) (ϑ : D.Twist)
    (hϑ : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (twistError ℓ D))
    {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair D.E r n}
    {E : MonoidAlgebra ℂ (O.ChosenGL r)} {Z : Submodule ℂ O.FormV}
    (h_span : Z ≤ span ℂ {y : O.FormV | IsLiftGenerator ϑ O E Z (twistError ℓ D) y}) :
    DenominatorLe ι.ιℓ O E Z (clearingBound D ℓ * log ℓ) := by
  obtain ⟨Λ, h_det, h_int, h_pair⟩ := exists_operator_det_clearingBound ϑ hϑ h_span
  refine ⟨Λ, h_det, fun y hy hy_test ↦ ⟨?_, fun y' hy' ↦ ?_⟩⟩
  · exact h_int y hy hy_test
  · exact h_pair y' y hy' hy hy_test

end New.Selmer
