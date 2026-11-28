import Lib.General.NumberTheory.LargeResidueField
import New.Congruences.FirstOrder.EvenClasses
import New.Congruences.Selmer.GeneralTheorem
import New.Congruences.Selmer.LValueSystems
import New.Congruences.Selmer.MainSummands

/-!
# The twisting theorem

The general twisting theorem is applied to the Selmer data of finitely many representations of
main-summand type and to the Stickelberger systems of the ramified pairs, and the Galois character
it gives is read as the `ℓ`-adic avatar of a tame character.

* `New.Selmer.SelmerDatum.TwistedLengthLe.hasDivisibleSelmerLengthLe`: a bound for the twisted
  Selmer group of a datum bounds the crystalline Selmer group of the twisted representation.
* `New.Selmer.exists_mFoldTwist_hasDivisibleSelmerLengthLe`: one tame character whose first `D.m`
  powers have small ramification, short Selmer groups on the main summands, and ratios of `L`-values
  of small valuation.

Notions from other files:
* `New.Selmer.HasDivisibleSelmerLengthLe`: a bound for the length of the Selmer group of a twisted
  representation with coefficients in `Frac(O) / O`.
* `New.Selmer.IsMainSummandLike`: the hypotheses on an `ℓ`-adic representation of the Galois group
  of `D.E` under which its Selmer groups are estimated.
* `New.Selmer.SelmerDatum`: a lattice `T` with Galois action, local conditions and an inertial
  element that acts by a scalar.
* `New.Selmer.twistError`: the number `e'_ℓ = (4 f + 3) r v(D.chosenGroupOrder) + 2 ^ (-ℓ)`.
* `New.Data.MFoldTwist`: a tame character whose tame part has non-trivial `n`-th power at every
  place of its modulus `Q`, for `1 ≤ n ≤ D.m`.
* `New.Data.CriticalPair.ratio`: the ratio `|L(z, (νϑ^s)⁻¹)| / |L(z, ν⁻¹)|` for a sign `s`, without
  the Euler factors at the chosen places, the modulus and their conjugates.

## Relation to the literature

For finitely many main summands of Galois representations of lifts, one finite-order anticyclotomic
twist ramified at new primes makes, for each of its first m powers, all Selmer groups short and the
ratios of twisted to untwisted Hecke values barely divisible by ℓ. This limits congruences. Twists
of ℓ-power order at new primes that kill a Selmer group or keep L-values barely divisible are known
in the literature. Related work: Mazur–Rubin, Diophantine stability, 2018; Kriz–Nordentoft,
Horizontal p-adic L-functions, 2023; Hida, Non-vanishing modulo p of Hecke L-values, 2004.
-/

namespace New.Selmer

open Filter Real

open scoped NNReal ENNReal

section Lemmas

open Matrix Module Finsupp Finset CoeffRing Subalgebra RingHom

/-- If the image of a complex number `x` under `ιℓ : ℂ ≃ ℚ̄_ℓ` has `ℓ`-adic valuation at most `c`,
then the image of `x⁻¹` has norm at most `ℓ ^ c`. -/
lemma norm_inv_le_exp_of_ellVal_le {ℓ : ℕ} [ThePrime ℓ] {ι : PadicIso ℓ} {x : ℂ} {c : ℝ≥0}
    (h_val : ellVal (ιℓ x : PadicAlgCl ℓ) ≤ c) :
    ‖(ιℓ x⁻¹ : PadicAlgCl ℓ)‖ ≤ exp (c * log ℓ) := by
  have hℓ : (0 : ℝ) < ℓ := Nat.cast_pos.2 (NeZero.pos ℓ)
  have h_norm : (ℓ : ℝ) ^ (-(c : ℝ)) ≤ ‖(ιℓ x : PadicAlgCl ℓ)‖ := ellVal_le_iff.1 h_val
  rw [rpow_neg hℓ.le] at h_norm
  rw [map_inv₀, norm_inv, mul_comm, ← rpow_def_of_pos hℓ]
  exact inv_le_of_inv_le₀ (rpow_pos_of_pos hℓ c) h_norm

section General

variable {ℓ : ℕ} [ThePrime ℓ] {E n : Type} [Field E] [CMFieldWithRoot5040 E] [Fintype n]
  {O : CoeffRing ℓ}

/-- Let `u` be a Galois representation over a coefficient ring `O ≤ O'`, and let `ψ` be an
`O'`-valued character that is trivial on the chosen decomposition groups above `ℓ`. A linear
relation that holds on the crystalline cocycles of `u` at a place above `ℓ`, with its coefficients
mapped to `O'`, is such a relation for the twist by `ψ` of the extension of `u` to `O'`. -/
lemma mapRel_crysRelations_subset [DecidableEq n] {O' : CoeffRing ℓ} (hO : O ≤ O')
    (u : Gal(Ω/E) →* Matrix n n O) {ψ : Gal(Ω/E) →* O'}
    (hψ : ∀ v ∈ placesDividing E ℓ, ∀ g ∈ decompGroup Gal(Ω/E) (placeOver v), ψ g = 1) :
    mapRel (inclusion hO).toRingHom '' crysRelations u ⊆
      crysRelations
        (twistRep (.id O') ψ ((inclusion hO).toRingHom.mapMatrix.toMonoidHom.comp u)) := by
  let : Algebra O O' := (inclusion hO).toRingHom.toAlgebra
  -- `O'` is finite and torsion-free over `O`, hence projective.
  have h_torsionFree : IsTorsionFree O O' := (inclusion.faithfulSMul hO).to_isTorsionFree
  have h_finite : Module.Finite O O' := Finite.right ℤ_[ℓ] O O'
  -- Let `f` be a relation on `crysCocyclesAt v u`, `v` above `ℓ`; we show that `mapRel _ f` holds
  -- on each crystalline cocycle `z` of the twist at `v`.
  rintro _ ⟨f', hf', rfl⟩
  obtain ⟨v, f, hf, rfl⟩ := Set.mem_iUnion.1 hf'
  refine Set.mem_iUnion.2 ⟨v, mapRel (inclusion hO).toRingHom f, fun z hz ↦ ?_,
    mapDomain_mapRange _ _ _ _ (map_add _)⟩
  -- As `O'` is projective over `O`, it suffices to test the relation with each `O`-linear form.
  suffices h_dual : ∀ (i : n) (l : Dual O O'),
      l (relEval O' (mapRel (inclusion hO).toRingHom f) z i) = 0 from
    funext fun i ↦ (forall_dual_apply_eq_zero_iff O _).1 (h_dual i)
  intro i l
  have h_mulVec (A : Matrix n n O) (x : n → ↑O') (j : n) :
      l ((A.map (inclusion hO) *ᵥ x) j) = (A *ᵥ (l ∘ x)) j := by
    have h_linear (a : ↑O) (y : ↑O') : l (inclusion hO a * y) = a * l y := l.map_smul a y
    simp only [mulVec, dotProduct, Matrix.map_apply, map_sum, h_linear, Function.comp_apply]
  let lz : decompGroup Gal(Ω/E) (placeOver v.1) → n → ↑O :=
    (l.restrictScalars ℤ_[ℓ]).compLeft n ∘ z
  -- `ψ` is trivial on the decomposition group, so `l` is equivariant there and `l ∘ z` is a
  -- crystalline cocycle of `u`.
  have h_mem : lz ∈ crysCocyclesAt v u := by
    refine Period.crysCocycles.comp_mem hz _ fun g x ↦ funext fun j ↦ ?_
    have hψg : ψ g = 1 := hψ v v.2 g g.2
    have h_comp : (l.restrictScalars ℤ_[ℓ]).compLeft n x = l ∘ x := rfl
    simpa [twistRep, hψg, h_comp] using h_mulVec (u g) x j
  calc
    l (relEval O' (mapRel (inclusion hO).toRingHom f) z i) = relEval O f lz i := by
      rw [relEval_apply, relEval_apply, mapRel, sum_mapRange_index (by simp), sum, sum,
        Finset.sum_apply, Finset.sum_apply, map_sum]
      exact sum_congr rfl fun g _ ↦ h_mulVec (f g) (z g) i
    _ = 0 := congrFun (hf lz h_mem) i

/-- Let `S₀` be a finite set of places of `E` containing those above `ℓ`, and let `Q` be auxiliary
for `S₀`: its places have prime norm, and `Q`, its conjugate `Q̄` and `S₀` are pairwise disjoint.
Let `ψ` satisfy `IsSmallTwist T Y ε Q ψ`, the list of conclusions of `exists_anticyclotomic_twist`
for Galois lattices with local conditions `T i` and families `Y k` of group ring elements, both
attached to `S₀` and `g₀ ∈ Gal(Ω/E)`. Only two clauses are used, which involve neither `T` nor `Y`:
`ψ` comes by `x ↦ x / x̄` from an idele class character of modulus `Q` trivial above `ℓ`, and the
valuations of `ψ γ_w - 1` for tame inertia generators `γ_w`, `w ∈ Q ∪ Q̄`, have sum at most `ε`.
Then `IsAuxTwist S₀ Q ψ ε` holds: `Q` is auxiliary for `S₀` and prime to `ℓ`, `ψ` has the form
above, and the sum of these valuations over `w ∈ Q` is at most `ε`. -/
lemma IsSmallTwist.isAuxTwist {S₀ Q : Finset (FinPlace E)} {g₀ : Gal(Ω/E)} {ι κ : Type}
    {r : ι → Type} [∀ i : ι, Fintype (r i)] [∀ i : ι, DecidableEq (r i)]
    {T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O (r i)} {Y : κ → StickelbergerSystem ℓ S₀ g₀} {ε : ℝ≥0}
    {ψ : Gal(Ω/E) →* PadicAlgCl ℓ} (hψ : IsSmallTwist T Y ε Q ψ) (hS₀ : placesDividing E ℓ ⊆ S₀)
    (hQ : IsAuxiliary S₀ Q) :
    IsAuxTwist S₀ Q ψ ε := by
  classical
  let γ (w : FinPlace E) : Gal(Ω/E) := w.isPlaceOver_placeOver.tameGenerator
  refine ⟨hQ, hψ.isFromU1, fun v ↦ γ v, fun v ↦ ?_, ?_⟩
  · have hvℓ : v.1 ∉ placesDividing E ℓ := fun hv ↦ by
      obtain ⟨hvS, -⟩ := hQ v v.2
      exact hvS (hS₀ hv)
    exact ⟨hvℓ, map_one _, placeOver v.1, v.1.isPlaceOver_placeOver, rfl⟩
  · calc
      ∑ v : Q, ellVal (ψ (γ v) - 1) = ∑ w ∈ Q, ellVal (ψ (γ w) - 1) :=
        Q.sum_coe_sort fun w ↦ ellVal (ψ (γ w) - 1)
      _ ≤ ∑ w ∈ Q ∪ Q.image star, ellVal (ψ (γ w) - 1) := sum_le_sum_of_subset subset_union_left
      _ ≤ ε := hψ.sum_ellVal_tameGenerator_sub_one_le (fun w ↦ placeOver w)
        FinPlace.isPlaceOver_placeOver

end General

/-- Let `T` be a Selmer datum over `O₀`: a Galois lattice `T.ρ` unramified outside the finite set
`T.places ⊆ S₀`, with modules of local cocycles at the places above `ℓ` and an inertial element
`T.γ` that acts by a scalar. Let `O` be a discrete valuation ring, `e : O₀ → O` a ring map, `ρ` the
twist by the `O`-valued character `ψ` of `T.ρ` extended along `e`, and `S = T.places ∪ Q ∪ Q̄`. The
group `Sel_Q(T ψ)`, of length `T.divisibleLength Q e ψ`, consists of the cocycles for `ρ` unramified
outside `S` that obey the images under `e` of the relations `T.classRelations`. If the set of linear
relations `L` contains these images, then the module of cocycles for `ρ` unramified outside `S` that
obey `L` is at most as long as `Sel_Q(T ψ)`, both with coefficients in `Frac(O) / O`. -/
lemma divisibleSelmerLength_le_divisibleLength {ℓ : ℕ} [ThePrime ℓ] {E O n : Type} [Field E]
    [CMFieldWithRoot5040 E] [CommRing O] [DVR O] [Fintype n] [DecidableEq n]
    {ρ : Gal(Ω/E) → Matrix n n O} {S : Set (FinPlace E)} {L : Set (Gal(Ω/E) →₀ Matrix n n O)}
    {O₀ : Type} [CommRing O₀] [PadicIntegerRing O₀ ℓ]
    {S₀ : Finset (FinPlace E)} {g₀ : Gal(Ω/E)} (T : SelmerDatum ℓ S₀ g₀ O₀ n)
    {Q : Finset (FinPlace E)} {e : O₀ →+* O} {ψ : Gal(Ω/E) →* O}
    (hρ : ρ = twistRep e ψ T.ρ) (hS : S = unionWithConj T.places Q)
    (hL : mapRel e '' T.classRelations ⊆ L) :
    divisibleSelmerLength ρ S L ≤ T.divisibleLength Q e ψ := by
  subst hρ hS
  -- Both modules have the same set of places, so there is no ramification condition to check.
  exact length_mono fun z hz ↦ mem_selmerModule_of_eq_zero_on_inertiaAbove hz hL (by simp)

/-- Let `T` be a Selmer datum for `S₀`: a Galois lattice unramified outside `S₀` with local
conditions above `ℓ` and an element `T.γ`, inertial at a place of `S₀`, that acts by a scalar. Let
`Q` be auxiliary for `S₀`, so that neither `Q` nor `Q̄` meets `S₀`. A character `ψ` that comes by
`x ↦ x / x̄` from an idele class character of modulus `Q` trivial above `ℓ` is trivial at `T.γ`. -/
lemma SelmerDatum.apply_γ_eq_one {ℓ : ℕ} [ThePrime ℓ] {E O n : Type} [Field E]
    [CMFieldWithRoot5040 E] [CommRing O] [PadicIntegerRing O ℓ] [Fintype n] [DecidableEq n]
    {S₀ Q : Finset (FinPlace E)} {g₀ : Gal(Ω/E)} (T : SelmerDatum ℓ S₀ g₀ O n)
    {ψ : Gal(Ω/E) →* PadicAlgCl ℓ} (hQ : IsAuxiliary S₀ Q)
    (hψ : IsFromU1 (placesDividing E ℓ) Q ψ) : ψ T.γ = 1 := by
  obtain ⟨v, ⟨hvS, -⟩, hγ⟩ := T.γ_mem_inertiaAbove
  have hv : v ∈ S₀ := T.subset hvS
  have hvQ : v ∉ Q := fun hQv ↦ by
    obtain ⟨hv_notMem, -⟩ := hQ v hQv
    exact hv_notMem hv
  have hv'Q : star v ∉ Q := fun hQv' ↦ by
    obtain ⟨-, -, -, hv_notMem⟩ := hQ (star v) hQv'
    exact hv_notMem (by rwa [star_star])
  exact hψ.eq_one_of_mem_inertiaAbove T.γ ⟨v, by simp [Set.conjClosure, hvQ, hv'Q], hγ⟩

/-- Let `D` be admissible data, with CM field `D.E`, primes `p₀, p₁` and level `D.N`;
`badPlaces D ℓ` is the set of places dividing `ℓ p₀ p₁ D.N`. Let `R` be an `ℓ`-adic representation
of the Galois group of `D.E`, and `T` a Selmer datum over `O` whose representation `T.ρ` is
conjugate to `R` over `ℚ̄_ℓ`, whose places are those above `ℓ p₀ p₁` and whose local conditions are
the crystalline ones; the inertial element `T.γ` acts by the scalar `T.ζ`. Let the places of `Q`
have prime norm, with `Q`, `Q̄` and the bad places pairwise disjoint, and let `ψ` come by
`x ↦ x / x̄` from an idele class character of modulus `Q` trivial above `ℓ`. Suppose that for all
large coefficient rings `O' ⊇ O` the character `ψ` has values in `O'` and `Sel_Q(T ψ)` has length at
most `b`, where `O' / ℓ` has length `1`. Then for all large `O'` there is a lattice in `ψ R` on
which `T.γ` acts by `T.ζ` and whose crystalline Selmer group for `Q` and `T.γ` has length at most
`b`. -/
lemma SelmerDatum.TwistedLengthLe.hasDivisibleSelmerLengthLe {ℓ : ℕ} [ThePrime ℓ] {P : Parameters}
    {D : Data P} {n : Type} [Fintype n] [DecidableEq n]
    {O : CoeffRing ℓ} {g₀ : AbsGal D} {T : SelmerDatum ℓ (badPlaces D ℓ) g₀ O n}
    {Q : Finset (FinPlace D.E)} {ψ : AbsGal D →* PadicAlgCl ℓ} {b : ℝ≥0∞}
    (hT_length : T.TwistedLengthLe Q ψ b) {R : GalRep ℓ D.E n} (h_lattice : IsLatticeIn R T.ρ)
    (hT_places : (T.places : Set (FinPlace D.E)) = placesDividing D.E ℓ ∪ placesAboveM D)
    (hT_crys : T.localRelations = crysRelations T.ρ) (hQ : IsAuxiliary (badPlaces D ℓ) Q)
    (hψ : IsFromU1 (placesDividing D.E ℓ) Q ψ) :
    HasDivisibleSelmerLengthLe ψ R Q T.γ (O.toIntQpBar T.ζ) b := by
  refine Eventually.mono hT_length fun O' ⟨hO, ψ', hψ', h_le⟩ ↦ ?_
  let e : O →+* O' := (inclusion hO).toRingHom
  have hψ'γ : ψ' T.γ = 1 := Subtype.ext ((hψ' T.γ).trans (T.apply_γ_eq_one hQ hψ))
  obtain ⟨v, ⟨-, hvℓ⟩, hγ⟩ := T.γ_mem_inertiaAbove
  have hψ'ℓ : ∀ w ∈ placesDividing D.E ℓ, ∀ g ∈ decompGroup (AbsGal D) (placeOver w), ψ' g = 1 :=
    fun w hw g hg ↦
      Subtype.ext ((hψ' g).trans (hψ.eq_one_of_mem_decompGroup hw w.isPlaceOver_placeOver hg))
  have h_places : placesDividing D.E ℓ ∪ placesAboveM D ∪ Set.conjClosure Q =
      (unionWithConj T.places Q : Set (FinPlace D.E)) := by
    simp [unionWithConj, hT_places, Set.conjClosure]
  let u : AbsGal D →* Matrix n n O' := e.mapMatrix.toMonoidHom.comp T.ρ
  have h_rel : mapRel e '' T.classRelations ⊆
      crysRelations (twistRep (.id O') ψ' u) ∪ {Finsupp.single T.γ 1} := by
    rintro _ ⟨f, hf | rfl, rfl⟩
    · exact .inl (mapRel_crysRelations_subset hO T.ρ hψ'ℓ ⟨f, hT_crys.subset hf, rfl⟩)
    · simp [mapRel]
  have h_scalar : twistRep (.id O') ψ' u T.γ = e T.ζ • 1 := by
    have hργ : T.ρ T.γ = T.ζ • 1 := T.ρ_eq_smul_one true
    have huγ : u T.γ = e T.ζ • 1 := by
      change (T.ρ T.γ).map e = e T.ζ • 1
      rw [hργ, map_smul' e T.ζ 1 (map_mul e), Matrix.map_one e (map_zero e) (map_one e)]
    simp [twistRep, huγ, hψ'γ]
  have h_twisted : IsTwistedLattice ψ R T.γ (O.toIntQpBar T.ζ) u ψ' (e T.ζ) :=
    { scalar_eq := rfl
      isLatticeIn := h_lattice
      twist_eq := hψ'
      apply_eq_smul := h_scalar
      isUnit_sub_one := by simpa using T.isUnit_ζ_sub_one.map e
      mem_inertiaAbove := ⟨v, hvℓ, hγ⟩ }
  have h_length :
      crystallineSelmerLength (twistRep (.id O') ψ' u) Q T.γ ≤ T.divisibleLength Q e ψ' :=
    divisibleSelmerLength_le_divisibleLength T rfl h_places h_rel
  exact ⟨u, ψ', e T.ζ, h_twisted, (normLength_mono h_length).trans h_le⟩

/-- For each of the two primes `p_i = D.levelPrime i` of the admissible data `D`, the number
`4 v(p_i - 1) + 2 ^ (-ℓ)` is at most
`twistError ℓ D = (4 D.f + 3) D.r v(D.chosenGroupOrder) + 2 ^ (-ℓ)`, where `v` is the `ℓ`-adic
valuation with `v(ℓ) = 1`. -/
lemma four_mul_ellVal_levelPrime_sub_one_add_le_twistError {ℓ : ℕ} [ThePrime ℓ] {P : Parameters}
    {D : Data P} (i : Fin 2) :
    4 * ellVal (D.levelPrime i - 1 : PadicAlgCl ℓ) + ((1 / 2) ^ ℓ : ℝ≥0) ≤ twistError ℓ D := by
  let v : ℕ := padicValNat ℓ D.chosenGroupOrder
  have h_val : ellVal (D.levelPrime i - 1 : PadicAlgCl ℓ) ≤ v := by
    simpa using ellVal_levelPrime_pow_sub_one_le D ℓ i ⟨le_rfl, D.nat_le_of_hasLogBound⟩
  have h_four : 4 * v ≤ (4 * D.f + 3) * D.r * v :=
    Nat.mul_le_mul_right v D.nat_le_of_hasLogBound
  calc
    _ ≤ 4 * v + (((1 / 2) ^ ℓ : ℝ≥0) : ℝ≥0∞) := by gcongr
    _ ≤ ((4 * D.f + 3) * D.r * v : ℕ) + (((1 / 2) ^ ℓ : ℝ≥0) : ℝ≥0∞) := by
      gcongr
      exact_mod_cast h_four
    _ = twistError ℓ D := by simp [twistError, v]

/-- For a tame character `τ` and `j : ℕ`, `(τ.pow j).invAvatar`, the `ℓ`-adic Galois character
attached to the inverse of `τ ^ j`, is the `j`-th power of `τ.invAvatar`. -/
lemma invAvatar_pow {ℓ : ℕ} [ThePrime ℓ] {P : Parameters} {D : Data P} [PadicIso ℓ]
    (τ : D.TameChar) (j : ℕ) :
    (τ.pow j).invAvatar = (τ.invAvatar : AbsGal D →* PadicAlgCl ℓ) ^ j := by
  ext g
  -- Both sides are computed on Artin symbols, which exhaust the abelianised Galois group.
  obtain ⟨x, hx⟩ := artinMap_surjective (AbsGal D) g
  simp [Data.TameChar.pow, invAvatar_eq_of_artinMap_eq hx]

/-- Let `τ` be a character of `U(1)(𝔸)` of weight `0` for the CM field `D.E` whose tame part, a
character `τ.tamePart w` of the residue field at each finite place `w`, is supported on `τ.Q`. Let
`τ.invAvatar` be the `ℓ`-adic Galois character that class field theory and the fixed isomorphism
`ℂ ≃ ℚ̄_ℓ` attach to the base change of `τ⁻¹` to `D.E`. If it is non-trivial at an element `g` of an
inertia group above a place `w` of `τ.Q`, then the tame part of `τ` at `w` is non-trivial. -/
lemma tamePart_ne_one_of_invAvatar_ne_one {ℓ : ℕ} [ThePrime ℓ] {P : Parameters} {D : Data P}
    [PadicIso ℓ] (τ : D.TameChar) {w : FinPlace D.E}
    (hw : w ∈ τ.Q) {g : AbsGal D} (hg : g ∈ inertiaAbove ({w} : Set (FinPlace D.E)))
    (h_ne : (τ.invAvatar : AbsGal D →* PadicAlgCl ℓ) g ≠ 1) : τ.tamePart w ≠ 1 := by
  intro h_triv
  obtain ⟨w', hw', A, hA, hgA⟩ := hg
  obtain rfl : w' = w := hw'
  -- The class of the inertial element `g` is the local Artin symbol of a unit `x` at `w'`.
  obtain ⟨x, hx_unit, h_art⟩ : ∃ x : (LocField w')ˣ,
      Valued.v x.val = 1 ∧ artinMap (AbsGal D) (locIdele w' x) = g := by
    obtain ⟨x, hx_unit, hx_art⟩ := hA.exists_localArtin_eq_of_mem_inertiaGroup hgA
    exact ⟨x, hx_unit, by simp [hA.artinAt_eq_of_localArtin_eq hx_art]⟩
  have h_unr : CharUnramifiedAt τ.toAutChar.baseChange.finPart w' :=
    τ.hasWeight.charUnramifiedAt h_triv (τ.tamePart_eq_one (star w') (τ.star_notMem w' hw))
  apply h_ne
  simp [invAvatar_eq_of_artinMap_eq h_art, h_unr x hx_unit]

open IsDiscreteValuationRing in
/-- Let `D` be admissible data, with CM field `D.E` and primes `p₀, p₁`, and let `badPlaces D ℓ` be
the places dividing `ℓ p₀ p₁ D.N`. Fix an isomorphism `ℂ ≃ ℚ̄_ℓ` and finitely many `ℓ`-adic
representations `R i` of the Galois group of `D.E` that satisfy `IsMainSummandLike`. Let `w` be a
chosen place, that is, one dividing the factor `D.piM` of `p₀ p₁`, prime to `ℓ`. Let
`c = (4 f + 3) · D.r · v(D.chosenGroupOrder)`, where `f = D.f` is the number of infinite places of
`D.E`, `v` is the `ℓ`-adic valuation and `D.chosenGroupOrder` is the product of the orders of
`GL (D.r * D.t)` over the residue fields of the chosen places. Over some coefficient ring `O` every
`R i` has a lattice that carries a Selmer datum `T i` for the bad places and a generator `g₀` of
tame inertia at `w`. It is unramified outside `ℓ p₀ p₁` and its local conditions are the crystalline
ones. Its error term `(T i).β`, a sum of a global term and of local terms among which is the
valuation of `det((T i).ρ g₀ - 1)`, is at most `c` when `O / ℓ` is given length `1`. Finally
`IsTorsionLevel T (c + 2)` holds: `c + 2` exceeds each such `β` by more than `1`, and the residue
field of `O` has more than `2 rank(T i) len(O / ℓ ^ (c + 2)) + 1` elements. -/
lemma exists_selmerData_isTorsionLevel {ℓ : ℕ} [ThePrime ℓ] {P : Parameters} {D : Data P}
    [PadicIso ℓ] {I : Type} [Finite I] {r : I → Type}
    [∀ i : I, Fintype (r i)] [∀ i : I, DecidableEq (r i)] {R : ∀ i : I, GalRep ℓ D.E (r i)}
    (hR : ∀ i : I, ∃ (t : ℕ) (J : (D.E →+* ℂ) → Multiset ℤ), IsMainSummandLike D t J (R i))
    {w : FinPlace D.E} (hw : D.IsChosen w) (hwℓ : w ∈ placesAboveM D \ placesDividing D.E ℓ)
    {c : ℕ} (hc : c = (4 * D.f + 3) * D.r * padicValNat ℓ D.chosenGroupOrder) :
    ∃ (O : CoeffRing ℓ) (T : ∀ i : I,
        SelmerDatum ℓ (badPlaces D ℓ) w.isPlaceOver_placeOver.tameGenerator O (r i)),
      (∀ i : I, IsLatticeIn (R i) (T i).ρ) ∧
      (∀ i : I, ((T i).places : Set (FinPlace D.E)) = placesDividing D.E ℓ ∪ placesAboveM D) ∧
      (∀ i : I, (T i).localRelations = crysRelations (T i).ρ) ∧
      (∀ i : I, O.normLength (T i).β ≤ c) ∧
      IsTorsionLevel T (c + 2) := by
  choose t J h_main using hR
  have h_rank (i : I) : Fintype.card (r i) ≤ D.r := (h_main i).rank_mem.2
  -- All large rings carry the data, and arbitrarily large ones have a large residue field.
  have h_large : ∀ᶠ O : CoeffRing ℓ in atTop, ∀ i : I,
      ∃ T : SelmerDatum ℓ (badPlaces D ℓ) w.isPlaceOver_placeOver.tameGenerator O (r i),
        IsLatticeIn (R i) T.ρ ∧
        ↑T.places = placesDividing D.E ℓ ∪ placesAboveM D ∧
        T.localRelations = crysRelations T.ρ ∧
        O.normLength T.β ≤
          (4 * D.f + 3) * Fintype.card (r i) * padicValNat ℓ D.chosenGroupOrder :=
    eventually_all.2 fun i ↦ (h_main i).eventually_exists_selmerDatum hw hwℓ
  obtain ⟨O, h_card, h_data⟩ :=
    ((frequently_lt_card_residueField ℓ (2 * D.r * (c + 2))).and_eventually h_large).exists
  choose T h_lattice h_places h_crys hβ using h_data
  have hβ_le (i : I) : O.normLength (T i).β ≤ c := by
    grw [hβ i, h_rank i]
    simp [hc]
  have hβ_lt (i : I) : O.normLength (T i).β + 1 < (c + 2 : ℕ) := by
    grw [hβ_le i]
    exact_mod_cast (c + 1).lt_succ_self
  have h_room (i : I) : 2 * Fintype.card (r i) * addVal O (ℓ ^ (c + 2)) + 1 ≤
      (2 * D.r * (c + 2) : ℕ) * addVal O ℓ + 1 := by
    rw [addVal_pow, nsmul_eq_mul, ← mul_assoc]
    gcongr
    exact_mod_cast Nat.mul_le_mul_right (c + 2) (Nat.mul_le_mul_left 2 (h_rank i))
  exact ⟨O, T, h_lattice, h_places, h_crys, hβ_le, hβ_lt, fun i ↦ (h_room i).trans_lt h_card⟩

end Lemmas

/-- The twisting theorem. Let `D` be admissible data for the parameters `P` (a modulus and the field
`K = ℚ(√-d)`), with CM field `D.E`, primes `p₀, p₁` and level `D.N`. The bad places are those
dividing `ℓ p₀ p₁ D.N`; the chosen places are those dividing the factor `D.piM` of `p₀ p₁` from `K`.
Fix an isomorphism `ιℓ : ℂ ≃ ℚ̄_ℓ` (the datum `ι`) and finitely many `ℓ`-adic representations `R i`
of the Galois group of `D.E` that satisfy `IsMainSummandLike D t J` for some `t` and `J`:
`R^c ≅ R^∨(1 - t)`, `J` gives the jumps at the complex embeddings, the image is large and inertia
above `p₀ p₁` is controlled. Let
`e'_ℓ = twistError ℓ D = (4 D.f + 3) D.r v(D.chosenGroupOrder) + 2 ^ (-ℓ)`, with `v` the `ℓ`-adic
valuation. Then there is a character `τ` of `U(1)(𝔸)` of weight `0`, tamely ramified on a finite set
`Q` of places, such that each power `ξ = τ ^ j` with `1 ≤ j ≤ D.m` is ramified at every place of
`Q = ξ.Q` (`D.MFoldTwist`) and satisfies:
* the `ℓ`-adic Galois character `ψ = ξ.invAvatar` attached to `ξ⁻¹` is anticyclotomic and trivial
  above `ℓ`; the places of `Q` have prime norm, and `Q`, `Q̄` and the bad places are pairwise
  disjoint; `∑ v(ψ γ_w - 1) ≤ e'_ℓ` for some tame inertia generators `γ_w`, `w ∈ Q`;
* for each `i` there are an inertial element `γ` away from `ℓ` and a scalar `ζ`, with `ζ - 1` a
  unit, such that over all large coefficient rings `O` the element `γ` acts by `ζ` on a lattice in
  `ψ R i`, and the module of cocycles with coefficients in `Frac(O) / O` that are unramified outside
  `ℓ p₀ p₁`, `Q`, `Q̄`, crystalline above `ℓ` and zero at `γ` has length at most `e'_ℓ` (`O / ℓ` has
  length `1`);
* for each pair `p = (ν, z)` of a character `ν` of `U(1)(𝔸)` of weight `-c` and an integer
  `1 ≤ z ≤ D.t` with `z ≤ c ≤ 4 D.b`, the tame part of `ν` being non-trivial exactly at the chosen
  places, and each sign `s = ±1`, the image under `ιℓ` of `|L(z, (ν ξ^s)⁻¹)| / |L(z, ν⁻¹)|` has
  valuation at most `e'_ℓ`. The Euler factors at the chosen places, in the numerator also at `Q`,
  and at their conjugates are omitted. -/
theorem exists_mFoldTwist_hasDivisibleSelmerLengthLe {P : Parameters} (D : Data P) (ℓ : ℕ)
    [ThePrime ℓ] (ι : PadicIso ℓ) {I : Type} [Finite I] {r : I → Type} [∀ i : I, Fintype (r i)]
    [∀ i : I, DecidableEq (r i)] {R : ∀ i : I, GalRep ℓ D.E (r i)}
    (hR : ∀ i : I, ∃ (t : ℕ) (J : (D.E →+* ℂ) → Multiset ℤ), IsMainSummandLike D t J (R i)) :
    ∃ τ : D.MFoldTwist, ∀ j : D.LiftIndex,
      let ξ : D.Twist := τ.powTwist j
      -- The ramification is auxiliary and small.
      IsAuxTwist (badPlaces D ℓ) ξ.Q ξ.invAvatar (twistError ℓ D) ∧
      -- The Selmer groups of the twisted representations are short.
      (∀ i : I, ∃ (γ : AbsGal D) (ζ : intQpBar ℓ),
        HasDivisibleSelmerLengthLe ξ.invAvatar (R i) ξ.Q γ ζ (twistError ℓ D)) ∧
      -- The ratios of `L`-values have small valuation.
      ∀ (p : D.CriticalPair) (s : ℤˣ), p.IsRamified →
        ellVal (ιℓ (p.ratio ξ s)) ≤ twistError ℓ D := by
  -- Apply the general theorem for the bad places and the tame generator at a chosen place `w₀`
  -- that is prime to `ℓ`, with `ε = 2 ^ (-ℓ)`.
  obtain ⟨w₀, i₀, hw₀, hw₀ℓ, hq⟩ : ∃ (w₀ : FinPlace D.E) (i₀ : Fin 2), D.IsChosen w₀ ∧
      w₀ ∈ placesAboveM D \ placesDividing D.E ℓ ∧ w₀.q = D.levelPrime i₀ :=
    exists_chosen_notMem_placesDividing D ℓ
  obtain ⟨hw₀_above, hw₀_notMem⟩ := hw₀ℓ
  have hS₀ : placesDividing D.E ℓ ⊆ badPlaces D ℓ :=
    Set.subset_union_left.trans (placesDividing_union_subset_badPlaces D ℓ)
  let g₀ : AbsGal D := w₀.isPlaceOver_placeOver.tameGenerator
  have hg₀ : g₀ ∈ inertiaAbove (badPlaces D ℓ \ placesDividing D.E ℓ) :=
    ⟨w₀, ⟨placesDividing_union_subset_badPlaces D ℓ (.inr hw₀_above), hw₀_notMem⟩,
      placeOver w₀, w₀.isPlaceOver_placeOver, Subtype.property _⟩
  have hm : 1 ≤ D.m := D.nat_le_of_hasLogBound
  have h_one : 1 ∈ D.LiftIndex := ⟨le_rfl, hm⟩
  let c : ℕ := (4 * D.f + 3) * D.r * padicValNat ℓ D.chosenGroupOrder
  let ε : ℝ≥0 := (1 / 2) ^ ℓ
  have h_error : (twistError ℓ D : ℝ≥0∞) = c + ε := by simp [twistError, c, ε]
  obtain ⟨O, T, h_lattice, h_places, h_crys, hβ_le, h_level⟩ :
      ∃ (O : CoeffRing ℓ) (T : ∀ i : I, SelmerDatum ℓ (badPlaces D ℓ) g₀ O (r i)),
        (∀ i : I, IsLatticeIn (R i) (T i).ρ) ∧
        (∀ i : I, ((T i).places : Set (FinPlace D.E)) = placesDividing D.E ℓ ∪ placesAboveM D) ∧
        (∀ i : I, (T i).localRelations = crysRelations (T i).ρ) ∧
        (∀ i : I, O.normLength (T i).β ≤ c) ∧
        IsTorsionLevel T (c + 2) :=
    exists_selmerData_isTorsionLevel hR hw₀ ⟨hw₀_above, hw₀_notMem⟩ rfl
  have h_systems (k : {p : D.CriticalPair // p.IsRamified} × ℤˣ) :
      ∃ Y : StickelbergerSystem ℓ (badPlaces D ℓ) g₀, ∀ ξ : D.Twist,
        IsAuxiliary (badPlaces D ℓ) ξ.Q → IsFromU1 (placesDividing D.E ℓ) ξ.Q ξ.invAvatar →
        ∀ b : ℝ≥0∞, ellVal (groupRingEval ξ.invAvatar (Y.element ξ.Q)) ≤ Y.β + b →
          ellVal (ιℓ ((k.1 : D.CriticalPair).ratio ξ k.2)) ≤
            4 * ellVal (w₀.q - 1 : PadicAlgCl ℓ) + b :=
    exists_stickelbergerSystem_ellVal_ratio_le hw₀ hw₀_notMem k.1.property k.2
  choose Y hY using h_systems
  obtain ⟨Q, ψ, hQ, hψ⟩ : ∃ (Q : Finset (FinPlace D.E)) (ψ : AbsGal D →* PadicAlgCl ℓ),
      IsAuxiliary (badPlaces D ℓ) Q ∧ ∀ j ∈ D.LiftIndex, IsSmallTwist T Y ε Q (ψ ^ j) :=
    exists_anticyclotomic_twist T Y hS₀ hg₀ h_level hm (by positivity)
  -- `ψ` is the avatar of the inverse of a tame character `τ`, an `m`-fold twist because
  -- `ψ, …, ψ ^ m` ramify at all primes of `Q`.
  have hψ_U1 : IsFromU1 (placesDividing D.E ℓ) Q ψ := by simpa using (hψ 1 h_one).isFromU1
  obtain ⟨τ, rfl, rfl⟩ : ∃ τ : D.TameChar, τ.Q = Q ∧ ψ = τ.invAvatar :=
    exists_tameChar_invAvatar_eq hQ hψ_U1
  have h_pow : ∀ j ∈ D.LiftIndex, IsSmallTwist T Y ε τ.Q (τ.pow j).invAvatar := by
    simpa only [invAvatar_pow] using hψ
  have h_ram : ∀ j ∈ D.LiftIndex, ∀ w ∈ τ.Q, τ.tamePart w ^ j ≠ 1 := by
    intro j hj w hw
    obtain ⟨g, hg, h_ne⟩ := (h_pow j hj).ramified w hw
    exact tamePart_ne_one_of_invAvatar_ne_one (τ.pow j) hw hg h_ne
  let τ' : D.MFoldTwist :=
    { toTameChar := τ, tamePart_ne_one := by simpa using h_ram 1 h_one, pow_ne_one := h_ram }
  refine ⟨τ', fun ⟨j, hj⟩ ↦ ?_⟩
  have h_small : IsSmallTwist T Y ε τ.Q (τ.pow j).invAvatar := h_pow j hj
  refine ⟨?_, fun i ↦ ?_, fun p s hp ↦ ?_⟩
  · have hε : ε ≤ twistError ℓ D := le_add_self
    exact (h_small.mono T Y hε).isAuxTwist hS₀ hQ
  · have h_length : (T i).TwistedLengthLe τ.Q (τ.pow j).invAvatar (twistError ℓ D) := by
      refine (h_small.length_le i).mono ?_
      grw [h_error, hβ_le i]
    exact ⟨(T i).γ, O.toIntQpBar (T i).ζ, h_length.hasDivisibleSelmerLengthLe (h_lattice i)
      (h_places i) (h_crys i) hQ h_small.isFromU1⟩
  · calc
      ellVal (ιℓ (p.ratio (τ.pow j) s)) ≤ 4 * ellVal (w₀.q - 1 : PadicAlgCl ℓ) + ε :=
        hY (⟨p, hp⟩, s) (τ'.powTwist ⟨j, hj⟩) hQ h_small.isFromU1 ε
          (h_small.ellVal_value_le (⟨p, hp⟩, s))
      _ ≤ twistError ℓ D := by
        rw [hq]
        exact four_mul_ellVal_levelPrime_sub_one_add_le_twistError i₀

end New.Selmer
