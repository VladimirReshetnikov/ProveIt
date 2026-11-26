import New.Congruences.GaloisRepresentations.AttachedRepresentations
import New.Congruences.LocalLoss.LocalLattices
import New.Congruences.Selmer.SelmerData

/-!
# Main summands are Selmer data

A row is an `ℓ`-adic representation `R` that satisfies `IsMainSummandLike`. A main summand is a
lattice `u` in a row `R`, with the crystalline conditions above `ℓ`; the row is the main summand
with scalars extended to `ℚ̄_ℓ`.

* `New.Selmer.IsMainSummandLike.eventually_exists_selmerDatum`: over all large coefficient rings a
  row has a lattice that is a Selmer datum, with bounds for the global and the local terms.

Notions from other files:
* `New.Selmer.IsMainSummandLike`: the hypotheses on an `ℓ`-adic representation of the Galois group
  of `D.E` under which its Selmer groups are estimated.
* `New.Selmer.IsLatticeIn`: `u` over the coefficient ring `O` is conjugate to `R` over `ℚ̄_ℓ`.
* `New.Selmer.SelmerDatum`: a lattice `T` with local conditions and the number `β_T`.
* `New.Selmer.crysCocyclesAt`, `New.Selmer.crysRelations`: the crystalline cocycles at a place above
  `ℓ`, and the linear relations that hold on them.
* `New.CoeffRing.normLength`: a length over `O`, rescaled so that `O / ℓ` has length `1`.

## Relation to the literature

See `New.Congruences.Selmer.TwistingTheorem` for related work.
-/

namespace New.Selmer

open NumberField Matrix Period Fintype IsDiscreteValuationRing LinearMap Finset DFunLike

/-- A nonzero element `a` of a coefficient ring `O` divides some power of `ℓ`. -/
lemma exists_dvd_ell_pow (ℓ : ℕ) [ThePrime ℓ] {O : CoeffRing ℓ} {a : ↑O} (ha : a ≠ 0) :
    ∃ M : ℕ, a ∣ ℓ ^ M := by
  have h_ell : ‖(ℓ : PadicAlgCl ℓ)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ‖(ℓ : PadicAlgCl ℓ)‖ ^ M < ‖(a : PadicAlgCl ℓ)‖ :=
    exists_pow_lt_of_lt_one (by simpa) h_ell
  exact ⟨M, (O.dvd_iff_norm_le _ _).2 (by simpa using hM.le)⟩

/-- A length `k` over `O` whose normalisation `O.normLength k` has a finite bound is finite. -/
lemma ne_top_of_normLength_le {ℓ : ℕ} [ThePrime ℓ] {O : CoeffRing ℓ} {k : ℕ∞} {b : ENNReal}
    (hk : O.normLength k ≤ b) (hb : b ≠ ⊤) : k ≠ ⊤ := by
  rintro rfl
  exact hb (top_le_iff.1 hk)

variable {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {n : Type} [Fintype n]
  [DecidableEq n] {t : ℕ} {J : (D.E →+* ℂ) → Multiset ℤ} {R : GalRep ℓ D.E n}
  {O : CoeffRing ℓ} {u : AbsGal D →* Matrix n n O}

lemma IsMainSummandLike.nonempty (hrow : IsMainSummandLike D t J R) : Nonempty n :=
  card_pos_iff.1 hrow.rank_mem.1

/-- Conjugate self-duality of a lattice `u` in a main summand `R`, on traces: `tr u
(g^c) = cyclotomicInv(g) ^ (t - 1) * tr u (g⁻¹)` (truncated `ℕ` subtraction), where
`g^c = conjGal g` is the conjugate of `g` by complex conjugation and `cyclotomicInv` is the inverse
of the cyclotomic character `cyc`. -/
lemma IsMainSummandLike.trace_lattice_conjGal (hrow : IsMainSummandLike D t J R)
    (hu : IsLatticeIn R u) (g : AbsGal D) :
    (u (conjGal g)).trace = cyclotomicInv ℓ D.E O g ^ (t - 1) * (u g⁻¹).trace := by
  have h_dual : (R (conjGal g)).val.trace =
      cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ (t - 1) * (R g⁻¹).val.trace := hrow.trace_conj g
  rw [← hu.trace_eq, ← hu.trace_eq] at h_dual
  simpa [Subtype.ext_iff, cyclotomicInv] using h_dual

/-- Let `u` be an `O`-lattice (`IsLatticeIn R u`) in a main summand `R`
(`IsMainSummandLike D t J R`, of which conjugate self-duality is used) whose image spans all
matrices. If `g` acts by the scalar `y`, then `(conjGal g)⁻¹ = (c g c)⁻¹`, with `c` the complex
conjugation, acts by the scalar `cyc(g) ^ (t - 1) * y`. Here `cyc` is the cyclotomic character and
`cyclotomicInv` is its inverse. -/
lemma IsMainSummandLike.conjGal_inv_eq_smul_one (hrow : IsMainSummandLike D t J R)
    (hu : IsLatticeIn R u)
    (h_span_top : Submodule.span O (Set.range u) = ⊤) {g : AbsGal D} {y : ↑O} (hy : u g = y • 1) :
    u (conjGal g)⁻¹ = (cyclotomicInv ℓ D.E O g⁻¹ ^ (t - 1) * y) • 1 := by
  -- The `u x` span all matrices, so it is enough to compare traces against them.
  set y' : ↑O := cyclotomicInv ℓ D.E O g⁻¹ ^ (t - 1) * y with hy'
  have h_trace (x : AbsGal D) :
      (u x * u (conjGal g)⁻¹).trace = (u x * y' • (1 : Matrix n n O)).trace := by
    -- Self-duality at `x^c g⁻¹` and at `x^c`: both traces are multiples of `tr u (x^c)⁻¹`.
    have h_dual_xg : (u x * u (conjGal g)⁻¹).trace =
        cyclotomicInv ℓ D.E O (conjGal x * g⁻¹) ^ (t - 1) * (y * (u (conjGal x)⁻¹).trace) := by
      simpa [hy] using hrow.trace_lattice_conjGal hu (conjGal x * g⁻¹)
    have h_dual_x : (u x).trace =
        cyclotomicInv ℓ D.E O (conjGal x) ^ (t - 1) * (u (conjGal x)⁻¹).trace := by
      simpa using hrow.trace_lattice_conjGal hu (conjGal x)
    rw [h_dual_xg, Matrix.mul_smul, mul_one, trace_smul, smul_eq_mul, h_dual_x, map_mul, hy']
    ring
  have h_forms : traceLinearMap n O O ∘ₗ mulRight O (u (conjGal g)⁻¹) =
      traceLinearMap n O O ∘ₗ mulRight O (y' • (1 : Matrix n n O)) :=
    ext_on_range h_span_top h_trace
  exact ext_iff_trace_mul_left.2 (LinearMap.ext_iff.1 h_forms)

/-- A scalar by which a Galois element acts through `u` is a unit. The hypothesis `hrow` is used
only to know that `n` is not empty. -/
lemma IsMainSummandLike.isUnit_of_eq_smul_one (hrow : IsMainSummandLike D t J R) {g : AbsGal D}
    {y : ↑O} (hy : u g = y • 1) : IsUnit y := by
  have h_pow : IsUnit (y ^ card n) := by simpa [hy] using isUnits_det_units (u.toHomUnits g)
  exact (isUnit_pow_iff (Nat.ne_of_gt hrow.rank_mem.1)).1 h_pow

/-- For a main summand `R`, the number of negative integers among the Hodge–Tate jumps `J σ`,
counted with multiplicity and summed over all complex embeddings `σ` of `D.E`, is at most the number
of infinite places of `D.E` times `card n`. -/
lemma IsMainSummandLike.sum_countP_neg_le (hrow : IsMainSummandLike D t J R) :
    ∑ σ : D.E →+* ℂ, (J σ).countP (· < 0) ≤ Core.numInfPlaces D.E * card n := by
  -- An embedding and its conjugate have at most `card n` negative jumps together.
  let neg (σ : D.E →+* ℂ) : ℕ := (J σ).countP (· < 0)
  have h_star : ∑ σ, neg (star σ) = ∑ σ, neg σ := star_involutive.bijective.sum_comp neg
  refine Nat.le_of_mul_le_mul_left ?_ two_pos
  calc 2 * ∑ σ, neg σ = ∑ σ, (neg σ + neg (star σ)) := by rw [sum_add_distrib, h_star, two_mul]
    _ ≤ ∑ _ : D.E →+* ℂ, card n := sum_mono hrow.card_neg_le
    _ = 2 * (Core.numInfPlaces D.E * card n) := by
      simp [Embeddings.card, finrank_eq_two_mul_card_infinitePlace, mul_assoc]

/-- The rank inequality for an `O`-lattice `u` (`IsLatticeIn R u`) in a main summand `R`. For a
place `v` above `ℓ` let `crysCocyclesAt v u` be the `O`-module of crystalline cocycles of the
decomposition group at `v` with values in `O ^ n`, acted on through `u`. The ranks of these modules
add up to at most `card n` times the sum of the numbers of places of `D.E` above `ℓ` and of infinite
places of `D.E`. -/
lemma IsMainSummandLike.sum_finrank_crysCocyclesAt_le (hrow : IsMainSummandLike D t J R)
    (hu : IsLatticeIn R u) :
    ∑ v : placesDividing D.E ℓ, Module.finrank O (crysCocyclesAt v u) ≤
      (card (placesDividing D.E ℓ) + Core.numInfPlaces D.E) * card n := by
  -- The rank at `v` is `card n` plus the number of negative jumps at the embeddings of `v`.
  classical
  have h_jumps (v : placesDividing D.E ℓ) (g : Gp ℓ) :
      HasJumps (localLattice u v).ρ (coefficientEmbedding O g) (J (complexEmbeddingAt v g)) :=
    hrow.toIsConjSelfDualOfLevel.hasJumps_localLattice hu v g
  have h_potCrys (v : placesDividing D.E ℓ) : IsPotentiallyCrystalline (localLattice u v).ρ :=
    (hrow.toIsConjSelfDualOfLevel.inClass_localLattice (𝓡 := IsMainSummandLike D t J) hrow hu
      v).isPotentiallyCrystalline
  let negJumps (v : placesDividing D.E ℓ) : ℕ :=
    ∑ σ with ∃ g : Gp ℓ, complexEmbeddingAt v g = σ, (J σ).countP (· < 0)
  have h_rank (v : placesDividing D.E ℓ) :
      Module.finrank O (crysCocyclesAt v u) = card n + negJumps v :=
    (finrank_crysCocycles_eq_add_neg_jumps (localChart ℓ D.E v).inducesPlace.2 (h_potCrys v)
      (h_jumps v)).trans (by simp [negJumps])
  -- Each embedding is counted at one place at most.
  have h_sum : ∑ v, negJumps v ≤ Core.numInfPlaces D.E * card n :=
    (sum_complexEmbeddingOf_le _).trans hrow.sum_countP_neg_le
  calc _ = card (placesDividing D.E ℓ) * card n + ∑ v, negJumps v := by
        simp [h_rank, sum_add_distrib]
    _ ≤ (card (placesDividing D.E ℓ) + Core.numInfPlaces D.E) * card n := by grw [h_sum, add_mul]

/-- The global term. Let `u` be an `O`-lattice (`IsLatticeIn R u`) in a main summand `R` whose image
spans all matrices. Let some `g` act by a scalar `α` and have cyclotomic character `p_l ^ card n`,
where `p_l = D.levelPrime l` is one of the primes `p₀, p₁` of the data and `Ω = New.Ω` is the
algebraic closure of `ℚ`. The number `congruenceTerm ℓ u` is the supremum, over nonzero `a` in `O`,
of the lengths of the modules of equivariant maps from `W = (O / a) ^ n` to its conjugate dual: the
character module of `W`, on which `x` acts by `y ↦ cyc(x^c) · y ∘ (x^c)⁻¹`, with `cyc` the
cyclotomic character and `x^c = conjGal x`. Normalised so that `O / ℓ` has length `1`, it is at most
`card n` times the `ℓ`-adic valuation of `D.chosenGroupOrder`, the product of the orders of
`GL (D.r * D.t)` over the residue fields of the chosen places above `p₀` and `p₁`. -/
lemma IsMainSummandLike.normLength_congruenceTerm_le (hrow : IsMainSummandLike D t J R)
    (hu : IsLatticeIn R u)
    (h_span_top : Submodule.span O (Set.range u) = ⊤) {g : AbsGal D} {l : Fin 2} {α : ↑O}
    (h_cyc : (cyclotomicChar Ω ℓ g : ℤ_[ℓ]) = D.levelPrime l ^ card n) (hg : u g = α • 1) :
    O.normLength (congruenceTerm ℓ u) ≤ card n * padicValNat ℓ D.chosenGroupOrder := by
  -- The scalars `α` of `g` and `α'` of `g^{-c}` satisfy `α - cyc(g^c) α' = (1 - p_l ^ d) α` with
  -- `d = card n · t` (`d = card n` if `t = 0`); `α` is a unit and `1 ≤ d ≤ D.r * D.t`.
  have : Nonempty n := hrow.nonempty
  let δ : ↑O := α - cyclotomicCharIn O Ω ℓ (conjGal g) * (cyclotomicInv ℓ D.E O g⁻¹ ^ (t - 1) * α)
  let d : ℕ := card n * (t - 1 + 1)
  have hd : d ∈ Set.Icc 1 (D.r * D.t) :=
    ⟨mul_pos hrow.rank_mem.1 (t - 1).succ_pos,
      mul_le_mul' hrow.rank_mem.2 (by grind [D.t_odd.pos, hrow.t_le])⟩
  have hδ : δ.1 = (1 - D.levelPrime l ^ d) * α.1 := by
    simp [δ, d, cyclotomicInv, h_cyc, ← mul_assoc, pow_succ', ← one_sub_mul, pow_mul]
  have hα : ‖α.1‖ = 1 := (O.isUnit_iff_norm_eq_one α).1 (hrow.isUnit_of_eq_smul_one hg)
  have h_gap : ellVal δ.1 ≤ ellVal (D.levelPrime l ^ d - 1 : PadicAlgCl ℓ) :=
    ellVal_le_ellVal (by rw [hδ, norm_mul, hα, mul_one, norm_sub_rev])
  have h_term : congruenceTerm ℓ u ≤ card n * addVal O δ :=
    congruenceTerm_le h_span_top hg (hrow.conjGal_inv_eq_smul_one hu h_span_top hg)
  grw [h_term, O.normLength_natCast_mul, O.normLength_addVal, h_gap,
    ellVal_levelPrime_pow_sub_one_le D ℓ l hd]

omit [PadicIso ℓ] in
/-- For a lattice `u` in `R`, the valuation of `det (u g - 1)` in `O`, normalised by `v(ℓ) = 1`, is
the valuation `ellVal` of `det (R g - 1)` in `ℚ̄_ℓ`. -/
lemma IsLatticeIn.normLength_addVal_det_sub_one (hu : IsLatticeIn R u) (g : AbsGal D) :
    O.normLength (addVal O (u g - 1).det) = ellVal ((R g).1 - 1).det := by
  obtain ⟨Φ, -, hΦ_u, hΦ_det_trace⟩ := hu.exists_algHom
  rw [O.normLength_addVal, ← (hΦ_det_trace (u g - 1)).1, map_sub, map_one, hΦ_u]

/-- The local term. Let `u` be an `O`-lattice (`IsLatticeIn R u`) in a main summand `R` and `v` a
place above one of the primes `p₀, p₁` of the data and prime to `ℓ`. The number `localTerm u v` is
the supremum, over nonzero `a` in `O`, of the excess over the length of `W = (O / a) ^ n` of the
length of the module of restrictions to the decomposition group at `v` of the locally constant
global cocycles with values in `W`. Normalised so that `O / ℓ` has length `1`, it is at most
`card n` times the `ℓ`-adic valuation of `D.chosenGroupOrder`, the product of the orders of
`GL (D.r * D.t)` over the residue fields of the chosen places above `p₀` and `p₁`. -/
lemma IsMainSummandLike.normLength_localTerm_le (hrow : IsMainSummandLike D t J R)
    (hu : IsLatticeIn R u) {v : FinPlace D.E} (hv : v ∈ placesAboveM D \ placesDividing D.E ℓ) :
    O.normLength (localTerm u v) ≤ card n * padicValNat ℓ D.chosenGroupOrder := by
  -- The term is at most the valuation of `det (u γ - 1)` for the inertial `γ` of the row.
  obtain ⟨γ, m, -, hm_unit : (placeOver v).valuation m = 1,
      hm_pow : ∀ s ∈ inertiaGroup (AbsGal D) (placeOver v), R (s ^ m) = 1,
      h_det : ellVal ((R γ).1 - 1).det ≤ card n * padicValNat ℓ D.chosenGroupOrder, -⟩ :=
    hrow.inertia_above_M v hv v.isPlaceOver_placeOver
  have hℓ_unit : (placeOver v).valuation ℓ = 1 :=
    v.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2 hv.2
  have h_near : ∀ᶠ s in nhds 1, s ∈ inertiaGroup (AbsGal D) (placeOver v) → u s = 1 := by
    obtain ⟨⟨h_near_R, -⟩, -⟩ := hrow.local_conditions v (by simp) v.isPlaceOver_placeOver
    filter_upwards [h_near_R hℓ_unit] with s hRs hs using hu.eq_one (hRs hs)
  have h_term : localTerm u v ≤ addVal O (u γ - 1).det := by
    refine iSup₂_le fun a ha ↦ tsub_le_iff_left.2 ?_
    obtain ⟨M, hM⟩ := exists_dvd_ell_pow ℓ ha
    have h_val_one : (placeOver v).valuation (m * ℓ ^ M : ℕ) = 1 := by simp [hℓ_unit, hm_unit]
    grw [length_localCocycles_le (nsmul_quot_eq_zero hM) v.isPlaceOver_placeOver
      (fun s hs ↦ hu.eq_one (hm_pow s hs)) h_near γ h_val_one, length_ker_le_addVal_det]
  grw [h_term, hu.normLength_addVal_det_sub_one, h_det]

/-- The terms at the tame generator. Let `R` be a main summand and let `u` be a lattice in `R`. Let
`w` be a chosen place above `p₀ p₁` and prime to `ℓ`, and let `γ` be the tame generator at `w`. The
number `firstPrimeTerms ℓ u γ` is the sum of the valuations of `det (u g - 1)` for `g = γ` and
`g = (conjGal γ)⁻¹`. Its normalised length `O.normLength` is at most `2 · card n` times the `ℓ`-adic
valuation of `D.chosenGroupOrder`. -/
lemma IsMainSummandLike.normLength_firstPrimeTerms_le (hrow : IsMainSummandLike D t J R)
    (hu : IsLatticeIn R u) {w : FinPlace D.E} (hw_chosen : D.IsChosen w)
    (hw : w ∈ placesAboveM D \ placesDividing D.E ℓ) :
    O.normLength (firstPrimeTerms ℓ u w.isPlaceOver_placeOver.tameGenerator) ≤
      2 * (card n * padicValNat ℓ D.chosenGroupOrder) := by
  obtain ⟨γ, -, hγ : D.IsChosen w → γ = w.isPlaceOver_placeOver.tameGenerator, -, -,
    h_det, h_det_conj⟩ := hrow.inertia_above_M w hw w.isPlaceOver_placeOver
  rw [firstPrimeTerms, map_sum, ← hγ hw_chosen, Fintype.sum_bool, two_mul]
  simp only [hu.normLength_addVal_det_sub_one]
  exact add_le_add h_det h_det_conj

/-- The sum of the local terms. Let `u` be an `O`-lattice (`IsLatticeIn R u`) in a main summand `R`,
let `S` be the set of places above `ℓ p₀ p₁`, and let `w` be a chosen place above `p₀ p₁` and prime
to `ℓ`. Add the terms `localTerm u v` at the places `v` of `S` prime to `ℓ` and the valuations of
`det (u g - 1)` for `g` the generator `γ` of tame inertia at `w` and for `g = (conjGal γ)⁻¹`
(`firstPrimeTerms`). The normalised sum is at most `(4 f + 2) · card n` times the `ℓ`-adic valuation
of `D.chosenGroupOrder`, the product of the orders of `GL (D.r * D.t)` over the residue fields of
the chosen places above `p₀` and `p₁`; `f = D.f` is the number of infinite places. -/
lemma IsMainSummandLike.normLength_placeTerms_add_firstPrimeTerms_le
    (hrow : IsMainSummandLike D t J R) (hu : IsLatticeIn R u)
    {S : Finset (FinPlace D.E)} (hS : ↑S = placesDividing D.E ℓ ∪ placesAboveM D) {w : FinPlace D.E}
    (hw_chosen : D.IsChosen w) (hw : w ∈ placesAboveM D \ placesDividing D.E ℓ) :
    O.normLength (placeTerms ℓ u S +
        firstPrimeTerms ℓ u w.isPlaceOver_placeOver.tameGenerator) ≤
      (4 * D.f + 2) * card n * padicValNat ℓ D.chosenGroupOrder := by
  -- At most `4 f` places of `S` are prime to `ℓ`, and the tame generator gives two more terms.
  classical
  let b : ENNReal := card n * padicValNat ℓ D.chosenGroupOrder
  let S' : Finset (FinPlace D.E) := {v ∈ S | v ∉ placesDividing D.E ℓ}
  have h_mem (v : FinPlace D.E) (hv : v ∈ S') : v ∈ placesAboveM D \ placesDividing D.E ℓ := by
    obtain ⟨hvS, hvℓ⟩ := mem_filter.1 hv
    exact ⟨(hS.subset hvS).resolve_left hvℓ, hvℓ⟩
  have h_card : #S' ≤ 4 * D.f := card_le_of_subset_placesAboveM D fun v hv ↦ (h_mem v hv).1
  have h_places : O.normLength (placeTerms ℓ u S) ≤ #S' • b :=
    calc _ = ∑ v ∈ S', O.normLength (localTerm u v) := by rw [placeTerms, map_sum]
      _ ≤ _ := sum_le_card_nsmul S' _ b fun v hv ↦ hrow.normLength_localTerm_le hu (h_mem v hv)
  calc _ ≤ (4 * D.f) • b + 2 * b := by
        grw [map_add, h_places, h_card, hrow.normLength_firstPrimeTerms_le hu hw_chosen hw]
    _ = _ := by simp [b, add_mul, mul_assoc]

/-- For an `O`-lattice `u` (`IsLatticeIn R u`) in a main summand `R`, some element `γ` of an inertia
group (`inertiaAbove`) at a place above the primes `p₀ p₁` of the data `D` and prime to `ℓ` acts
through `u` by a scalar `ζ` in `O` such that `ζ ^ 2 - 1` is a unit. -/
lemma IsMainSummandLike.exists_mem_inertiaAbove_eq_smul_one_isUnit
    (hrow : IsMainSummandLike D t J R) (hu : IsLatticeIn R u) :
    ∃ γ ∈ inertiaAbove (placesAboveM D \ placesDividing D.E ℓ), ∃ ζ : ↑O,
      u γ = ζ • 1 ∧ IsUnit (ζ ^ 2 - 1) := by
  obtain ⟨i⟩ := hrow.nonempty
  obtain ⟨Φ, hΦ_inj, hΦ_u : ∀ g, Φ (u g) = R g, -⟩ := hu.exists_algHom
  obtain ⟨γ, hγ, y, hRγ : (R γ).1 = y • 1, hy⟩ := hrow.exists_scalar_inertia
  have hy_unit : ‖y ^ 2 - 1‖ = 1 := by simpa using hy 0 2 ⟨one_le_two, le_add_self⟩
  -- The scalar `y` lies in `O`, being a diagonal entry of `u γ`, a conjugate of `R γ`.
  obtain ⟨ζ, rfl⟩ : ∃ ζ : ↑O, (ζ : PadicAlgCl ℓ) = y := by
    obtain ⟨Q, hQ⟩ := hu
    have h_conj : (u γ).map O.val.val = y • 1 := (hQ γ).symm.trans (by simp [hRγ])
    exact ⟨u γ i i, by simpa using congrFun₂ h_conj i i⟩
  exact ⟨γ, hγ, ζ, hΦ_inj (by simpa [hΦ_u]),
    (O.isUnit_iff_norm_eq_one _).2 (by simpa using hy_unit)⟩

/-- Main summands are Selmer data. Let `D` be the data for the parameters `P`, with field `D.E`, and
let `n` be a finite index type. Fix a prime `ℓ` and an isomorphism `ℂ ≃ ℚ̄_ℓ` (`PadicIso ℓ`). Let
`R` be a row (`IsMainSummandLike`): a continuous representation on `n`-vectors of the Galois group
of `D.E` over `ℚ̄_ℓ`, unramified off `ℓ p₀ p₁`, with `R^c ≅ R^∨(1 - t)` on traces (`t = 0` read as
`1`) and Hodge–Tate jumps `J σ` at the complex embeddings `σ`, such that the images of its lattices
span all matrices and contain suitable scalars, and `det (R g - 1)` has bounded valuation for
suitable inertia elements `g` above `p₀ p₁`. Let `w` be a chosen place above `p₀ p₁` and prime to
`ℓ`, and `γ` the chosen generator of tame inertia at `w`.

Over all large coefficient rings `O` there is a Selmer datum `T` for `γ` and the places
`badPlaces D ℓ` dividing `ℓ p₀ p₁` or the level `D.N`, such that `T.ρ` is a lattice in `R`, and
`T.places` consists of the places above `ℓ p₀ p₁`; the linear relations `T.localRelations` that hold
on the allowed cocycles are those that hold on the crystalline cocycles at the places above `ℓ`
(`crysRelations`); and `T.β` has normalised length `O.normLength T.β` at most `(4 f + 3) · card n`
times the `ℓ`-adic valuation of `D.chosenGroupOrder`, with `f = D.f` the number of infinite
places. -/
theorem IsMainSummandLike.eventually_exists_selmerDatum (hrow : IsMainSummandLike D t J R)
    {w : FinPlace D.E} (hw_chosen : D.IsChosen w) (hw : w ∈ placesAboveM D \ placesDividing D.E ℓ) :
    ∀ᶠ O : CoeffRing ℓ in .atTop,
      ∃ T : SelmerDatum ℓ (badPlaces D ℓ) w.isPlaceOver_placeOver.tameGenerator O n,
        IsLatticeIn R T.ρ ∧
        ↑T.places = placesDividing D.E ℓ ∪ placesAboveM D ∧
        T.localRelations = crysRelations T.ρ ∧
        O.normLength T.β ≤ (4 * D.f + 3) * card n * padicValNat ℓ D.chosenGroupOrder := by
  filter_upwards [hrow.eventually_span_eq_top_and_exists_eq_smul_one,
    eventually_exists_isLatticeIn hrow.continuous]
    with O h_span_scalar ⟨u, hu⟩
  obtain ⟨h_span_top : Submodule.span O (Set.range u) = ⊤, g, l, α,
    h_cyc : (cyclotomicChar Ω ℓ g : ℤ_[ℓ]) = D.levelPrime l ^ card n, hg : u g = α • 1⟩ :=
    h_span_scalar u hu
  obtain ⟨γ, ⟨v, ⟨hv_M, hv_ℓ⟩, hγ⟩, ζ, hζ : u γ = ζ • 1, h_unit : IsUnit (ζ ^ 2 - 1)⟩ :=
    hrow.exists_mem_inertiaAbove_eq_smul_one_isUnit hu
  have h_bad : placesDividing D.E ℓ ∪ placesAboveM D ⊆ badPlaces D ℓ :=
    placesDividing_union_subset_badPlaces D ℓ
  let S : Finset (FinPlace D.E) := ((finite_toSet _).subset h_bad).toFinset
  have hS : ↑S = placesDividing D.E ℓ ∪ placesAboveM D := Set.Finite.coe_toFinset _
  have h_global : O.normLength (congruenceTerm ℓ u) ≤ card n * padicValNat ℓ D.chosenGroupOrder :=
    hrow.normLength_congruenceTerm_le hu h_span_top h_cyc hg
  have h_local : O.normLength (placeTerms ℓ u S +
      firstPrimeTerms ℓ u w.isPlaceOver_placeOver.tameGenerator) ≤
        (4 * D.f + 2) * card n * padicValNat ℓ D.chosenGroupOrder :=
    hrow.normLength_placeTerms_add_firstPrimeTerms_le hu hS hw_chosen hw
  -- The cyclotomic character is trivial at `γ`, so `γ^{-c}` acts by the same scalar.
  have hζ' : u (conjGal γ)⁻¹ = ζ • 1 := by
    simp [hrow.conjGal_inv_eq_smul_one hu h_span_top hζ, cyclotomicInv,
      cyclotomicChar_eq_one_of_mem_inertiaAbove ⟨v, hv_ℓ, hγ⟩]
  let T : SelmerDatum ℓ (badPlaces D ℓ) w.isPlaceOver_placeOver.tameGenerator O n :=
    { nonempty := hrow.nonempty
      ρ := u
      isLocallyConstant M s := (isOpen_discrete s).preimage
        ((hu.continuous hrow.continuous).matrix_map continuous_quot_mk)
      places := S
      subset := coe_subset.1 (hS.le.trans h_bad)
      placesDividing_subset := Set.subset_union_left.trans hS.ge
      unramified s hs := hu.eq_one (hrow.eq_one_of_mem_inertiaAbove s (by simpa [hS] using hs))
      Z v' := crysCocyclesAt v' u
      finite_Z v' :=
        crysCocycles.fg (hrow.toIsConjSelfDualOfLevel.inClass_localLattice hrow hu
          v').isPotentiallyCrystalline
      apply_mul_of_mem_Z _ _ hz := crysCocycles.apply_mul hz
      coboundary_mem_Z _ b := crysCocycles.coboundary_mem b
      span_range_eq_top := h_span_top
      sum_finrank_Z_le := hrow.sum_finrank_crysCocyclesAt_le hu
      congruenceTerm_ne_top := ne_top_of_normLength_le h_global (by finiteness)
      localTerms_ne_top := ne_top_of_normLength_le h_local (by finiteness)
      γ := γ
      ζ := ζ
      γ_mem_inertiaAbove := ⟨v, ⟨hS.superset (.inr hv_M), hv_ℓ⟩, hγ⟩
      ρ_eq_smul_one := Bool.forall_bool.2 ⟨hζ', hζ⟩
      isUnit_sq_sub_one := h_unit }
  refine ⟨T, hu, hS, rfl, ?_⟩
  calc O.normLength T.β = O.normLength T.globalTerm + O.normLength T.localTerms := map_add ..
    _ ≤ card n * padicValNat ℓ D.chosenGroupOrder +
        (4 * D.f + 2) * card n * padicValNat ℓ D.chosenGroupOrder := add_le_add h_global h_local
    _ = (4 * D.f + 3) * card n * padicValNat ℓ D.chosenGroupOrder := by ring

end New.Selmer
