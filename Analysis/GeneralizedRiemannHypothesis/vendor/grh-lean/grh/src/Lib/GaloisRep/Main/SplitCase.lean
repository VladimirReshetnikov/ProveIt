import Lib.GaloisRep.Main.AttachedRepresentations
import Lib.GaloisRep.Main.SeedRepresentation
import Lib.GaloisRep.WeightCongruence

/-!
# Attached Galois representations in odd rank: the split case

This file proves that eigenforms on the definite space `New.stdSpace` of odd rank have attached
Galois representations in the split case. Here `E` is a CM field containing a primitive 5040th
root of unity and `ℚ(√−D)`, with `D ≡ 3 mod 4`. The spherical place `u` and the places above `ℓ`
lie over split primes of `ℚ(√−D)`. The proof is an ℓ-adic limit argument. For it, the file
constructs places apart from given places and levels of a given type at a split place.

## Main definitions and results

* `New.GaloisRep.sphericalCompat_of_split`: in odd rank, eigenforms have attached Galois
  representations compatible at a spherical place `u`, when `u` and the places above `ℓ` lie over
  split primes of `ℚ(√−D)`. The eigenvalues of f are ℓ-adic limits of combinations of eigenvalues
  of forms that satisfy the hypotheses of `New.GaloisRep.exists_rep_of_cuspidal_type`. The limit of
  the traces of their representations is the trace of a representation attached to f
  (`New.GaloisRep.Attached`), and the local properties at `u` pass to the limit.
* `New.GaloisRep.exists_isTypeLevel`: Let `v` and `x` be split places with `v` apart from `x` and
  its conjugate, `H` an open subgroup, and `ϑ` a character of the matrices `≡ 1` modulo `v` that is
  trivial on those `≡ 1` modulo `v ^ 2`. Then there is a level of type `ϑ` at `v` that lies in `H`
  away from `v` and `x`.

Notions from other files:
* `New.IsEigenform`: f ≠ 0, and almost all places w of prime norm are split and f has the Hecke
  polynomial P w at w.
* `New.GaloisRep.Attached` P r i: r is continuous with non-degenerate trace form, i (by default the
  identity) is an open map to Gal(Ω/E), and at most Frobenius elements the characteristic
  polynomials of r are ℓ-adically close to those given by P.
* `New.InducesPlacePair` w τ: the place of E that the ℓ-adic embedding belonging to the infinite
  place τ induces is w or its conjugate.
* `New.GaloisRep.IsSplitPrimeToDisc` u: the place u of ℚ(√−D) contains some (1 + √−D)/2 − b
  (b an integer) that is coprime to its conjugate; in particular u is split.

## Relation to the literature

Known; see `Lib.GaloisRep.Main.OddRank` for sources.
-/

section OddRank

open Matrix Polynomial Filter Finset Metric Nat New.Gf

/-- The finite place `x` of `E` is induced by the `ℓ`-adic embedding `θ`, lies over the same split
place of `QuadField D` as `z`, and is apart from `y` and `u` up to conjugation. The infinite place
of the complex embedding `ιℓ⁻¹ ∘ θ` of `E` induces `x` or its conjugate, and induces neither `u` nor
its conjugate (`New.InducesPlacePair`). -/
structure New.GaloisRep.IsPlaceApart {ℓ : ℕ} {E : Type} (D : ℕ) [ThePrime ℓ] [PadicIso ℓ]
    [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield D E]
    (z y u x : FinPlace E) (θ : Ω →+* PadicAlgCl ℓ) : Prop where
  /-- The restriction of `θ` to `E` induces `x`. -/
  placeOfEmb_eq : placeOfEmb (θ.comp (algebraMap E Ω)) = x
  /-- The infinite place of `ιℓ⁻¹ ∘ θ` induces `x` or its conjugate. -/
  inducesPlacePair : InducesPlacePair (l := ℓ) x
    (NumberField.InfinitePlace.mk (RingHom.comp ιℓ.symm (θ.comp (algebraMap E Ω))))
  /-- The infinite place of `ιℓ⁻¹ ∘ θ` induces neither `u` nor its conjugate. -/
  not_inducesPlacePair : ¬InducesPlacePair (l := ℓ) u
    (NumberField.InfinitePlace.mk (RingHom.comp ιℓ.symm (θ.comp (algebraMap E Ω))))
  /-- The place of `QuadField D` below `x` is split and prime to `D`. -/
  isSplitPrimeToDisc : IsSplitPrimeToDisc (x.below (QuadField D))
  /-- The places `x` and `z` lie over the same place of `QuadField D`. -/
  below_eq : x.below (QuadField D) = z.below (QuadField D)
  /-- The place `x` is not `y`. -/
  ne_left : x ≠ y
  /-- The conjugate of `x` is not `y`. -/
  star_ne_left : star x ≠ y
  /-- The place `x` is not `u`. -/
  ne_right : x ≠ u
  /-- The conjugate of `x` is not `u`. -/
  star_ne_right : star x ≠ u

/-- Let `z` lie above `ℓ` and over a split place of `QuadField D`, and let `y` and `u` be any places
of `E`. Over the place below `z` there is a place `x`, induced by an `ℓ`-adic embedding `θ`, that
is apart from `y` and `u` up to conjugation (`New.GaloisRep.IsPlaceApart`). -/
lemma New.GaloisRep.exists_place_apart {ℓ : ℕ} {E : Type} {D : ℕ} [ThePrime ℓ] [PadicIso ℓ]
    [Field E] [CMType E] [EmbeddedNumberField E] [HasPrimitiveRoot5040 E] [HasQuadSubfield D E]
    {z : FinPlace E} (hz : ↑ℓ ∈ z.asIdeal) (z_split : IsSplitPrimeToDisc (z.below (QuadField D)))
    (y u : FinPlace E) :
    ∃ (x : FinPlace E) (θ : Ω →+* PadicAlgCl ℓ), IsPlaceApart D z y u x θ := by
  obtain ⟨x, x_below, x_ne_y, star_ne_y, x_ne_u, star_ne_u⟩ :
      ∃ x : FinPlace E, x.below (QuadField D) = z.below (QuadField D) ∧
        x ≠ y ∧ star x ≠ y ∧ x ≠ u ∧ star x ≠ u := z_split.exists_place_above_ne y u
  -- `x` lies above `ℓ`, so some `ℓ`-adic embedding `θ` induces it.
  have hℓ_below : ↑ℓ ∈ (x.below (QuadField D)).asIdeal := by simpa [x_below] using hz
  have hx : ↑ℓ ∈ x.asIdeal := by simpa using hℓ_below
  obtain ⟨θ, hθ⟩ : ∃ θ : Ω →+* PadicAlgCl ℓ, (intQpBar ℓ).comap θ = placeOver x :=
    exists_comap_intQpBar_eq (x.isPlaceOver_placeOver.valuation_natCast_lt_one_iff.mpr hx)
  have h_place : placeOfEmb (θ.comp (algebraMap E Ω)) = x :=
    (isPlaceOver_placeOfEmb θ).unique (by simpa [hθ] using x.isPlaceOver_placeOver)
  let σ : E →+* ℂ := RingHom.comp ιℓ.symm (θ.comp (algebraMap E Ω))
  have hσ : ιℓ.toRingHom.comp σ = θ.comp (algebraMap E Ω) := RingHom.ext fun a ↦ by simp [σ]
  have x_induced : InducesPlacePair (l := ℓ) x (NumberField.InfinitePlace.mk σ) :=
    inducesPlacePair_mk x σ (by rw [inducedPrime, hσ, h_place])
  -- An infinite place induces one place up to conjugation, and `u` is neither `x` nor `star x`.
  have u_not_induced : ¬InducesPlacePair (l := ℓ) u (NumberField.InfinitePlace.mk σ) := by
    rintro (hu | hu) <;> obtain hx' | hx' := x_induced
    · exact x_ne_u (star_injective (hx'.symm.trans hu))
    · exact star_ne_u (star_eq_iff_star_eq.mp (hu.symm.trans hx'))
    · exact star_ne_u (hx'.symm.trans hu)
    · exact x_ne_u (hx'.symm.trans hu)
  exact ⟨x, θ,
    { placeOfEmb_eq := h_place
      inducesPlacePair := x_induced
      not_inducesPlacePair := u_not_induced
      isSplitPrimeToDisc := by rwa [x_below]
      below_eq := x_below
      ne_left := x_ne_y
      star_ne_left := star_ne_y
      ne_right := x_ne_u
      star_ne_right := star_ne_u }⟩

/-- If `ιℓ` takes the values of a nonzero `f` into a field `L`, it does so with the coefficient
`a - 1` of a Hecke polynomial `Q` of `f`: the eigenvalues are sums of values divided by a
nonzero value. -/
lemma New.HasHeckePolyAt.coeff_pred_mem {ℓ : ℕ} {E : Type} {a : ℕ} {M : Type} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [CMType E] {f : Gf E (Fin a) → M → ℂ} {w : FinPlace E} {hw : star w ≠ w}
    {Q : ℂ[X]} (h_hecke : HasHeckePolyAt f w hw Q) {L : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)}
    (hL : ∀ (g : Gf E (Fin a)) (i : M), ιℓ (f g i) ∈ L) {g₀ : Gf E (Fin a)} {i₀ : M}
    (hf₀ : f g₀ i₀ ≠ 0) :
    ιℓ (Q.coeff (a - 1)) ∈ L := by
  obtain ⟨f_sph, c, rfl, hc⟩ := h_hecke
  have c_mem (j : ℕ) : ιℓ (c j) ∈ L := by
    have h_value : c j * f g₀ i₀ =
        heckeSplit (rightRegular ℂ (Gf E (Fin a)) (M → ℂ)) hw j f g₀ i₀ := by simp [hc j]
    rw [eq_div_of_mul_eq hf₀ h_value, map_div₀]
    refine div_mem ?_ (hL g₀ i₀)
    simp [heckeSplit, heckeGL_eq_sum ((mem_sphericalAt_iff hw).mp f_sph), sum_mem, hL]
  -- The coefficient is an integer multiple of an eigenvalue.
  rw [coeff_heckePoly, map_mul]
  exact mul_mem (by simp [-Int.cast_mul]) (c_mem _)

/-- Let the continuous `r i` have characteristic polynomials `Q i` at most Frobenius elements. Let
the monoid `N` of an approximation (`New.IsApproximatingMonoid`: on it the first component is the
uniform limit of the combinations, with coefficients `t`, of the others) contain the pairs formed
by the coefficients of `P` and of the `Q i`, with the sign changed. If `P` is monic of degree `a`
and these coefficients of `P` in degree `a - 1` lie in a complete set, some `R` is attached to `P`,
and the pairs of the traces of `R` and of the `r i` lie in `N`. -/
lemma New.GaloisRep.exists_attached_of_isApproximatingMonoid {ℓ : ℕ} {E : Type} {a : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [NeZero a] {s : Set.Ioi (0 : ℝ) → ℕ}
    {t : (η : Set.Ioi 0) → Fin (s η) → PadicAlgCl ℓ}
    {N : Submonoid (PadicAlgCl ℓ × ((η : Set.Ioi 0) × Fin (s η) → PadicAlgCl ℓ))}
    (apx : IsApproximatingMonoid s t N)
    {r : (Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → GalRep ℓ E (Fin a)}
    {Q : (Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → FinPlace E → ℂ[X]}
    (r_cont : ∀ i : (η : Set.Ioi 0) × Fin (s η), Continuous (r i))
    (r_frob : ∀ i : (η : Set.Ioi 0) × Fin (s η), ∀ᶠ p : FrobeniusDatum E in mostFrobenii E,
      (r i p.frob).val.charpoly = (Q i p.place).map ιℓ)
    {L : Set (PadicAlgCl ℓ)} (hL : IsComplete L) (d : FrobeniusDatum E → ℕ → N)
    {P : FinPlace E → ℂ[X]}
    (hd : ∀ᶠ p : FrobeniusDatum E in mostFrobenii E,
      (P p.place).IsMonicOfDegree a ∧
      -ιℓ ((P p.place).coeff (a - 1)) ∈ L ∧
      ∀ j : ℕ,
        (d p j).val =
          (-ιℓ ((P p.place).coeff j), fun i : (η : Set.Ioi 0) × Fin (s η) ↦
            -ιℓ ((Q i p.place).coeff j))) :
    ∃ R : GalRep ℓ E (Fin a),
      Attached P R ∧
      ∀ g : Gal(Ω/E),
        ((R g).val.trace, fun i : (η : Set.Ioi 0) × Fin (s η) ↦ (r i g).val.trace) ∈ N := by
  -- The trace of a matrix is minus the coefficient `a - 1` of its characteristic polynomial.
  have trace_eq (i : (η : Set.Ioi 0) × Fin (s η)) : ∀ᶠ p : FrobeniusDatum E in mostFrobenii E,
      (r i p.frob).val.trace = (d p (a - 1)).val.snd i := by
    filter_upwards [r_frob i, hd] with p h_char ⟨_, _, h_pair⟩
    simp [trace_eq_neg_charpoly_coeff, h_char, h_pair]
  have fst_mem : ∀ᶠ p : FrobeniusDatum E in mostFrobenii E, (d p (a - 1)).val.fst ∈ L :=
    hd.mono fun p ⟨_, h_mem, h_pair⟩ ↦ by rwa [h_pair]
  have trace_tendsto (g : Gal(Ω/E)) (i : (η : Set.Ioi 0) × Fin (s η)) :
      (mostFrobeniiAt E g).Tendsto (fun p : FrobeniusDatum E ↦ (d p (a - 1)).val.snd i)
        (nhds (r i g).val.trace) :=
    (tendsto_mostFrobeniiAt fun g ↦ (r i g).val.trace).congr' (mem_inf_of_left (trace_eq i))
  obtain ⟨R, R_cont, R_nondeg, R_mem⟩ :=
    exists_continuous_isTraceNondeg_of_tendsto_trace apx
      (fun g ↦ (mostFrobeniiAt E g).map fun p ↦ d p (a - 1)) hL
      (fun _ ↦ mem_inf_of_left fst_mem) r_cont fun g i ↦ tendsto_map' (trace_tendsto g i)
  let tr (g : Gal(Ω/E)) : N := ⟨_, R_mem g⟩
  -- By Newton's identities the coefficient `i` of a characteristic polynomial is a polynomial in
  -- the traces of the powers. Add `d p i`: for each `r i` the sum is `0` at most Frobenius
  -- elements, and for `R` and `P` it is the difference to bound.
  refine ⟨R, ⟨R_cont, R_nondeg, .id, fun η hη ↦ ?_⟩, R_mem⟩
  let B (i : ℕ) : MvPolynomial ℕ (PadicAlgCl ℓ) :=
    .C ((-1) ^ (a - i) / (a - i)!) * newtonPoly (a - i) 1
  have tends (i : ℕ) : TendstoUniformly
      (fun (ε : Set.Ioi (0 : ℝ)) (p : FrobeniusDatum E) ↦
        ∑ j : Fin (s ε), t ε j * (B i).eval (fun m : ℕ ↦ (r ⟨ε, j⟩ (p.frob ^ m)).val.trace) +
          ∑ j : Fin (s ε), t ε j * (d p i).val.snd ⟨ε, j⟩)
      (fun p : FrobeniusDatum E ↦
        (B i).eval (fun m : ℕ ↦ (R (p.frob ^ m)).val.trace) + (d p i).val.fst) atBot :=
    (apx.tendstoUniformly_eval (B i) fun (p : FrobeniusDatum E) m ↦ tr (p.frob ^ m)).add
      (apx.tendstoUniformly.comp fun p ↦ d p i)
  obtain ⟨ε, close⟩ :=
    ((Iic a).eventually_all.mpr fun i _ ↦ tendstoUniformly_iff.mp (tends i) η hη).exists
  filter_upwards [eventually_all.mpr fun i ↦ r_frob ⟨ε, i⟩, hd] with p h_char ⟨h_monic, _, h_pair⟩
  refine forall_eq.mpr fun i ↦ ?_
  obtain hi | hi := le_or_gt i a
  · -- Newton's identities give the coefficient `i` from the traces of the powers.
    have eval_B (G : GalRep ℓ E (Fin a)) :
        (B i).eval (fun m : ℕ ↦ ((G p.frob).val ^ m).trace) = (G p.frob).val.charpoly.coeff i := by
      simp [B, hi, eval_newtonPoly, trace_pow_eq_sum_roots, charpoly_monic,
        coeff_eq_esymm_roots_of_splits, IsAlgClosed.splits, ← mul_assoc]
    simpa [eval_B, h_char, h_pair, sub_eq_add_neg] using (close i (mem_Iic.2 hi) p).le
  · simp [hi, hη.le, coeff_eq_zero_of_natDegree_lt, h_monic.natDegree_eq]

/-- The `ℓ`-adic model `padicModel κ κ 1 f` of a nonzero `f` (from weight `κ` to itself, with matrix
`1`; applying `weylRep κ` at the `ℓ`-adic components of `g` to it gives back `ιℓ ∘ f g`) is
nonzero. -/
lemma New.padicModel_one_ne_zero {ℓ : ℕ} {E : Type} {a : ℕ} [ThePrime ℓ] [PadicIso ℓ] [Field E]
    [CMType E] {κ : Weight E} {f : Gf E (Fin a) → WeylIndex (Fin a) κ.1 → ℂ} (hf : f ≠ 0) :
    padicModel (l := ℓ) κ κ 1 f ≠ 0 := by
  intro h_zero
  refine hf (funext fun g ↦ funext fun i ↦ ?_)
  -- Applying the weight representation at `padicComponents g` to the model gives back `ιℓ (f g i)`.
  have h_apply :
      (weylRep κ.1 κ.2 (padicComponents g) *ᵥ
        fun j : WeylIndex (Fin a) κ.1 ↦ padicModel (l := ℓ) κ κ 1 f ⟨g, j⟩) i = ιℓ (f g i) := by
    simp [padicModel, ← map_mul]
  simpa [h_zero, ← Pi.zero_def] using h_apply.symm

/-- A free family of integers (`New.HasNoSmallRelations`: for small `d`, two choices of `d` entries
with repetition that have the same sum coincide) stays free when it is multiplied by `ε ≠ 0` and
shifted by `c`. -/
lemma New.HasNoSmallRelations.const_add_mul {n : ℕ} {e : Fin n → ℤ} (he : HasNoSmallRelations e)
    (c : ℤ) {ε : ℤ} (hε : ε ≠ 0) :
    HasNoSmallRelations fun i : Fin n ↦ c + ε * e i := by
  intro d hd α hα β hβ h_eq
  have h_weight (γ : Fin n →₀ ℕ) (hγ : Finsupp.degree γ = d) :
      Finsupp.weight (fun i : Fin n ↦ c + ε * e i) γ = d * c + ε * Finsupp.weight e γ := by
    simp [← hγ, Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, mul_add, sum_add_distrib, sum_mul,
      mul_sum, mul_left_comm]
  rw [h_weight α hα, h_weight β hβ] at h_eq
  exact he d hd hα hβ (mul_left_cancel₀ hε (add_left_cancel h_eq))

/-- Let `κ_h` be the entries of the weight `κ` at the infinite place of `σ`. If the `a` integers
`-∑_{j < h < a} (κ_h + 1)`, for `j < a`, form a free family (`New.HasNoSmallRelations`), then the
jumps of `κ` at `σ` contain a free family of `a` integers. -/
lemma New.HasNoSmallRelations.exists_mem_jumps {E : Type} {a : ℕ} [Field E] [CMType E]
    {κ : Weight E} {σ : E →+* ℂ}
    (h_free : HasNoSmallRelations fun j : Fin a ↦
      -∑ h ∈ Finset.Ioo ↑j a, (κ.1 (NumberField.InfinitePlace.mk σ) h + 1)) :
    ∃ e : Fin a → ℤ, HasNoSmallRelations e ∧ ∀ i : Fin a, e i ∈ jumps κ a σ := by
  -- The jumps are, up to a common sign and shift, the free integers of `h_free`.
  unfold jumps
  generalize NumberField.InfinitePlace.mk σ = τ at h_free ⊢
  have h_sum (i : Fin a) :
      ((∑ h ∈ Finset.Ioo ↑i a, (κ.1 τ h + 1) : ℕ) : ℤ) =
        (∑ h ∈ Finset.Ioo ↑i a, κ.1 τ h : ℕ) + (a - 1 - i) := by
    rw [sum_add_distrib, ← card_eq_sum_ones, Nat.card_Ioo]
    omega
  by_cases hσ : σ = Φ τ
  · refine ⟨_, h_free.const_add_mul (a - 1 - κ.2 τ) one_ne_zero, fun i ↦ Multiset.mem_map.2
      ⟨i, Multiset.mem_range.2 i.2, (ite_eq_left hσ).trans (by linarith [h_sum i])⟩⟩
  · refine ⟨_, h_free.const_add_mul (κ.2 τ) (neg_ne_zero.2 one_ne_zero), fun i ↦ Multiset.mem_map.2
      ⟨i, Multiset.mem_range.2 i.2, (ite_eq_right hσ).trans (by linarith [h_sum i])⟩⟩

/-- Let `v` be a split place, `V` an open subgroup, and `ϑ` a character of the matrices `≡ 1`
modulo `v` that is trivial on those `≡ 1` modulo `v ^ 2`. There are a level `K` and a character
`χ` of `K`, trivial near `1`, such that an integral point that is `1` at `v` lies in `K` exactly
when it lies in `V`, and is then killed by `χ`, while the matrices `≡ 1` modulo `v`, placed at `v`,
lie in `K` and `χ` is `ϑ` on them. -/
lemma New.GaloisRep.exists_isLevel_of_localCongruence_hom {E : Type} {a : ℕ} [Field E] [CMType E]
    {v : FinPlace E} (v_split : v.IsSplit) (V : OpenSubgroup (Gf E (Fin a)))
    {ϑ : localCongruence (Fin a) v 0 →* ℂ}
    (ϑ_one : ∀ k : localCongruence (Fin a) v 0, k.val ∈ localCongruence (Fin a) v 1 → ϑ k = 1) :
    ∃ (K : Subgroup (Gf E (Fin a))) (χ : K →* ℂ),
      IsLevel K ∧
      χ =ᶠ[nhds 1] 1 ∧
      (∀ k ∈ stdLevel E (Fin a), atPlace v k = 1 → (k ∈ K ↔ k ∈ V)) ∧
      (∀ k : K, atPlace v k.val = 1 → χ k = 1) ∧
      ∀ j : localCongruence (Fin a) v 0, ∃ k : K,
        k.val = ofSplitPlace v_split j.val ∧ χ k = ϑ j := by
  -- `K`: the integral points that are `≡ 1` modulo `v` and whose part off `v` lies in `V`;
  -- `χ` is `ϑ` read at `v`
  let K : OpenSubgroup (Gf E (Fin a)) :=
    .comap (atPlace v) (continuous_atPlace v)
        ⟨localCongruence (Fin a) v 0, isOpen_localCongruence⟩ ⊓
      offPartComap v_split V ⊓ ⟨stdLevel E (Fin a), isOpen_stdLevel⟩
  have mem_K (k : Gf E (Fin a)) : k ∈ K.1 ↔ atPlace v k ∈ localCongruence (Fin a) v 0 ∧
      k * (ofSplitPlace v_split (atPlace v k))⁻¹ ∈ V ∧ k ∈ stdLevel E (Fin a) := by
    simp [K, offPartComap, and_assoc]
  let χ : K.1 →* ℂ :=
    ϑ.comp (.mk' (fun k ↦ ⟨atPlace v k, ((mem_K k).1 k.2).left⟩) (by simp))
  have χ_near : χ =ᶠ[nhds 1] 1 :=
    .mono (isOpen_localCongruence.preimage_of_continuous.mem_nhds (by simp)) fun _ ↦ ϑ_one _
  have K_off (k : Gf E (Fin a)) (k_int : k ∈ stdLevel E (Fin a)) (k_v : atPlace v k = 1) :
      k ∈ K.1 ↔ k ∈ V := by simp [mem_K, k_v, k_int]
  have χ_off (k : K.1) (k_v : atPlace v k.val = 1) : χ k = 1 := by simp [χ, k_v, ϑ_one]
  have j_mem (j : localCongruence (Fin a) v 0) : ofSplitPlace v_split j.val ∈ K.1 := by
    have j_int : j.val ∈ localIntGL (Fin a) v := j.prop.1
    simpa [mem_K] using j_int
  exact ⟨K.1, χ, ⟨inf_le_right, K.2⟩, χ_near, K_off, χ_off,
    fun j ↦ ⟨⟨_, j_mem j⟩, rfl, by simp [χ]⟩⟩

/-- Let `N` be a closed monoid of pairs `(x, φ)` such that `∑ i, t η i * φ (η, i)` tends to `x`
uniformly on `N` as `η → 0`. Let `ρ` and the `r i` be continuous, let `ρ` have a non-degenerate
trace form, and let `N` contain the pairs of traces of `ρ` and of the `r i`. Let each `r i` be
spherical above `u` (good, with the jumps of `κ`, and `ιℓ (Q i)` kills geometric Frobenii), with
`Q i` of degree `a` if `u` is split. For each Hecke polynomial `X` of `f ≠ 0` at `u`, let `N`
contain a nonzero multiple of each pair of coefficients of `X` and the `Q i`. Then `ρ` is compatible
with `f` at every place `A` over `u` (`IsCompatibleAt`: unramified or crystalline, with the jumps of
`κ`, and `ιℓ X` kills geometric Frobenii). -/
lemma New.GaloisRep.isCompatibleAt_of_isApproximatingMonoid {ℓ : ℕ} {E : Type} {a : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] {s : Set.Ioi (0 : ℝ) → ℕ}
    {t : (η : Set.Ioi 0) → Fin (s η) → PadicAlgCl ℓ}
    {N : Submonoid (PadicAlgCl ℓ × ((η : Set.Ioi 0) × Fin (s η) → PadicAlgCl ℓ))}
    (apx : IsApproximatingMonoid s t N) {κ : Weight E}
    {f : Gf E (Fin a) → WeylIndex (Fin a) κ.1 → ℂ} (hf : f ≠ 0) {u : FinPlace E}
    {r : (Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → GalRep ℓ E (Fin a)}
    {Q : (Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → ℂ[X]}
    (r_cont : ∀ i : (η : Set.Ioi 0) × Fin (s η), Continuous (r i))
    (r_sph : ∀ i : (η : Set.Ioi 0) × Fin (s η),
      IsSphericalAbove (r i) Eq (jumps κ a) u ((Q i).map ιℓ))
    (Q_deg : star u ≠ u → ∀ i : (η : Set.Ioi 0) × Fin (s η), (Q i).natDegree = a)
    (coeff_mem : ∀ (hu : star u ≠ u) (X : ℂ[X]), HasHeckePolyAt f u hu X → ∀ j : ℕ,
      ∃ c : PadicAlgCl ℓ, c ≠ 0 ∧
        (c * ιℓ (X.coeff j), fun i : (η : Set.Ioi 0) × Fin (s η) ↦ c * ιℓ ((Q i).coeff j)) ∈ N)
    {ρ : GalRep ℓ E (Fin a)} (ρ_cont : Continuous ρ) (ρ_nondeg : IsTraceNondeg ρ)
    (trace_mem : ∀ g : Gal(Ω/E),
      ((ρ g).val.trace, fun i : (η : Set.Ioi 0) × Fin (s η) ↦ (r i g).val.trace) ∈ N)
    {A : ClosurePlace} (hA : IsPlaceOver A u) :
    IsCompatibleAt f a u ρ A := by
  -- The trace of `ρ` is a limit of combinations of the traces of the `r i`, so the local clauses
  -- pass from the `r i` to `ρ`.
  let tr (g : Gal(Ω/E)) : N := ⟨_, trace_mem g⟩
  have r_jump (η : Set.Ioi (0 : ℝ)) (i : Fin (s η)) : HasJumpsAt (r ⟨η, i⟩) A (jumps κ a) :=
    (r_sph ⟨η, i⟩ hA).2.1
  have ρ_limit : IsTraceLimit ρ A atBot t fun η i ↦ ⟨r ⟨η, i⟩⟩ :=
    ⟨ρ_cont, ρ_nondeg, fun η i ↦ r_cont ⟨η, i⟩, fun η i ↦ (r_sph ⟨η, i⟩ hA).1,
      .inr ⟨jumps κ a, r_jump⟩, apx.tendstoUniformly.comp tr⟩
  refine ⟨ρ_limit.isGoodAt, ρ_limit.jumpsRelAt r_jump fun τ k m n h_eq h_lim ↦ ?_,
    fun u_split X hX σ hσ ↦ ?_⟩
  · -- The coefficients `t η i` sum to `1` in the limit (take `1 : N` in `apx`), so the common jump
    -- multiplicity of the `r i` is that of the limit.
    have h_sum : Tendsto (fun η : Set.Ioi (0 : ℝ) ↦ ∑ i : Fin (s η), t η i) atBot (nhds 1) := by
      simpa using apx.tendstoUniformly.tendsto_at 1
    have h_count : Tendsto (fun η : Set.Ioi 0 ↦ ∑ i : Fin (s η), t η i * m η i) atBot
        (nhds ((jumps κ a τ).count k : PadicAlgCl ℓ)) := by
      simpa [← h_eq, sum_mul] using h_sum.mul_const ((jumps κ a τ).count k : PadicAlgCl ℓ)
    exact cast_inj.1 (tendsto_nhds_unique h_count h_lim)
  · have X_deg : X.natDegree = a := by simpa using (hX.isMonicOfDegree hf).natDegree_eq
    refine ρ_limit.polyKillsAt (n := a + 1) (Q := fun η i ↦ (Q ⟨η, i⟩).map ιℓ) (by simp [X_deg])
      (fun η i ↦ by simp [Q_deg u_split]) (fun η i ↦ (r_sph ⟨η, i⟩ hA).2.2 σ hσ) fun j ↦ ?_
    -- Divide the pair `d` of coefficients by `c` and multiply it by the pair of traces.
    obtain ⟨c, hc, c_mem⟩ := coeff_mem u_split X hX j
    let d : N := ⟨_, c_mem⟩
    simpa [tr, d, mul_assoc, hc] using
      apx.tendstoUniformly_eval (c⁻¹ • .X 0 * .X 1) fun g ↦ ![d, tr g]

/-- Let `x` be a split place and `H` an open subgroup. There is a finite set `S` of places such that
the integral points trivial at `S` have their part off `x` (the point times the inverse of its
component at `x`, placed at `x`) in `H`. It avoids `x` and its conjugate, and also `w` and its
conjugate when `w` is apart from them and `H` contains `maxCompactAt _ w`. -/
private lemma New.GaloisRep.exists_inf_trivialOn_le_offPartComap {E : Type} {a : ℕ} [Field E]
    [CMType E] {x : FinPlace E} (x_split : x.IsSplit) (H : OpenSubgroup (Gf E (Fin a))) :
    ∃ S : Finset (FinPlace E),
      x ∉ S ∧
      star x ∉ S ∧
      (∀ w : FinPlace E, x ≠ w → star x ≠ w → maxCompactAt (Fin a) w ≤ H.1 → w ∉ S ∧ star w ∉ S) ∧
      stdLevel E (Fin a) ⊓ trivialOn (Fin a) S ≤ (offPartComap x_split H).1 := by
  obtain ⟨S, S_min, S_level⟩ : ∃ S : Finset (FinPlace E),
      (∀ w : FinPlace E, maxCompactAt (Fin a) w ≤ (offPartComap x_split H).1 → w ∉ S ∧ star w ∉ S) ∧
      stdLevel E (Fin a) ⊓ trivialOn (Fin a) S ≤ (offPartComap x_split H).1 :=
    exists_inf_trivialOn_le (offPartComap x_split H).2
  -- A point supported at `x` and its conjugate has trivial part off `x`.
  have x_le : maxCompactAt (Fin a) x ≤ (offPartComap x_split H).1 :=
    inf_le_of_right_le (by simp [LE.le, ← range_ofSplitPlace x_split, offPartComap])
  obtain ⟨x_off, star_off⟩ := S_min x x_le
  refine ⟨S, x_off, star_off, fun w x_ne star_ne le_H ↦ S_min w fun g hg ↦ ?_, S_level⟩
  -- A point supported at `w` and its conjugate is `1` at `x`, so it is its own part off `x`.
  have g_x : atPlace x g = 1 := by simp [mem_supportedOn.1 hg.2 x, x_ne, star_ne]
  simpa [g_x, offPartComap] using le_H hg

/-- The level `K` with its character `χ` has the type `ϑ` at the split place `v`, lies in `H` away
from `v` and `x`, and is spherical off the finite set `U`, which contains `v` and avoids `x`. -/
private structure New.GaloisRep.IsTypeLevel {E : Type} {a : ℕ} [Field E] [CMType E]
    {v : FinPlace E} (v_split : v.IsSplit) (ϑ : localCongruence (Fin a) v 0 →* ℂ) (x : FinPlace E)
    (H : Subgroup (Gf E (Fin a))) (K : Subgroup (Gf E (Fin a))) (χ : K →* ℂ)
    (U : Finset (FinPlace E)) : Prop where
  /-- The subgroup `K` is open and consists of integral points. -/
  isLevel : IsLevel K
  /-- The character `χ` is trivial near `1`. -/
  eventuallyEq_one : χ =ᶠ[nhds 1] 1
  /-- The matrices `≡ 1` modulo `v`, placed at `v`, lie in `K`, and `χ` is `ϑ` on them. -/
  exists_eq_ofSplitPlace (j : localCongruence (Fin a) v 0) :
    ∃ k : K, k.val = ofSplitPlace v_split j.val ∧ χ k = ϑ j
  /-- An element of `K` that is `1` at `v` and at `x` lies in `H` and is killed by `χ`. -/
  mem_of_atPlace_eq_one (k : K) (k_v : atPlace v k.val = 1) (k_x : atPlace x k.val = 1) :
    k.val ∈ H ∧ χ k = 1
  /-- The integral points trivial at `U` lie in `K` and are killed by `χ`. -/
  exists_mem_of_trivialOn (k : Gf E (Fin a)) (hk : k ∈ stdLevel E (Fin a) ⊓ trivialOn (Fin a) U) :
    ∃ k_mem : k ∈ K, χ ⟨k, k_mem⟩ = 1
  /-- The place `v` is in `U`. -/
  mem : v ∈ U
  /-- The place `x` is not in `U`. -/
  notMem : x ∉ U
  /-- The conjugate of `x` is not in `U`. -/
  star_notMem : star x ∉ U
  /-- A place `w` apart from `v`, `x` and their conjugates, at which `H` contains the integral
  points, is off `U` with its conjugate. -/
  notMem_of_maxCompactAt_le (w : FinPlace E) (v_ne : v ≠ w) (star_v_ne : star v ≠ w)
    (x_ne : x ≠ w) (star_x_ne : star x ≠ w) (le_H : maxCompactAt (Fin a) w ≤ H) :
    w ∉ U ∧ star w ∉ U

/-- Let `v` and `x` be split places with `v` apart from `x` and its conjugate, `H` an open subgroup,
and `ϑ` a character of the matrices `≡ 1` modulo `v` that is trivial on those `≡ 1` modulo `v ^ 2`.
Then there is a level of type `ϑ` at `v` that lies in `H` away from `v` and `x`. -/
private lemma New.GaloisRep.exists_isTypeLevel {E : Type} {a : ℕ} [Field E] [CMType E]
    {v x : FinPlace E} (v_split : v.IsSplit) (x_split : x.IsSplit) (x_ne : x ≠ v)
    (star_x_ne : star x ≠ v) (H : OpenSubgroup (Gf E (Fin a)))
    {ϑ : localCongruence (Fin a) v 0 →* ℂ}
    (ϑ_one : ∀ k : localCongruence (Fin a) v 0, k.val ∈ localCongruence (Fin a) v 1 → ϑ k = 1) :
    ∃ (K : Subgroup (Gf E (Fin a))) (χ : K →* ℂ) (U : Finset (FinPlace E)),
      IsTypeLevel v_split ϑ x H.1 K χ U := by
  classical
  -- Off `v` the level is the group of integral points whose part off `x` lies in `H`.
  obtain ⟨S, x_off, star_x_off, S_min, S_level⟩ := exists_inf_trivialOn_le_offPartComap x_split H
  obtain ⟨K, χ, K_level, χ_near, K_off, χ_off, K_at⟩ :=
    exists_isLevel_of_localCongruence_hom v_split (offPartComap x_split H) ϑ_one
  refine ⟨K, χ, insert v S, K_level, χ_near, K_at, fun k k_v k_x ↦ ⟨?_, χ_off k k_v⟩, ?_,
    mem_insert_self v S, by simp [x_off, x_ne], by simp [star_x_off, star_x_ne], ?_⟩
  · have k_mem : k.val ∈ offPartComap x_split H := (K_off k (K_level.le k.prop) k_v).1 k.prop
    simpa [k_x, offPartComap] using k_mem
  · rintro k ⟨k_int, k_off⟩
    obtain ⟨k_v, k_S⟩ : atPlace v k = 1 ∧ ∀ w ∈ S, atPlace w k = 1 := by simpa using k_off
    have k_mem : k ∈ K := (K_off k k_int k_v).2 (S_level ⟨k_int, mem_trivialOn.2 k_S⟩)
    exact ⟨k_mem, χ_off ⟨k, k_mem⟩ k_v⟩
  · intro w v_ne star_v_ne x_ne_w star_x_ne_w le_H
    obtain ⟨w_off, star_w_off⟩ := S_min w x_ne_w star_x_ne_w le_H
    have star_w_ne : star w ≠ v := fun h ↦ star_v_ne (star_eq_iff_star_eq.mp h)
    exact ⟨by simp [w_off, v_ne.symm], by simp [star_w_off, star_w_ne]⟩

/-- For a level `K` with character `χ` that is spherical off `U`, the forms of type `χ` and weight
`μ` are spanned by those that are Hecke eigenforms off `U` (`New.IsSphericalOff`). -/
private lemma New.GaloisRep.IsTypeLevel.levelSpace_le_span {E : Type} {a : ℕ} [Field E]
    [CMType E] {v x : FinPlace E} {v_split : v.IsSplit} {ϑ : localCongruence (Fin a) v 0 →* ℂ}
    {H K : Subgroup (Gf E (Fin a))} {χ : K →* ℂ} {U : Finset (FinPlace E)}
    (hK : IsTypeLevel v_split ϑ x H K χ U) (μ : Weight E) :
    levelSpace ((stdSpace E (Fin a)).formTranslation μ) K χ ≤
      Submodule.span ℂ {g ∈ levelSpace ((stdSpace E (Fin a)).formTranslation μ) K χ |
        ∃ Q : FinPlace E → ℂ[X], IsSphericalOff U g.val Q} := by
  have le_sph : levelSpace ((stdSpace E (Fin a)).formTranslation μ) K χ ≤
      levelSpace ((stdSpace E (Fin a)).formTranslation μ)
        (stdLevel E (Fin a) ⊓ trivialOn (Fin a) U) := by
    rintro g hg ⟨k, k_off⟩
    obtain ⟨k_mem, χ_k⟩ := hK.exists_mem_of_trivialOn k k_off
    simpa [χ_k] using hg ⟨k, k_mem⟩
  have : Module.Finite ℂ (levelSpace ((stdSpace E (Fin a)).formTranslation μ) K χ) :=
    (stdSpace E (Fin a)).finite_formTranslation_levelSpace μ hK.isLevel.isOpen χ
  refine le_span_isSphericalOff _ le_sph fun y hy y_off star_off j g hg ↦ ?_
  exact heckeSplit_mem_levelSpace hy j (levelSpace_le_sphericalAt y_off star_off (le_sph hg))
    hK.isLevel.le hg

/-- Let `a` be odd, and let `v` and `x` lie over the split place of `QuadField D` below `z`, apart
from `u` and from each other. Let `u` lie over a split place of `QuadField D` prime to `D`, and let
`u = z` if `u` is above `ℓ`. Let the level `K` with character `χ` have the cuspidal type `ϑ` at `v`,
and let the form `g` of type `χ` and weight `μ` have Hecke polynomials `Q` off `U`. Let `μ` agree
with `κ` at the infinite places that induce `u` or its conjugate and be free at the others (the
integers `-∑_{j < h < a} (μ_h + 1)` satisfy `New.HasNoSmallRelations`). Then a continuous
representation has characteristic polynomials `Q` at most Frobenius elements and, if `u` and its
conjugate are off `U`, satisfies the spherical clause at `u` with the jumps of `κ`. -/
private lemma New.GaloisRep.exists_rep_of_free_weight {ℓ : ℕ} {E : Type} {a D : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [HasPrimitiveRoot5040 E]
    [HasQuadSubfield D E] (ha : Odd a) {z u v x : FinPlace E} {θ θ' : Ω →+* PadicAlgCl ℓ}
    (hv : IsPlaceApart D z u u v θ') (hx : IsPlaceApart D z v u x θ)
    (u_split : IsSplitPrimeToDisc (u.below (QuadField D))) (huz : ↑ℓ ∈ u.asIdeal → u = z)
    {κ μ : Weight E}
    (μ_eq : ∀ τ : NumberField.InfinitePlace E,
      InducesPlacePair (l := ℓ) u τ → μ.1 τ = κ.1 τ ∧ μ.2 τ = κ.2 τ)
    (μ_free : ∀ τ : NumberField.InfinitePlace E, ¬InducesPlacePair (l := ℓ) u τ →
      HasNoSmallRelations fun j : Fin a ↦ -∑ h ∈ Finset.Ioo ↑j a, (μ.1 τ h + 1))
    {v_split : v.IsSplit} {ϑ : localCongruence (Fin a) v 0 →* ℂ}
    (ϑ_type : Variety.IsCuspidalType (localCongruence (Fin a) v 0) ϑ)
    {H K : Subgroup (Gf E (Fin a))} {χ : K →* ℂ} {U : Finset (FinPlace E)}
    (hK : IsTypeLevel v_split ϑ x H K χ U) {g : (stdSpace E (Fin a)).forms μ}
    (hg : g ∈ levelSpace ((stdSpace E (Fin a)).formTranslation μ) K χ) {Q : FinPlace E → ℂ[X]}
    (hQ : IsSphericalOff U g.val Q) :
    ∃ r : GalRep ℓ E (Fin a),
      Continuous r ∧
      (∀ᶠ p : FrobeniusDatum E in mostFrobenii E, (r p.frob).val.charpoly = (Q p.place).map ιℓ) ∧
      (u ∉ U ∧ star u ∉ U → IsSphericalAbove r Eq (jumps κ a) u ((Q u).map ιℓ)) := by
  -- The matrices `≡ 1` modulo `v`, placed at `v`, lie in `K` and act on `g` by `ϑ`.
  have g_type (j : localCongruence (Fin a) v 0) :
      rightRegular ℂ (Gf E (Fin a)) (WeylIndex (Fin a) μ.1 → ℂ)
        (ofSplitPlace v_split j.val) g.val = ϑ j • g.val := by
    obtain ⟨k, k_eq, χ_eq⟩ := hK.exists_eq_ofSplitPlace j
    simpa [k_eq, χ_eq] using congrArg Subtype.val (hg k)
  -- The weight `μ` is free at the infinite place given by `θ`, so its jumps there are free.
  obtain ⟨e, e_free, e_mem⟩ : ∃ e : Fin a → ℤ, HasNoSmallRelations e ∧
      ∀ i : Fin a, e i ∈ jumps μ a (RingHom.comp ιℓ.symm (θ.comp (algebraMap E Ω))) :=
    (μ_free _ hx.not_inducesPlacePair).exists_mem_jumps
  have x_below : x.below (QuadField D) = v.below (QuadField D) := hx.below_eq.trans hv.below_eq.symm
  have u_below (hu : ↑ℓ ∈ u.asIdeal) : u.below (QuadField D) = v.below (QuadField D) := by
    rw [huz hu, hv.below_eq]
  obtain ⟨r, r_cont, r_frob, r_sph⟩ :=
    exists_rep_of_cuspidal_type ha g.prop hQ hK.mem hv.isSplitPrimeToDisc ϑ_type g_type
      ⟨hK.notMem, hK.star_notMem, x_below⟩ hx.placeOfEmb_eq e_free e_mem u ⟨u_split, u_below⟩
  refine ⟨r, r_cont, r_frob, fun hu A hA ↦ ?_⟩
  -- Over `u` the weights `μ` and `κ` agree, so they have the same jumps.
  obtain ⟨r_good, r_jump, r_poly⟩ := r_sph hu hA
  refine ⟨r_good, r_jump.congr hA fun σ hσ ↦ ?_, r_poly⟩
  obtain ⟨h_columns, h_det⟩ := μ_eq _ (inducesPlacePair_mk u σ hσ)
  simp [jumps, h_columns, h_det]

/-- Let `f` be an eigenform with polynomials `P`, and let the continuous `r i` have characteristic
polynomials `Q i` at most Frobenius elements. Let the monoid `N` of an approximation contain, at
each split place `w` prime to `ℓ` with `w` and its conjugate off `U`, the pairs formed by the
coefficients of the Hecke polynomial of `f` and of the `Q i w`, with the sign changed. Then some `R`
is attached to `P`, and the pairs of the traces of `R` and of the `r i` lie in `N`. -/
private lemma New.GaloisRep.exists_attached_of_coeff_mem {ℓ : ℕ} {E : Type} {a : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [NeZero a]
    {s : Set.Ioi (0 : ℝ) → ℕ} {t : (η : Set.Ioi 0) → Fin (s η) → PadicAlgCl ℓ}
    {N : Submonoid (PadicAlgCl ℓ × ((η : Set.Ioi 0) × Fin (s η) → PadicAlgCl ℓ))}
    (apx : IsApproximatingMonoid s t N) {κ : Weight E}
    {f : Gf E (Fin a) → WeylIndex (Fin a) κ.1 → ℂ} (hf : f ∈ (stdSpace E (Fin a)).forms κ)
    {P : FinPlace E → ℂ[X]} (h_eig : IsEigenform f P)
    {r : (Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → GalRep ℓ E (Fin a)}
    {Q : (Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → FinPlace E → ℂ[X]}
    (r_cont : ∀ i : (η : Set.Ioi 0) × Fin (s η), Continuous (r i))
    (r_frob : ∀ i : (η : Set.Ioi 0) × Fin (s η), ∀ᶠ p : FrobeniusDatum E in mostFrobenii E,
      (r i p.frob).val.charpoly = (Q i p.place).map ιℓ) {U : Finset (FinPlace E)}
    (coeff_mem : ∀ (w : FinPlace E) (hw : star w ≠ w) (X : ℂ[X]) (j : ℕ),
      w ∉ U → star w ∉ U → ↑ℓ ∉ w.asIdeal → HasHeckePolyAt f w hw X →
      (-ιℓ (X.coeff j), fun i : (η : Set.Ioi 0) × Fin (s η) ↦ -ιℓ ((Q i w).coeff j)) ∈ N) :
    ∃ R : GalRep ℓ E (Fin a),
      Attached P R ∧
      ∀ g : Gal(Ω/E),
        ((R g).val.trace, fun i : (η : Set.Ioi 0) × Fin (s η) ↦ (r i g).val.trace) ∈ N := by
  obtain ⟨hf_ne, h_hecke⟩ := h_eig
  -- The values of `f` lie in a finite, so complete, extension `L` of `ℚ_ℓ`.
  obtain ⟨L, L_finite, hL⟩ : ∃ L : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ), Module.Finite ℚ_[ℓ] L ∧
      ∀ (g : Gf E (Fin a)) (i : WeylIndex (Fin a) κ.1), ιℓ (f g i) ∈ L :=
    exists_padic_field_of_form_values hf
  obtain ⟨g₀, i₀, hf₀⟩ : ∃ (g : Gf E (Fin a)) (i : WeylIndex (Fin a) κ.1), f g i ≠ 0 := by
    simpa [funext_iff] using hf_ne
  -- `d p j` is the pair of coefficients as an element of `N`, when it lies in `N`.
  let pair (p : FrobeniusDatum E) (j : ℕ) :
      PadicAlgCl ℓ × ((η : Set.Ioi 0) × Fin (s η) → PadicAlgCl ℓ) :=
    (-ιℓ ((P p.place).coeff j), fun i ↦ -ιℓ ((Q i p.place).coeff j))
  have exists_lift (p : FrobeniusDatum E) (j : ℕ) (h_mem : pair p j ∈ N) :
      ∃ d : N, d.val = pair p j := ⟨⟨pair p j, h_mem⟩, rfl⟩
  choose! d hd using exists_lift
  -- Most Frobenius elements are at places off `U` and prime to `ℓ`.
  have most_frob : ∀ᶠ p : FrobeniusDatum E in mostFrobenii E,
      (P p.place).IsMonicOfDegree a ∧
      -ιℓ ((P p.place).coeff (a - 1)) ∈ L ∧
      ∀ j : ℕ, (d p j).val = pair p j := by
    refine eventually_mostFrobenii ((eventually_notMem_star_notMem ℓ U).and h_hecke) ?_
    rintro p ⟨⟨p_off, star_off, p_prime⟩, h_at⟩
    obtain ⟨p_split, p_hecke⟩ := h_at p.prime_q
    exact ⟨by simpa using p_hecke.isMonicOfDegree hf_ne, neg_mem (p_hecke.coeff_pred_mem hL hf₀),
      fun j ↦ hd p j (coeff_mem p.place p_split _ j p_off star_off p_prime p_hecke)⟩
  exact exists_attached_of_isApproximatingMonoid apx r_cont r_frob
    L.toSubmodule.complete_of_finiteDimensional d
    most_frob

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `E` be a CM field containing a primitive 5040th root of unity and `ℚ(√−D)`, with
`D ≡ 3 mod 4`, and let `a` be odd. Suppose `u` and every place above `ℓ` lie over primes of `ℚ(√−D)`
that split (`New.GaloisRep.IsSplitPrimeToDisc`). Then every eigenform of any weight on the standard
definite unitary group of rank `a` has an attached Galois representation. If the form is spherical
at `u`, every representation attached to its Hecke polynomials satisfies the local conditions
`IsCompatibleAt` at every place of `Ω` over `u` (`New.GaloisRep.SphericalCompat`): it is good there,
has the jumps of the weight and, if `u` is split, the Hecke polynomial kills geometric Frobenius. -/
lemma New.GaloisRep.sphericalCompat_of_split {ℓ : ℕ} {E : Type} {a D : ℕ} [ThePrime ℓ] [PadicIso ℓ]
    [Field E] [CMType E] [EmbeddedNumberField E] [HasPrimitiveRoot5040 E] (ha : Odd a)
    [HasQuadSubfield D E] {u : FinPlace E}
    (hsp : ∀ v : FinPlace E,
      ↑ℓ ∈ v.asIdeal ∨ v = u → IsSplitPrimeToDisc (v.below (QuadField D))) :
    SphericalCompat (ℓ := ℓ) E (Fin a) a u := by
  classical
  -- Approximate the `ℓ`-adic model of `f` by eigenforms that are wildly ramified at a place `v`
  -- above `ℓ` and whose weights equal `κ` at the infinite places that induce `u` or its conjugate
  -- and are free at the others; these have representations by `exists_rep_of_free_weight`.
  -- The limit of their traces is a trace, and `isCompatibleAt_of_isApproximatingMonoid` carries the
  -- local clauses over to it.
  intro P κ f hf h_eig
  have : NeZero a := .of_pos ha.pos
  -- Places `v`, `x` above `ℓ`, over one split place of `QuadField D`, apart from each other and
  -- from `u` up to conjugation.
  obtain ⟨z, hz, huz⟩ : ∃ z : FinPlace E, ↑ℓ ∈ z.asIdeal ∧ (↑ℓ ∈ u.asIdeal → u = z) := by
    by_cases hu : ↑ℓ ∈ u.asIdeal
    · exact ⟨u, hu, fun _ ↦ rfl⟩
    · obtain ⟨z, hz⟩ := FinPlace.exists_natCast_mem E ℓ
      exact ⟨z, hz, fun hu' ↦ absurd hu' hu⟩
  obtain ⟨v, θ', hv⟩ := exists_place_apart hz (hsp z (.inl hz)) u u
  obtain ⟨x, θ, hx⟩ := exists_place_apart hz (hsp z (.inl hz)) v u
  have v_split : v.IsSplit := hv.isSplitPrimeToDisc.isSplit_of_below
  have x_split : x.IsSplit := hx.isSplitPrimeToDisc.isSplit_of_below
  -- `ϑ`: a cuspidal type on the matrices `≡ 1` modulo `v`, trivial on those `≡ 1` modulo `v ^ 2`
  obtain ⟨ϑ, ϑ_type, ϑ_one⟩ := Variety.exists_isCuspidalType v a
  -- `K` is a level and `χ` a character of `K` that is `ϑ` at `v`; away from `v` and `x` the level
  -- fixes `f`.
  let stab : OpenSubgroup (Gf E (Fin a)) := ⟨rightStabilizer f, hf.1⟩
  obtain ⟨K, χ, U, hK⟩ : ∃ (K : Subgroup (Gf E (Fin a))) (χ : K →* ℂ) (U : Finset (FinPlace E)),
      IsTypeLevel v_split ϑ x (rightStabilizer f) K χ U :=
    exists_isTypeLevel v_split x_split hx.ne_left hx.star_ne_left stab ϑ_one
  -- Hecke operators `T y hy j` that do not increase the sup norm (`hT`). On the model of a form
  -- with polynomial `X` at `y` the eigenvalue is `b y hy j * ιℓ (X.coeff j)` (`hE`), where `b` is
  -- not zero (`hb`) and is `-1` for `y` prime to `ℓ` (`hb'`).
  choose b hb hb' T hT hE using exists_padicModel_hecke_contraction (N := a) (l := ℓ) κ
  -- A seed is a common eigenvector, with polynomials `Q`, that has a representation `r`.
  let Seed : Set (Gf E (Fin a) × WeylIndex (Fin a) κ.1 → PadicAlgCl ℓ) :=
    {F | ∃ (r : GalRep ℓ E (Fin a)) (Q : FinPlace E → ℂ[X]),
      (∀ (y : FinPlace E) (hy : star y ≠ y) (j : ℕ), y ∉ U → star y ∉ U →
        (↑ℓ ∈ y.asIdeal → y = u) → T y hy j F = (b y hy j * ιℓ ((Q y).coeff j)) • F) ∧
      Continuous r ∧
      (∀ᶠ p : FrobeniusDatum E in mostFrobenii E, (r p.frob).val.charpoly = (Q p.place).map ιℓ) ∧
      (u ∉ U ∧ star u ∉ U →
        IsSphericalAbove r Eq (jumps κ a) u ((Q u).map ιℓ) ∧ (star u ≠ u → (Q u).natDegree = a))}
  -- The model of `f` is a uniform limit of combinations of models of forms of type `χ`, whose
  -- weights `μ` are free except at the infinite places that induce the pair of `u`.
  have mem_closure : padicModel κ κ 1 f ∈ uniformClosure Seed := by
    refine padicModel_mem_uniformClosure κ hK.isLevel hK.eventuallyEq_one
      {σ | ¬InducesPlacePair u σ} ⟨f, hf⟩ (fun k hk ↦ ?_) fun μ g₀ hg₀ μ_eq μ_free M hM ↦ ?_
    · -- Such a `k` is `1` at `v` and at `x`, so it fixes `f` and `χ k = 1`.
      exact hK.mem_of_atPlace_eq_one k
        (hv.inducesPlacePair.atPlace_eq_one v (hk _ hv.not_inducesPlacePair))
        (hx.inducesPlacePair.atPlace_eq_one x (hk _ hx.not_inducesPlacePair))
    -- The forms of type `χ` and weight `μ` are spanned by Hecke eigenforms `g` off `U`.
    refine Submodule.mapsTo_span (f := (padicModel κ μ M).domRestrict _) ?_
      (hK.levelSpace_le_span μ hg₀)
    rintro g ⟨hg, Q, hQ⟩
    obtain ⟨r, r_cont, r_frob, r_sph⟩ :=
      exists_rep_of_free_weight ha hv hx (hsp u (.inr rfl)) huz
        (fun τ hτ ↦ μ_eq τ (not_not_intro hτ)) μ_free ϑ_type hK hg hQ
    obtain ⟨g_ne, -, g_hecke⟩ := hQ
    refine ⟨r, Q, fun y hy j h₁ h₂ h₃ ↦ ?_, r_cont, r_frob, fun hu ↦ ⟨r_sph hu, fun h ↦ ?_⟩⟩
    · -- The matrix `M` intertwines the two weights at `y`, so `T y hy j` has the eigenvalue wanted.
      refine hE y hy j M _ (g_hecke y hy h₁ h₂) fun _ ↦ hM _ fun _ h_not_over ↦ ?_
      exact padicComponents_ofSplitPlace _ _ _ fun hℓ ↦ by rwa [h₃ hℓ]
    · simpa using ((g_hecke u h hu.left hu.right).isMonicOfDegree g_ne).natDegree_eq
  -- So there are seeds `y i` and a closed monoid `N` of pairs on which the first entry is the
  -- limit of combinations of the others. It contains the pairs of eigenvalues of the `T w hw j`.
  obtain ⟨s, t, N, apx, y, mem_N⟩ :=
    exists_isApproximatingMonoid_of_mem_uniformClosure (padicModel_one_ne_zero h_eig.1) mem_closure
  choose r Q y_eig y_cont y_frob y_sph using fun i ↦ (y i).2
  have pair_mem (w : FinPlace E) (hw : star w ≠ w) (X : ℂ[X]) (j : ℕ) (h₁ : w ∉ U)
      (h₂ : star w ∉ U) (h₃ : ↑ℓ ∈ w.asIdeal → w = u) (hX : HasHeckePolyAt f w hw X) :
      (b w hw j * ιℓ (X.coeff j), fun i ↦ b w hw j * ιℓ ((Q i w).coeff j)) ∈ N :=
    mem_N _ ⟨T w hw j, hT w hw j, hE w hw j 1 X hX (by simp [← map_mul]),
      fun i ↦ y_eig i w hw j h₁ h₂ h₃⟩
  -- At places prime to `ℓ` the constant `b` is `-1`.
  have neg_pair_mem (w : FinPlace E) (hw : star w ≠ w) (X : ℂ[X]) (j : ℕ) (h₁ : w ∉ U)
      (h₂ : star w ∉ U) (hℓ : ↑ℓ ∉ w.asIdeal) (hX : HasHeckePolyAt f w hw X) :
      (-ιℓ (X.coeff j), fun i ↦ -ιℓ ((Q i w).coeff j)) ∈ N := by
    simpa only [hb' w hw j hℓ, neg_one_mul] using
      pair_mem w hw X j h₁ h₂ (fun h ↦ absurd h hℓ) hX
  obtain ⟨R, attached, R_mem⟩ :=
    exists_attached_of_coeff_mem apx hf h_eig y_cont y_frob neg_pair_mem
  -- Any attached `ρ` has the trace of `R`, the limit of combinations of the traces of the `r i`.
  refine ⟨⟨R, attached⟩, fun ρ hρ f_sph A hA ↦ ?_⟩
  have u_good : u ∉ U ∧ star u ∉ U :=
    hK.notMem_of_maxCompactAt_le u hv.ne_right hv.star_ne_right hx.ne_right hx.star_ne_right
      fun g hg ↦ mem_rightStabilizer.2 (by simpa [funext_iff] using f_sph ⟨g, hg⟩)
  have coeff_mem (u_split : star u ≠ u) (X : ℂ[X]) (hX : HasHeckePolyAt f u u_split X) (j : ℕ) :
      ∃ c : PadicAlgCl ℓ, c ≠ 0 ∧
        (c * ιℓ (X.coeff j), fun i ↦ c * ιℓ ((Q i u).coeff j)) ∈ N :=
    ⟨b u u_split j, hb u u_split j,
      pair_mem u u_split X j u_good.left u_good.right (fun _ ↦ rfl) hX⟩
  have trace_mem (g : Gal(Ω/E)) : ((ρ g).val.trace, fun i ↦ (r i g).val.trace) ∈ N := by
    simpa [hρ.trace_eq attached g rfl] using R_mem g
  exact isCompatibleAt_of_isApproximatingMonoid apx h_eig.1 y_cont (fun i ↦ (y_sph i u_good).1)
    (fun u_split i ↦ (y_sph i u_good).2 u_split) coeff_mem hρ.continuous hρ.isTraceNondeg
    trace_mem hA

end OddRank
