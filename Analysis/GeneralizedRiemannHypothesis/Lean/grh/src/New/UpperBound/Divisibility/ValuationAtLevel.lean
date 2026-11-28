import New.UpperBound.Divisibility.ChainDatumExpansion
import New.UpperBound.Divisibility.SetupAtLevel
import New.UpperBound.Objects.CharactersAtLevel

/-!
# N-adic valuation of the lifts between the X_j at the level prime N

This file bounds how many powers of `N` the lifts between the `X_j` lose at the level prime `p = N`.
It first bounds the values of the lift characters at `N` and the loss of the direct datum on the
standard lattices. The lifts with data at `Σ_N` obey the rules of `IsSplitLevel.LiftLaw`. So on
ramified source forms the chain of glued double lifts is a scalar of bounded valuation times the
chain of direct lifts after `Up ^ (m / 2)`. Each direct lift loses at most `f b` powers of `N`. The
main result is that on ramified source forms `φ` with `Up ^ (m / 2) φ` integral for `L_0`, the
composite lift loses at most `2 m f b` powers of `N`.

Notions from other files:
* `Σ_N` is `D.nonInducedPlaces`, the places above `N` conjugate to the induced places;
* `diagN n S` is `diag (1, …, 1, N)` at the places in `S` and `1` at the others, and
  `δ_j = D.diagPointN j` is this matrix on `X_j` for `S` the set `D.piNPlaces` of places dividing
  `π`. It takes the standard lattice to `L_j` at `Σ_N`: if `e` is the last standard basis vector,
  the last vector of the basis of `L_j` is `N e` or `e` at each place, a unit times `π e`. The unit
  is the same for all `j`, and the direct datum and `Up` do not depend on it;
* `ιₚ` is the chosen embedding of `ℂ` into `ℂ_N`, and `D.chainChar ϑ i` is the character of lift
  `i`, from `X_{i-1}` to `X_i`;
* `schrodingerOpAt Ψ v` puts the function `Ψ` of matrices at `Σ_N` on the finite datum `v` of a
  lift;
* `directDatum` is the indicator of the integral matrices whose last column is the last basis vector
  modulo `N`, and `Up` is the operator `upOperator`;
* the data in `k.raises d d' C` give lifts that raise gauges from `d` to `d'` by a factor at most
  `C`.

## Relation to the literature

Denominators at the level prime N are traded for the operator `Up`. Related work: Z. Liu, Test
Schwartz functions at p for theta lifts of Hida families, arXiv 2510.21644, 2025; S. Rallis,
Langlands' functoriality and the Weil representation, 1982.
-/

namespace New.Data

/-! ## Values of the lift characters, and the direct datum on the standard lattices -/

section DirectDatum

open NumberField Finset Parameters Seesaw Ideal Quotient Space Kernel QuadField Real Matrix
  IsSplitLevel

variable {P : Parameters} (D : Data P) (ϑ : D.TameChar) [PadicPlace D.N]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
open scoped Classical in
/-- Let `E` be the CM field, `N` the level prime, `b` the weight and `m` the number of lifts of the
admissible data `D`, and let `ιₚ : ℂ →+* ℂ_[N]` be the chosen embedding. Each infinite place
`τ : D.Φ` of `E` induces through `ιₚ` a prime `D.inducedPlace τ` above `N`; their complex conjugates
form `Σ_N = D.nonInducedPlaces`. Let `χ` be the base change to `E` of the character
`D.chainChar ϑ i` of `U(1)`, the `i`-th character attached to the tame character `ϑ`, with
`i ≤ 2 m`. Let `g` be the matrix of size `n_j` that is `diag (1, …, 1, N)` at the places of `Σ_N` in
`S` and `1` at the other places of `Σ_N`. Then the `N`-adic absolute value of
`χ (det g) |det g| ^ (-k / 2)` is at most the product of one factor `N ^ (2 b)` for each `τ` whose
conjugate induced prime lies in `S`. -/
lemma norm_detCharAt_diagN_le {i : ℕ} (hi : i ≤ 2 * D.m) (k j : ℕ) (S : Finset (FinPlace D.E)) :
    ‖ιₚ (detCharAt (D.chainChar ϑ i).baseChange k
      (diagN (P := D.nonInducedPlaces) (D.InitIndex j) S))‖ ≤
      ∏ τ : D.Φ, if star (D.inducedPlace τ) ∈ S then (D.N : ℝ) ^ (2 * D.b) else 1 := by
  -- For `k = 0` the norm is a product over the infinite places `τ` of
  -- `‖(det g)_τ‖ ^ D.liftWeight i τ`, where `g = diagPoint j S`, `(det g)_τ` is `N⁻¹` or `1`, and
  -- `D.liftWeight i τ ≤ 2 b`.
  have h_place (τ : D.Φ) :
      ‖adeleExtension (ιₚ.comp (Φ τ)) (G.det (s := 1) (1, D.diagPoint j S)).1.2‖ ^
        (D.liftWeight i τ : ℤ) ≤
        if star (D.inducedPlace τ) ∈ S then (D.N : ℝ) ^ (2 * D.b) else 1 := by
    have h_det : adeleExtension (ιₚ.comp (Φ τ)) (G.det (s := 1) (1, D.diagPoint j S)).1.2 =
        ((diagGL fun l : D.X j ↦ if l.isLeft then 1
          else if star (D.inducedPlace τ) ∈ S then .mk0 ↑D.N NeZero.out else 1)⁻¹).1.det := by
      -- `g` is unitary, so `det g` at `τ` is `det g⁻¹` at the conjugate embedding. The rewriting is
      -- up to the definitions of `G` and of the unitary group, hence `erw`.
      erw [G.det_snd, ← star_star (det _), adeleExtension_star, ← det_conjTranspose,
        ← U.inv_val_eq_conjTranspose, RingHom.map_det]
      exact congrArg (fun g : GL (D.X j) ℂ_[D.N] ↦ g⁻¹.1.det) (D.map_adeleExtension_diagPoint j S τ)
    rw [h_det]
    split
    · grw [← D.liftWeight_le_two_mul_b hi τ] <;> simp [norm_p_eq_inv, NeZero.one_le]
    · simp
  -- It suffices to take `k = 0`, where the character is `χ` at the determinant of the finite point.
  -- As `χ` has weight `D.liftWeight i`, its norm there is the product of the factors bounded in
  -- `h_place`.
  grw [norm_detCharAt_diagN_anti (n' := D.InitIndex j) bot_le, ← atPlaces_embedGL (diagN ..)]
  suffices ‖ιₚ ((D.chainChar ϑ i).baseChange.1 (detOn D.nonInducedPlaces (D.diagPoint j S).1))‖ ≤
      ∏ τ : D.Φ, if star (D.inducedPlace τ) ∈ S then (D.N : ℝ) ^ (2 * D.b) else 1 by
    simpa [detCharAt, -atPlaces_embedGL, -prod_ite_mem] using this
  erw [D.hasWeight_liftChar.norm_padic_eq_prod ιₚ _ (unitary _).one_mem.2,
    ← G.detFin_of_mem_supportedOn (s := 1) isConjDisjoint (embedGL_mem_supportedOn _)]
  exact prod_le_prod₀ (by simp) fun τ _ ↦ by simpa using h_place τ

/-- Let `K = ℚ(√(-d))` with `d = P.d`, let `E ⊇ K` be the CM field and `N` the level prime of the
admissible data `D` for `P`, and let `ιₚ : ℂ →+* ℂ_[N]` be the chosen embedding. There is an
integer `δ` of `K` with `1 ≤ ‖ιₚ (δ̄ d)‖` that lies in every prime `D.inducedPlace σ` of `E`, the
prime above `N` induced by `ιₚ` and the infinite place `σ : D.Φ` of `E`. -/
lemma exists_mem_inducedPlace_one_le_norm : ∃ δ : 𝓞 P.K, 1 ≤ ‖ιₚ (star ↑δ * P.d)‖ ∧
    ∀ σ : D.Φ, algebraMap (𝓞 P.K) (𝓞 D.E) δ ∈ (D.inducedPlace σ).asIdeal := by
  -- Let `q` be the reduction of the integers of `K` at the prime induced by `ιₚ`.
  -- It maps into the residue field of `E` at that prime.
  let q : 𝓞 P.K →+* 𝓞 D.E ⧸ (D.inducedPlace 1).asIdeal := algebraMap _ _
  have h_ker (x : 𝓞 P.K) : q x = 0 ↔ ‖ιₚ x‖ < 1 := by
    -- `q x` is by definition the class of `algebraMap x`, hence `erw`.
    erw [eq_zero_iff_mem, mem_placeOfEmb, ιₚ.comp_apply, phi_algebraMap]
  -- The residue field has prime order `N`, so the generator `betaK P.d` reduces to some `c : ℕ`.
  have h_card : Nat.card (𝓞 D.E ⧸ (D.inducedPlace 1).asIdeal) = D.N :=
    q_eq_of_modEq_one D.N_modEq_one (p_mem_inducedPlace ..)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c • 1 = q (betaK P.d) := mem_multiples_of_prime_card h_card one_ne_zero
  let δ : 𝓞 P.K := betaK P.d - c
  refine ⟨δ, ?_, fun σ ↦ ?_⟩
  · -- The conjugate `1 - betaK P.d - c` reduces to `1 - 2 q (betaK P.d)`, whose square is `-d`. As
    -- `N` does not divide `d`, neither this nor the image of `d` is zero.
    have h_ne : q (star δ * P.d) ≠ 0 := by
      suffices 1 - q (betaK P.d) - c ≠ 0 ∧ q P.d ≠ 0 by simpa [δ] using this
      grind [two_mul, map_natCast, map_sqrtNegDInt_sq q,
        (FinPlace.charP_quotient _ (D.p_mem_inducedPlace 1)).cast_eq_zero_iff,
        not_dvd_q₁_mul_d_of_modEq_one D.N_modEq_one]
    simpa using (h_ker _).2.mt h_ne
  · -- On `K` all the induced primes give the kernel of `q`.
    erw [mem_placeOfEmb, ιₚ.comp_apply, phi_algebraMap, ← h_ker]
    simp [δ, ← hc]

/-- Let `x = (x_j)` be a tuple of finite adelic matrices, and let `D.translateDatum x j` be the
Heisenberg translate by `x_j` of the integral vacuum of the hermitian space
`D.homX j = Hom (X_j, X_{j+1})`. Let `𝔪` be a modulus whose places are those of
`Σ_N = D.nonInducedPlaces`, one from each conjugate pair of places above `N`, so that `projOn` is
the projection on the vacuum at all places above `N`. For every integer `δ` of `K`, the projection
lies in `standardData`, the span over the `N`-integral complex numbers of the translates of the
integral vacuum by the points `z` with `δ z` integral above `N`. -/
lemma projOn_translateDatum_mem_standardData (x : D.Translations) (j : ℕ) (δ : 𝓞 P.K)
    {𝔪 : Modulus D.E} (h_places : 𝔪.places = Set.range ((↑) : D.nonInducedPlaces → FinPlace D.E)) :
    (D.homX j).projOn 𝔪.places (D.translateDatum x j).1 ∈
      Parameters.standardData (p := D.N) (D.homX j) δ := by
  -- A translate datum is a Heisenberg translate of the vacuum by definition, hence `erw`.
  erw [projOn_finHeisenbergOp _ (by simp [intVacuum]), boxIndicator_apply]
  split_ifs with h_box
  · rw [one_smul]
    refine Submodule.subset_span ⟨_, fun l w hw ↦ ?_, rfl⟩
    -- Every place above `N` is in the box on which `x j` is integral.
    have hw_box : w ∈ 𝔪.places.conjClosure := by
      simp_all [D.isSplitLevel_nonInducedPlaces.natCast_mem_iff]
    have hx_box : idem 𝔪.places.conjClosure * x j l ∈ Ô D.E := by tauto
    exact mul_mem (w.coe_algebraMap_mem _ _ (algebraMap (𝓞 P.K) (𝓞 D.E) δ))
      (idem_mul_mem_Ô.1 hx_box w hw_box)
  · simp

/-- Let `j < m`, and let `D.liftKernel ϑ j` be the theta kernel from `X_j` to `X_{j+1}` for the tame
character `ϑ`. Take the Heisenberg translate `D.translateDatum x j` of the integral vacuum of
`Hom (X_j, X_{j+1})`, and put on it (`schrodingerOpAt`), at the set `Σ_N = D.nonInducedPlaces` of
places above `N`, the function `directDatum`: the indicator of the integral matrices whose last
column is the last basis vector modulo `N`. The kernel of this datum multiplies the `N`-adic gauge
(`weylGauge`, the largest absolute value of a coordinate) by at most `N ^ (f b)`, where `f` is the
number of infinite places of `E` and `b` the weight. -/
lemma schrodingerOpAt_directDatum_mem_raises (x : D.Translations) {j : ℕ} (hj : j < D.m) :
    schrodingerOpAt (P := D.nonInducedPlaces) directDatum (D.translateDatum x j) ∈
      (D.liftKernel ϑ j).raises (p := D.N) (1 : Gf D.E (D.X j)) (1 : Gf D.E (D.X (j + 1)))
        (D.N ^ (D.f * D.b)) := by
  -- By Fourier expansion modulo `N`, `c = N ^ (2 f n_{j+1} n_j)` times the datum `Θ` is an integral
  -- combination of translates whose poles above `N` are simple and lie at the induced places. These
  -- are cleared by a `δ` with `1 ≤ ‖ιₚ (δ̄ d)‖`, so `c • Θ` is a standard datum for `δ`. It loses
  -- nothing, because the loss of such a datum is at most a power of `‖ιₚ (δ̄ d)‖⁻¹`.
  obtain ⟨δ, hδ_norm, hδ_mem⟩ := D.exists_mem_inducedPlace_one_le_norm
  obtain ⟨𝔪, hS, h𝔪⟩ : ∃ 𝔪 : Modulus D.E,
      𝔪.places = Set.range ((↑) : D.nonInducedPlaces → FinPlace D.E) ∧
      (univ.inf fun w : D.nonInducedPlaces ↦ w.1.asIdeal) ≤ 𝔪.ideal :=
    exists_modulus_places_eq (by simp [star_notMem])
  set Θ := schrodingerOpAt (P := D.nonInducedPlaces) directDatum (D.translateDatum x j)
  let c : ℕ := absNorm (span {(D.N : 𝓞 D.E)}) ^ Fintype.card (D.X (j + 1) × D.X j)
  let δ' : 𝓞 D.E := star (algebraMap (𝓞 P.K) (𝓞 D.E) δ)
  have hN_mem : (D.N : 𝓞 D.E) * (1 : ℕ) ∈ 𝔪.ideal := h𝔪 (by simpa using natCast_level_mem)
  have hδ'_mem : δ' ∈ 𝔪.ideal := by
    suffices ∀ w ∈ D.nonInducedPlaces, δ' ∈ w.1 from h𝔪 (by simpa)
    simpa [δ', nonInducedPlaces] using hδ_mem
  -- `Θ` is given by the function `Ψ` modulo `𝔪` that tests the last column at each place.
  let Ψ : (D.X (j + 1) × D.X j → 𝔪.ResidueRing) → ℂ := fun T ↦
    if (fun (a : D.X (j + 1)) (w : D.nonInducedPlaces) ↦ residueEquiv w
      (Rows.modulusResidue 𝔪 (hS.ge ⟨w, rfl⟩) (vecToMatrix T a (.inr ())))) = lastBasisVector
    then 1 else 0
  have hΘ : (D.homX j).schrodingerOp 𝔪.places (𝔪.liftFn Ψ) (D.translateDatum x j).1 = Θ.1 := by
    simp only [Θ, IsSplitLevel.schrodingerOpAt, directDatum, lastColDatum]
    simp [Ψ, liftFn_eq_residueDatum, ← Rows.liftFn_eq_residueDatum hS, hS]
    rfl
  have hΨ (T : D.X (j + 1) × D.X j → 𝔪.ResidueRing) : Ψ T ∈ integralAway 1 := by
    unfold Ψ
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h_translate (z : D.X (j + 1) × D.X j → 𝔸f D.E)
      (hz : z ∈ translations (D.X (j + 1) × D.X j) 1 (star (δ' : 𝔸f D.E))) :
      (D.homX j).finHeisenbergOp z ((D.homX j).projOn 𝔪.places (D.translateDatum x j).1) ∈
        Parameters.standardData (D.homX j) δ :=
    -- `hz` is the integrality condition up to the definition of `translations`, hence `using!`.
    finHeisenbergOp_mem_standardData (fun l w _ ↦ by simpa [δ', one_notMem] using! hz l w)
      (D.projOn_translateDatum_mem_standardData x j δ hS)
  have h_std : (c : ℂ) • Θ.1 ∈ Parameters.standardData (D.homX j) δ := by
    rw [← hΘ]
    exact (isAdmissibleCombination_schrodingerOp_of_reduction _ 𝔪 (B := 0) hN_mem hΨ id rfl
      (d := algebraMap _ _ δ') (by simpa using eq_zero_iff_mem.2 hδ'_mem)).smul_mem (by simp)
      h_translate
  have hδ_ne : δ ≠ 0 := fun hδ ↦ by norm_num [hδ] at hδ_norm
  rw [← inv_smul_smul₀ (a := (c : ℂ)) (by simp [c, NeZero.ne]) Θ]
  refine smul_mem_raises _ (mem_raises_of_standardData hδ_ne h_std) ?_
  -- The exponent `2 f n_{j+1} n_j` is at most `2 f n_m² ≤ f b`.
  unfold c
  grw [norm_star_piMBar_le_one, ← hδ_norm, absNorm_span_natCast, RingOfIntegers.rank,
    finrank_eq_two_mul_card_infinitePlace, ← pow_mul]
  suffices 2 * (D.f : ℝ) * (D.n (j + 1) * D.n j) ≤ D.f * D.b by
    -- `↓card_X` counts the rows and columns before `simp` unfolds their index types.
    simpa [norm_p_eq_inv, ← rpow_natCast, ↓card_X, D.N_prime.one_lt]
  grw [D.n_mono hj, D.n_mono hj.le]
  exact D.le_of_hasLogBound

end DirectDatum

/-! ## Reduction of all lifts to direct lifts at N -/

section ChainAtLevel

open Finset Real IsSplitLevel SemilocalField

variable {P : Parameters} (D : Data P) (ϑ : D.TameChar) [PadicPlace D.N]

/-- The character `g ↦ χ (det g) |det g| ^ (-r / 2)` of `GL n` over the product of the completions
at `Σ_N`, for the base change `χ` of the character `chainChar ϑ i` of lift `i`. -/
noncomputable abbrev liftCharAtN {n : Type} [Fintype n] [DecidableEq n] (i r : ℕ) :
    GL n (LocProd D.nonInducedPlaces) →* ℂˣ :=
  detCharAt (D.chainChar ϑ i).baseChange r

/-- Let `φ` be an algebraic form on the definite space `X_j` of rank `n_j = D.n j`, and let `v` be a
vector of the finite part of the Weil representation of `Hom (X_j, X_{j+1})`. For a function `Ψ` of
matrices over `LocProd Σ_N`, the product of the completions at `Σ_N = D.nonInducedPlaces`, write
`θ Ψ` for the theta lift (`D.liftKernel ϑ j`) from `X_j` to `X_{j+1}` by `schrodingerOpAt Ψ v`. Let
`Ψ = liftFn f` be a function `f` of matrices modulo `N`, read on integral matrices and extended by
zero. Let `g`, `k` act on forms by right translation (`smoothFormRep`) through `embedGL`. Then `θ
(T ↦ Ψ (k⁻¹ T g)) φ = (χ_{n_{j+1}} g / χ_{n_j} k) • k (θ Ψ (g⁻¹ φ))`, where
`χ_r = D.liftCharAtN ϑ (j + 1) r` is `χ (det ·) |det ·| ^ (-r / 2)` for the base change `χ` of the
character of this lift. -/
lemma lift_schrodingerOpAt_comp (j : ℕ) (v : (D.homX j).finitePart)
    (f : Matrix (D.X (j + 1)) (D.X j) (D.nonInducedPlaces → ZMod D.N) → ℂ)
    (g : GL (D.X j) (LocProd D.nonInducedPlaces))
    (k : GL (D.X (j + 1)) (LocProd D.nonInducedPlaces)) (φ : D.FormX j) :
    (D.liftKernel ϑ j).lift (schrodingerOpAt (P := D.nonInducedPlaces)
        (fun T : Matrix (D.X (j + 1)) (D.X j) (LocProd D.nonInducedPlaces) ↦
          liftFn f (k⁻¹.val * T * g.val)) v) φ =
      (D.liftCharAtN ϑ (j + 1) (D.n (j + 1)) g / D.liftCharAtN ϑ (j + 1) (D.n j) k) •
        smoothFormRep (stdSpace D.E (D.X (j + 1))).embFin _ (embedGL k)
          ((D.liftKernel ϑ j).lift (schrodingerOpAt (liftFn f) v)
            (smoothFormRep (stdSpace D.E (D.X j)).embFin _ (embedGL g)⁻¹ φ)) := by
  have h_datum : schrodingerOpAt (P := D.nonInducedPlaces)
      (fun T ↦ liftFn f (k⁻¹.val * T * g.val)) v =
      (D.liftCharAtN ϑ (j + 1) (D.n (j + 1)) g / D.liftCharAtN ϑ (j + 1) (D.n j) k) •
        (D.liftKernel ϑ j).ω (embedGL g, embedGL k) (schrodingerOpAt (liftFn f) v) := by
    -- The two `↓` lemmas have to apply before `simp` unfolds the characters and the index types.
    simp [liftKernel_ω, pairWeilFinite_schrodingerOpAt, ↓spaceChar_rankTwist, ↓card_X, smul_smul]
  rw [h_datum, ← (D.liftKernel ϑ j).lift_equivariant (embedGL g)]
  simp [Units.smul_def]

/-- Put a function `Ψ` of matrices at `Σ_N`, written in bases of `L_j` and `L_{j+1}`, on a finite
datum. -/
noncomputable def schrodingerOpAtN (j : ℕ)
    (Ψ : Matrix (D.X (j + 1)) (D.X j) (LocProd D.nonInducedPlaces) → ℂ) :
    Module.End ℂ (D.homX j).finitePart :=
  (D.liftKernel ϑ j).ω (D.diagPointN j, D.diagPointN (j + 1)) ∘ₗ schrodingerOpAt Ψ

/-- Complex scalars on forms commute. A shortcut for instance search. -/
local instance smulCommClass_formX (j : ℕ) : SMulCommClass ℂ ℂ (D.FormX j) :=
  ⟨fun a b φ ↦ Subtype.ext (smul_comm a b φ.1)⟩

/-- The lift from `X_j` to `X_{j+1}` by `v` with the function `Ψ` at `Σ_N`, written in bases of
`L_j` and `L_{j+1}`, as a linear map in `Ψ`. -/
noncomputable def liftAtN (j : ℕ) (v : (D.homX j).finitePart) :
    (Matrix (D.X (j + 1)) (D.X j) (LocProd D.nonInducedPlaces) → ℂ) →ₗ[ℂ]
      D.FormX j →ₗ[ℂ] D.FormX (j + 1) :=
  (D.liftKernel ϑ j).lift ∘ₗ (D.liftKernel ϑ j).ω (D.diagPointN j, D.diagPointN (j + 1)) ∘ₗ
    LinearMap.applyₗ v ∘ₗ schrodingerOpAt

/-- `D.liftAtN ϑ j v Ψ φ` is computed in three steps. First translate `φ` on the right
(`smoothFormRep`) by `δ_j⁻¹`. Then apply the lift of the kernel `D.liftKernel ϑ j` by
`schrodingerOpAt Ψ v`. Finally translate on the right by `δ_{j+1} = D.diagPointN (j + 1)`. -/
lemma liftAtN_apply (j : ℕ) (v : (D.homX j).finitePart)
    (Ψ : Matrix (D.X (j + 1)) (D.X j) (LocProd D.nonInducedPlaces) → ℂ) (φ : D.FormX j) :
    D.liftAtN ϑ j v Ψ φ = smoothFormRep (stdSpace D.E (D.X (j + 1))).embFin _ (D.diagPointN (j + 1))
      ((D.liftKernel ϑ j).lift (schrodingerOpAt Ψ v)
        (smoothFormRep (stdSpace D.E (D.X j)).embFin _ (D.diagPointN j)⁻¹ φ)) := by
  simp [← (D.liftKernel ϑ j).lift_equivariant (D.diagPointN j), liftAtN]

/-- The factor by which `Up` moves through the direct lift from `X_j` to `X_{j+1}`: the ratio of the
values of `liftCharAtN` at `diag (1, …, 1, N)` on `X_j` and on `X_{j+1}`. -/
noncomputable def upCommutationFactor (j : ℕ) : ℂˣ :=
  D.liftCharAtN ϑ (j + 1) (D.n (j + 1)) (diagN (D.InitIndex j) D.nonInducedPlaces) /
    D.liftCharAtN ϑ (j + 1) (D.n j) (diagN (D.InitIndex (j + 1)) D.nonInducedPlaces)

/-- Let `v` be in the finite part of the Weil representation of `Hom (X_j, X_{j+1})`, and let
`L Ψ = D.liftAtN ϑ j v Ψ` be the theta lift, for the tame character `ϑ`, from forms on `X_j` to
forms on `X_{j+1}` by `v` with the function `Ψ` of matrices at `Σ_N = D.nonInducedPlaces`. Then the
two rules of `LiftLaw` hold:
* `b ∘ L (liftFn (T ↦ f (b T a))) ∘ a = L (liftFn f)` for integral invertible `a`, `b` and every
  function `f` of matrices modulo `N`;
* `d ∘ L lastRowDatum = γ • L directDatum ∘ d`, where `d = diagNInv = diag (1, …, 1, N⁻¹)`,
  `γ = D.upCommutationFactor ϑ j`, and the two data are the indicators of the integral matrices
  whose last row, respectively last column, is the last basis vector modulo `N`. -/
lemma liftLaw_liftAtN (j : ℕ) (v : (D.homX j).finitePart) :
    LiftLaw (D.formRepAtN j) (D.formRepAtN (j + 1)) (D.liftAtN ϑ j v)
      (D.upCommutationFactor ϑ j) where
  integral_equivariant a b f φ := by
    -- The characters are unramified above `N`, so trivial on integral matrices.
    have h_unr {n : Type} [Fintype n] [DecidableEq n] (r : ℕ) (g : GL n O) :
        D.liftCharAtN ϑ (j + 1) r (inclGL g) = 1 := by
      rw [liftCharAtN, ← D.spaceChar_rankTwist ϑ 0]
      exact detCharAt_inclGL _ (fun w hw ↦
        D.charUnramifiedAt_rankTwist_of_N_mem _ _ _ w (natCast_level_mem _ hw)) ..
    rw [liftAtN_apply, liftAtN_apply, liftFn_comp_mul, ← inv_inv (inclGL b),
      D.lift_schrodingerOpAt_comp]
    simp [conjEmbedGL, h_unr]
  diagNInv_lastRowDatum φ := by
    rw [liftAtN_apply, liftAtN_apply, ← funext lastRowDatum_conj_diagNInv]
    simp only [lastRowDatum, D.lift_schrodingerOpAt_comp]
    simp [upCommutationFactor, conjEmbedGL, Units.smul_def, smul_smul, div_mul_eq_mul_div]

open scoped Classical in
/-- The factor for rewriting the glued datum of `X_{2i} → X_{2i+1} → X_{2i+2}` in bases of `L_{2i}`
and `L_{2i+2}^∨`: the product of the values of `liftCharAtN` at `diag (1, …, 1, N)`, taken on
`X_{2i+2}` at the places of `Σ_N` prime to `π` and on `X_{2i}` at those dividing `π`. -/
noncomputable def gluedFactor (i : ℕ) : ℂˣ :=
  D.liftCharAtN ϑ (2 * i + 2) (D.n (2 * i + 1))
      (diagN (D.InitIndex (2 * i + 2)) (D.nonInducedPlaces \ D.piNPlaces)) *
    D.liftCharAtN ϑ (2 * i + 1) (D.n (2 * i + 1)) (diagN (D.InitIndex (2 * i)) D.piNPlaces)

/-- For `i ≤ ϱ`, where `m = 2 (ϱ + 1)`, each place of `Σ_N` contributes one character value to
`gluedFactor`, so this factor loses at most `2 f b` powers of `N`. -/
lemma norm_gluedFactor_le {i : ℕ} (hi : i ≤ D.ϱ) :
    ‖ιₚ (D.gluedFactor ϑ i)‖ ≤ D.N ^ (2 * D.f * D.b) := by
  classical
  have hm := D.m_eq_two_mul_varrho_add_two
  grw [gluedFactor, Units.val_mul, map_mul, norm_mul, D.norm_detCharAt_diagN_le ϑ (by lia),
    D.norm_detCharAt_diagN_le ϑ (by lia), ← prod_mul_distrib]
  calc _ = ∏ _τ : D.Φ, (D.N : ℝ) ^ (2 * D.b) := prod_congr rfl fun τ _ ↦ by
        by_cases hτ : star (D.inducedPlace τ) ∈ D.piNPlaces <;> simp [nonInducedPlaces, hτ]
    _ ≤ (D.N : ℝ) ^ (2 * D.f * D.b) := by
      rw [mul_right_comm, rpow_mul_natCast (Nat.cast_nonneg _), prod_const, card_univ]

attribute [local irreducible] IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
open scoped Classical in
/-- Let `D.liftKernel ϑ j` be the theta kernel from `X_j` to `X_{j+1}` for the tame character `ϑ`,
and let `v j` be in the finite part of the Weil representation of `Hom (X_j, X_{j+1})`. Let `π` be
the integer of `E` with `π π̄ = N`. The places `D.piNPlaces` dividing `π`, like those of
`Σ_N = D.nonInducedPlaces`, give with their conjugates all places above `N`. Project the `v j` on
the vacuum at these places (`vacuumProjFinPart`), glue `v (2 i)` and `v (2 i + 1)` to one tensor
(`gluedDoubleLiftDatum`), and take the double lift `X_{2i} → X_{2i+1} → X_{2i+2}`: `liftInPairs`
sends a pure tensor to the composite of the two lifts. The result is `gluedFactor`, a product of two
values of the lift characters at matrices `diag (1, …, 1, N)`, times a sum over the vectors `y`
modulo `N` at `Σ_N`, followed by the action of `diagNInv = diag (1, …, 1, N⁻¹)`. The term for `y` is
the lift `liftAtN` by `lastColDatum y`, the indicator of the integral matrices with last column `y`
modulo `N`, followed by the lift by `charDatum y`, the character `ψ_N` of the last row paired with
`y`. -/
lemma liftInPairs_gluedDoubleLiftDatum (v : ∀ j : ℕ, (D.homX j).finitePart) (i : ℕ) :
    TensorChain.liftInPairs (fun j : ℕ ↦ (D.liftKernel ϑ j).lift) i
        (D.gluedDoubleLiftDatum (fun j : ℕ ↦ (D.homX j).vacuumProjFinPart D.piNPlaces (v j)) i) =
      (D.gluedFactor ϑ i : ℂ) • (D.formRepAtN (2 * i + 1 + 1)).ρ diagNInv ∘ₗ
        ∑ y : D.X (2 * i + 1) → D.nonInducedPlaces → ZMod D.N,
          D.liftAtN ϑ (2 * i + 1) (v (2 * i + 1)) (charDatum y) ∘ₗ
          D.liftAtN ϑ (2 * i) (v (2 * i)) (lastColDatum y) := by
  -- Move the two matrices `diagN` out of the data, at the cost of one character value each. The
  -- points `δ_{2i+1}` then cancel between the two lifts.
  let ρ : Representation ℂ (Gf D.E (D.X (2 * i + 1))) (D.FormX (2 * i + 1)) :=
    smoothFormRep (stdSpace D.E (D.X (2 * i + 1))).embFin _
  have h_first (f : Matrix (D.X (2 * i + 1)) (D.X (2 * i)) (D.nonInducedPlaces → ZMod D.N) → ℂ)
      (φ : D.FormX (2 * i)) :
      (D.liftKernel ϑ (2 * i)).lift (schrodingerOpAt (P := D.nonInducedPlaces) (fun T ↦ liftFn f
          (T * (diagN (P := D.nonInducedPlaces) (D.InitIndex (2 * i)) D.piNPlaces).val)) (v _)) φ =
        D.liftCharAtN ϑ (2 * i + 1) (D.n (2 * i + 1)) (diagN (D.InitIndex (2 * i)) D.piNPlaces) •
          ρ (D.diagPointN (2 * i + 1))⁻¹ (D.liftAtN ϑ (2 * i) (v (2 * i)) (liftFn f) φ) := by
    simpa [ρ, liftAtN_apply] using D.lift_schrodingerOpAt_comp ϑ _ _ f (diagN _ D.piNPlaces) 1 φ
  have h_second
      (f : Matrix (D.X (2 * i + 1 + 1)) (D.X (2 * i + 1)) (D.nonInducedPlaces → ZMod D.N) → ℂ)
      (ψ : D.FormX (2 * i + 1)) :
      (D.liftKernel ϑ (2 * i + 1)).lift (schrodingerOpAt (P := D.nonInducedPlaces)
          (fun R ↦ liftFn f ((diagN (P := D.nonInducedPlaces) (D.InitIndex (2 * i + 1 + 1))
            (D.nonInducedPlaces \ D.piNPlaces)).val * R)) (v (2 * i + 1))) ψ =
        D.liftCharAtN ϑ (2 * i + 2) (D.n (2 * i + 1))
            (diagN (D.InitIndex (2 * i + 2)) (D.nonInducedPlaces \ D.piNPlaces)) •
          (D.formRepAtN (2 * i + 1 + 1)).ρ diagNInv (D.liftAtN ϑ (2 * i + 1) (v (2 * i + 1))
            (liftFn f) (ρ (D.diagPointN (2 * i + 1)) ψ)) := by
    -- The matrix `diagN` for all of `Σ_N` is the one moved here times the one of `δ_{2i+2}`.
    simpa [ρ, liftAtN_apply, conjEmbedGL, diagN_eq_sdiff_mul D.piNPlaces] using
      D.lift_schrodingerOpAt_comp ϑ _ _ f 1 (diagN _ (D.nonInducedPlaces \ D.piNPlaces))⁻¹ ψ
  -- The glued datum is a sum over `y` of tensors of the two kinds of data treated above.
  refine LinearMap.ext fun φ ↦ ?_
  rw [gluedDoubleLiftDatum,
    D.isSplitLevel_nonInducedPlaces.doubleLiftGluing_eq_sum_schrodingerOpAt
      D.isSplitLevel_piNPlaces]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_sum,
    TensorChain.liftInPairs_tmul, lastColDatum, charDatum, h_first, h_second]
  simp [ρ.self_inv_apply, gluedFactor, smul_smul, Units.smul_def]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- **All lifts become direct.** Let `m = 2 (ϱ + 1)` be the number of lifts, `f` the number of
infinite places of `E` and `b` the weight of the data `D`. There is a scalar `c` with
`‖ιₚ c‖ ≤ N ^ (m f b)` such that the following holds for all finite data `v j` of
`Hom (X_j, X_{j+1})` and all forms `φ` on `X_0` of level `levelX 0` that are ramified. The composite
`doubleLiftChain` of the `ϱ + 1` double lifts, whose data are glued from the projections of the
`v j` on the vacuum above `N`, sends `φ` to `c` times the image of `Up ^ (ϱ + 1) φ` under the
composite `chain` of the `m` direct lifts. -/
lemma doubleLiftChain_gluedDoubleLiftDatum_eq_smul_chain : ∃ c : ℂ,
    ‖ιₚ c‖ ≤ D.N ^ (D.m * D.f * D.b) ∧
    ∀ (v : ∀ j : ℕ, (D.homX j).finitePart) (φ : D.SourceForm), φ ∈ D.ramifiedSourceForms →
      doubleLiftChain (D.liftKernel ϑ)
          (D.gluedDoubleLiftDatum fun j : ℕ ↦ Space.vacuumProjFinPart (homX j) D.piNPlaces (v j))
            (D.ϱ + 1) φ =
        c • chain (D.liftKernel ϑ) (fun j : ℕ ↦ D.schrodingerOpAtN ϑ j directDatum (v j))
          (2 * (D.ϱ + 1))
          ((upOperator (D.formRepAtN 0) ^ (D.ϱ + 1)) φ) := by
  refine ⟨∏ i ∈ range (D.ϱ + 1), D.gluedFactor ϑ i *
    #(primitiveVectors (P := D.nonInducedPlaces) (N := D.N) (D.X (2 * i + 1))) •
      ∏ l ∈ range (2 * i + 2), (D.upCommutationFactor ϑ l : ℂ), ?_, fun v φ h_ram ↦ ?_⟩
  · -- Only the numbers `gluedFactor` can have negative valuation.
    have h_upCommutationFactor_le (j : ℕ) : ‖ιₚ (D.upCommutationFactor ϑ j)‖ ≤ 1 := by
      simpa [upCommutationFactor, div_le_one₀, field] using
        norm_detCharAt_diagN_anti (D.n_mono j.le_succ)
    have h_gluedFactor_le (i : ℕ) (hi : i ∈ range (D.ϱ + 1)) :
        ‖ιₚ (D.gluedFactor ϑ i)‖ ≤ D.N ^ (2 * D.f * D.b) :=
      D.norm_gluedFactor_le ϑ (mem_range_succ_iff.1 hi)
    have h_exp : (D.m : ℝ) * D.f * D.b = 2 * D.f * D.b * (D.ϱ + 1) := by
      push_cast [D.m_eq_two_mul_varrho_add_two]
      ring
    simp only [map_prod, map_mul, norm_prod, norm_mul, nsmul_eq_mul, map_natCast]
    grw [h_gluedFactor_le _ (by assumption), IsUltrametricDist.norm_natCast_le_one,
      h_upCommutationFactor_le]
    simp [h_exp, ← rpow_mul_natCast]
  · rw [doubleLiftChain, funext (D.liftInPairs_gluedDoubleLiftDatum ϑ v)]
    -- The direct lifts are the lifts `D.liftAtN ϑ j (v j) directDatum` by definition.
    exact compUpTo_gluedLift_eq_smul D.formRepAtN (fun j ↦ D.liftLaw_liftAtN ϑ j (v j))
      (D.mem_ramified_of_mem_ramifiedSourceForms h_ram) (D.ϱ + 1)

end ChainAtLevel

section ValuationAtLevel

open Real Matrix GeneralLinearGroup IsSplitLevel Function

variable {P : Parameters} (D : Data P) [PadicPlace D.N]

/-- Let `π` be the integer of `E` with `π π̄ = N`, and let `ω` be the Weil action of the finite
unitary groups of `X_j` and `X_{j+1}` on the finite data `v` of the theta kernel
`D.liftKernel ϑ j`. The operator `D.schrodingerOpAtN ϑ j directDatum` puts on `v`, at
`Σ_N = D.nonInducedPlaces`, the indicator of the integral matrices whose last column is the last
basis vector modulo `N`, in bases of the lattices `L_j`, `L_{j+1}` of integral vectors with last
coordinate divisible by `π`. It commutes with `ω (a, b)` for `a`, `b` in the levels `levelX` of
`X_j` and `X_{j+1}`, whose elements have last row congruent to `(0, …, 0, 1)` modulo `π`. -/
lemma omega_schrodingerOpAtN_directDatum (ϑ : D.TameChar) (j : ℕ) (v : (D.homX j).finitePart)
    (a : D.levelX j) (b : D.levelX (j + 1)) :
    (D.liftKernel ϑ j).ω (a, b) (D.schrodingerOpAtN ϑ j directDatum v) =
      D.schrodingerOpAtN ϑ j directDatum ((D.liftKernel ϑ j).ω (a, b) v) := by
  -- In bases of `L_j` and `L_{j+1}`, the parts `part a` and `part b` of `a` and `b` at `Σ_N`
  -- stabilise the standard marked lattices, so they fix the direct datum.
  let part {i : ℕ} (k : D.levelX i) : GL (D.X i) (LocProd D.nonInducedPlaces) :=
    atPlaces D.nonInducedPlaces ((D.diagPointN i)⁻¹ * k.1 * D.diagPointN i)
  have h_fix (S : Matrix (D.X (j + 1)) (D.X j) (LocProd D.nonInducedPlaces)) :
      directDatum ((part b)⁻¹.1 * S * (part a).1) = directDatum S :=
    directDatum_mul_mul_of_mem_mirabolic (D.atPlaces_conj_mem_mirabolic a)
      (D.atPlaces_conj_mem_mirabolic b) S
  -- Move the points `δ_j = diagPointN j` and `δ_{j+1}` into the function; the factor is the same
  -- on both sides. After `simp` the goal is an equation of two operators applied to `v`.
  ext1
  simp [schrodingerOpAtN, liftKernel_ω, directDatum, lastColDatum, pairWeilFinite_schrodingerOpAt,
    smul_left_cancel_iff, -coe_units_inv]
  dsimp [schrodingerOpAt, comp_def]
  -- The integral pair `(a, b)` passes through the operator and acts on its function.
  have h_int {i : ℕ} (k : D.levelX i) : k.1 ∈ stdLevel D.E (D.X i) :=
    levelOf_le_stdLevel (D.mem_levelX.1 k.2).1
  rw [pairWeil_schrodingerOp_of_mem isConjDisjoint (hΨ := isSchwartzBruhat_liftFn_mul ..) (h_int a)
    (h_int b)]
  refine congrArg (Space.schrodingerOp _ _ · _)
    (funext fun x ↦ .trans (congrArg directDatum ?_) (h_fix _))
  have h_left : (b.1.1.1)⁻¹.map (evalPlaces D.nonInducedPlaces) =
      (atPlaces D.nonInducedPlaces b.1).1⁻¹ := by
    rw [← coe_units_inv (atPlaces _ _), ← map_inv, ← coe_units_inv b.1.1]
    rfl
  have h_right : a.1.1.1.map (evalPlaces _) = (atPlaces D.nonInducedPlaces a.1).1 := rfl
  simp [part, h_left, h_right, Matrix.mul_assoc, -val_map_apply]

/-- **Direct lifts lose little.** For `j < m`, the direct datum at `Σ_N`, in bases of `L_j` and
`L_{j+1}`, on a translate of the integral vacuum raises `N`-adic gauges from
`δ_j = D.diagPointN j` to `δ_{j+1}` by a factor at most `N ^ (f b)`. -/
lemma schrodingerOpAtN_directDatum_mem_raises (ϑ : D.TameChar) (x : D.Translations) {j : ℕ}
    (hj : j < D.m) :
    D.schrodingerOpAtN ϑ j directDatum (D.translateDatum x j) ∈
      (D.liftKernel ϑ j).raises (p := D.N) (D.diagPointN j) (D.diagPointN (j + 1))
        (D.N ^ (D.f * D.b)) := by
  -- The datum is the translate by `(δ_j, δ_{j+1})` of one that raises gauges from `1` to `1`.
  rw [← mul_one (D.diagPointN j), ← mul_one (D.diagPointN (j + 1)), schrodingerOpAtN,
    LinearMap.comp_apply,
    Kernel.omega_mem_raises_iff]
  exact D.schrodingerOpAt_directDatum_mem_raises ϑ x hj

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- **The prime `N`, valuation.** Let `m` be the number of lifts, `f` the number of infinite places
of `E`, `b` the weight and `M` the principal level of the data `D`. Let `ϑ` be a twist, a character
of `U(1)` of weight `0` whose tame part is non-trivial exactly on the finite set `ϑ.Q` of places,
and let `q` be the product of their norms. Let `Ψ` be a chain datum for `ϑ`: a finitely supported
function on the tuples of finite adelic matrices by which the integral vacua of the
`Hom (X_j, X_{j+1})` are translated, supported on admissible tuples that vanish at the places prime
to `M q`, with values integral away from `q` (and bounded in size if `ϑ.Q` is empty), whose glued
tensor is fixed by the levels of `X_0, …, X_{m-1}`. Let `φ` be a ramified source form on `X_0` in
`upIntegralForms`: `Up ^ (m / 2) φ`, for the operator `Up = upOperator`, is a source form with
values integral for the lattice `L_0`. The composite lift of `φ` is the chain of double lifts by the
glued tensor of `Ψ`, restricted from `X_m` to `Y_m`. Then at every point `g` its value, moved by
`g⁻¹`, has coordinates of `N`-adic absolute value at most `N ^ (2 m f b)`. -/
lemma gaugeLe_compositeLift_at_N {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ} (hΨ : IsChainDatum ϑ Ψ)
    {φ : D.SourceForm} (hφ_ramified : φ ∈ D.ramifiedSourceForms)
    (hφ_integral : φ.val ∈ D.upIntegralForms) :
    GaugeLe (p := D.N) 1 (D.N ^ (2 * D.m * D.f * D.b)) (compositeLift ϑ Ψ φ) := by
  let ψ₀ : D.FormX 0 := (upOperator (D.formRepAtN 0) ^ (D.ϱ + 1)) φ
  obtain ⟨h_source, h_integral⟩ : ψ₀ ∈ D.SourceForm ∧ GaugeLe (D.diagPointN 0) 1 ψ₀ := hφ_integral
  let ψ : D.SourceForm := ⟨ψ₀, h_source⟩
  let direct (x : D.Translations) (j : ℕ) : (D.homX j).finitePart :=
    D.schrodingerOpAtN ϑ j directDatum (D.translateDatum x j)
  -- All lifts become direct, at the cost of a scalar `c` and of replacing `φ` by `ψ`.
  obtain ⟨c, hc, h_chain⟩ := D.doubleLiftChain_gluedDoubleLiftDatum_eq_smul_chain ϑ
  have h_term (x : D.Translations) (hx : x ∈ Ψ.support) :
      chainOfTensor ϑ φ (D.gluedVacuum x) =
        c • chain (D.liftKernel ϑ) (direct x) (2 * (D.ϱ + 1)) ψ := by
    rw [← h_chain (D.translateDatum x) φ hφ_ramified,
      funext (D.vacuumProjFinPart_translateDatum ϑ (hΨ.mem_admissibleTranslations hx))]
    exact TensorChain.lift_pure ..
  have h_sum : chainOfTensor ϑ φ (gluedTensor Ψ) =
      c • chainCombination ϑ Ψ direct (2 * (D.ϱ + 1)) ψ := by
    simp +contextual only [gluedTensor, Finsupp.sum, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, Finset.smul_sum, smul_comm c, h_term]
  have h_compositeLift_eq :
      compositeLift ϑ Ψ φ = D.restrictToY (c • chainCombination ϑ Ψ direct D.m ψ) := by
    rw [compositeLift, h_sum]
    exact restrictToYOfEq_apply (l := 2 * (D.ϱ + 1)) _ fun j ↦ c • chainCombination ϑ Ψ direct j ψ
  -- Each of the `m` direct lifts loses at most `f b`.
  have h_direct : GaugeLe (D.diagPointN D.m) (D.N ^ ∑ _ ∈ Finset.range D.m, D.f * D.b)
      (chainCombination ϑ Ψ direct D.m ψ) :=
    hΨ.isWeakChainDatum.gaugeLe_chain ϑ.coprime.coprime_mul_left
      (fun j ↦ D.schrodingerOpAtN ϑ j directDatum)
      (fun j _ _ a b hb ↦ D.omega_schrodingerOpAtN_directDatum ϑ j _ a ⟨b, hb⟩) D.diagPointN
      (fun x _ _ hj ↦ D.schrodingerOpAtN_directDatum_mem_raises ϑ x hj) h_integral
  -- A bound at `D.diagPointN D.m` gives the same bound for the restriction at `1`: the change of
  -- lattice cancels the normalising division in the restriction map.
  rw [h_compositeLift_eq]
  refine GaugeLe.restrictToY_of_diag D (D.map_adeleExtension_diagPoint _ _) fun g ↦ ?_
  calc _ = ‖ιₚ c‖ * weylGauge _ (D.lastEntry D.m) (g * D.diagPointN D.m)
          ((chainCombination ϑ Ψ direct D.m ψ).1 g) := weylGauge_smul ..
    _ ≤ D.N ^ (D.m * D.f * D.b) * D.N ^ ∑ _ ∈ Finset.range D.m, D.f * D.b := by
      grw [h_direct g, hc]
    _ = D.N ^ (2 * D.m * D.f * D.b) := by
      simp [← rpow_add (Nat.cast_pos.2 D.N_prime.pos), two_mul, add_mul, mul_assoc]

end ValuationAtLevel

end New.Data
