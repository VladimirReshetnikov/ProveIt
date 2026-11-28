import New.Spanning.Frames.FixedLines
import New.Spanning.MainTerm.SiegelTopBound

/-!
# The sieve system at the finite places

The finite half of the input of the sieve `New.Filling.sieve`.

* `New.Filling.IsFillingData.exists_intermediateGroup_sieveSystem`: read the completions at a finite
  set `T` of places as one ring `LocProd T`. There is a subgroup `Z` of the unitary group over it
  that contains the components at `T` of the integral elements fixing given vectors at a set `Sg` of
  chosen places, and for which the forms `New.Floors.PlaceData.floorForm` and the density
  `New.Floors.PlaceData.lastEntryDensity`, divided by `Z.massRatio`, satisfy `New.SieveSystem`.

The subgroup is that of `New.Filling.IsFillingData.exists_intermediateGroup_norm_floorForm_div_le`,
which bounds the form of floor `0`: it saves the power `b ^ (6 * 𝔰.k)` of the base `b` of the
filling for each place in a given set `Sg` of chosen places.

Notions from other files:
* `New.Filling.IsAdmissible`: the standing hypotheses on the level and the sizes of a filling `S`.
* `New.Filling.IsFillingData`: `F` is a large lattice datum over `LocProd T`, its modulus
  `g = F.levelUnit` is the component at `T` of `S.ideleM` (the product `S.M` of the two level primes
  as a finite idele), and the character is that of `S` at `T`.
* `New.Floors.PlaceData.massIntegral`: `ϰ(Z) = ∫ |∫_Z phase(y x y⁻¹) dy| ^ 2 dx`.
* `New.Floors.PlaceData.IntermediateGroup.massRatio`: `vol(Z) vol(K(g)) / unipotentMass ^ 2`, where
  `vol` is `New.Floors.PlaceData.groupMeasure` and `Z` lies between `K(g)` and the integral points.
* `New.SieveSystem`: the recursion, positivity, continuity and bounds that the sieve asks of a
  family of forms at a place.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

namespace New.Filling

open Finset ComplexOrder MeasureTheory Floors ENNReal PlaceData IntegralPlace.IsLargeLatticeData

/-- Let `S` be admissible filling data over the CM field `E`. Let `b = S.b` be the real number in
whose powers sizes are measured, `M = S.M` the product of the two level primes, `f = numInfPlaces E`
the number of infinite places, and `n = 𝔰.n = ϱ + 1` with `ϱ` the number of hyperbolic planes. Then
`(2 (M ^ f) ^ 2) ^ (n ^ 6) ≤ b ^ (n ^ 9 * f)`. -/
lemma two_mul_M_pow_sq_pow_le {E : Type} {𝔰 : Shape} [Field E] [CMType E] [WeilData E]
    (S : Filling E 𝔰) [S.IsAdmissible] :
    (2 * ((S.M : ℝ) ^ numInfPlaces E) ^ 2) ^ 𝔰.n ^ 6 ≤ S.b ^ (𝔰.n ^ 9 * numInfPlaces E) := by
  have one_le_b : 1 ≤ S.b := S.one_le_b
  have exponent_le : 46 * numInfPlaces E + 1 ≤ 𝔰.n ^ 3 * numInfPlaces E := by
    grw [Shape.n, ← S.ten_pow_five_le_varrho]
    grind [S.k_le_f, S.pow_chain]
  calc
    _ ≤ (S.b * ((S.b ^ 23) ^ numInfPlaces E) ^ 2) ^ 𝔰.n ^ 6 := by
      grw [S.M_le_b_pow, show 2 ≤ S.b by linarith [S.thousand_le_b]]
    _ = S.b ^ ((46 * numInfPlaces E + 1) * 𝔰.n ^ 6) := by ring
    _ ≤ S.b ^ (𝔰.n ^ 3 * numInfPlaces E * 𝔰.n ^ 6) := by gcongr
    _ = S.b ^ (𝔰.n ^ 9 * numInfPlaces E) := by ring

/-- Let `S` be admissible filling data, `T` a conjugation-stable finite set of finite places, and
`F` a filling datum at `T`: measures and a modulus `g` for the unitary group `G` of the hermitian
form of `S` over the product `LocProd T` of the completions. Let `K` be the group of integral points
of `G`, `K(g) = F.congruenceSubgroup` its principal congruence subgroup and `vol = F.groupMeasure`
the Haar measure. Then `F.massIntegral K = ∫_G |∫_K χ(y x y⁻¹) dy| ^ 2 dx`, with
`χ = phase F.levelUnit` the generic character of the unipotent group `U` extended to `U K(g)` and by
zero, is at most `vol(K) vol(K(g)) (1 + b⁻¹ ^ 6)`, where `b = S.b` is the size parameter of `S`. -/
lemma IsFillingData.massIntegral_full_le {E : Type} {𝔰 : Shape} [Field E] [CMType E] [WeilData E]
    {S : Filling E 𝔰} [S.IsAdmissible] {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) :
    let K := unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram
    F.massIntegral K ≤
      F.groupMeasure K * F.groupMeasure F.congruenceSubgroup * .ofReal (1 + S.b⁻¹ ^ 6) := by
  intro K
  obtain ⟨-, h_box : F.boxSet = K, -⟩ := hF.volume_le_and_boxSet_closePairs_positions_eq
  -- `massIntegral_le_main_add_error` for `Z = K` and `Q = 2`
  have h_main_term : F.massIntegral K ≤
      F.groupMeasure K * F.groupMeasure F.congruenceSubgroup * (F.groupMeasure K + 2⁻¹ ^ 𝔰.n) :=
    massIntegral_le_main_add_error ⟨K, P.unitaryLevel_le_unitaryLevel_one, le_rfl⟩ le_rfl
      modulus_le_half (by grind [S.pow_chain, Nat.le_self_pow (n := 4) (by norm_num) 𝔰.n])
  grw [h_main_term, ← half_pow_le_inv_pow_six]
  gcongr
  calc F.groupMeasure K + 2⁻¹ ^ 𝔰.n
      ≤ .ofReal (1 + 2⁻¹ ^ 𝔰.n) + 2⁻¹ ^ 𝔰.n := by grw [← h_box, hF.groupMeasure_boxSet_le]
    _ = .ofReal (1 + 2⁻¹ ^ 𝔰.ϱ) := by
      simp [ofReal_add, pow_succ, add_assoc, ← mul_add, inv_two_add_inv_two, -inv_pow]

/-- Let `Z` be a group between the congruence subgroup of the place datum `F` and the integral
points, and let `c = Z.massRatio` be its normalising constant in `ℝ≥0∞`. A bound `‖x‖ₑ ≤ c * D` with
`D` finite gives `‖x / c.toReal‖ ≤ D.toReal`. -/
lemma norm_div_massRatio_le {E : Type} {𝔰 : Shape} [Field E] [CMType E] [WeilData E]
    {S : Filling E 𝔰} {T : Finset (FinPlace E)} [T.StarStable] {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (Z : F.IntermediateGroup) {x : ℂ} {D : ℝ≥0∞} (hD : D ≠ ∞)
    (h_le : ‖x‖ₑ ≤ Z.massRatio * D) : ‖x / Z.massRatio.toReal‖ ≤ D.toReal := by
  simpa using toReal_mono hD (div_le_of_le_mul' h_le : ‖x‖ₑ / Z.massRatio ≤ D)

/-- Let `F` be a filling datum with modulus `g = F.levelUnit` on the unitary group over `LocProd T`,
the product of the completions at `T`, with integers `O`; let both level primes be units off `T`.
Let `Z` lie between `K(g)` and the integral points, `j ≤ ϱ`, let `p`, `q` be sequences of units and
`ξ` a unit. Let the weight `ω` be either `x ↦ P.ψ (ξ * G x j j)`, with `P.ψ` the additive character
of the place and `G x` the matrix of products of the frame with its image under `x`, or the constant
`1` with `j = i + 1` and `ξ = g⁻¹ * ((p i)⁻¹ - (q i)⁻¹)`. Take the orbital integral
`F.floorForm j p q` of floor `j` of `Z.besselVector` and divide it by `Z.massRatio = vol(Z)
vol(K(g)) / F.unipotentMass ^ 2`. The norm is at most `S.frequencyDecay T ξ = [O : ξ O] ^ ((k -
n⁷) / 2) / [O : O ∩ ξ⁻¹ O] ^ 3 * b ^ (n⁹ f)` times the weights `finHeadWeight (n ^ 6) j` of `p` and
`q`; that of `p` is the product over `l < j` of `[O : D O] ^ (n⁶ / 2)` for `D = p 0 * ⋯ * p l`, and
`0` if some `D` is not integral. Here `n = 𝔰.n = ϱ + 1`, `k = 𝔰.k`, `b = S.b`, `f` is the number of
infinite places, and `[O : ξ O]` is the generalised index `genIndex ξ`. -/
lemma IsFillingData.norm_floorForm_div_massRatio_le {E : Type} {𝔰 : Shape} [Field E] [CMType E]
    [WeilData E] {S : Filling E 𝔰} [S.IsAdmissible] {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] (Z : F.IntermediateGroup)
    {j : ℕ} {p q : ℕ → (LocProd T)ˣ}
    {ξ : LocProd T} {ω : (S.latticeMiddle (LocProd T)).G → ℂ} (hj : j ≤ 𝔰.ϱ) (hξ : IsUnit ξ)
    (hω : (ω = fun x : (S.latticeMiddle (LocProd T)).G ↦
        P.ψ (ξ * ((S.latticeMiddle (LocProd T)).frameGram x.1.1).diag ⟨j, by lia⟩)) ∨
      ∃ i : ℕ, j = i + 1 ∧ ω = 1 ∧ ξ = F.levelUnit⁻¹.1 * ((p i)⁻¹.1 - (q i)⁻¹.1)) :
    ‖F.floorForm j p q Z.besselVector ω / Z.massRatio.toReal‖ ≤
      S.frequencyDecay T ξ * (finHeadWeight (𝔰.n ^ 6) j p * finHeadWeight (𝔰.n ^ 6) j q) := by
  obtain ⟨pow_four_le, half_pow_le_inv_pow_six, pow_seven_le⟩ : 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.n ^ 6 ∧
    3 * 𝔰.n ^ 6 + 12 ≤ 𝔰.n ^ 7 ∧ 𝔰.n ^ 7 ≤ 𝔰.k := S.pow_chain
  have h_bound : ‖F.floorForm j p q Z.besselVector ω‖ₑ ≤ Z.massRatio *
      (.ofReal √(genIndex ξ) ^ (𝔰.k - 𝔰.n ^ 7) * (denomIndex P.integers ξ : ℝ≥0∞)⁻¹ ^ 6 *
        (2 / P.modulus F.levelUnit) ^ 𝔰.n ^ 6 *
          .ofReal (finHeadWeight (𝔰.n ^ 6) j p * finHeadWeight (𝔰.n ^ 6) j q)) :=
    enorm_floorForm_le (ξ := hξ.unit) Z (𝔰.k - 𝔰.n ^ 7) hj (by omega) pow_four_le hω
  -- `frequencyDecay` keeps only the third power of the index of the denominator
  have h_cube : (denomIndex P.integers ξ : ℝ≥0∞)⁻¹ ^ 6 ≤ (denomIndex P.integers ξ : ℝ≥0∞)⁻¹ ^ 3 :=
    pow_le_pow_right_of_le_one' (by simp [Nat.one_le_iff_ne_zero, denomIndex_ne_zero]) (by norm_num)
  grw [h_cube] at h_bound
  grw [norm_div_massRatio_le Z (by simp [denomIndex_ne_zero, mul_eq_top, div_eq_top]) h_bound]
  -- the factors agree one by one, except the power of `2 / modulus F.levelUnit = 2 (S.M ^ f) ^ 2`
  -- (`modulus_levelUnit`), which is bounded by `two_mul_M_pow_sq_pow_le`
  simp (disch := positivity) [-Nat.cast_mul, modulus_levelUnit, frequencyDecay, finHeadWeight,
    -map_prod]
  gcongr _ * ?_ * _
  exact S.two_mul_M_pow_sq_pow_le

/-- Let `F` be a filling datum with modulus `g` on the unitary group `G` over the completions at
`T`, and let `Z` lie between the congruence subgroup `K(g)` and the integral points. Take the
orbital integral `F.floorForm 0` of `Z.besselVector`, the vector of the translates of the generic
character `χ = phase F.levelUnit` by the cosets of `K(g)` in `Z`. Its norm times the square of
`F.unipotentMass` is at most `F.massIntegral Z = ∫_G |∫_Z χ(y x y⁻¹) dy| ^ 2 dx`. -/
lemma IsFillingData.enorm_floorForm_zero_mul_le {E : Type} {𝔰 : Shape} [Field E] [CMType E]
    [WeilData E] {S : Filling E 𝔰} [S.IsAdmissible] {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Z : F.IntermediateGroup) (p q : ℕ → (LocProd T)ˣ) :
    ‖F.floorForm 0 p q Z.besselVector 1‖ₑ * F.unipotentMass ^ 2 ≤ F.massIntegral Z := by
  -- Both sides are integrals of `|k₀|²`, up to the factor `F.unipotentMass ^ 2`.
  let k₀ (z : (S.latticeMiddle (LocProd T)).G) : ℂ :=
    F.partialCorrelation 0 (frameCorrelation Z.besselVector 1) 1 z
  have h_form : ‖F.floorForm 0 p q Z.besselVector 1‖ₑ ≤ ∫⁻ z, ‖k₀ z‖ₑ ^ 2 ∂F.groupMeasure := by
    rw [floorForm_zero_eq_integral hF.gauge (isCut_besselVector Z), ← integral_complex_ofReal]
    exact (enorm_integral_le_lintegral_enorm _).trans_eq (by simp [k₀, ← ofReal_norm])
  have h_floorZeroForm_eq :
      F.massIntegral Z = ∫⁻ z, ‖k₀ z‖ₑ ^ 2 * F.unipotentMass ^ 2 ∂F.groupMeasure := by
    simp only [massIntegral, enorm_integral_extendedBesselChar_eq_enorm_mul, mul_pow, k₀]
  grw [h_form, h_floorZeroForm_eq, lintegral_mul_const_le]

/-- Let `F` be a filling datum with modulus `g` on the unitary group `G` over the completions at
`T`, `K` the integral points, `vol = F.groupMeasure` the Haar measure, and `K(g) ≤ Z ≤ K`. Write
`ϰ(Z) = F.massIntegral Z = ∫_G |∫_Z χ(y x y⁻¹) dy| ^ 2 dx` with `χ = phase F.levelUnit` the generic
character, `b = S.b` for the size parameter and `k = 𝔰.k` for the rank of the definite summand. If
`ϰ(Z) vol(K) (b ^ (6 k)) ^ s ≤ ϰ(K) vol(Z)` for a natural number `s`, then the orbital integral
`F.floorForm 0` of `Z.besselVector`, divided by `Z.massRatio = vol(Z) vol(K(g)) / F.unipotentMass ^
2`, has norm at most `(1 + b⁻¹ ^ 6) / (b ^ (6 k)) ^ s`. -/
lemma IsFillingData.norm_floorForm_zero_div_massRatio_le {E : Type} {𝔰 : Shape} [Field E]
    [CMType E] [WeilData E] {S : Filling E 𝔰} [S.IsAdmissible] {T : Finset (FinPlace E)}
    [T.StarStable] {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Z : F.IntermediateGroup) (s : ℕ)
    (h_floorZeroForm_le : let K := unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram
      F.massIntegral Z * F.groupMeasure K * .ofReal (S.b ^ (6 * 𝔰.k)) ^ s ≤
        F.massIntegral K * F.groupMeasure Z)
    (p q : ℕ → (LocProd T)ˣ) :
    ‖F.floorForm 0 p q Z.besselVector 1 / Z.massRatio.toReal‖ ≤
      (1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ s := by
  let K := unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram
  let vol : Measure (S.latticeMiddle (LocProd T)).G := F.groupMeasure
  have one_le_b : 1 ≤ S.b := S.one_le_b
  have h_cleared : ‖F.floorForm 0 p q Z.besselVector 1‖ₑ * F.unipotentMass ^ 2 *
        .ofReal (S.b ^ (6 * 𝔰.k)) ^ s * vol K ≤
      vol Z * vol F.congruenceSubgroup * .ofReal (1 + S.b⁻¹ ^ 6) * vol K := calc
    _ ≤ F.massIntegral Z * vol K * .ofReal (S.b ^ (6 * 𝔰.k)) ^ s := by
      grw [hF.enorm_floorForm_zero_mul_le, mul_right_comm]
    _ ≤ F.massIntegral K * vol Z := h_floorZeroForm_le
    _ ≤ vol K * vol F.congruenceSubgroup * .ofReal (1 + S.b⁻¹ ^ 6) * vol Z :=
      mul_le_mul_left hF.massIntegral_full_le _
    _ = vol Z * vol F.congruenceSubgroup * .ofReal (1 + S.b⁻¹ ^ 6) * vol K := by ring
  refine (norm_div_massRatio_le Z ofReal_ne_top ?_).trans_eq (toReal_ofReal (by positivity))
  -- clear the denominators and multiply by `vol K`, which is finite and nonzero
  rwa [ofReal_div_of_pos (by positivity), IntermediateGroup.massRatio,
    ← ENNReal.mul_div_mul_comm (by simp) (by simp),
    ENNReal.le_div_iff_mul_le (by simp; left; positivity) (by simp [mul_eq_top]),
    ← ENNReal.mul_le_mul_iff_left (P.unitaryLevel_open_compact.1.measure_ne_zero _ (by simp))
      (hF.groupMeasure_ne_top le_rfl : vol K ≠ ∞), ← mul_assoc, ofReal_pow (by positivity)]

/-- Let `S` be admissible and `F` a filling datum (a large lattice datum on the unitary group over
the completions at `T`, whose modulus `g` is the component of `S.ideleM`, the product of the two
level primes of `S`), and let `S.ideleM⁻¹` be integral off `T`. Let `Sg` be a set of chosen places
above the first level prime, and for each such place `w` let `d w` be a nonzero vector of the span
of the frame modulo `w` or its conjugate. There is a subgroup `Z` between the congruence subgroup
`K(g)` and the integral points such that (a) `Z` contains the component at `T` of each integral
adelic element whose reduction lies in `S.fixer Sg d`, that is, fixes `d w` for all `w ∈ Sg`; (b)
the orbital integral `F.floorForm 0` of `Z.besselVector` (the translates of the generic character by
the cosets of `K(g)` in `Z`), divided by `Z.massRatio = vol(Z) vol(K(g)) / F.unipotentMass ^ 2`, is
a real number between `0` and `(1 + b⁻¹ ^ 6) / (b ^ (6 k)) ^ #Sg`, where `b = S.b` is the size
parameter and `k = 𝔰.k` the rank of the definite summand. -/
theorem IsFillingData.exists_intermediateGroup_norm_floorForm_div_le {E : Type} {𝔰 : Shape}
    [Field E] [CMType E]
    [WeilData E] {S : Filling E 𝔰} [S.IsAdmissible] {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Sg : Finset (S.chosenPlaces 0))
    (d : ∀ w : S.chosenPlaces 0, S.FrameVector w) [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] :
    ∃ Z : F.IntermediateGroup,
      (∀ k : S.latticeStabilizer, S.reduction k ∈ S.fixer Sg d → S.toPlaces T k ∈ Z.val) ∧
      ∀ p q : ℕ → (LocProd T)ˣ,
        0 ≤ F.floorForm 0 p q Z.besselVector 1 / Z.massRatio.toReal ∧
        ‖F.floorForm 0 p q Z.besselVector 1 / Z.massRatio.toReal‖ ≤
          (1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ #Sg := by
  obtain ⟨Z, h_mem, h_floorZeroForm_le⟩ := hF.exists_intermediateGroup_places Sg d Fact.out
  refine ⟨Z, h_mem, fun p q ↦
    ⟨?_, hF.norm_floorForm_zero_div_massRatio_le Z #Sg h_floorZeroForm_le p q⟩⟩
  rw [floorForm_zero_eq_integral hF.gauge (isCut_besselVector Z), ← Complex.ofReal_div]
  positivity

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `F` be a filling datum on the unitary group over the completions at `T`, and let `Z` lie
between its congruence subgroup and the integral points. Let `S.piNAt T` be the component at `T` of
the idele `π_N` with `π π̄ = N`, where `N = S.N` is the split rational prime of `S`. For sequences
of units `p`, `q`, the density `F.lastEntryDensity (S.piNAt T) Z p q` integrates the pairing of the
scaled orbital integrals of `p` and `q` over the vectors of the top quadric with last entry `p ϱ`.
On finitely many sequences `a i` with the same entry `t` at position `ϱ = 𝔰.ϱ`, the number of
hyperbolic planes, it is a positive semidefinite matrix. -/
lemma IsFillingData.posSemidef_lastEntryDensity {E : Type} {𝔰 : Shape} [Field E] [CMType E]
    [WeilData E] {S : Filling E 𝔰} [S.IsAdmissible] {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Z : F.IntermediateGroup) {κ : Type} [Fintype κ]
    (a : κ → ℕ → (LocProd T)ˣ) (t : (LocProd T)ˣ) (ha : ∀ i : κ, a i 𝔰.ϱ = t) :
    (Matrix.of fun i j : κ ↦ F.lastEntryDensity (S.piNAt T) Z (a i) (a j)).PosSemidef := by
  classical
  refine ⟨.ext fun i j ↦ ?_, fun x ↦ ?_⟩
  · -- the pairing is Hermitian
    simp [lastEntryDensity, fiberPairing, ← integral_conj, apply_dite, ha]
  · -- the quadratic form of `x` is the integral of a nonnegative function
    have h_nonneg : 0 ≤ ∑ i : κ, ∑ j : κ,
        Matrix.vecMulVec (star ⇑x) ⇑x i j * F.lastEntryDensity (S.piNAt T) Z (a i) (a j) :=
      sum_lastEntryDensity_nonneg Z piNAt_mul_star (Matrix.posSemidef_vecMulVec_star_self x) a ha
    simpa [x.sum_fintype, Matrix.vecMulVec_apply, mul_right_comm] using h_nonneg

/-- Let `F` be a filling datum of admissible data `S` on the unitary group over `LocProd T`, the
product of the completions at the finite places `T`. Its modulus `g = F.levelUnit` is the component
at `T` of `S.ideleM`, the product `M = S.M` of the two level primes as a finite idele; let
`S.ideleM⁻¹` be integral off `T`. Let `Sg` be a set of chosen places above the first level prime and
`d w` a nonzero vector of the span of the frame modulo `w` or its conjugate. There is a subgroup `Z`
between the congruence subgroup `K(g)` and the integral points such that (a) `Z` contains the
component at `T` of each integral adelic element whose reduction lies in `S.fixer Sg d`, that is,
fixes `d w` for all `w ∈ Sg`; (b) the forms `J j p q` in two sequences of units, given by the
orbital integral `F.floorForm j` for `j ≤ ϱ` (the number of hyperbolic planes) and by the density
`F.lastEntryDensity` at the prime `S.piNAt T` above `S.N` for `j > ϱ`, divided by the ratio of
volumes `Z.massRatio`, are a `SieveSystem`. That is: `J j` is the integral of `J (j + 1)` over a
common entry `unitOrOne c` at position `j ≤ ϱ`; the same integral twisted by `ψ (ξ * c)` at a unit
`ξ`, and also `J (j + 1) p q` if `j < ϱ` and `ξ = M⁻¹ (p j)⁻¹ - M⁻¹ (q j)⁻¹` is a unit, are bounded
by `S.frequencyDecay T ξ` times the weights `finHeadWeight (n ^ 6)` of `p` and `q`; `J (ϱ + 1)` is
continuous, and positive semidefinite on sequences with a common entry at `ϱ`; and
`‖J 0 p q‖ ≤ (1 + b⁻¹ ^ 6) / (b ^ (6 k)) ^ #Sg`. Here `ψ = S.charOnPlaces T` is the additive
character of `S` restricted to `T`, `b = S.b` is the size parameter, `n = 𝔰.n = ϱ + 1` and `k = 𝔰.k`
is the rank of the definite summand. -/
lemma IsFillingData.exists_intermediateGroup_sieveSystem {E : Type} {𝔰 : Shape} [Field E] [CMType E]
    [WeilData E] {S : Filling E 𝔰} [S.IsAdmissible] {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Sg : Finset (S.chosenPlaces 0))
    (d : ∀ w : S.chosenPlaces 0, S.FrameVector w) [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] :
    ∃ Z : F.IntermediateGroup,
      -- (a)
      (∀ k : S.latticeStabilizer, S.reduction k ∈ S.fixer Sg d → S.toPlaces T k ∈ Z.val) ∧
      -- (b)
      SieveSystem unitOrOne (fun u : (LocProd T)ˣ ↦ ratToPlaces T S.M⁻¹ * ↑u⁻¹) 𝔰.ϱ
        (fun (j : ℕ) (p q : ℕ → (LocProd T)ˣ) ↦ (if j ≤ 𝔰.ϱ then F.floorForm j p q Z.besselVector 1
          else F.lastEntryDensity (S.piNAt T) Z p q) / Z.massRatio.toReal)
        (S.charOnPlaces T) ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ #Sg)
        (finHeadWeight (𝔰.n ^ 6)) (S.frequencyDecay T) := by
  -- `Z` and the bottom bound come from the bound of floor `0`; the steps are the descent of the
  -- floors below the top and `integral_lastEntryDensity` at the top.
  obtain ⟨Z, h_mem, h_floor_zero⟩ := hF.exists_intermediateGroup_norm_floorForm_div_le Sg d
  obtain ⟨pow_four_le, half_pow_le_inv_pow_six, pow_seven_le⟩ : 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.n ^ 6 ∧
    3 * 𝔰.n ^ 6 + 12 ≤ 𝔰.n ^ 7 ∧ 𝔰.n ^ 7 ≤ 𝔰.k := S.pow_chain
  rw [← hF.psi_eq]
  refine ⟨Z, h_mem, by simp, fun j p q ξ hj ↦ ?step, fun a t ha ↦ ?posSemidef, ?continuous,
    fun p q ↦ ?bottom, fun j p q hj hξ ↦ ?off_diagonal⟩
  case step =>
    -- floor `j` is the integral of floor `j + 1`
    simp_rw [← mul_div_assoc, integral_div, ite_eq_left hj]
    split_ifs with hj'
    · obtain ⟨h_int, h_eq⟩ := hF.gauge.integral_psi_mul_floorForm_succ (p := p) (q := q)
        (isCut_besselVector Z) ⟨j, hj'⟩ 1 ξ (hF.lintegral_formMajorant_ne_top Z 0 hj (by omega))
      simp only [one_mul] at h_int h_eq
      rw [h_eq]
      exact ⟨h_int.div_const _, fun hξ ↦ by simp [hξ, Pi.one_def],
        fun hξ ↦ hF.norm_floorForm_div_massRatio_le Z hj hξ (.inl rfl)⟩
    · obtain rfl : j = 𝔰.ϱ := by omega
      obtain ⟨h_int, h_eq⟩ := integral_lastEntryDensity Z p q piNAt_mul_star ξ
      rw [h_eq]
      exact ⟨h_int.div_const _, fun hξ ↦ by simp [hξ, Pi.one_def],
        fun hξ ↦ hF.norm_floorForm_div_massRatio_le Z hj hξ (.inl rfl)⟩
  case posSemidef =>
    simp only [Nat.not_succ_le_self, ↓reduceIte, div_eq_inv_mul]
    exact .smul (α := ℂ) (hF.posSemidef_lastEntryDensity Z a t ha) (by positivity)
  case continuous =>
    simpa [Function.uncurry_def] using (continuous_lastEntryDensity Z piNAt_mul_star).div_const _
  case bottom => simpa only [ite_eq_left zero_le] using (h_floor_zero p q).2
  case off_diagonal =>
    -- the second case of `norm_floorForm_div_massRatio_le`
    rw [ite_eq_left (Nat.succ_le_of_lt hj)]
    refine hF.norm_floorForm_div_massRatio_le Z hj hξ (.inr ⟨j, rfl, rfl, ?_⟩)
    rw [hF.levelUnit_eq, mul_sub]
    rfl

end New.Filling
